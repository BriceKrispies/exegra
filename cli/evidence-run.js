// The evidence step of `exegra verify`: which test references run, and which recorded results are reused
// (WG-5684, criterion 9: incremental re-verification).
//
// Without a change set every test reference runs. With one, only the evidence of the claims the change re-marks
// (src/core/impact.js, decided in Lean) runs; the result of every other test reference is reused when it was fresh
// on the tree the last verification recorded (its stamp equals the stamp that run recorded), and is recorded again
// on the current tree. A reference without such a result runs.

/** @typedef {import('../src/core/types.js').Model} Model */
/**
 * @typedef {{outcome: 'pass'|'fail'|'skipped'|'not-run', detail?: string, obtained?: 'run'|'reused', ranAt?: string, attempted?: boolean, covers?: string[], coverage?: string}} RunResult
 * @typedef {{id: string, outcome: 'pass'|'fail'|'skipped'|'not-run', detail?: string, ranAt: string, obtained?: 'run'|'reused'|'impact', attempted?: boolean, covers?: string[], coverage?: string, ref?: string}} Run
 */

/**
 * The recorded result that answers a test evidence entity outside a change's impact, or undefined: one recorded
 * fresh on the tree the last verification recorded (its stamp equals the stamp that run recorded).
 * @param {{remark?: Set<string>|null, priorResults?: Record<string, any>, priorStamp?: string|null}} opts
 * @returns {(ev: any) => any}
 */
function keptResultFn(opts) {
  const prior = opts.priorResults ?? {};
  return (ev) => {
    const kept = Object.hasOwn(prior, ev.id) ? prior[ev.id] : undefined;
    return opts.remark && !opts.remark.has(String(ev.data.claim)) && kept && typeof opts.priorStamp === 'string' && kept.stamp === opts.priorStamp
      && (kept.outcome === 'pass' || kept.outcome === 'fail' || kept.outcome === 'not-run') ? kept : undefined;
  };
}

/**
 * The test evidence that executeEvidence will hand to `run`: not answered by a realisation root or by a result
 * kept outside the change's impact. verify batches these before it calls executeEvidence.
 * @param {Model} model @param {{external?: Map<string, any>, remark?: Set<string>|null, priorResults?: Record<string, any>, priorStamp?: string|null}} opts
 * @returns {{id: string, ref: string}[]}
 */
export function pendingTestEvidence(model, opts) {
  const keptOf = keptResultFn(opts);
  return (model.byKind.evidence ?? [])
    .filter((ev) => ev.data.kind === 'test' && !opts.external?.get(ev.id) && !keptOf(ev))
    .map((ev) => ({ id: ev.id, ref: String(ev.data.ref) }));
}

/**
 * Run the test evidence of a model through `run` (the runner adapter), or reuse recorded results outside the
 * change's impact.
 * @param {Model} model
 * @param {{
 *   run: (ref: string, id: string) => RunResult,
 *   external?: Map<string, any>,
 *   remark?: Set<string>|null,
 *   priorResults?: Record<string, any>,
 *   priorStamp?: string|null,
 *   now?: () => string,
 * }} opts external: results a realisation root already holds, by evidence id; remark: the claims to re-mark (null:
 *   every claim); priorResults and priorStamp: the results and the stamp of the last verification
 * @returns {{runs: Run[], evidence: Record<string, any>[], reused: string[]}}
 */
export function executeEvidence(model, opts) {
  const keptOf = keptResultFn(opts);
  const now = opts.now ?? (() => new Date().toISOString());
  /** @type {Run[]} */
  const runs = [];
  /** @type {Record<string, any>[]} */
  const evidence = [];
  /** @type {string[]} */
  const reused = [];
  for (const ev of model.byKind.evidence ?? []) {
    const base = { id: ev.id, kind: ev.data.kind, ref: ev.data.ref, claim: ev.data.claim };
    if (ev.data.kind !== 'test') {
      evidence.push({ ...base, outcome: 'not-executed' });
      continue;
    }
    const ext = opts.external?.get(ev.id);
    if (ext) {
      const ranAt = ext.ranAt ?? now();
      runs.push({ id: ev.id, outcome: ext.outcome, ...(ext.detail !== undefined ? { detail: ext.detail } : {}), ranAt });
      evidence.push({ ...base, ...ext, ranAt });
      continue;
    }
    // Outside the change's impact: the result recorded fresh by the last verification still describes this claim.
    const kept = keptOf(ev);
    if (kept) {
      reused.push(ev.id);
      runs.push({ id: ev.id, outcome: kept.outcome, ...(kept.detail !== undefined ? { detail: kept.detail } : {}), ranAt: kept.ranAt ?? now(), obtained: 'impact', ref: String(ev.data.ref), ...(Array.isArray(kept.covers) ? { covers: kept.covers } : {}), ...(typeof kept.coverage === 'string' ? { coverage: kept.coverage } : {}) });
      evidence.push({ ...base, outcome: kept.outcome === 'not-run' ? 'skipped' : kept.outcome, obtained: 'impact', ...(kept.detail !== undefined ? { detail: kept.detail } : {}) });
      continue;
    }
    const r = opts.run(String(ev.data.ref), ev.id);
    const ranAt = r.ranAt ?? now();
    runs.push({ id: ev.id, outcome: r.outcome, ...(r.detail !== undefined ? { detail: r.detail } : {}), ranAt, ref: String(ev.data.ref), ...(r.obtained ? { obtained: r.obtained } : {}), ...(r.attempted === false ? { attempted: false } : {}), ...(r.covers ? { covers: r.covers } : {}), ...(r.coverage ? { coverage: r.coverage } : {}) });
    if (r.outcome === 'skipped') {
      evidence.push({ ...base, outcome: 'skipped', ...(r.obtained === 'reused' ? { obtained: 'reused' } : {}), ...(r.detail !== undefined ? { detail: r.detail } : {}) });
      continue;
    }
    evidence.push({ ...base, outcome: r.outcome, ...(r.obtained ? { obtained: r.obtained } : {}), ...(r.detail !== undefined ? { detail: r.detail } : {}), ranAt });
  }
  return { runs, evidence, reused };
}
