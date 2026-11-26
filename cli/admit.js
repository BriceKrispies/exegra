// The comparison behind `exegra admit`: what a change set does to a specification, as a diff of what
// was true before and after, and the verdict on it. Pure functions of two snapshots; cli/commands.js
// loads the project, runs the transaction and writes.

import { evaluateIntegrity, counterexampleJson, violationKey } from '../src/core/integrity.js';
import { readinessGaps } from '../src/core/readiness.js';
import { CLAIM_METHODS } from '../src/core/claim-methods.js';
import { durationNs } from '../src/core/constructs.js';
import { claimStrength, strengthCounts, VACUOUS_CHECKS } from '../src/core/claim-strength.js';

/** @typedef {import('../src/core/types.js').Model} Model */
/** @typedef {import('../src/core/types.js').Diagnostic} Diagnostic */

/**
 * Claim statuses ranked best to worst. A claim whose status falls to a lower rank has regressed.
 * supported and model-holds share a rank; so do inconclusive and not-evaluated, both undecided. A fall from
 * a positive status to not-evaluated (a stale or missing fact, a check that no longer runs) is a regression
 * like any other; a positive claim that is removed is the reason admit.claim-removed.
 * @type {Record<string, number>}
 */
export const CLAIM_RANK = { proved: 5, verified: 4, supported: 3, 'model-holds': 3, inconclusive: 2, 'not-evaluated': 2, violated: 1 };

/** Statuses that assert something holds. */
export const POSITIVE_STATUSES = new Set(['proved', 'verified', 'supported', 'model-holds']);

/** Statuses a claim created by the change may have. */
const STRONG = new Set(['proved', 'verified']);

/** @param {string} a @param {string} b */
const byText = (a, b) => (a < b ? -1 : a > b ? 1 : 0);

/**
 * Everything admit compares, evaluated once for one side.
 * @param {Model} model @param {Diagnostic[]} diagnostics @param {any[]} claimResults results of evaluateClaims for the model
 */
export function snapshot(model, diagnostics, claimResults) {
  /** @type {Map<string, {id: string, status: string, explanation: string}>} */
  const claims = new Map();
  for (const r of claimResults) claims.set(r.claimId, { id: r.claimId, status: r.status, explanation: r.explanation ?? '' });
  /** @type {Map<string, any>} */
  const errors = new Map();
  /** @type {Map<string, any>} */
  const warnings = new Map();
  for (const d of diagnostics) {
    // Integrity violations are compared as violations, with their counterexamples, not as diagnostics.
    if (d.code === 'integrity.violated') continue;
    if (d.severity !== 'error' && d.severity !== 'warning') continue;
    const key = `${d.code}\u0000${d.entityId ?? ''}\u0000${d.message}`;
    (d.severity === 'error' ? errors : warnings).set(key, { code: d.code, entityId: d.entityId ?? null, message: d.message });
  }
  /** @type {Map<string, any>} */
  const gaps = new Map();
  for (const g of readinessGaps(model)) gaps.set(`${g.code}\u0000${g.entityId}\u0000${g.message}`, { code: g.code, entityId: g.entityId, message: g.message });
  /** @type {Map<string, any>} */
  const violations = new Map();
  for (const r of evaluateIntegrity(model)) {
    for (const c of r.counterexamples) {
      violations.set(violationKey(r.ruleId, c), { ruleId: r.ruleId, severity: r.severity, counterexample: counterexampleJson(model, c) });
    }
  }
  return { claims, errors, warnings, gaps, violations, model };
}

/** @typedef {ReturnType<typeof snapshot>} Snapshot */

/** @param {Snapshot} s */
export function sideCounts(s) {
  /** @type {Record<string, number>} */
  const claims = { total: s.claims.size };
  for (const c of s.claims.values()) claims[c.status] = (claims[c.status] ?? 0) + 1;
  return { claims, validationErrors: s.errors.size, validationWarnings: s.warnings.size, readinessGaps: s.gaps.size, integrityViolations: s.violations.size };
}

/**
 * New and resolved entries of a keyed collection, each in key order.
 * @param {Map<string, any>} before @param {Map<string, any>} after
 */
function delta(before, after) {
  const added = [...after].filter(([k]) => !before.has(k)).sort(([a], [b]) => byText(a, b)).map(([, v]) => v);
  const resolved = [...before].filter(([k]) => !after.has(k)).sort(([a], [b]) => byText(a, b)).map(([, v]) => v);
  return { new: added, resolved };
}

/**
 * Compare two snapshots and decide.
 * @param {Snapshot} before @param {Snapshot} after
 * @param {{accept?: string[]}} [options] accept: reason codes the caller acknowledges (see acknowledge)
 */
export function compare(before, after, options = {}) {
  const ids = [...new Set([...before.claims.keys(), ...after.claims.keys()])].sort(byText);
  /** @type {any[]} */ const changed = [];
  /** @type {any[]} */ const added = [];
  /** @type {any[]} */ const removed = [];
  for (const id of ids) {
    const b = before.claims.get(id);
    const a = after.claims.get(id);
    if (b && a) {
      if (b.status !== a.status) {
        const rb = CLAIM_RANK[b.status];
        const ra = CLAIM_RANK[a.status];
        const direction = rb === undefined || ra === undefined ? 'unranked' : ra < rb ? 'worse' : ra > rb ? 'better' : 'same-rank';
        changed.push({ id, before: b.status, after: a.status, direction, explanation: a.explanation });
      }
    } else if (a) added.push({ id, status: a.status, explanation: a.explanation });
    else if (b) removed.push({ id, status: b.status });
  }
  const errors = delta(before.errors, after.errors);
  const warnings = delta(before.warnings, after.warnings);
  const gaps = delta(before.gaps, after.gaps);
  const violations = delta(before.violations, after.violations);

  /** @type {{code: string, message: string, id?: string, [k: string]: any}[]} */
  const reasons = [];
  for (const c of changed) {
    if (c.direction === 'worse') reasons.push({ code: 'admit.claim-regressed', id: c.id, before: c.before, after: c.after, message: `Claim "${c.id}" moved from ${c.before} to ${c.after}.` });
  }
  // Removing a claim that held takes a guarantee away: a reason, which the caller may accept explicitly
  // (--accept admit.claim-removed) when the removal is the decision.
  for (const r of removed) {
    if (POSITIVE_STATUSES.has(r.status)) reasons.push({ code: 'admit.claim-removed', acknowledgeable: true, id: r.id, before: r.status, message: `Claim "${r.id}" was ${r.status} and the change removes it.` });
  }
  for (const e of errors.new) reasons.push({ code: 'admit.new-error', id: e.entityId ?? undefined, diagnosticCode: e.code, message: `New validation error ${e.code}${e.entityId ? ` at "${e.entityId}"` : ''}: ${e.message}` });
  for (const v of violations.new) {
    const bindings = v.counterexample.map((/** @type {any} */ b) => `${b.variable} = ${b.entity ?? b.value}`).join(', ') || 'the rule is false';
    reasons.push({ code: 'admit.new-violation', id: v.ruleId, severity: v.severity, counterexample: v.counterexample, message: `New violation of integrity rule "${v.ruleId}" (${v.severity}): ${bindings}.` });
  }
  const pending = newClaimReasons(after.model, added, reasons);
  const privilege = privilegeChanges(before.model, after.model);
  reasons.push(...privilege.reasons);
  reasons.push(...guaranteeChanges(before.model, after.model));
  const ack = acknowledge(reasons, options.accept ?? []);
  reasons.splice(0, reasons.length, ...ack.open);
  reasons.sort((x, y) => byText(x.code, y.code) || byText(x.id ?? '', y.id ?? '') || byText(x.message, y.message));

  return {
    verdict: reasons.length ? 'rejected' : 'admitted',
    reasons,
    acknowledged: ack.acknowledged,
    ...(ack.refused.length ? { refusedAccept: ack.refused } : {}),
    pendingRealisation: pending,
    diff: {
      claims: { changed, added, removed },
      privilege: { added: privilege.added, removed: privilege.removed },
      validation: { errors, warnings },
      readiness: gaps,
      integrity: violations,
    },
    counts: {
      before: sideCounts(before),
      after: sideCounts(after),
      changedClaims: changed.length,
      regressedClaims: changed.filter((c) => c.direction === 'worse').length,
      addedClaims: added.length,
      removedClaims: removed.length,
      newValidationErrors: errors.new.length,
      resolvedValidationErrors: errors.resolved.length,
      newValidationWarnings: warnings.new.length,
      resolvedValidationWarnings: warnings.resolved.length,
      newReadinessGaps: gaps.new.length,
      resolvedReadinessGaps: gaps.resolved.length,
      newIntegrityViolations: violations.new.length,
      resolvedIntegrityViolations: violations.resolved.length,
    },
  };
}

// ---------------------------------------------------------------------------------------------------------
// Acknowledgement: `admit --accept <code>`.

/** Codes of reasons that can never be acknowledged: they are failures, not decisions. */
export const NON_ACKNOWLEDGEABLE = new Set([
  'admit.transaction-refused', 'admit.claim-regressed', 'admit.new-error', 'admit.new-violation',
  'admit.new-claim-weak', 'admit.requirement-without-milestone',
]);

/**
 * Split reasons into those still blocking and those acknowledged by an accepted code. Only a reason that carries
 * `acknowledgeable: true` can be acknowledged; an accepted code that names a reason without it (or one of
 * NON_ACKNOWLEDGEABLE) is returned in `refused`. An accepted code no reason carries is ignored.
 * @param {any[]} reasons @param {string[]} accept
 */
export function acknowledge(reasons, accept) {
  const accepted = new Set(accept);
  const refused = [...accepted].filter((c) => NON_ACKNOWLEDGEABLE.has(c) || reasons.some((r) => r.code === c && r.acknowledgeable !== true)).sort(byText);
  const open = reasons.filter((r) => !(r.acknowledgeable === true && accepted.has(r.code)));
  const acknowledged = reasons.filter((r) => r.acknowledgeable === true && accepted.has(r.code));
  return { open, acknowledged, refused };
}

// ---------------------------------------------------------------------------------------------------------
// New claims: decided at specification time, or pending realisation (WG-5273).

/**
 * Whether a claim cannot be decided when it is written: it is realised by code and shown by executed
 * evidence. That is a claim whose method is external-evidence or a verification method the specification
 * declares as carried out outside Exegra, or a requirement whose method is none Exegra evaluates itself
 * (a method of CLAIM_METHODS, the structural, data-model, integrity and lean-theorem ones included, stays decidable).
 * @param {any} model @param {any} claim
 */
export function realisedByCode(model, claim) {
  const method = claim?.data?.evaluate?.method;
  if (typeof method !== 'string') return claim?.data?.kind === 'requirement';
  if (method === 'external-evidence') return true;
  if (Object.hasOwn(model.meta?.verificationMethods ?? {}, method)) return true;
  return claim.data.kind === 'requirement' && !Object.hasOwn(CLAIM_METHODS, method);
}

/**
 * Judge the claims the change adds. A claim decided at specification time must be verified or proved. A claim
 * realised by code is admitted when it names a milestone and has no result yet (not-evaluated or inconclusive,
 * for lack of evidence) or has one that holds; it is then listed as pending realisation. Without a milestone a
 * requirement is the reason admit.requirement-without-milestone, any other code-realised claim stays weak.
 * Pushes the reasons onto `reasons` and returns the pending claims.
 * @param {any} model @param {{id: string, status: string}[]} added @param {any[]} reasons
 */
function newClaimReasons(model, added, reasons) {
  /** @type {any[]} */
  const pending = [];
  for (const c of added) {
    if (STRONG.has(c.status)) continue;
    const claim = model.entities.get(c.id);
    const weak = () => reasons.push({ code: 'admit.new-claim-weak', id: c.id, status: c.status, message: `New claim "${c.id}" is ${c.status}; a claim the change creates must be verified or proved.` });
    if (!claim || !realisedByCode(model, claim)) { weak(); continue; }
    const milestone = claim.data.milestone;
    const named = (typeof milestone === 'number' && Number.isFinite(milestone)) || (typeof milestone === 'string' && milestone.trim() !== '');
    if (!named) {
      if (claim.data.kind === 'requirement') reasons.push({ code: 'admit.requirement-without-milestone', id: c.id, status: c.status, message: `New requirement "${c.id}" is realised by code and cannot be verified yet, so it must name its milestone.` });
      else weak();
      continue;
    }
    if (c.status === 'not-evaluated' || c.status === 'inconclusive') pending.push({ id: c.id, kind: claim.data.kind, method: claim.data.evaluate?.method ?? null, milestone, status: c.status });
    else if (c.status !== 'supported') weak();
  }
  pending.sort((a, b) => byText(a.id, b.id));
  return pending;
}

// ---------------------------------------------------------------------------------------------------------
// Privilege diff (WG-5275): capabilities and unbounded grants a change adds.

const PRIVILEGE_KINDS = ['role', 'grant', 'delegation', 'tokenScope'];

/** @param {any} v */
const stable = (v) => JSON.stringify(v, (_k, x) => (x && typeof x === 'object' && !Array.isArray(x) ? Object.fromEntries(Object.entries(x).sort(([a], [b]) => byText(a, b))) : x));
/** @param {any} v @returns {string[]} */
const strings = (v) => (Array.isArray(v) ? v.filter((x) => typeof x === 'string') : []);

/** The entities of the given kinds of a model, by id. @param {any} model @param {string[]} kinds @returns {Map<string, any>} */
function entitiesOf(model, kinds) {
  const out = new Map();
  for (const k of kinds) for (const e of model?.byKind?.[k] ?? []) out.set(e.id, e);
  return out;
}

/**
 * What the change adds to roles, grants, delegations and token scopes. `reasons` holds each capability an
 * entity gained (admit.privilege-change, `change: "capability-added"`, with the entity, its level and holders where
 * it has them), each new or changed grant or delegation without maxDuration (`"no-max-duration"`) and each
 * maxDuration made longer (`"max-duration-longer"`). `removed` lists the capabilities taken away (informational,
 * no reason).
 * @param {any} model0 @param {any} model1
 */
export function privilegeChanges(model0, model1) {
  const was = entitiesOf(model0, PRIVILEGE_KINDS);
  const now = entitiesOf(model1, PRIVILEGE_KINDS);
  /** @type {any[]} */ const reasons = [];
  /** @type {any[]} */ const added = [];
  /** @type {any[]} */ const removed = [];
  for (const [id, e] of [...now].sort(([a], [b]) => byText(a, b))) {
    const old = was.get(id);
    const level = typeof e.data.level === 'string' ? e.data.level : undefined;
    const holders = strings(e.data.holders);
    const who = [e.kind, level && `level ${level}`, holders.length && `holders ${holders.join('/')}`].filter(Boolean).join(', ');
    const oldCaps = new Set(strings(old?.data.capabilities));
    for (const cap of strings(e.data.capabilities)) {
      if (oldCaps.has(cap)) continue;
      const item = { entity: id, kind: e.kind, ...(level ? { level } : {}), ...(holders.length ? { holders } : {}), capability: cap };
      added.push(item);
      reasons.push({ code: 'admit.privilege-change', acknowledgeable: true, id, change: 'capability-added', ...item, message: `${e.kind} "${id}" (${who}) gains capability "${cap}"${old ? '' : ' (new entity)'}.` });
    }
    if (e.kind === 'grant' || e.kind === 'delegation') {
      const changed = !old || stable(old.data) !== stable(e.data);
      const d = e.data.maxDuration;
      if (changed && (d === undefined || d === null || d === '')) {
        reasons.push({ code: 'admit.privilege-change', acknowledgeable: true, id, change: 'no-max-duration', kind: e.kind, message: `${e.kind} "${id}" has no maxDuration: it can last without bound.` });
      } else if (old && d !== old.data.maxDuration) {
        const a = durationNs(old.data.maxDuration);
        const b = durationNs(d);
        if (a !== null && b !== null && b > a) {
          reasons.push({ code: 'admit.privilege-change', acknowledgeable: true, id, change: 'max-duration-longer', kind: e.kind, before: old.data.maxDuration, after: d, message: `${e.kind} "${id}" may now last ${d} instead of ${old.data.maxDuration}.` });
        }
      }
    }
  }
  for (const [id, old] of [...was].sort(([a], [b]) => byText(a, b))) {
    const kept = new Set(strings(now.get(id)?.data.capabilities));
    for (const cap of strings(old.data.capabilities)) if (!kept.has(cap)) removed.push({ entity: id, kind: old.kind, capability: cap, ...(now.has(id) ? {} : { entityRemoved: true }) });
  }
  return { reasons, added, removed };
}

// ---------------------------------------------------------------------------------------------------------
// Guarantee weakening (WG-5275): looser copy bounds, changed retentions, changed rules and claims.

const TIME_NS = { millisecond: 1e6, second: 1e9, minute: 6e10, hour: 3.6e12, day: 8.64e13 };

/** A bound (a number with a unit, or a duration text) in nanoseconds; null when it is not a time. @param {any} bound @param {any} unit */
function boundNs(bound, unit) {
  if (typeof bound === 'number' && Number.isFinite(bound) && typeof unit === 'string' && Object.hasOwn(TIME_NS, unit)) return bound * TIME_NS[/** @type {keyof typeof TIME_NS} */ (unit)];
  if (typeof bound === 'string') return durationNs(bound);
  return null;
}

/** @param {any} bound @param {any} unit */
const showBound = (bound, unit) => (typeof bound === 'number' && unit ? `${bound} ${unit}` : String(bound));

/**
 * What the change weakens, as reasons admit.guarantee-weakened. For a copy class the change creates or
 * changes: its freshness or erasure bound is longer than that of another class of the same record
 * (`change: "copy-freshness-looser"` / `"copy-erasure-looser"`, compared in nanoseconds; the tightest other class
 * is named). A retention whose keepFor, until, then, fields or archiveTo changed, or that was removed
 * (`"retention-changed"`). An integrity rule whose rule, statement or severity changed or that was removed
 * (`"integrity-rule-changed"`), and a claim whose statement or evaluate changed or that was removed
 * (`"claim-changed"`). Each carries `before` and `after`.
 * @param {any} model0 @param {any} model1
 */
export function guaranteeChanges(model0, model1) {
  /** @type {any[]} */ const reasons = [];
  /** @param {string} change @param {string} id @param {string} message @param {any} before @param {any} after */
  const push = (change, id, message, before, after) => reasons.push({ code: 'admit.guarantee-weakened', acknowledgeable: true, id, change, before, after, message });

  const copiesWas = entitiesOf(model0, ['copy']);
  const copiesNow = entitiesOf(model1, ['copy']);
  for (const [id, c] of [...copiesNow].sort(([a], [b]) => byText(a, b))) {
    const old = copiesWas.get(id);
    if (old && stable(old.data) === stable(c.data)) continue;
    for (const field of ['freshness', 'erasure']) {
      const mine = boundNs(c.data[field]?.bound, c.data[field]?.unit);
      if (mine === null) continue;
      for (const record of strings(c.data.of).sort(byText)) {
        /** @type {{id: string, ns: number, shown: string}|null} */
        let tightest = null;
        for (const [oid, o] of copiesNow) {
          if (oid === id || !strings(o.data.of).includes(record)) continue;
          const ns = boundNs(o.data[field]?.bound, o.data[field]?.unit);
          if (ns !== null && (!tightest || ns < tightest.ns)) tightest = { id: oid, ns, shown: showBound(o.data[field].bound, o.data[field].unit) };
        }
        if (tightest && mine > tightest.ns) {
          const shown = showBound(c.data[field].bound, c.data[field].unit);
          push(`copy-${field}-looser`, id, `Copy class "${id}" of record "${record}" has a ${field} bound of ${shown}, looser than ${tightest.shown} of "${tightest.id}", another class of the same record.`, tightest.shown, shown);
        }
      }
    }
  }

  const retWas = entitiesOf(model0, ['retention']);
  const retNow = entitiesOf(model1, ['retention']);
  const RET = ['keepFor', 'until', 'then', 'fields', 'archiveTo'];
  /** @param {any} e */
  const retShown = (e) => (e ? stable(Object.fromEntries(RET.filter((k) => e.data[k] !== undefined).map((k) => [k, e.data[k]]))) : 'removed');
  for (const [id, old] of [...retWas].sort(([a], [b]) => byText(a, b))) {
    const now = retNow.get(id);
    if (now && retShown(now) === retShown(old)) continue;
    push('retention-changed', id, `Retention "${id}" of record "${old.data.record}" changed from ${retShown(old)} to ${retShown(now)}.`, retShown(old), retShown(now));
  }

  const rulesWas = entitiesOf(model0, ['integrityRule']);
  const rulesNow = entitiesOf(model1, ['integrityRule']);
  /** @param {any} e */
  const ruleShown = (e) => (e ? `${e.data.severity}: ${e.data.rule} (${e.data.statement})` : 'removed');
  for (const [id, old] of [...rulesWas].sort(([a], [b]) => byText(a, b))) {
    const now = rulesNow.get(id);
    if (now && ruleShown(now) === ruleShown(old)) continue;
    push('integrity-rule-changed', id, `Integrity rule "${id}" changed from [${ruleShown(old)}] to [${ruleShown(now)}].`, ruleShown(old), ruleShown(now));
  }

  const claimsWas = entitiesOf(model0, ['claim']);
  const claimsNow = entitiesOf(model1, ['claim']);
  /** @param {any} e */
  const claimShown = (e) => (e ? `${e.data.statement} / ${stable(e.data.evaluate ?? null)}` : 'removed');
  for (const [id, old] of [...claimsWas].sort(([a], [b]) => byText(a, b))) {
    const now = claimsNow.get(id);
    if (now && claimShown(now) === claimShown(old)) continue;
    push('claim-changed', id, `Claim "${id}" changed from [${claimShown(old)}] to [${claimShown(now)}].`, claimShown(old), claimShown(now));
  }
  return reasons;
}

// ---------------------------------------------------------------------------
// Claim strength (WG-5274, WG-5276; decision dec-claim-check-and-grounding)
// ---------------------------------------------------------------------------

/**
 * Add the strength of the claims to an admit report: counts by check and grounding before and after,
 * the check and grounding of each claim the change creates, and for those claims only the reasons
 * admit.claim-vacuous (holds-by-construction or restated-scenario), admit.claim-single-trace and
 * admit.claim-self-contained. Each of these reasons carries acknowledgeable: true: a caller may accept
 * it explicitly. Existing claims are counted and never a reason. Under the change, an entity it creates
 * anchors nothing (the before model is the baseline).
 * Its reasons go through `acknowledge` with the same accepted codes as compare's, so `--accept` waives them too.
 * @param {ReturnType<typeof compare>} report @param {Model} beforeModel @param {Model} afterModel
 * @param {string[]} [accept] reason codes the caller acknowledges
 */
export function withClaimStrength(report, beforeModel, afterModel, accept = []) {
  const before = claimStrength(beforeModel);
  const after = claimStrength(afterModel, { existing: new Set(beforeModel.entities.keys()) });
  /** @type {{code: string, message: string, id?: string, [k: string]: any}[]} */
  const reasons = [];
  const added = [];
  for (const c of report.diff.claims.added) {
    const s = after.get(c.id);
    if (!s) continue;
    added.push({ id: c.id, check: s.check, grounding: s.grounding, details: s.details });
    const base = { id: c.id, check: s.check, grounding: s.grounding, acknowledgeable: true };
    if (VACUOUS_CHECKS.has(s.check)) reasons.push({ code: 'admit.claim-vacuous', ...base, message: `New claim "${c.id}" is ${s.check}: ${s.details.check}` });
    if (s.check === 'single-trace') reasons.push({ code: 'admit.claim-single-trace', ...base, message: `New claim "${c.id}" is single-trace: ${s.details.check}` });
    if (s.grounding === 'self-contained') reasons.push({ code: 'admit.claim-self-contained', ...base, message: `New claim "${c.id}" is self-contained: ${s.details.grounding}` });
  }
  const ack = acknowledge(reasons, accept);
  const order = (/** @type {any} */ x, /** @type {any} */ y) => byText(x.code, y.code) || byText(x.id ?? '', y.id ?? '') || byText(x.message, y.message);
  const all = [...report.reasons, ...ack.open].sort(order);
  const refused = [...new Set([...(report.refusedAccept ?? []), ...ack.refused])].sort(byText);
  return {
    ...report,
    verdict: all.length ? 'rejected' : 'admitted',
    reasons: all,
    acknowledged: [...(report.acknowledged ?? []), ...ack.acknowledged].sort(order),
    ...(refused.length ? { refusedAccept: refused } : {}),
    strength: { before: strengthCounts(before), after: strengthCounts(after), added },
  };
}

// ---------------------------------------------------------------------------
// Regression gating of `exegra verify` (epistemics D8): the statuses the last passing run recorded
// ---------------------------------------------------------------------------

/**
 * A fingerprint of a counterexample: what it names (summary, entities, path, scenario, step and reason), so that
 * a change of any of them changes the fingerprint. Deterministic, entity order ignored, no dependency.
 * @param {any} cx
 * @returns {string|null}
 */
export function counterexampleFingerprint(cx) {
  if (!cx || typeof cx !== 'object') return null;
  const text = [
    String(cx.summary ?? ''),
    [...(Array.isArray(cx.entities) ? cx.entities : [])].map(String).sort(byText).join(','),
    (Array.isArray(cx.path) ? cx.path : []).map(String).join('>'),
    String(cx.scenario ?? ''),
    String(cx.stepIndex ?? ''),
    String(cx.reason ?? ''),
  ].join('\u0000');
  // Two FNV-1a passes with different offsets over the UTF-16 code units: a stable 64-bit hex text.
  let a = 0x811c9dc5;
  let b = 0x050c5d1f;
  for (let i = 0; i < text.length; i++) {
    const c = text.charCodeAt(i);
    a = Math.imul(a ^ c, 0x01000193) >>> 0;
    b = Math.imul(b ^ c, 0x01000193) >>> 0;
    b = (b ^ (b >>> 13)) >>> 0;
  }
  return a.toString(16).padStart(8, '0') + b.toString(16).padStart(8, '0');
}

/**
 * The baseline `exegra verify` records with a passing run: each claim's status and, for a violated one, the
 * fingerprint of its counterexample.
 * @param {{claimId: string, status: string, counterexample?: any}[]} claimResults
 * @returns {Record<string, {status: string, counterexample?: string}>}
 */
export function claimBaseline(claimResults) {
  /** @type {Record<string, {status: string, counterexample?: string}>} */
  const out = {};
  for (const r of claimResults) {
    const fp = r.status === 'violated' ? counterexampleFingerprint(r.counterexample) : null;
    out[r.claimId] = { status: r.status, ...(fp ? { counterexample: fp } : {}) };
  }
  return out;
}

/**
 * What a verify run regressed against the baseline of the last passing run.
 * - verify.claim-regressed: a claim that was positive (proved, verified, supported, model-holds) now has a lower
 *   rank (CLAIM_RANK, so inconclusive and not-evaluated count); a fall to violated is reported here too unless the
 *   claim is expected to be violated.
 * - verify.claim-removed: a positive claim of the baseline no longer exists.
 * - verify.counterexample-changed: an expected-violated claim that was violated is violated with another
 *   counterexample, so the violation is no longer the known one.
 * A claim named in `accept` is not reported.
 * @param {Record<string, {status: string, counterexample?: string}>} baseline
 * @param {Record<string, {status: string, counterexample?: string}>} current
 * @param {{expectViolated?: string[], accept?: string[]}} [options]
 * @returns {{code: string, id: string, before: string, after: string|null, message: string}[]}
 */
export function verifyRegressions(baseline, current, options = {}) {
  const expected = new Set(options.expectViolated ?? []);
  const accepted = new Set(options.accept ?? []);
  /** @type {{code: string, id: string, before: string, after: string|null, message: string}[]} */
  const out = [];
  for (const id of Object.keys(baseline).sort(byText)) {
    if (accepted.has(id)) continue;
    const b = baseline[id];
    if (!b || typeof b.status !== 'string') continue;
    const a = Object.hasOwn(current, id) ? current[id] : undefined;
    if (!a) {
      if (POSITIVE_STATUSES.has(b.status)) out.push({ code: 'verify.claim-removed', id, before: b.status, after: null, message: `Claim "${id}" was ${b.status} and no longer exists.` });
      continue;
    }
    if (expected.has(id) && b.status === 'violated' && a.status === 'violated') {
      if (b.counterexample && a.counterexample && b.counterexample !== a.counterexample) {
        out.push({ code: 'verify.counterexample-changed', id, before: b.status, after: a.status, message: `Claim "${id}" is expected to be violated, but its counterexample changed (${b.counterexample} to ${a.counterexample}): the violation is no longer the known one.` });
      }
      continue;
    }
    if (!POSITIVE_STATUSES.has(b.status)) continue;
    if (a.status === 'violated' && expected.has(id)) continue;
    const rb = CLAIM_RANK[b.status];
    const ra = CLAIM_RANK[a.status];
    if (ra === undefined || ra < rb) out.push({ code: 'verify.claim-regressed', id, before: b.status, after: a.status, message: `Claim "${id}" moved from ${b.status} to ${a.status}.` });
  }
  return out;
}
