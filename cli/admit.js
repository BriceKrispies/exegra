// The comparison behind `exegra admit`: what a change set does to a specification, as a diff of what
// was true before and after, and the verdict on it. Pure functions of two snapshots; cli/commands.js
// loads the project, runs the transaction and writes.

import { evaluateIntegrity, counterexampleJson, violationKey } from '../src/core/integrity.js';
import { readinessGaps } from '../src/core/readiness.js';
import { CLAIM_METHODS } from '../src/core/claim-methods.js';
import { durationNs } from '../src/core/constructs.js';
import { claimStrength, strengthCounts, VACUOUS_CHECKS } from '../src/core/claim-strength.js';
import { isRegression, statusOf } from '../src/core/verdict.js';
import { call } from '../src/core/lean.js';
import { specChanges } from '../src/core/impact.js';
import { analyzeLayers } from '../src/core/layers.js';
import { NAMESPACE_SEPARATOR } from '../src/core/layer-values.js';
import { exploreExecutions } from '../src/core/refinement-explore.js';
import { parseExpr, exprRefs, evalExpr } from '../src/core/expr.js';

/** @typedef {import('../src/core/types.js').Model} Model */
/** @typedef {import('../src/core/types.js').Diagnostic} Diagnostic */

/** Statuses that assert something holds (the words Lean shows a positive strength with). */
export const POSITIVE_STATUSES = new Set(['proved', 'verified', 'supported', 'model-holds']);

/** Statuses a claim created by the change may have. */
const STRONG = new Set(['proved', 'verified']);

/** A status tuple in words. @param {any} v */
const verdictText = (v) => (v ? `${v.strength}, ${v.subject}, ${v.freshness}${v.openAssumptions?.length ? `, open: ${v.openAssumptions.join(', ')}` : ''}` : 'no status');

/** @param {string} a @param {string} b */
const byText = (a, b) => (a < b ? -1 : a > b ? 1 : 0);

/**
 * Everything admit compares, evaluated once for one side.
 * @param {Model} model @param {Diagnostic[]} diagnostics @param {any[]} claimResults results of evaluateClaims for the model
 */
export function snapshot(model, diagnostics, claimResults) {
  /** @type {Map<string, {id: string, status: string, explanation: string, verdict?: import('../src/core/verdict.js').Status}>} */
  const claims = new Map();
  for (const r of claimResults) claims.set(r.claimId, { id: r.claimId, status: r.status, explanation: r.explanation ?? '', ...(r.verdict ? { verdict: statusOf(r.verdict) } : {}) });
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
 * @param {{accept?: string[], theorems?: {old: Record<string, any>, new: Record<string, any>}}} [options] accept:
 *   reason codes the caller acknowledges, and claim ids whose theorem weakening it accepts (see acknowledge);
 *   theorems: the Lean theorem checks recorded before the change and made after it (theoremChanges)
 */
export function compare(before, after, options = {}) {
  const ids = [...new Set([...before.claims.keys(), ...after.claims.keys()])].sort(byText);
  /** @type {any[]} */ const changed = [];
  /** @type {any[]} */ const added = [];
  /** @type {any[]} */ const removed = [];
  // Whether a move is a regression is decided in Lean (Exegra.Verdict.isRegression): a removal, or a new status
  // that is not at least the old one in the status order.
  const kept = ids.filter((id) => before.claims.get(id)?.verdict && after.claims.get(id)?.verdict);
  const index = new Map(kept.map((id, i) => [id, i]));
  const moves = isRegression(kept.flatMap((id) => {
    const b = /** @type {any} */ (before.claims.get(id)).verdict;
    const a = /** @type {any} */ (after.claims.get(id)).verdict;
    return [{ old: b, new: a }, { old: a, new: b }];
  }));
  for (const id of ids) {
    const b = before.claims.get(id);
    const a = after.claims.get(id);
    if (b && a) {
      const i = index.get(id);
      const worse = i !== undefined ? moves[2 * i] : false;
      const back = i !== undefined ? moves[2 * i + 1] : false;
      if (b.status !== a.status || worse || back) {
        const direction = i === undefined ? 'unranked' : worse && back ? 'incomparable' : worse ? 'worse' : back ? 'better' : 'same';
        changed.push({ id, before: b.status, after: a.status, direction, regression: worse, explanation: a.explanation, ...(b.verdict ? { beforeVerdict: b.verdict } : {}), ...(a.verdict ? { afterVerdict: a.verdict } : {}) });
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
    if (c.regression) reasons.push({ code: 'admit.claim-regressed', id: c.id, before: c.before, after: c.after, message: `Claim "${c.id}" moved from ${c.before} to ${c.after}${c.before === c.after ? ` (${verdictText(c.beforeVerdict)} to ${verdictText(c.afterVerdict)})` : ''}.` });
  }
  // Removing a claim takes away what it established (Exegra.Verdict.isRegression counts every removal): a reason,
  // which the caller may accept explicitly (--accept admit.claim-removed) when the removal is the decision.
  const removedWith = removed.filter((r) => before.claims.get(r.id)?.verdict);
  const removedMoves = isRegression(removedWith.map((r) => ({ old: /** @type {any} */ (before.claims.get(r.id)).verdict, new: null })));
  for (const r of removed) {
    const i = removedWith.indexOf(r);
    if (i >= 0 ? removedMoves[i] : POSITIVE_STATUSES.has(r.status)) reasons.push({ code: 'admit.claim-removed', acknowledgeable: true, id: r.id, before: r.status, message: `Claim "${r.id}" was ${r.status} and the change removes it.` });
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
  const theorems = theoremChanges(before.model, after.model, options.theorems?.old ?? {}, options.theorems?.new ?? {});
  reasons.push(...theorems.reasons);
  const ack = acknowledge(reasons, options.accept ?? []);
  reasons.splice(0, reasons.length, ...ack.open);
  reasons.sort((x, y) => byText(x.code, y.code) || byText(x.id ?? '', y.id ?? '') || byText(x.message, y.message));

  return {
    verdict: reasons.length ? 'rejected' : 'admitted',
    reasons,
    acknowledged: ack.acknowledged,
    ...(ack.refused.length ? { refusedAccept: ack.refused } : {}),
    pendingRealisation: pending,
    // Changes to what claims guarantee (a statement, an evaluate, a theorem's statement), listed apart from the diff.
    guaranteeChanges: [...specChanges(before.model, after.model).guaranteeChanges, ...theorems.guaranteeChanges]
      .sort((x, y) => byText(x.claim, y.claim) || byText(x.change, y.change)),
    ...(theorems.notCompared.length ? { theoremsNotCompared: theorems.notCompared } : {}),
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
      regressedClaims: changed.filter((c) => c.regression).length,
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
  const refused = [...accepted].filter((c) => NON_ACKNOWLEDGEABLE.has(c) || reasons.some((r) => r.code === c && (r.acknowledgeable !== true || r.acceptBy === 'claim'))).sort(byText);
  // A reason accepted by claim (admit.theorem-weakened) is acknowledged only when --accept names its claim.
  const ok = (/** @type {any} */ r) => r.acknowledgeable === true && (r.acceptBy === 'claim' ? accepted.has(r.id) : accepted.has(r.code));
  const open = reasons.filter((r) => !ok(r));
  const acknowledged = reasons.filter(ok);
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

// ---------------------------------------------------------------------------------------------------------
// Theorem weakening (WG-5684, criterion 11): decided in Lean (Exegra.Impact.weakening).

/**
 * What a change does to the theorems of lean-theorem claims, between the check recorded before it (`oldTheorems`,
 * the results file) and the check made after it (`newTheorems`, tools/lean-theorems.js on the changed tree). For
 * each claim kept by the change whose theorem has a recorded check: a weakening is the reason
 * admit.theorem-weakened, acknowledged only by `--accept <claim>`; a changed statement hash is a guarantee change.
 * Lean decides both. A check recorded before statements were hashed with binder names erased (no hashVersion 2)
 * cannot be compared by statement: the claim is listed in `notCompared` and only removal, axioms and about count.
 * @param {any} model0 @param {any} model1 @param {Record<string, any>} oldTheorems @param {Record<string, any>} newTheorems
 */
export function theoremChanges(model0, model1, oldTheorems, newTheorems) {
  /** @type {{id: string, theorem: string, old: any, new: any, oldAbout: string[], newAbout: string[]}[]} */
  const items = [];
  /** @type {string[]} */
  const notCompared = [];
  const about = (/** @type {any} */ ev) => (Array.isArray(ev?.about) ? ev.about.filter((/** @type {any} */ a) => typeof a === 'string') : []);
  for (const c of [...(model0?.byKind?.claim ?? [])].sort((a, b) => byText(a.id, b.id))) {
    const ev0 = c.data.evaluate;
    const ev1 = model1?.entities?.get(c.id)?.data?.evaluate;
    if (ev0?.method !== 'lean-theorem' || ev1?.method !== 'lean-theorem' || typeof ev0.theorem !== 'string') continue;
    const old = Object.hasOwn(oldTheorems, ev0.theorem) ? oldTheorems[ev0.theorem] : undefined;
    if (!old || !old.found) continue;
    const found = typeof ev1.theorem === 'string' && Object.hasOwn(newTheorems, ev1.theorem) ? newTheorems[ev1.theorem] : null;
    // The superseding theorem counts only when the claim names it.
    const fresh = found ? { ...found, supersedes: found.supersedes && found.supersedes.name === ev1.supersedes ? found.supersedes : null } : null;
    let oldCheck = old;
    if (fresh && old.hashVersion !== fresh.hashVersion) {
      notCompared.push(c.id);
      oldCheck = { ...old, statementHash: fresh.statementHash };
    }
    items.push({ id: c.id, theorem: ev1.theorem, old: oldCheck, new: fresh, oldAbout: about(ev0), newAbout: about(ev1) });
  }
  if (!items.length) return { reasons: [], guaranteeChanges: [], notCompared };
  const r = call('theorem.weakening', { items: items.map(({ old, new: n, oldAbout, newAbout }) => ({ old, new: n, oldAbout, newAbout })) });
  if (!r.ok) throw new Error(`The Lean theorem weakening check could not be computed: ${r.error}`);
  const why = { removed: 'the theorem is gone', 'axioms-gained': 'its proof now depends on more axioms', 'about-changed': 'the constants it is about changed', 'statement-changed': 'its statement changed and no superseding theorem of type new statement -> old statement passes the Lean gate' };
  /** @type {any[]} */
  const reasons = [];
  /** @type {any[]} */
  const guarantee = [];
  items.forEach((it, i) => {
    const out = r.value[i];
    if (out.weakened) {
      reasons.push({ code: 'admit.theorem-weakened', acknowledgeable: true, acceptBy: 'claim', id: it.id, theorem: it.theorem, weakening: out.weakened,
        message: `The change weakens the theorem "${it.theorem}" of claim "${it.id}": ${why[/** @type {keyof typeof why} */ (out.weakened)] ?? out.weakened}. Accept it explicitly with --accept ${it.id}.` });
    }
    if (out.statementChanged) guarantee.push({ claim: it.id, change: 'theorem-statement', before: it.old.statementHash ?? null, after: it.new?.statementHash ?? null });
  });
  return { reasons, guaranteeChanges: guarantee, notCompared };
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
 * The baseline `exegra verify` records with a passing run: each claim's status word, the status tuple Lean decided
 * (Exegra.Verdict.Status) and, for a violated one, the fingerprint of its counterexample.
 * @param {{claimId: string, status: string, verdict?: import('../src/core/verdict.js').Status, counterexample?: any}[]} claimResults
 * @returns {Record<string, {status: string, verdict?: import('../src/core/verdict.js').Status, counterexample?: string}>}
 */
export function claimBaseline(claimResults) {
  /** @type {Record<string, {status: string, verdict?: import('../src/core/verdict.js').Status, counterexample?: string}>} */
  const out = {};
  for (const r of claimResults) {
    const fp = r.status === 'violated' ? counterexampleFingerprint(r.counterexample) : null;
    out[r.claimId] = { status: r.status, ...(r.verdict ? { verdict: statusOf(r.verdict) } : {}), ...(fp ? { counterexample: fp } : {}) };
  }
  return out;
}

/**
 * What a verify run regressed against the baseline of the last passing run. Whether a move is a regression is
 * decided in Lean (Exegra.Verdict.isRegression over the recorded status tuples).
 * - verify.claim-regressed: a claim whose status is not at least its baseline status in the status order; a fall to
 *   violated is not reported here when the claim is expected to be violated.
 * - verify.claim-removed: a claim of the baseline no longer exists.
 * - verify.counterexample-changed: an expected-violated claim that was violated is violated with another
 *   counterexample, so the violation is no longer the known one.
 * A claim named in `accept` is not reported. A baseline entry without a status tuple (recorded before verdicts were
 * decided in Lean) is not compared; the next passing run records the tuple.
 * @param {Record<string, {status: string, verdict?: any, counterexample?: string}>} baseline
 * @param {Record<string, {status: string, verdict?: any, counterexample?: string}>} current
 * @param {{expectViolated?: string[], accept?: string[]}} [options]
 * @returns {{code: string, id: string, before: string, after: string|null, message: string}[]}
 */
export function verifyRegressions(baseline, current, options = {}) {
  const expected = new Set(options.expectViolated ?? []);
  const accepted = new Set(options.accept ?? []);
  /** @type {{code: string, id: string, before: string, after: string|null, message: string}[]} */
  const out = [];
  /** @type {{id: string, b: any, a: any}[]} */
  const pending = [];
  for (const id of Object.keys(baseline).sort(byText)) {
    if (accepted.has(id)) continue;
    const b = baseline[id];
    if (!b || typeof b.status !== 'string') continue;
    const a = Object.hasOwn(current, id) ? current[id] : undefined;
    if (a && expected.has(id) && b.status === 'violated' && a.status === 'violated') {
      if (b.counterexample && a.counterexample && b.counterexample !== a.counterexample) {
        out.push({ code: 'verify.counterexample-changed', id, before: b.status, after: a.status, message: `Claim "${id}" is expected to be violated, but its counterexample changed (${b.counterexample} to ${a.counterexample}): the violation is no longer the known one.` });
      }
      continue;
    }
    if (a && a.status === 'violated' && expected.has(id)) continue;
    if (!b.verdict || (a && !a.verdict)) continue;
    pending.push({ id, b, a });
  }
  const regressions = isRegression(pending.map((x) => ({ old: x.b.verdict, new: x.a ? x.a.verdict : null })));
  pending.forEach((x, i) => {
    if (!regressions[i]) return;
    if (!x.a) out.push({ code: 'verify.claim-removed', id: x.id, before: x.b.status, after: null, message: `Claim "${x.id}" was ${x.b.status} and no longer exists.` });
    else out.push({ code: 'verify.claim-regressed', id: x.id, before: x.b.status, after: x.a.status, message: `Claim "${x.id}" moved from ${x.b.status} to ${x.a.status}${x.b.status === x.a.status ? ` (${verdictText(x.b.verdict)} to ${verdictText(x.a.verdict)})` : ''}.` });
  });
  const order = { 'verify.claim-removed': 0, 'verify.counterexample-changed': 1, 'verify.claim-regressed': 2 };
  return out.sort((x, y) => (order[/** @type {keyof typeof order} */ (x.code)] - order[/** @type {keyof typeof order} */ (y.code)]) || byText(x.id, y.id));
}

/**
 * Admission of a product file into a layered specification (WG-5685, criterion 7; composition F6). Each product's
 * state-invariant claims are checked over every execution of the scenario they list (its own scenario), and then
 * over the composed scenario of the installation: the behaviors of every installed product's scenarios and of the
 * candidate's, with all their steps, explored in every delivery order (src/core/refinement-explore.js). A claim
 * that holds alone but fails composed refuses the installation, naming the composed scenario's behaviors and the
 * values of the claim's references at the failing configuration. An exploration that is incomplete refuses it too:
 * the composition is not shown to keep the claim.
 * @param {string} baseText the platform specification
 * @param {{file: string, text: string, platform: any}[]} installed the product layers already installed
 * @param {{file: string, text: string, platform: any}} candidate the product layer to install
 * @returns {{verdict: 'admitted'|'rejected', reasons: any[], own: any[], composed: {behaviors: string[], steps: number}|null}}
 */
export function admitProduct(baseText, installed, candidate) {
  const after = analyzeLayers(baseText, [...installed, candidate]);
  /** @type {any[]} */
  const reasons = [];
  const errors = after.diagnostics.filter((d) => d.severity === 'error');
  if (!after.model || errors.length) {
    reasons.push({ code: 'admit.product-invalid', message: `The specification with ${candidate.file} installed has ${errors.length} error(s): ${errors.slice(0, 3).map((d) => d.code).join(', ')}.` });
    return { verdict: 'rejected', reasons, own: [], composed: null };
  }
  const model = after.model;
  const products = after.layers.map((l) => l.product).filter((p) => typeof p === 'string');
  const productOf = (/** @type {string} */ id) => products.find((p) => id.startsWith(`${p}${NAMESPACE_SEPARATOR}`)) ?? null;
  const claims = (model.byKind.claim ?? []).filter((c) => productOf(c.id) && c.data.evaluate?.method === 'state-invariant' && typeof c.data.evaluate.expr === 'string');
  const scenarioIds = [...new Set(claims.flatMap((c) => (Array.isArray(c.data.evaluate.scenarios) ? c.data.evaluate.scenarios : [])))].filter((id) => model.entities.get(id)?.kind === 'scenario');

  /** @type {any[]} */
  const own = [];
  for (const c of claims) {
    for (const sid of c.data.evaluate.scenarios ?? []) {
      if (!scenarioIds.includes(sid)) continue;
      const x = exploreInvariant(model, sid, c.data.evaluate.expr);
      own.push({ claim: c.id, product: productOf(c.id), scenario: sid, status: x.status, ...(x.status === 'failure' ? { values: x.failure.values } : {}), ...(x.status === 'incomplete' ? { reason: x.reason } : {}) });
    }
  }

  // The composed scenario: every behavior and every step of the products' scenarios, in time order.
  const scenarios = scenarioIds.map((id) => /** @type {any} */ (model.entities.get(id)));
  const behaviors = [...new Set(scenarios.flatMap((s) => (Array.isArray(s.data.behaviors) ? s.data.behaviors : [])))];
  const steps = scenarios.flatMap((s) => (Array.isArray(s.data.steps) ? s.data.steps : [])).map((st, i) => ({ st, i })).sort((a, b) => (a.st.at - b.st.at) || (a.i - b.i)).map((x) => x.st);
  const id = 'installation__composed';
  const sc = { kind: 'scenario', id, data: { id, name: 'Composed installation', behaviors, steps }, owner: null, path: [], loc: { line: 1, column: 1, offset: 0, length: 0 } };
  const composed = /** @type {any} */ ({ ...model, entities: new Map([...model.entities, [id, sc]]), byKind: { ...model.byKind, scenario: [...(model.byKind.scenario ?? []), sc] } });
  for (const c of claims) {
    const refs = exprBehaviors(c.data.evaluate.expr);
    if (!refs.every((b) => behaviors.includes(b))) continue;
    const x = exploreInvariant(composed, id, c.data.evaluate.expr);
    if (x.status === 'failure') {
      const values = Object.entries(x.failure.values).map(([k, v]) => `${k} = ${JSON.stringify(v)}`).join(', ');
      reasons.push({
        code: 'admit.product-composition-violated', id: c.id, product: productOf(c.id),
        scenario: { id, behaviors }, counterexample: { values: x.failure.values, order: x.order, stepIndex: x.failure.stepIndex },
        message: `Installing ${candidate.file} breaks claim "${c.id}" of product ${productOf(c.id)}: it holds on its own scenario, but in the composed scenario {${behaviors.join(', ')}} the execution delivering ${x.order.join(', ')} reaches ${values}, where \`${c.data.evaluate.expr}\` is false.`,
      });
    } else if (x.status === 'incomplete') {
      reasons.push({ code: 'admit.product-composition-unexplored', id: c.id, product: productOf(c.id), scenario: { id, behaviors }, message: `Claim "${c.id}" was not shown to hold in the composed scenario {${behaviors.join(', ')}}: ${x.reason}` });
    }
  }
  return { verdict: reasons.length ? 'rejected' : 'admitted', reasons, own, composed: { behaviors, steps: steps.length } };
}

/** The behaviors a claim expression reads (`<behavior>.<name>`). @param {string} src */
function exprBehaviors(src) {
  const p = parseExpr(src);
  return p.ok ? [...new Set(exprRefs(p.ast).filter((r) => r.length === 2).map((r) => r[0]))] : [];
}

/**
 * A state invariant over every configuration of every execution of a scenario.
 * @param {Model} model @param {string} scenarioId @param {string} src
 */
function exploreInvariant(model, scenarioId, src) {
  const p = parseExpr(src);
  if (!p.ok) return /** @type {const} */ ({ status: 'incomplete', reason: `The expression does not parse: ${p.error.message}.`, states: 0, steps: 0 });
  const refs = exprRefs(p.ast).filter((r) => r.length === 2);
  /** @param {any} config @param {number} stepIndex */
  const at = (config, stepIndex) => {
    const resolve = (/** @type {string[]} */ r) => {
      const m = config?.machines?.[r[0]];
      if (r.length !== 2 || !m) return undefined;
      return r[1] === 'state' ? m.state : m.vars?.[r[1]];
    };
    let v;
    try { v = evalExpr(p.ast, resolve); } catch (e) { return { unsupported: `the expression cannot be evaluated: ${/** @type {Error} */ (e).message}` }; }
    if (v === true) return null;
    return { failure: { stepIndex, values: Object.fromEntries(refs.map((r) => [r.join('.'), resolve(r)])) } };
  };
  return exploreExecutions(model, scenarioId, (trace) => {
    if (trace.steps.length === 1) { const r0 = at(trace.initial, -1); if (r0) return r0; }
    const last = trace.steps[trace.steps.length - 1];
    return at(last.config, last.index);
  });
}
