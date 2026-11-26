// Claim evaluation. The one rule of this module: never confuse "declared" with
// "true". A claim is `verified` only when an evaluator actually checked it
// against the model, and every result says precisely what was and was not
// checked (`scope`). Vacuous checks (a selector that selects nothing) are
// `inconclusive`. Trace-based checks say they cover the listed traces only.
// Evidence is author-entered unless a recorded result of executing it exists.
//
// Pure and deterministic: no DOM, no clocks, no randomness.

import { faultModelOf, faultModelScope, faultCoverage } from './fault-model.js';
import { CLAIM_METHODS } from './claim-methods.js';
import { own } from './own.js';
import { componentGraph, selectComponents } from './query.js';
import { parseExpr, evalExpr, exprRefs, ExprError } from './expr.js';
import { semanticHash } from './hash.js';
import { runScenario, runEngineText } from './engine.js';
import { evaluateMetricClaim, quantileKey } from './metric-claims.js';
import { simulationInput, durationIn } from './sim-input.js';
import { checkContractEvents } from './contract-trace.js';
import { evaluateDataClaim } from './data-model.js';
import { checkRefinementTrace, refinementOf } from './refinement.js';
import { scenarioMachineIds } from './pools.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */

/**
 * @typedef {{ summary: string, entities: string[], path?: string[], scenario?: string, stepIndex?: number,
 *   reason?: string, trace?: import('./refinement.js').RefinementStep[] }} Counterexample
 *   reason and trace: a refines claim's failing check and the steps of the implementation behavior up to it
 * @typedef {{ id: string, kind: string, ref: string, supports: boolean, recorded: 'pass'|'fail'|'none', detail?: string,
 *   title?: string, proofs?: string[], derived?: boolean, revision?: 'matches'|'unknown', stale?: boolean, freshness?: 'fresh'|'unverifiable' }} EvidenceItem
 *   derived: a Concordance result applied from the project's results file (src/core/concordance.js), not a spec entity;
 *   revision: for a derived item, whether its results file named this text's specSha256 ("unknown" when its results file names none);
 *   stale: its recorded result was recorded on another tree (its stamp differs from the current one): a stale pass is
 *   read as no result (`recorded` is "none"), a stale fail still contradicts; freshness: of a result read as it is
 *   (unverifiable: no current stamp to compare with)
 * @typedef {{ code: string, severity: 'warning'|'info', message: string, entityId: string }} ClaimDiagnostic
 *   claim.stale-evidence, claim.stale-theorem: a recorded fact was recorded for other files than the current ones;
 *   claim.freshness-unverifiable: recorded facts were read with no current stamp to compare (the browser bundle)
 * @typedef {{
 *   claimId: string, kind: string, method: string|null,
 *   status: 'proved'|'verified'|'supported'|'model-holds'|'violated'|'inconclusive'|'not-evaluated',
 *   evaluator: string, semanticHash: string, scope: string, explanation: string,
 *   assumptions: string[], involved: string[], counterexample?: Counterexample,
 *   evidence: EvidenceItem[], negatives?: NegativeRun[], modelledBy?: {claimId: string, status: string}[],
 *   freshness?: 'fresh'|'stale'|'unverifiable', diagnostics?: ClaimDiagnostic[]
 * }} ClaimResult
 *   modelledBy: on a requirement, the claims whose `models` property names it, with their statuses (declaration order);
 *   freshness: present when the status rests on recorded facts (evidence results, a Lean theorem check, an external
 *   tool's outcome): fresh when each was recorded on the current stamps, stale when one was not (the status is then
 *   never positive: not-evaluated, or violated by a contradicting fact), unverifiable when no current stamp was given
 * @typedef {{ scenario: string, faults: string[], violated: boolean, outcome: string, stepIndex?: number, explanation: string }} NegativeRun
 *   one declared negative of a trace claim: its scenario run with the scenario's faults plus `faults`
 * @typedef {Object} Recorded
 * @property {Record<string, { outcome: 'pass'|'fail'|'not-run', detail?: string, ranAt?: string, stamp?: string }>} [results]
 *   outcomes of executing evidence entities, keyed by evidence id (written by `exegra verify`);
 *   not-run counts as no result; stamp: the records stamp of the tree it was recorded on (tools/tree-stamp.js)
 * @property {Record<string, { outcome: 'pass'|'fail', status?: string, detail?: string, proofs?: string[], stamp?: string }>} [claims]
 *   outcomes an external verification tool established per claim, keyed by claim id
 * @property {string} [tool]  the tool that wrote `claims`
 * @property {{id: string, claim: string, title: string, ref: string, outcome: 'pass'|'fail', revision?: 'matches'|'unknown', detail?: string, proofs?: string[]}[]} [derived]
 *   Concordance results for claims, applied by src/core/concordance.js; never recorded back to results.json
 * @property {Record<string, TheoremCheck>} [theorems]
 *   what Lean reported about theorems named by lean-theorem claims, keyed by theorem name
 *   (tools/lean-theorems.js, recorded by `exegra verify`)
 * @typedef {{found: boolean, kind?: string, kernel?: string, axioms?: string[],
 *   about?: Record<string, {kind: string, inStatement: boolean, implementedBy?: string|null, extern?: boolean, partial?: boolean}>,
 *   lean?: string, checkedAt?: string, statementHash?: string, formalHash?: string, stamp?: string}} TheoremCheck
 *   formalHash: the hash of the formal/ sources the check ran on (tools/tree-stamp.js formalSourcesHash);
 *   statementHash: sha256 of the theorem's type as Lean printed it; stamp: the records stamp of the tree
 * @typedef {{tree: string|null, formal: string|null}} Stamps
 *   the current stamps a read compares recorded facts with (tools/tree-stamp.js currentStamps); null where none can
 *   be computed (the browser bundle), which makes the freshness of every recorded fact unverifiable
 */

const STRUCTURAL = 'exegra.structural/0.1';
const TRACE = 'exegra.trace/0.1';
const EVIDENCE = 'exegra.evidence/0.1';
const METRIC = 'exegra.metric/0.1';
const REFINEMENT = 'exegra.refinement/0.1';
const LEAN = 'lean.kernel';
/** The axioms a lean-theorem may depend on: Lean's standard three. */
export const STANDARD_AXIOMS = ['propext', 'Classical.choice', 'Quot.sound'];
/** Axioms that native_decide introduces: Lean.ofReduceBool/ofReduceNat, Lean.trustCompiler, and since
 * Lean 4.2x an auxiliary axiom per use, named <theorem>._native.native_decide.ax_<n>_<m>. */
const NATIVE_AXIOM = /^Lean\.(ofReduceBool|ofReduceNat|trustCompiler)$|\._native\.native_decide\./;
const TRACE_METHODS = ['state-invariant', 'precedes', 'eventually', 'never'];

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/**
 * Evaluate every claim in declaration order. `stamps` are the current stamps recorded facts are compared with
 * (tools/tree-stamp.js currentStamps): a fact recorded on other stamps is stale and never makes a claim positive.
 * Without stamps (absent, or null as in the browser bundle) recorded facts are read as they are and every result
 * that rests on them says its freshness is unverifiable.
 * @param {Model} model @param {{recorded?: Recorded|null, stamps?: Stamps|null}} [opts]
 * @returns {ClaimResult[]}
 */
export function evaluateClaims(model, opts = {}) {
  const hash = semanticHash(model);
  const outer = passRuns;
  passRuns = new Map();
  try {
    const results = (model.byKind.claim ?? []).map((c) => evaluateOne(model, c, hash, opts.recorded ?? undefined, opts.stamps ?? null));
    attachModelledBy(model, results);
    return results;
  } finally {
    passRuns = outer;
  }
}

/**
 * The traces already run in the current evaluateClaims pass, by scenario and fault list. Many trace claims
 * (and their negatives) run the same scenario with the same faults over the same model; one pass runs each
 * once. It exists only for the duration of a pass over one model, so nothing can go stale.
 * @type {Map<string, any>|null}
 */
let passRuns = null;

/**
 * runScenario, remembered for the rest of the current pass.
 * @param {Model} model @param {string} scenarioId @param {{faults?: string[]}} [opts]
 */
function runScenarioOnce(model, scenarioId, opts) {
  if (!passRuns) return runScenario(model, scenarioId, opts);
  const key = `${scenarioId}\0${opts?.faults ? opts.faults.join('\x01') : '*'}`;
  if (passRuns.has(key)) {
    const hit = passRuns.get(key);
    if (hit instanceof Error) throw hit;
    return hit;
  }
  try {
    const trace = runScenario(model, scenarioId, opts);
    passRuns.set(key, trace);
    return trace;
  } catch (e) {
    passRuns.set(key, e);
    throw e;
  }
}

/**
 * Evaluate one claim.
 * @param {Model} model @param {string} claimId @param {{recorded?: Recorded|null, stamps?: Stamps|null}} [opts]
 * @returns {ClaimResult}
 */
export function evaluateClaim(model, claimId, opts = {}) {
  const claim = model.entities.get(claimId);
  if (!claim || claim.kind !== 'claim') throw new Error(`Unknown claim "${claimId}".`);
  const hash = semanticHash(model);
  const result = evaluateOne(model, claim, hash, opts.recorded ?? undefined, opts.stamps ?? null);
  if (claim.data.kind === 'requirement') {
    const outer = passRuns;
    passRuns = new Map();
    try {
      const checks = modellingClaims(model, claim.id).map((c) => evaluateOne(model, c, hash, opts.recorded ?? undefined, opts.stamps ?? null));
      attachModelledBy(model, [result, ...checks]);
    } finally {
      passRuns = outer;
    }
  }
  return result;
}

/** The claims whose `models` property names the requirement, in declaration order. @param {Model} model @param {string} requirementId */
function modellingClaims(model, requirementId) {
  return (model.byKind.claim ?? []).filter((c) => (Array.isArray(c.data.models) ? c.data.models : [c.data.models]).includes(requirementId));
}

/**
 * Set `modelledBy` on the result of every requirement that some claim names in `models`: which model claims
 * restate it, and their statuses. It is information; it never changes the requirement's own status.
 * @param {Model} model @param {ClaimResult[]} results
 */
function attachModelledBy(model, results) {
  const status = new Map(results.map((r) => [r.claimId, r.status]));
  for (const r of results) {
    if (model.entities.get(r.claimId)?.data.kind !== 'requirement') continue;
    const by = modellingClaims(model, r.claimId).filter((c) => status.has(c.id)).map((c) => ({ claimId: c.id, status: /** @type {string} */ (status.get(c.id)) }));
    if (by.length) r.modelledBy = by;
  }
}

/**
 * Evaluate every applicable invariant/temporal claim against one trace.
 * A claim is applicable when every behavior it refers to is part of the
 * trace's scenario (an event matcher is always applicable).
 * @param {Model} model @param {any} trace
 * @returns {{claimId: string, holds: boolean, pending?: boolean, stepIndex?: number, explanation: string, automatic?: boolean, check?: string}[]}
 *   `pending` marks a check that is undecided on this (unfinished or unevaluable) trace; it is not a violation.
 */
export function checkTrace(model, trace) {
  const scenario = model.entities.get(trace.scenarioId);
  const behaviors = scenarioMachineIds(model, scenario);
  const out = [];
  for (const claim of model.byKind.claim ?? []) {
    if (claim.data.kind !== 'invariant' && claim.data.kind !== 'temporal') continue;
    const ev = claim.data.evaluate;
    if (!ev || typeof ev !== 'object' || !TRACE_METHODS.includes(ev.method)) continue;
    // A claim is stated about the scenarios it lists; it says nothing about other inputs.
    if (!Array.isArray(ev.scenarios) || !ev.scenarios.includes(trace.scenarioId)) continue;
    if (!applicable(model, ev, behaviors)) continue;
    const r = evalTraceProperty(model, ev, trace);
    const unfinished = trace.outcome !== 'quiescent';
    if (r.verdict === 'holds' && ev.method === 'state-invariant' && trace.outcome !== 'running' && !r.exercised && antecedentText(ev.expr) !== null) {
      out.push({ claimId: claim.id, holds: false, pending: true, explanation: `The antecedent \`${antecedentText(ev.expr)}\` was never true in this trace, so the implication was never exercised.` });
    } else if (r.verdict === 'holds') {
      out.push({ claimId: claim.id, holds: true, explanation: r.explanation + (unfinished ? ` The run is ${describeOutcome(trace)}, so this holds for the steps executed so far.` : '') });
    } else if (r.verdict === 'violated') {
      let explanation = r.explanation;
      if (r.absence && unfinished) explanation += ` The run is ${describeOutcome(trace)}, so this may still happen.`;
      const item = { claimId: claim.id, holds: false, explanation };
      // Something that has not happened yet in an unfinished run is undecided, not violated.
      if (r.absence && unfinished) /** @type {any} */ (item).pending = true;
      if (r.stepIndex !== undefined) /** @type {any} */ (item).stepIndex = r.stepIndex;
      out.push(item);
    } else {
      out.push({ claimId: claim.id, holds: false, pending: true, explanation: `Could not be evaluated on this trace: ${r.explanation}` });
    }
  }
  // Automatic checks that need no claim: the contract events of the trace (contract-trace.js).
  out.push(...checkContractEvents(model, trace));
  return out;
}

// ---------------------------------------------------------------------------
// Dispatch and evidence
// ---------------------------------------------------------------------------

/**
 * @param {Model} model @param {Entity} claim @param {string} hash @param {Recorded|undefined} recorded
 * @param {Stamps|null} stamps
 * @returns {ClaimResult}
 */
function evaluateOne(model, claim, hash, recorded, stamps) {
  const ev = claim.data.evaluate && typeof claim.data.evaluate === 'object' ? claim.data.evaluate : null;
  const method = ev && typeof ev.method === 'string' ? ev.method : null;
  const evidence = collectEvidence(model, claim.id, recorded, stamps);
  const subjects = Array.isArray(claim.data.subjects) ? claim.data.subjects.filter((/** @type {any} */ s) => typeof s === 'string') : [];
  /** @type {ClaimResult} */
  const result = {
    claimId: claim.id,
    kind: claim.data.kind,
    method,
    status: 'not-evaluated',
    evaluator: 'none',
    semanticHash: hash,
    scope: '',
    explanation: '',
    assumptions: Array.isArray(claim.data.assumptions) ? [...claim.data.assumptions] : [],
    involved: [],
    evidence,
  };

  /** @type {any} */
  let r;
  if (!ev || !method) {
    r = { status: 'not-evaluated', evaluator: 'none', scope: 'Nothing was checked: the claim declares no evaluation method.', explanation: 'The claim has no "evaluate.method", so Exegra has nothing to run and does not report a result.', selected: [] };
  } else if (own(model.meta.verificationMethods, method)) {
    // A method the specification declares as carried out by tools outside Exegra:
    // the status can only come from evidence, exactly as for "external-evidence".
    const label = own(model.meta.verificationMethods, method)?.label;
    const base = evaluateEvidenceClaim(claim, evidence, recorded);
    r = {
      ...base,
      evaluator: `external:${method}`,
      scope: `Exegra ran nothing. "${label}" verification is carried out outside Exegra; only recorded evidence is reported. ${base.scope ?? ''}`.trim(),
      selected: evidence.map((e) => e.id),
    };
    // An outcome the external tool recorded for this claim. It can establish
    // "supported" or "violated"; Exegra still verified nothing itself.
    const outside = recorded?.claims && Object.hasOwn(recorded.claims, claim.id) ? recorded.claims[claim.id] : undefined;
    // An outcome recorded on another tree stamp is stale: a stale pass establishes nothing, a stale fail still counts.
    const outsideStale = !!outside && typeof stamps?.tree === 'string' && outside.stamp !== stamps.tree;
    if (outside && (outside.outcome === 'pass' || outside.outcome === 'fail')) r.usedRecorded = true;
    if (outside && outsideStale && outside.outcome === 'pass' && base.status !== 'violated') {
      r.status = 'not-evaluated';
      r.explanation = `Stale: ${typeof recorded?.tool === 'string' && recorded.tool ? recorded.tool : 'an external tool'} recorded this claim as passing on ${outside.stamp ? `tree stamp ${String(outside.stamp).slice(0, 12)}` : 'a tree it did not stamp'}, not on the current tree (${stamps?.tree?.slice(0, 12)}), so it establishes nothing now.`;
      r.stale = true;
    } else if (outside && (outside.outcome === 'pass' || outside.outcome === 'fail')) {
      const tool = typeof recorded?.tool === 'string' && recorded.tool ? recorded.tool : 'an external tool';
      const proofs = Array.isArray(outside.proofs) && outside.proofs.length ? ` Proofs: ${outside.proofs.join(', ')}.` : '';
      const detail = typeof outside.detail === 'string' && outside.detail ? ` ${outside.detail}` : '';
      const contradicted = base.status === 'violated';
      if (outside.outcome === 'fail' || contradicted) {
        r.status = 'violated';
        r.explanation = outside.outcome === 'fail'
          ? `Recorded by ${tool} as failing.${detail}${proofs}`
          : `Recorded by ${tool} as passing, but evidence in this specification contradicts it. ${base.explanation}`;
        if (outside.outcome === 'fail') r.counterexample = { summary: `${tool} reports this requirement as not met.${detail}`, entities: [claim.id] };
      } else {
        r.status = 'supported';
        r.explanation = `Recorded by ${tool} as established by "${label}" verification.${detail}${proofs} Exegra did not check this itself; the result is as current as the recorded file.`;
      }
      r.scope = `Exegra ran nothing. The status is the outcome ${tool} recorded for this claim.`;
    }
  } else if (!Object.hasOwn(CLAIM_METHODS, method)) {
    r = { status: 'not-evaluated', evaluator: 'none', scope: `Nothing was checked: this build of Exegra has no evaluator for method "${method}".`, explanation: `Method "${method}" is not supported, so the claim stays not evaluated. It is declared, not established.`, selected: [] };
  } else if (method === 'metric-bound') {
    try {
      r = evaluateMetricBound(model, ev);
    } catch (e) {
      r = { status: 'inconclusive', evaluator: METRIC, scope: 'The metric claim could not be completed.', explanation: `The evaluator failed: ${/** @type {Error} */ (e).message}`, selected: [] };
    }
  } else if (method === 'refines') {
    try {
      r = evaluateRefines(model, ev);
    } catch (e) {
      r = { status: 'inconclusive', evaluator: REFINEMENT, scope: 'The refinement check could not be completed.', explanation: `The evaluator failed: ${/** @type {Error} */ (e).message}`, selected: [] };
    }
    if (r.status === 'verified') {
      const bad = evidence.filter((e) => !e.supports || e.recorded === 'fail');
      if (bad.length) {
        r.status = 'violated';
        r.explanation += ` However, ${describeContradictions(bad)} contradict${bad.length === 1 ? 's' : ''} this result, so the claim is reported as violated.`;
        r.counterexample = { summary: `Contradicting evidence: ${bad.map((e) => e.id).join(', ')}.`, entities: bad.map((e) => e.id) };
      }
    }
  } else if (method === 'external-evidence') {
    r = { ...evaluateEvidenceClaim(claim, evidence, recorded), evaluator: EVIDENCE, selected: evidence.map((e) => e.id) };
  } else if (method === 'lean-theorem') {
    r = evaluateLeanTheorem(ev, recorded, stamps);
    if (r.status === 'proved') {
      const bad = evidence.filter((e) => !e.supports || e.recorded === 'fail');
      if (bad.length) {
        r.status = 'violated';
        r.explanation += ` However, ${describeContradictions(bad)} contradict${bad.length === 1 ? 's' : ''} it, so the claim is reported as violated.`;
        r.counterexample = { summary: `Contradicting evidence: ${bad.map((e) => e.id).join(', ')}.`, entities: bad.map((e) => e.id) };
      }
    }
  } else {
    try {
      r = TRACE_METHODS.includes(method) ? evaluateTraceClaim(model, claim, ev) : { ...evaluateStructural(model, ev), evaluator: STRUCTURAL };
    } catch (e) {
      r = { status: 'inconclusive', evaluator: TRACE_METHODS.includes(method) ? TRACE : STRUCTURAL, scope: `Method "${method}" could not be completed.`, explanation: `The evaluator failed: ${/** @type {Error} */ (e).message}`, selected: [] };
    }
    // Evidence can only make a model-evaluated claim worse, never better.
    if (r.status === 'verified') {
      const bad = evidence.filter((e) => !e.supports || e.recorded === 'fail');
      if (bad.length) {
        r.status = 'violated';
        r.explanation += ` However, ${describeContradictions(bad)} contradict${bad.length === 1 ? 's' : ''} this result, so the claim is reported as violated.`;
        r.counterexample = { summary: `Contradicting evidence: ${bad.map((e) => e.id).join(', ')}.`, entities: bad.map((e) => e.id) };
      }
    }
  }

  result.status = r.status;
  result.evaluator = r.evaluator;
  result.scope = r.scope;
  result.explanation = r.explanation;
  const fm = faultModelOf(model, claim);
  if (fm) {
    result.scope = `${faultModelScope(model, fm)} ${r.scope}`.trim();
    if (method && TRACE_METHODS.includes(method)) result.explanation = `${r.explanation} ${faultCoverage(model, fm, ev)}`.trim();
  }
  if (r.counterexample) result.counterexample = r.counterexample;
  if (r.negatives) result.negatives = r.negatives;
  result.involved = unique([...subjects, ...(r.selected ?? []), ...(r.counterexample?.entities ?? []), ...(r.counterexample?.path ?? [])]);
  applyFreshness(result, r, method, model, stamps);
  return result;
}

const POSITIVE = new Set(['proved', 'verified', 'supported', 'model-holds']);

/**
 * Set `freshness` and the freshness diagnostics of a result whose status rests on recorded facts: evidence
 * results (for the evidence-based methods), a Lean theorem check, an external tool's outcome. The status rule
 * itself is applied where each fact is read (collectEvidence, evaluateEvidenceClaim, evaluateLeanTheorem); this
 * only reports it. Without current stamps a positive status keeps its value but says its freshness is unverifiable.
 * @param {ClaimResult} result @param {any} r the evaluator's outcome @param {string|null} method @param {Model} model
 * @param {Stamps|null} stamps
 */
function applyFreshness(result, r, method, model, stamps) {
  const evidenceBased = method === 'external-evidence' || (method !== null && !!own(model.meta.verificationMethods, method));
  const staleEvidence = result.evidence.filter((e) => e.stale);
  /** @type {ClaimDiagnostic[]} */
  const diagnostics = [];
  if (staleEvidence.length) {
    diagnostics.push({ code: 'claim.stale-evidence', severity: 'warning', entityId: result.claimId,
      message: `The recorded result of ${staleEvidence.map((e) => `"${e.id}"`).join(', ')} was recorded on another tree than the current one; it is stale until exegra verify runs again.` });
  }
  if (r.staleTheorem) {
    diagnostics.push({ code: 'claim.stale-theorem', severity: 'warning', entityId: result.claimId, message: r.staleTheorem });
  }
  if (r.stale && !staleEvidence.length && !r.staleTheorem) {
    diagnostics.push({ code: 'claim.stale-evidence', severity: 'warning', entityId: result.claimId, message: 'The outcome an external tool recorded for this claim was recorded on another tree than the current one.' });
  }
  const usedEvidence = evidenceBased && result.evidence.some((e) => !e.derived && (e.recorded !== 'none' || e.stale));
  const usedRecorded = usedEvidence || !!r.usedTheorem || !!r.usedRecorded;
  const stale = (evidenceBased && staleEvidence.length > 0) || !!r.staleTheorem || !!r.stale;
  if (stale) result.freshness = 'stale';
  else if (usedRecorded && (method === 'lean-theorem' ? typeof stamps?.formal !== 'string' : typeof stamps?.tree !== 'string')) {
    result.freshness = 'unverifiable';
    diagnostics.push({ code: 'claim.freshness-unverifiable', severity: 'info', entityId: result.claimId,
      message: 'No stamp of the current files is available here, so whether the recorded facts this status rests on describe them cannot be checked.' });
    if (POSITIVE.has(result.status)) result.explanation += ' Freshness unverifiable: no stamp of the current files is available here, so this rests on results recorded for files that may since have changed.';
  } else if (usedRecorded) result.freshness = 'fresh';
  if (diagnostics.length) result.diagnostics = diagnostics;
}

// ---------------------------------------------------------------------------
// Lean theorems
// ---------------------------------------------------------------------------

/**
 * The theorems the lean-theorem claims of a model name, with the implementation constants each must
 * be about: what tools/lean-theorems.js is asked to check.
 * @param {Model} model
 * @returns {{theorem: string, about: string[]}[]}
 */
export function theoremRequests(model) {
  /** @type {Map<string, Set<string>>} */
  const by = new Map();
  for (const c of model.byKind.claim ?? []) {
    const ev = c.data.evaluate;
    if (!ev || ev.method !== 'lean-theorem' || typeof ev.theorem !== 'string' || !ev.theorem) continue;
    const set = by.get(ev.theorem) ?? new Set();
    for (const a of Array.isArray(ev.about) ? ev.about : []) if (typeof a === 'string') set.add(a);
    by.set(ev.theorem, set);
  }
  return [...by].map(([theorem, about]) => ({ theorem, about: [...about].sort() }));
}

/**
 * A lean-theorem claim, decided from what Lean reported (recorded.theorems). Pure: Lean ran in
 * tools/lean-theorems.js; this applies the rule. Proved only when the theorem exists, is a theorem,
 * the kernel accepted its proof again, every axiom it depends on is standard, the claim names at least one
 * implementation constant, and every named one is a definition (not an opaque constant, and not one the record
 * reports as implemented_by, extern or partial: its runtime body is then not the definition the theorem is
 * about) that occurs in its statement. A record checked on other formal/ sources than the current ones
 * (formalHash differs from stamps.formal) is stale: it never proves the claim, which is then not evaluated.
 * @param {any} ev @param {Recorded|undefined} recorded @param {Stamps|null} [stamps]
 */
function evaluateLeanTheorem(ev, recorded, stamps = null) {
  const thm = typeof ev.theorem === 'string' ? ev.theorem : '';
  const about = Array.isArray(ev.about) ? ev.about.filter((/** @type {any} */ a) => typeof a === 'string') : [];
  const rec = recorded?.theorems && Object.hasOwn(recorded.theorems, thm) ? recorded.theorems[thm] : undefined;
  const lean = rec?.lean ? `Lean ${rec.lean}` : 'Lean';
  const evaluator = rec?.lean ? `${LEAN}/${rec.lean}` : LEAN;
  const scope = `Checked by ${lean}${rec?.checkedAt ? ` at ${rec.checkedAt}` : ''}, as recorded: the theorem's proof re-checked by the kernel and its axioms collected. It establishes the statement about the Lean definitions it names. That the code which runs is those definitions rests on the trusted base: the Lean compiler and runtime, the WebAssembly toolchain and the JS glue (the claim's assumptions).`;
  const notChecked = (/** @type {string} */ why) => ({ status: 'not-evaluated', evaluator, scope: 'Nothing was checked: there is no recorded Lean check for this claim.', explanation: why, selected: [] });
  if (!thm) return notChecked('The claim names no theorem.');
  if (!rec) return notChecked(`Lean has not checked "${thm}": run "exegra verify" (or "exegra claims" where Lean is installed) to record the check.`);
  /** @param {string} why */
  const refuse = (why) => ({
    status: 'violated', evaluator, scope, selected: [],
    explanation: `Lean refuses "${thm}" as a proof of this claim: ${why}`,
    counterexample: { summary: `Lean refuses ${thm}: ${why}`, entities: [] },
  });
  if (!rec.found) return refuse('no such constant exists in the Lean core.');
  if (rec.kind !== 'theorem') return refuse(`it is ${rec.kind === 'axiom' ? 'an axiom' : `a ${rec.kind}`}, not a theorem.`);
  if (rec.kernel !== 'ok') return refuse(`the kernel does not accept its proof (${rec.kernel}).`);
  const axioms = Array.isArray(rec.axioms) ? rec.axioms : [];
  const extra = axioms.filter((a) => !STANDARD_AXIOMS.includes(a));
  if (extra.length) {
    const why = extra.map((a) => (a === 'sorryAx' ? 'sorryAx (the proof uses sorry)'
      : NATIVE_AXIOM.test(a) ? `${a} (the proof uses native_decide, which trusts compiled code instead of the kernel)`
        : `${a} (an axiom beyond Lean's standard ones)`));
    return refuse(`it depends on ${why.join(', ')}.`);
  }
  // A claim proved in Lean presents itself as a theorem about the code: it must name that code.
  if (!about.length) return refuse('the claim names no implementation constant ("about"), so the theorem is not shown to be about any code.');
  const unchecked = about.filter((/** @type {string} */ a) => !rec.about || !Object.hasOwn(rec.about, a));
  if (unchecked.length) return notChecked(`The recorded check of "${thm}" did not cover ${unchecked.map((/** @type {string} */ a) => `"${a}"`).join(', ')}: run "exegra verify" again.`);
  for (const a of about) {
    const info = /** @type {{kind: string, inStatement: boolean, implementedBy?: string|null, extern?: boolean, partial?: boolean}} */ (/** @type {any} */ (rec.about)[a]);
    if (info.kind === 'missing') return refuse(`the implementation constant "${a}" does not exist.`);
    if (info.kind === 'opaque') return refuse(`"${a}" is an opaque constant: a theorem about it says nothing about the body that runs (a partial def and an implemented_by opaque compile to one).`);
    if (info.kind !== 'definition') return refuse(`"${a}" is a ${info.kind}, not an implementation constant (a definition).`);
    if (info.implementedBy) return refuse(`"${a}" is implemented_by ${info.implementedBy}: the code that runs is not the definition the theorem is about.`);
    if (info.extern) return refuse(`"${a}" is extern: the code that runs is foreign code, not the definition the theorem is about.`);
    if (info.partial) return refuse(`"${a}" is a partial definition: its compiled body is not the definition the theorem is about.`);
    if (!info.inStatement) return refuse(`its statement does not mention the implementation constant "${a}", so it is not a theorem about that code.`);
  }
  // Read-time freshness: the check holds for the formal/ sources it ran on. Refusals above stand even when stale
  // (staleness never improves a status); a stale positive check proves nothing.
  if (typeof stamps?.formal === 'string' && rec.formalHash !== stamps.formal) {
    const why = `Stale: the recorded Lean check of "${thm}" ${rec.formalHash ? `ran on formal/ sources with hash ${String(rec.formalHash).slice(0, 12)}` : 'carries no hash of the formal/ sources it ran on'}, not on the current ones (${stamps.formal.slice(0, 12)}); run "exegra verify" where Lean is installed to check it again.`;
    return { status: 'not-evaluated', evaluator, scope: 'Nothing was checked against the current sources: the recorded Lean check is stale.', explanation: why, selected: [], usedTheorem: true, staleTheorem: why };
  }
  return {
    status: 'proved', evaluator, scope, selected: [], usedTheorem: true,
    explanation: `"${thm}" is a theorem; the Lean kernel accepted its proof again; it depends only on ${axioms.length ? axioms.join(', ') : 'no axiom'}; its statement is about ${about.join(', ')}${rec.statementHash ? ` (statement hash ${String(rec.statementHash).slice(0, 12)})` : ''}.`,
  };
}

// ---------------------------------------------------------------------------
// Metric claims (docs/simulation.md, "Claims over metrics")
// ---------------------------------------------------------------------------

/**
 * A metric-bound claim: each listed scenario (a format-2 scenario) runs N times with the run
 * seeds of the claim's seed, through the engine, and the per-run statistic decides by the exact
 * binomial test or the sign-test interval (src/core/metric-claims.js). A bound written as a
 * duration is converted to the base unit of the first scenario. The result is `model-holds`,
 * `violated` or `inconclusive`, never verified, and states N, the passes, β, the confidence and the
 * seeds' base.
 * @param {Model} model @param {any} ev
 */
function evaluateMetricBound(model, ev) {
  const sids = Array.isArray(ev.scenarios) ? ev.scenarios : [ev.scenarios];
  /** @param {string} sid @param {string[]} extra */
  const inputOf = (sid, extra) => {
    const sc = /** @type {any} */ (model.entities.get(sid));
    const own = Array.isArray(sc?.data?.faults) ? sc.data.faults : [];
    const input = /** @type {any} */ (simulationInput(model, sid, [...own, ...extra]));
    if (input.version !== 2) throw new Error(`Scenario "${sid}" is not a format-2 scenario: it declares no workloads, seed or horizon.`);
    const st = String(ev.metric?.statistic ?? '');
    if (/^p\d/.test(st)) {
      const qs = input.metrics?.quantiles ?? ['0.5', '0.9', '0.99'];
      input.metrics = { ...(input.metrics ?? {}), quantiles: [...new Set([...qs, quantileKey(st)])] };
    }
    return input;
  };
  const first = inputOf(sids[0], []);
  const unit = first.time.unit;
  /** @param {any} v */
  const num = (v) => (typeof v === 'string' && /[a-z]$/.test(v.trim()) ? String(durationIn(v, unit, 'bound')) : String(v));
  const claim = {
    metric: ev.metric, op: ev.op, bound: ev.bound === undefined ? undefined : num(ev.bound),
    approx: ev.approx ? { value: num(ev.approx.value), tolerance: String(ev.approx.tolerance) } : undefined,
    runs: Number(ev.runs ?? 59), fraction: ev.fraction ?? '0.95', confidence: ev.confidence ?? '0.95', seed: String(ev.seed ?? '0'),
  };
  const run = (/** @type {string} */ text) => JSON.parse(runEngineText(text));
  const neg = (/** @type {any[]} */ xs) => (Array.isArray(xs) ? xs : []).map((n) => inputOf(n.scenario, n.faults ?? []));
  const res = evaluateMetricClaim(run, { scenarios: sids.map((/** @type {string} */ sid) => inputOf(sid, [])), negatives: neg(ev.negatives), controlNegatives: neg(ev.controlNegatives) }, claim);
  const show = (/** @type {any} */ s, /** @type {string} */ what) => `${what}: ${s.verdict} over ${s.kept} of ${s.runs} runs${s.passes !== undefined ? ` (${s.passes} pass)` : ''}${s.leftOut ? `, ${s.leftOut} left out as underpowered` : ''}${s.underpowered > s.leftOut ? `, ${s.underpowered - s.leftOut} underpowered counted as not satisfying (${s.openStarted ? 'duplicate starts' : 'the class is not open-started'})` : ''}${s.truncated ? `, ${s.truncated} truncated` : ''}`;
  const parts = [
    ...res.scenarios.map((s, i) => show(s, `scenario "${sids[i]}"`)),
    ...res.negatives.map((s, i) => show(s, `negative ${i} (${ev.negatives[i].scenario} with ${ev.negatives[i].faults.join(', ')})`)),
    ...res.controlNegatives.map((s, i) => show(s, `control negative ${i} (${ev.controlNegatives[i].scenario} with ${ev.controlNegatives[i].faults.join(', ')})`)),
  ];
  const head = res.status === 'model-holds'
    ? `Holds in the model at ${claim.confidence} confidence over ${claim.runs} runs per scenario; parameters assumed, unvalidated.`
    : res.status === 'violated' ? `Fails in the model at ${claim.confidence} confidence over ${claim.runs} runs.` : `Inconclusive over ${claim.runs} runs: ${res.reason}.`;
  /** @type {any} */
  const out = {
    status: res.status, evaluator: METRIC,
    scope: `Model only; parameters as stated. Seeded runs: N = ${claim.runs}, β = ${claim.fraction}, confidence ${claim.confidence}, base seed ${claim.seed}${ev.asOf ? `, as of ${ev.asOf}` : ''}. Never verified, never counted as evidence.`,
    explanation: `${head} ${parts.join('; ')}.`,
    selected: [...sids],
  };
  if (res.status === 'violated') {
    const s = res.scenarios.find((x) => x.verdict === 'fails');
    const worst = s?.statistics?.find((/** @type {any} */ x) => x.value === 'inf') ?? s?.statistics?.[0];
    out.counterexample = { summary: `A failing scenario; replay seed ${worst?.seed ?? '?'} as a trace.`, entities: [...sids] };
  }
  return out;
}

/** @param {EvidenceItem[]} bad */
function describeContradictions(bad) {
  return bad.map((e) => (e.derived ? `evidence "${e.id}" (Concordance recorded: fail)` : e.recorded === 'fail' ? `evidence "${e.id}" (recorded result: fail)` : `evidence "${e.id}" (declared as contradicting)`)).join(' and ');
}

/**
 * The evidence entities of a claim with their recorded results. With a current tree stamp, a result recorded on
 * another stamp (or with none) is stale: a stale pass is read as no result, a stale fail still contradicts.
 * @param {Model} model @param {string} claimId @param {Recorded|undefined} recorded @param {Stamps|null} [stamps]
 * @returns {EvidenceItem[]}
 */
function collectEvidence(model, claimId, recorded, stamps = null) {
  /** @type {EvidenceItem[]} */
  const out = [];
  for (const e of model.byKind.evidence ?? []) {
    if (e.data.claim !== claimId) continue;
    const rec = recorded?.results && Object.hasOwn(recorded.results, e.id) ? recorded.results[e.id] : undefined;
    const outcome = rec && (rec.outcome === 'pass' || rec.outcome === 'fail') ? rec.outcome : 'none';
    const stale = outcome !== 'none' && typeof stamps?.tree === 'string' && rec?.stamp !== stamps.tree;
    /** @type {EvidenceItem} */
    const item = {
      id: e.id,
      kind: e.data.kind,
      ref: typeof e.data.ref === 'string' ? e.data.ref : '',
      supports: e.data.supports !== false,
      recorded: stale && outcome === 'pass' ? 'none' : outcome,
    };
    if (stale) item.stale = true;
    else if (outcome !== 'none') item.freshness = typeof stamps?.tree === 'string' ? 'fresh' : 'unverifiable';
    const detail = rec?.detail ?? (typeof e.data.observed === 'string' ? e.data.observed : undefined);
    if (detail !== undefined) item.detail = detail;
    out.push(item);
  }
  for (const d of recorded?.derived ?? []) {
    if (d.claim !== claimId) continue;
    /** @type {EvidenceItem} */
    const item = { id: d.id, kind: 'test', ref: d.ref, supports: true, recorded: d.outcome, title: d.title, derived: true, revision: d.revision };
    if (d.detail !== undefined) item.detail = d.detail;
    if (d.proofs !== undefined) item.proofs = d.proofs;
    out.push(item);
  }
  return out;
}

/**
 * @param {Entity} claim @param {EvidenceItem[]} evidence @param {Recorded|undefined} recorded
 */
function evaluateEvidenceClaim(claim, evidence, recorded) {
  void recorded;
  if (!evidence.length) {
    return {
      status: /** @type {const} */ ('not-evaluated'),
      scope: 'Nothing was checked: the model cannot establish this claim and no evidence is attached to it.',
      explanation: `Claim "${claim.id}" relies on external evidence, but no evidence entity refers to it. It is declared, not established.`,
    };
  }
  const recordedCount = evidence.filter((e) => e.recorded !== 'none').length;
  const scope = `No model evaluation was performed. This rests on ${evidence.length} evidence ${evidence.length === 1 ? 'entity' : 'entities'} (${evidence.map((e) => e.id).join(', ')}), of which ${recordedCount} ${recordedCount === 1 ? 'has' : 'have'} a recorded execution result; the rest is author-entered.`;
  const bad = evidence.filter((e) => !e.supports || e.recorded === 'fail');
  if (bad.length) {
    return {
      status: /** @type {const} */ ('violated'),
      scope,
      explanation: `${capitalise(describeContradictions(bad))} contradict${bad.length === 1 ? 's' : ''} the claim.`,
      counterexample: { summary: `Contradicting evidence: ${bad.map((e) => e.id).join(', ')}.`, entities: bad.map((e) => e.id) },
    };
  }
  // A result recorded on another tree than the current one establishes nothing now: the claim is not evaluated
  // until exegra verify records it again, whatever else is attached.
  const stale = evidence.filter((e) => e.stale);
  if (stale.length) {
    return {
      status: /** @type {const} */ ('not-evaluated'),
      scope,
      explanation: `Stale: the recorded result${stale.length === 1 ? '' : 's'} of ${list(stale.map((e) => `"${e.id}"`))} ${stale.length === 1 ? 'was' : 'were'} recorded on another tree than the current one (the stamp differs or is missing), so ${stale.length === 1 ? 'it establishes' : 'they establish'} nothing now; run exegra verify to record ${stale.length === 1 ? 'it' : 'them'} again.`,
    };
  }
  const passedTests = evidence.filter((e) => e.kind === 'test' && !e.derived && e.recorded === 'pass');
  const passedDerived = evidence.filter((e) => e.derived && e.recorded === 'pass');
  const nonTests = evidence.filter((e) => e.kind !== 'test');
  const pendingTests = evidence.filter((e) => e.kind === 'test' && !e.derived && e.recorded === 'none');
  if (passedTests.length || passedDerived.length || nonTests.length) {
    const parts = [];
    if (passedTests.length) parts.push(`Exegra holds a recorded result of executing ${list(passedTests.map((e) => e.id))}: pass.`);
    for (const e of passedDerived) parts.push(`Concordance recorded "${e.id}" as passing, a result Exegra did not execute.${e.revision === 'unknown' ? ' It was computed for an unknown revision of the specification (the results file names no specSha256), so it may describe an earlier text.' : ''}${e.detail ? ` ${e.detail}` : ''}${e.proofs?.length ? ` Proofs: ${e.proofs.join(', ')}.` : ''}`);
    if (nonTests.length) parts.push(`${capitalise(list(nonTests.map((e) => `${e.kind} "${e.id}"`)))} ${nonTests.length === 1 ? 'is' : 'are'} author-entered only; Exegra did not execute or check ${nonTests.length === 1 ? 'it' : 'them'}.`);
    if (pendingTests.length) parts.push(`Test evidence ${list(pendingTests.map((e) => `"${e.id}"`))} has no recorded result.`);
    if (!passedTests.length) parts.unshift('Exegra executed nothing for this claim.');
    return { status: /** @type {const} */ ('supported'), scope, explanation: parts.join(' ') };
  }
  return {
    status: /** @type {const} */ ('inconclusive'),
    scope,
    explanation: `Only test evidence (${list(pendingTests.map((e) => `"${e.id}"`))}) is attached and no result of running it is recorded, so Exegra cannot tell whether the test passes.`,
  };
}

// ---------------------------------------------------------------------------
// Structural evaluators
// ---------------------------------------------------------------------------

/** @typedef {{ status: string, scope: string, explanation: string, selected: string[], counterexample?: Counterexample, negatives?: NegativeRun[] }} Outcome */

/** @param {Model} model @param {any} ev @returns {Outcome} */
function evaluateStructural(model, ev) {
  switch (ev.method) {
    case 'no-relationship': return noRelationship(model, ev);
    case 'reachable': return reachable(model, ev);
    case 'only-via': return onlyVia(model, ev);
    case 'has-port': return hasPort(model, ev);
    case 'property-defined': return propertyDefined(model, ev);
    case 'acyclic': return acyclic(model, ev);
    case 'data-model': return evaluateDataClaim(model, ev);
    case 'implementation-language': return implementationLanguage(model, ev);
  }
  throw new Error(`No structural evaluator for "${ev.method}".`);
}

/** @param {string} scope @param {string} explanation @param {string[]} [selected] @returns {Outcome} */
function inconclusive(scope, explanation, selected = []) {
  return { status: 'inconclusive', scope, explanation, selected };
}

/**
 * Select components and return their ids; also reports an empty selection.
 * @param {Model} model @param {any} selector
 */
function select(model, selector) {
  return selectComponents(model, selector).map((c) => c.id);
}

/**
 * Validate the `kinds` and `where` parameters. Returns {kinds, where} or {error}.
 * @param {Model} model @param {any} ev
 * @returns {{kinds: string[]|null, where: {property: string, values: string[]}|null} | {error: string}}
 */
function checkKinds(model, ev) {
  const w = checkWhere(model, ev.where);
  if ('error' in w) return w;
  const kinds = ev.kinds;
  if (kinds === undefined) return { kinds: null, where: w.where };
  if (!Array.isArray(kinds) || !kinds.every((k) => typeof k === 'string')) return { error: 'The "kinds" parameter is not a list of relationship kind names.' };
  if (!kinds.length) return { error: 'The "kinds" parameter lists no relationship kind, so nothing can be followed.' };
  const unknown = kinds.filter((k) => !Object.hasOwn(model.meta.relationshipKinds, k));
  if (unknown.length) return { error: `Unknown relationship kind${unknown.length === 1 ? '' : 's'} ${list(unknown.map((k) => `"${k}"`))}; a misspelt kind would make the check pass vacuously.` };
  return { kinds, where: w.where };
}

/**
 * Validate a `where` filter on relationship properties. A value no relationship
 * carries is an error: a misspelt value would empty the graph and pass vacuously.
 * @param {Model} model @param {any} where
 * @returns {{where: {property: string, values: string[]}|null} | {error: string}}
 */
function checkWhere(model, where) {
  if (where === undefined) return { where: null };
  if (!where || typeof where !== 'object' || typeof where.property !== 'string' || !Array.isArray(where.values) || !where.values.length || !where.values.every((/** @type {any} */ x) => typeof x === 'string')) return { error: 'The "where" parameter is not {"property": name, "values": [one or more strings]}.' };
  const carried = new Set((model.byKind.relationship ?? []).map((r) => r.data[where.property]));
  const unknown = where.values.filter((x) => !carried.has(x));
  if (unknown.length) return { error: `No relationship has ${where.property} ${list(unknown.map((x) => `"${x}"`))}; a misspelt value would make the check pass vacuously.` };
  return { where: { property: where.property, values: where.values } };
}

/** @param {string[]|null} kinds @param {{property: string, values: string[]}|null} [where] */
const kindsText = (kinds, where) => (kinds ? `kinds ${kinds.join(', ')}` : 'all kinds') + (where ? ` with ${where.property} ${where.values.join(' or ')}` : '');

/** @param {Map<string, {to: string, rel: string}[]>} g */
const edgeCount = (g) => [...g.values()].reduce((n, es) => n + es.length, 0);

/** @param {number} n @param {string} one @param {string} many */
const plural = (n, one, many) => `${n} ${n === 1 ? one : many}`;

/**
 * Shortest directed path (at least one relationship) from `source` to any node
 * accepted by `isTarget`, never entering a blocked node. The result alternates
 * component and relationship ids. The source itself is a valid end only when
 * it is reached again through at least one relationship.
 * @param {Map<string, {to: string, rel: string}[]>} g
 * @param {string} source @param {(id: string) => boolean} isTarget @param {(id: string) => boolean} [blocked]
 * @returns {string[]|null}
 */
function findPath(g, source, isTarget, blocked) {
  const visited = new Set([source]);
  /** @type {Map<string, {from: string, rel: string}>} */
  const pred = new Map();
  const queue = [source];
  for (let qi = 0; qi < queue.length; qi++) {
    const u = queue[qi];
    for (const e of g.get(u) ?? []) {
      const v = e.to;
      if (blocked?.(v)) continue;
      if (isTarget(v)) {
        const path = [e.rel, v];
        let node = u;
        for (;;) {
          path.unshift(node);
          if (node === source) break;
          const p = /** @type {{from: string, rel: string}} */ (pred.get(node));
          path.unshift(p.rel);
          node = p.from;
        }
        return path;
      }
      if (visited.has(v)) continue;
      visited.add(v);
      pred.set(v, { from: u, rel: e.rel });
      queue.push(v);
    }
  }
  return null;
}

/** Component and relationship ids of a path, split. @param {string[]} path */
const pathRels = (path) => path.filter((_, i) => i % 2 === 1);

/** @param {Model} model @param {any} ev @returns {Outcome} */
function noRelationship(model, ev) {
  const k = checkKinds(model, ev);
  const from = select(model, ev.from);
  const to = select(model, ev.to);
  if ('error' in k) return inconclusive('Nothing was checked.', k.error, [...from, ...to]);
  if (!from.length || !to.length) return inconclusive('Nothing was checked: a selector selected no component.', `The "${from.length ? 'to' : 'from'}" selector selects no component, so "no relationship" would hold vacuously. It is not reported as verified.`, [...from, ...to]);
  const g = componentGraph(model, { kinds: k.kinds, where: k.where });
  const toSet = new Set(to);
  const transitive = ev.transitive === true;
  const scope = `Checked the ${plural(edgeCount(g), 'relationship', 'relationships')} of ${kindsText(k.kinds, k.where)} between ${plural(from.length, 'source component', 'source components')} and ${plural(to.length, 'target component', 'target components')}${transitive ? ', following multi-hop paths too,' : ' (direct relationships only)'} at this model revision.`;
  const selected = [...from, ...to];

  /** @type {{rel: string, from: string, to: string}[]} */
  const direct = [];
  for (const f of from) for (const e of g.get(f) ?? []) if (toSet.has(e.to)) direct.push({ rel: e.rel, from: f, to: e.to });
  if (direct.length) {
    const first = direct[0];
    return {
      status: 'violated', scope, selected,
      explanation: `Relationship "${first.rel}" leads from "${first.from}" to "${first.to}"${direct.length > 1 ? `, and ${direct.length - 1} more do` : ''}, although no relationship was to exist.`,
      counterexample: { summary: `${plural(direct.length, 'relationship', 'relationships')} from the source to the target set: ${direct.map((d) => d.rel).join(', ')}.`, entities: direct.map((d) => d.rel), path: [first.from, first.rel, first.to] },
    };
  }
  if (transitive) {
    for (const f of from) {
      const path = findPath(g, f, (id) => toSet.has(id));
      if (path) {
        return {
          status: 'violated', scope, selected,
          explanation: `A path of ${plural(pathRels(path).length, 'relationship', 'relationships')} leads from "${path[0]}" to "${path[path.length - 1]}": ${path.join(' -> ')}.`,
          counterexample: { summary: `Path ${path.join(' -> ')}.`, entities: pathRels(path), path },
        };
      }
    }
  }
  return { status: 'verified', scope, selected, explanation: `No ${transitive ? 'directed path' : 'relationship'} of ${kindsText(k.kinds, k.where)} leads from any of the ${from.length} source components to any of the ${to.length} target components.` };
}

/** @param {Model} model @param {any} ev @returns {Outcome} */
function reachable(model, ev) {
  const k = checkKinds(model, ev);
  const from = select(model, ev.from);
  const to = select(model, ev.to);
  if ('error' in k) return inconclusive('Nothing was checked.', k.error, [...from, ...to]);
  if (!from.length || !to.length) return inconclusive('Nothing was checked: a selector selected no component.', `The "${from.length ? 'to' : 'from'}" selector selects no component, so reachability cannot be decided. It is not reported as verified.`, [...from, ...to]);
  const g = componentGraph(model, { kinds: k.kinds, where: k.where });
  const toSet = new Set(to);
  const scope = `Checked directed reachability over the ${plural(edgeCount(g), 'relationship', 'relationships')} of ${kindsText(k.kinds, k.where)} from ${plural(from.length, 'source component', 'source components')} to ${plural(to.length, 'target component', 'target components')} at this model revision.`;
  const selected = [...from, ...to];
  const unreachable = from.filter((f) => !findPath(g, f, (id) => toSet.has(id)));
  if (!unreachable.length) return { status: 'verified', scope, selected, explanation: `Each of the ${from.length} source components reaches a target component along at least one directed relationship (being a target itself does not count).` };
  return {
    status: 'violated', scope, selected,
    explanation: `${list(unreachable.map((c) => `"${c}"`))} ${unreachable.length === 1 ? 'does' : 'do'} not reach any target component along directed relationships of ${kindsText(k.kinds, k.where)}.`,
    counterexample: { summary: `Unreachable source ${unreachable.length === 1 ? 'component' : 'components'}: ${unreachable.join(', ')}.`, entities: unreachable },
  };
}

/** @param {Model} model @param {any} ev @returns {Outcome} */
function onlyVia(model, ev) {
  const k = checkKinds(model, ev);
  const from = select(model, ev.from);
  const to = select(model, ev.to);
  const via = select(model, ev.via);
  if ('error' in k) return inconclusive('Nothing was checked.', k.error, [...from, ...to, ...via]);
  const empty = !from.length ? 'from' : !to.length ? 'to' : !via.length ? 'via' : null;
  if (empty) return inconclusive('Nothing was checked: a selector selected no component.', `The "${empty}" selector selects no component, so the check would be vacuous. It is not reported as verified.`, [...from, ...to, ...via]);
  const g = componentGraph(model, { kinds: k.kinds, where: k.where });
  const viaSet = new Set(via);
  const toSet = new Set(to);
  const scope = `Checked the ${plural(edgeCount(g), 'relationship', 'relationships')} of ${kindsText(k.kinds, k.where)} for directed paths from ${plural(from.length, 'source component', 'source components')} to ${plural(to.length, 'target component', 'target components')} that avoid ${plural(via.length, 'via component', 'via components')} at this model revision.`;
  const selected = [...from, ...to, ...via];
  // A source that is itself a via component starts its paths on the via component: that passes by
  // construction. Only the other sources can show anything, and only if a path exists at all.
  const open = from.filter((f) => !viaSet.has(f));
  if (!open.length) {
    return inconclusive(scope, 'Every source component is also a via component, so every path from them passes through a via component by construction. That shows nothing about the model, and the claim is not reported as verified.', selected);
  }
  if (!open.some((f) => findPath(g, f, (id) => toSet.has(id)))) {
    return inconclusive(scope, `No directed path of ${kindsText(k.kinds)} leads from the source components to any target component, so "every path passes through a via component" holds vacuously. The claim is not reported as verified.`, selected);
  }
  for (const f of from) {
    if (viaSet.has(f)) continue;
    const path = findPath(g, f, (id) => toSet.has(id), (id) => viaSet.has(id));
    if (path) {
      return {
        status: 'violated', scope, selected,
        explanation: `A path reaches "${path[path.length - 1]}" from "${path[0]}" without passing through any via component: ${path.join(' -> ')}.`,
        counterexample: { summary: `Bypassing path ${path.join(' -> ')}.`, entities: pathRels(path), path },
      };
    }
  }
  return { status: 'verified', scope, selected, explanation: `With the ${via.length} via components removed, no source component reaches a target component, so every path from source to target passes through a via component.` };
}

/** @param {Model} model @param {any} ev @returns {Outcome} */
function hasPort(model, ev) {
  const sel = select(model, ev.select);
  if (!sel.length) return inconclusive('Nothing was checked: the selector selected no component.', 'The "select" selector selects no component, so "has port" would hold vacuously. It is not reported as verified.');
  const wanted = [];
  if (ev.direction !== undefined) wanted.push(`direction ${ev.direction}`);
  if (ev.contract !== undefined) wanted.push(`contract ${ev.contract}`);
  if (ev.name !== undefined) wanted.push(`name ${ev.name}`);
  const what = wanted.length ? `a port with ${wanted.join(', ')}` : 'any port';
  const scope = `Checked the declared ports of ${plural(sel.length, 'component', 'components')} for ${what} at this model revision.`;
  const ports = model.byKind.port ?? [];
  const lacking = sel.filter((id) => !ports.some((p) => p.owner === id
    && (ev.direction === undefined || p.data.direction === ev.direction)
    && (ev.contract === undefined || p.data.contract === ev.contract)
    && (ev.name === undefined || p.data.name === ev.name)));
  if (!lacking.length) return { status: 'verified', scope, selected: sel, explanation: `Each of the ${sel.length} selected components declares ${what}.` };
  return {
    status: 'violated', scope, selected: sel,
    explanation: `${list(lacking.map((c) => `"${c}"`))} ${lacking.length === 1 ? 'declares' : 'declare'} no matching port (${what}).`,
    counterexample: { summary: `Components without ${what}: ${lacking.join(', ')}.`, entities: lacking },
  };
}

/** @param {Model} model @param {any} ev @returns {Outcome} */
function propertyDefined(model, ev) {
  const comps = selectComponents(model, ev.select);
  if (!comps.length) return inconclusive('Nothing was checked: the selector selected no component.', 'The "select" selector selects no component, so "property defined" would hold vacuously. It is not reported as verified.');
  const prop = String(ev.property);
  const scope = `Checked the declared property "${prop}" of ${plural(comps.length, 'component', 'components')} at this model revision; only whether a non-empty value is present, not whether it is correct.`;
  const selected = comps.map((c) => c.id);
  const missing = comps.filter((c) => isMissing(lookup(c.data, prop))).map((c) => c.id);
  if (!missing.length) return { status: 'verified', scope, selected, explanation: `Each of the ${comps.length} selected components has a non-empty "${prop}".` };
  return {
    status: 'violated', scope, selected,
    explanation: `${list(missing.map((c) => `"${c}"`))} ${missing.length === 1 ? 'has' : 'have'} no non-empty "${prop}".`,
    counterexample: { summary: `Components missing "${prop}": ${missing.join(', ')}.`, entities: missing },
  };
}

/**
 * Every selected, implemented component records implementation.language = ev.language.
 * @param {Model} model @param {any} ev @returns {Outcome}
 */
function implementationLanguage(model, ev) {
  const excluded = new Set(ev.exclude === undefined ? [] : selectComponents(model, ev.exclude, { exact: true }).map((c) => c.id));
  const comps = selectComponents(model, ev.select).filter((c) => !excluded.has(c.id) && c.data.implementation && c.data.implementation.status !== 'not-implemented');
  const lang = String(ev.language);
  if (!comps.length) return inconclusive('Nothing was checked: the selector selected no implemented component.', `No implemented component is selected, so "implemented in ${lang}" would hold vacuously.`);
  const selected = comps.map((c) => c.id);
  const scope = `Checked the declared implementation.language of ${plural(comps.length, 'implemented component', 'implemented components')} at this model revision${excluded.size ? `, leaving out ${plural(excluded.size, 'component', 'components')}` : ''}. The declaration is not compared with the files (the assumption that declarations match the code).`;
  const unknown = comps.filter((c) => typeof c.data.implementation.language !== 'string' || !c.data.implementation.language).map((c) => c.id);
  const other = comps.filter((c) => !unknown.includes(c.id) && c.data.implementation.language !== lang);
  const done = comps.length - unknown.length - other.length;
  const plan = typeof ev.plannedBy === 'string' && ev.plannedBy ? ` Porting the rest is planned (${ev.plannedBy}).` : '';
  if (other.length) {
    /** @type {Record<string, string[]>} */
    const by = {};
    for (const c of other) (by[c.data.implementation.language] ??= []).push(c.id);
    const parts = Object.keys(by).sort().map((l) => `${l}: ${by[l].join(', ')}`);
    return {
      status: 'violated', scope, selected,
      explanation: `${done} of ${comps.length} implemented components are ${lang}; ${other.length} are not yet (${parts.join('; ')})${unknown.length ? `, and ${unknown.length} record no language (${unknown.join(', ')})` : ''}.${plan}`,
      counterexample: { summary: `Not yet ${lang}: ${other.map((c) => c.id).join(', ')}.`, entities: other.map((c) => c.id) },
    };
  }
  if (unknown.length) return inconclusive(scope, `${unknown.length} selected components record no implementation.language: ${unknown.join(', ')}.`, selected);
  return { status: 'verified', scope, selected, explanation: `All ${comps.length} selected implemented components are ${lang}.` };
}

/** @param {any} data @param {string} dotPath */
function lookup(data, dotPath) {
  let cur = data;
  for (const part of dotPath.split('.')) {
    if (cur === null || typeof cur !== 'object' || !Object.hasOwn(cur, part)) return undefined;
    cur = cur[part];
  }
  return cur;
}

/** @param {any} v */
const isMissing = (v) => v === undefined || v === null || v === '' || (Array.isArray(v) && v.length === 0);

/** @param {Model} model @param {any} ev @returns {Outcome} */
function acyclic(model, ev) {
  const k = checkKinds(model, ev);
  if ('error' in k) return inconclusive('Nothing was checked.', k.error);
  const full = componentGraph(model, k.kinds ? { kinds: k.kinds, where: k.where } : { dependencyOnly: true, where: k.where });
  const depKinds = Object.entries(model.meta.relationshipKinds).filter(([, v]) => /** @type {any} */ (v).dependency).map(([id]) => id);
  const kindsDesc = k.kinds ? kindsText(k.kinds, k.where) : `dependency kinds (${depKinds.join(', ')})`;
  /** @type {string[]} */
  let selected = [];
  let g = full;
  let within = '';
  if (ev.within !== undefined) {
    selected = select(model, ev.within);
    if (!selected.length) return inconclusive('Nothing was checked: the "within" selector selected no component.', 'The "within" selector selects no component, so there is no graph to check. It is not reported as verified.');
    const set = new Set(selected);
    g = new Map([...full].filter(([id]) => set.has(id)).map(([id, es]) => [id, es.filter((e) => set.has(e.to))]));
    within = ` restricted to ${plural(selected.length, 'component', 'components')}`;
  }
  const n = edgeCount(g);
  const scope = `Checked the ${plural(n, 'relationship', 'relationships')} of ${kindsDesc}${within} for directed cycles at this model revision.`;
  if (n === 0) return inconclusive(scope, `No relationship of ${kindsDesc} exists${within ? ' within the selected components' : ''}, so there was nothing to check. It is not reported as verified.`, selected);
  const cycle = findCycle(g);
  if (!cycle) return { status: 'verified', scope, selected, explanation: `The directed graph of ${kindsDesc} has no cycle.` };
  return {
    status: 'violated', scope, selected,
    explanation: `The relationships ${list(pathRels(cycle).map((r) => `"${r}"`))} form a directed cycle: ${cycle.join(' -> ')}.`,
    counterexample: { summary: `Cycle ${cycle.join(' -> ')}.`, entities: unique(cycle), path: cycle },
  };
}

/** @param {Map<string, {to: string, rel: string}[]>} g @returns {string[]|null} */
function findCycle(g) {
  /** @type {Map<string, number>} */
  const state = new Map();
  /** @type {string[]} */
  const nodes = [];
  /** @type {string[]} */
  const rels = [];
  /** @type {string[]|null} */
  let found = null;
  /** @param {string} u */
  const visit = (u) => {
    state.set(u, 1);
    nodes.push(u);
    for (const e of g.get(u) ?? []) {
      if (found) return;
      const s = state.get(e.to);
      if (s === 1) {
        const i = nodes.indexOf(e.to);
        /** @type {string[]} */
        const path = [];
        for (let j = i; j < nodes.length - 1; j++) path.push(nodes[j], rels[j]);
        path.push(nodes[nodes.length - 1], e.rel, e.to);
        found = path;
        return;
      }
      if (s === undefined) {
        rels.push(e.rel);
        visit(e.to);
        rels.pop();
      }
    }
    nodes.pop();
    state.set(u, 2);
  };
  for (const id of g.keys()) {
    if (found) break;
    if (!state.has(id)) visit(id);
  }
  return found;
}

// ---------------------------------------------------------------------------
// Refinement (docs/claims-and-evidence.md, "Refinement")
// ---------------------------------------------------------------------------

/**
 * A refines claim: run each scenario of the implementation behavior (the listed ones, or every scenario
 * that runs it) with its own faults, and check every step the behavior takes against its model through
 * the refinement mapping (src/core/refinement.js). Violated at the first failing step; verified when every
 * step of every run passed, at least one step moved the model, and no run ended in an error.
 * @param {Model} model @param {any} ev
 */
function evaluateRefines(model, ev) {
  const id = typeof ev.behavior === 'string' ? ev.behavior : Array.isArray(ev.behavior) && ev.behavior.length === 1 ? ev.behavior[0] : null;
  const impl = id ? model.entities.get(id) : undefined;
  if (!impl || impl.kind !== 'behavior') {
    return { status: 'inconclusive', evaluator: REFINEMENT, scope: 'Nothing was checked: the claim names no behavior.', explanation: `"behavior" must name one implementation behavior; ${id ? `"${id}" is not a behavior` : 'it names none or several'}.`, selected: [] };
  }
  const ref = refinementOf(model, impl);
  if (!ref) {
    return { status: 'inconclusive', evaluator: REFINEMENT, scope: 'Nothing was checked: the behavior declares no refinement.', explanation: `Behavior "${impl.id}" does not declare "refines" naming a behavior together with a "refinement" mapping.`, selected: [impl.id] };
  }
  const A = ref.model;
  const listed = typeof ev.scenarios === 'string' ? [ev.scenarios] : Array.isArray(ev.scenarios) ? ev.scenarios : null;
  const scenarios = listed
    ? listed.map((/** @type {string} */ s) => model.entities.get(s)).filter((/** @type {any} */ s) => s && s.kind === 'scenario')
    : (model.byKind.scenario ?? []).filter((s) => Array.isArray(s.data.behaviors) && s.data.behaviors.includes(impl.id));
  const selected = unique([impl.id, A.id, ...scenarios.map((/** @type {Entity} */ s) => s.id)]);
  const what = `every step of "${impl.id}" against "${A.id}" through its refinement mapping`;
  if (!scenarios.length) {
    return { status: 'inconclusive', evaluator: REFINEMENT, scope: `Nothing was checked: ${listed ? 'no listed scenario exists' : `no scenario runs "${impl.id}"`}.`, explanation: 'There is no trace of the implementation behavior to check, so the refinement is not established.', selected };
  }

  /** @type {{id: string, steps: number, outcome: string}[]} */
  const ran = [];
  /** @type {string[]} */
  const reasons = [];
  /** @type {string[]} */
  const notes = [];
  let checked = 0, moving = 0;
  for (const sc of scenarios) {
    if (!(Array.isArray(sc.data.behaviors) && sc.data.behaviors.includes(impl.id))) { reasons.push(`Scenario "${sc.id}" does not run "${impl.id}".`); continue; }
    /** @type {any} */
    let trace;
    try { trace = runScenarioOnce(model, sc.id); } catch (e) { reasons.push(`Scenario "${sc.id}" could not be run: ${/** @type {Error} */ (e).message}`); continue; }
    ran.push({ id: sc.id, steps: trace.steps.length, outcome: trace.outcome });
    const r = checkRefinementTrace(model, impl, trace, sc.id);
    checked += r.checkedSteps;
    moving += r.movingSteps;
    if (r.failure) {
      const f = r.failure;
      const scope = `Checked ${what} in the trace of scenario "${sc.id}" up to its first failing step. This is a check of these traces, not of all possible executions.`;
      return {
        status: 'violated', evaluator: REFINEMENT, scope, selected: unique([...selected, ...f.entities]),
        counterexample: { summary: f.summary, entities: f.entities, scenario: f.scenario, stepIndex: f.stepIndex, reason: f.reason, trace: f.trace },
        explanation: `${f.summary} (scenario "${f.scenario}", ${f.stepIndex < 0 ? 'initial configuration' : `step ${f.stepIndex}`}).`,
      };
    }
    if (r.unsupported) { reasons.push(r.unsupported); continue; }
    const errStep = trace.steps.find((/** @type {any} */ s) => s.error);
    if (trace.outcome === 'error') reasons.push(`Scenario "${sc.id}" ended in an error${errStep ? ` at step ${errStep.index}: ${errStep.error.message}` : ''}; every step before it refined the model, but the run did not complete.`);
    else if (trace.outcome === 'step-limit') notes.push(`Scenario "${sc.id}" stopped at its step limit after ${trace.steps.length} steps, so later steps were not run.`);
  }
  const label = ran.map((t) => `${t.id} (${plural(t.steps, 'step', 'steps')})`).join(', ') || 'no scenario';
  const scope = `Checked ${what} in the traces of scenarios ${label}, each run with its own faults. This is a check of these traces, not of all possible executions.${notes.length ? ` ${notes.join(' ')}` : ''}`;
  if (reasons.length) return { status: 'inconclusive', evaluator: REFINEMENT, scope, selected, explanation: reasons.join(' ') };
  if (!moving) {
    return { status: 'inconclusive', evaluator: REFINEMENT, scope, selected, explanation: checked ? `Every one of the ${plural(checked, 'step', 'steps')} of "${impl.id}" is a stutter, so no step of the model was matched. It is not reported as verified.` : `"${impl.id}" fired no transition in any trace, so only initial configurations were compared. It is not reported as verified.` };
  }
  return {
    status: 'verified', evaluator: REFINEMENT, scope, selected,
    explanation: `The initial configuration of "${impl.id}" maps to that of "${A.id}", and each of its ${plural(checked, 'step', 'steps')} (${moving} matched to a model transition, ${checked - moving} stutters) refined the model in ${plural(ran.length, 'trace', 'traces')}.${notes.length ? ` ${notes.join(' ')}` : ''} Other executions, inputs or orders of simultaneous events were not examined.`,
  };
}

// ---------------------------------------------------------------------------
// Trace evaluators
// ---------------------------------------------------------------------------

/**
 * Evaluate one trace method over each listed scenario and aggregate.
 * @param {Model} model @param {Entity} claim @param {any} ev @returns {Outcome & {evaluator: string}}
 */
function evaluateTraceClaim(model, claim, ev) {
  const ids = typeof ev.scenarios === 'string' ? [ev.scenarios] : Array.isArray(ev.scenarios) ? ev.scenarios : [];
  /** @type {Entity[]} */
  const scenarios = [];
  /** @type {string[]} */
  const problems = [];
  for (const id of ids) {
    const sc = model.entities.get(id);
    if (!sc || sc.kind !== 'scenario') problems.push(`"${id}" is not a scenario`);
    else scenarios.push(sc);
  }
  const selected = unique(scenarios.flatMap((s) => [s.id, ...(Array.isArray(s.data.behaviors) ? s.data.behaviors : [])]));
  if (!ids.length) return { status: 'inconclusive', evaluator: TRACE, scope: 'Nothing was checked: the claim lists no scenario.', explanation: 'No scenario is listed, so there is no trace to check.', selected };

  /** @type {{id: string, steps: number, faults: string[], outcome: string}[]} */
  const ran = [];
  /** @type {string[]} */
  const reasons = [...problems.map((p) => `${p[0].toUpperCase()}${p.slice(1)}.`)];
  /** @type {Counterexample|null} */
  let counter = null;
  let exercised = false;
  /** @type {string[]} */
  const vacuousWhy = [];
  /** @type {Set<string>} */
  const orderNotes = new Set();
  let totalSteps = 0;
  const notes = [];
  for (const sc of scenarios) {
    /** @type {any} */
    let trace;
    try { trace = runScenarioOnce(model, sc.id); } catch (e) { reasons.push(`Scenario "${sc.id}" could not be run: ${/** @type {Error} */ (e).message}`); continue; }
    totalSteps += trace.steps.length;
    ran.push({ id: sc.id, steps: trace.steps.length, faults: trace.faults ?? [], outcome: trace.outcome });
    const errStep = trace.steps.find((/** @type {any} */ s) => s.error);
    const r = evalTraceProperty(model, ev, trace);
    if (r.exercised) exercised = true;
    else if (r.vacuous) vacuousWhy.push(`in scenario "${sc.id}" ${r.vacuous}`);
    for (const d of orderDecisions(model, trace)) orderNotes.add(d);
    if (r.verdict === 'violated' && !(r.absence && trace.outcome !== 'quiescent')) {
      if (!counter) {
        counter = { summary: r.explanation, entities: unique([...(r.entities ?? [])]), scenario: sc.id };
        if (r.stepIndex !== undefined) counter.stepIndex = r.stepIndex;
      }
    } else if (r.verdict === 'violated') {
      reasons.push(`Scenario "${sc.id}" ended ${trace.outcome === 'error' ? `in an error${errStep ? ` at step ${errStep.index}: ${errStep.error.message}` : ''}` : `at its step limit after ${trace.steps.length} steps`} before the expected occurrence was seen, so its absence is not established.`);
    } else if (r.verdict === 'inconclusive') {
      reasons.push(`Scenario "${sc.id}": ${r.explanation}`);
    } else if (trace.outcome === 'error') {
      reasons.push(`Scenario "${sc.id}" ended in an error${errStep ? ` at step ${errStep.index}: ${errStep.error.message}` : ''}; nothing violated the property before it, but the run did not complete.`);
    } else if (trace.outcome === 'step-limit') {
      notes.push(`Scenario "${sc.id}" stopped at its step limit after ${trace.steps.length} steps, so later steps were not run.`);
    }
  }

  const label = ran.length
    ? ran.map((t) => `${t.id} (${plural(t.steps, 'step', 'steps')}${t.faults.length ? `, faults: ${t.faults.join(', ')}` : ''})`).join(', ')
    : 'no scenario';
  const caveat = 'This is a check of these traces, not of all possible executions.';
  const baseScope = ev.method === 'state-invariant'
    ? `Checked every configuration of the traces of scenarios ${label}. ${caveat}`
    : ev.method === 'eventually' && ev.expr !== undefined && ev.occurs === undefined
      ? `Checked the final configuration of the traces of scenarios ${label}. ${caveat}`
      : `Checked the events delivered and transitions fired in the traces of scenarios ${label}. ${caveat}`;
  /** @type {string[]} */
  const extra = [];
  if (orderNotes.size) extra.push(`Declaration order decided which transition fired: ${[...orderNotes].join('; ')}. Swapping the declaration order of those transitions would change these traces.`);
  if (ev.method === 'never') {
    const only = faultOnlyProducers(model, ev.occurs, scenarios);
    if (only.length && !ran.some((t) => enablesAny(model, t.faults, only))) {
      extra.push(`The forbidden occurrence can only be produced through faultOnly transition${only.length === 1 ? '' : 's'} ${list(only.map((id) => `"${id}"`))}, which fire${only.length === 1 ? 's' : ''} only when an enable-transition fault targets ${only.length === 1 ? 'it' : 'them'}; no listed scenario enables ${only.length === 1 ? 'it' : 'them'}, so this holds for runs without such a fault, and for runs with one only as far as a negative exercises it.`);
    }
  }
  if (ev.method === 'precedes') extra.push('An occurrence counts as produced by the system when a transition fired or emitted it; a delivery from the scenario script does not, and an ordering between two scripted deliveries is not reported as verified.');
  const scope = extra.length ? `${baseScope} ${extra.join(' ')}` : baseScope;

  if (counter) {
    return { status: 'violated', evaluator: TRACE, scope, selected: unique([...selected, ...counter.entities]), counterexample: counter, explanation: `${counter.summary} (scenario "${counter.scenario}"${counter.stepIndex !== undefined ? `, ${counter.stepIndex < 0 ? 'initial configuration' : `step ${counter.stepIndex}`}` : ''}).` };
  }
  if (reasons.length) return { status: 'inconclusive', evaluator: TRACE, scope, selected, explanation: reasons.join(' ') };
  if (ev.method === 'precedes' && !exercised) {
    const why = vacuousWhy.length ? `The ordering was never witnessed by the system: ${vacuousWhy.join('; ')}.` : 'The "then" occurrence never happens in any listed trace, so the ordering was never exercised and the check is vacuous.';
    return { status: 'inconclusive', evaluator: TRACE, scope, selected, explanation: `${why} It is not reported as verified.` };
  }
  if (ev.method === 'state-invariant') {
    if (!totalSteps) {
      return { status: 'inconclusive', evaluator: TRACE, scope, selected, explanation: 'Every listed trace has zero steps, so the invariant was only looked at in initial configurations and nothing was exercised. It is not reported as verified.' };
    }
    const ante = antecedentText(ev.expr);
    if (ante !== null && !exercised) {
      const why = vacuousWhy.length ? `The antecedent \`${ante}\` was true, but ${vacuousWhy.join('; ')}, so the implication was never exercised and the check is vacuous.` : `The antecedent \`${ante}\` was never true in any configuration reached by a step of any listed trace, so the implication was never exercised and the check is vacuous.`;
      return { status: 'inconclusive', evaluator: TRACE, scope, selected, explanation: `${why} It is not reported as verified.` };
    }
  }
  const holdsText = {
    'state-invariant': 'The expression held on every listed trace',
    precedes: 'The ordering held on every listed trace',
    eventually: 'The expected occurrence or final state was observed on every listed trace',
    never: 'The forbidden occurrence did not happen on any listed trace',
  }[/** @type {'state-invariant'} */ (ev.method)];
  const neg = runNegatives(model, ev);
  if (!neg.runs.length) {
    return { status: 'inconclusive', evaluator: TRACE, scope, selected, negatives: [], explanation: `${holdsText}, but the claim declares no negative, so nothing shows this check can fail. A trace claim is verified only when one of its scenarios, run with a fault that removes the protection, violates it (evaluate.negatives).` };
  }
  const failedNeg = neg.runs.filter((n) => !n.violated);
  if (failedNeg.length) {
    return { status: 'inconclusive', evaluator: TRACE, scope, selected, negatives: neg.runs, explanation: `${holdsText}, but ${failedNeg.map((n) => `the negative "${n.scenario}" with ${n.faults.join(', ')} did not violate it (${n.explanation})`).join('; and ')}. A check its negatives cannot break is not told apart from one that always passes.` };
  }
  const negText = ` Each of its ${plural(neg.runs.length, 'negative', 'negatives')} violated it: ${neg.runs.map((n) => `"${n.scenario}" with ${n.faults.join(', ')}${n.stepIndex !== undefined ? ` at step ${n.stepIndex}` : ''}`).join('; ')}.`;
  const what = {
    'state-invariant': `The expression held in the initial configuration and after every step of`,
    precedes: 'Every occurrence of the "then" matcher had an earlier occurrence of the "first" matcher in',
    eventually: 'The expected occurrence or final state was observed in',
    never: 'The forbidden occurrence did not happen in',
  }[/** @type {'state-invariant'} */ (ev.method)];
  return { status: 'verified', evaluator: TRACE, scope, selected, negatives: neg.runs, explanation: `${what} each of the ${plural(ran.length, 'trace', 'traces')} of ${list(ran.map((t) => `"${t.id}"`))}.${notes.length ? ` ${notes.join(' ')}` : ''}${negText} Other executions, faults or inputs were not examined.` };
}

/**
 * Run the declared negatives of a trace claim. A negative counts only when it definitely violates the
 * claim: the absence of a required occurrence in a run that did not finish quiescent does not count.
 * @param {Model} model @param {any} ev
 * @returns {{runs: NegativeRun[]}}
 */
function runNegatives(model, ev) {
  const decl = Array.isArray(ev.negatives) ? ev.negatives : [];
  /** @type {NegativeRun[]} */
  const runs = [];
  for (const n of decl) {
    const faults = Array.isArray(n?.faults) ? n.faults.filter((/** @type {any} */ x) => typeof x === 'string') : [];
    const sc = typeof n?.scenario === 'string' ? model.entities.get(n.scenario) : undefined;
    if (!sc || sc.kind !== 'scenario') { runs.push({ scenario: String(n?.scenario), faults, violated: false, outcome: 'not-run', explanation: 'it is not a scenario of this model' }); continue; }
    const own = Array.isArray(sc.data.faults) ? sc.data.faults : [];
    /** @type {any} */
    let trace;
    try { trace = runScenarioOnce(model, sc.id, { faults: [...own, ...faults] }); } catch (e) {
      runs.push({ scenario: sc.id, faults, violated: false, outcome: 'not-run', explanation: `it could not be run: ${/** @type {Error} */ (e).message}` });
      continue;
    }
    const r = evalTraceProperty(model, ev, trace);
    const definite = r.verdict === 'violated' && !(r.absence && trace.outcome !== 'quiescent');
    /** @type {NegativeRun} */
    const run = { scenario: sc.id, faults, violated: definite, outcome: trace.outcome,
      explanation: definite ? r.explanation
        : r.verdict === 'violated' ? `the run was ${describeOutcome(trace)} before the expected occurrence was seen`
        : r.verdict === 'inconclusive' ? r.explanation
        : `the claim held on that run, which ended ${trace.outcome === 'quiescent' ? 'quiescent' : describeOutcome(trace)}` };
    if (definite && r.stepIndex !== undefined) run.stepIndex = r.stepIndex;
    runs.push(run);
  }
  return { runs };
}

/**
 * Evaluate the property of a trace method on one trace.
 * verdict: holds | violated | inconclusive. `absence` marks a violation that is
 * only the absence of a required occurrence (not final while the run is unfinished).
 * @param {Model} model @param {any} ev @param {any} trace
 * @returns {{verdict: 'holds'|'violated'|'inconclusive', explanation: string, stepIndex?: number, entities?: string[], absence?: boolean, exercised?: boolean, vacuous?: string}}
 */
function evalTraceProperty(model, ev, trace) {
  switch (ev.method) {
    case 'state-invariant': return traceInvariant(ev, trace);
    case 'precedes': return tracePrecedes(ev, trace);
    case 'never': return traceNever(model, ev, trace);
    case 'eventually': return traceEventually(ev, trace);
  }
  return { verdict: 'inconclusive', explanation: `Method "${ev.method}" is not a trace method.` };
}

/** @param {any} config */
function configResolver(config) {
  return (/** @type {string[]} */ path) => {
    if (path.length === 1) return path[0] === 'time' ? config.time : undefined;
    if (path.length !== 2) return undefined;
    const m = config.machines?.[path[0]];
    if (!m || !Object.hasOwn(config.machines, path[0])) return undefined;
    if (path[1] === 'state') return m.state;
    return m.vars && Object.hasOwn(m.vars, path[1]) ? m.vars[path[1]] : undefined;
  };
}

/**
 * Evaluate a parsed expression on a configuration.
 * @param {any} ast @param {any} config
 * @returns {{ok: true, value: boolean} | {ok: false, message: string}}
 */
function evalBool(ast, config) {
  try {
    const v = evalExpr(ast, configResolver(config));
    if (typeof v !== 'boolean') return { ok: false, message: `The expression evaluates to ${v === null ? 'null' : typeof v}, not a boolean.` };
    return { ok: true, value: v };
  } catch (e) {
    if (e instanceof ExprError) return { ok: false, message: e.message };
    throw e;
  }
}

/** @param {any} step */
const stepText = (step) => `step ${step.index} (${step.kind === 'deliver' ? 'delivery of' : step.kind === 'drop' ? 'dropped' : 'delayed'} event "${step.event.id}" at time ${step.time})`;

/**
 * The values the expression's references had in a configuration, e.g. "worker.acked = true, db.durable = false".
 * @param {any} ast @param {any} config
 */
function valuesText(ast, config) {
  const seen = new Set();
  const parts = [];
  for (const path of exprRefs(ast)) {
    const key = path.join('.');
    if (seen.has(key)) continue;
    seen.add(key);
    let value;
    if (path.length === 1 && path[0] === 'time') value = config.time;
    else if (path.length === 2) {
      const m = config.machines?.[path[0]];
      value = m ? (path[1] === 'state' ? m.state : m.vars?.[path[1]]) : undefined;
    }
    parts.push(`${key} = ${value === undefined ? 'unknown' : JSON.stringify(value)}`);
  }
  return parts.join(', ');
}

/** @param {any} ev @param {any} trace @returns {ReturnType<typeof evalTraceProperty>} */
function traceInvariant(ev, trace) {
  const parsed = parseExpr(ev.expr);
  if (!parsed.ok) return { verdict: 'inconclusive', explanation: `The expression does not parse: ${parsed.error.message}` };
  const behaviors = exprRefs(parsed.ast).map((p) => p[0]).filter((n) => n !== 'time');
  const configs = [{ index: -1, config: trace.initial, text: 'the initial configuration', entities: unique(behaviors) }];
  trace.steps.forEach((/** @type {any} */ s, /** @type {number} */ i) => {
    if (!s.error) configs.push({ index: s.index ?? i, config: s.config, text: stepText(s), entities: s.responsible ?? [] });
  });
  const implication = parsed.ast.t === 'bin' && parsed.ast.op === '=>';
  let antecedentTrue = false;
  // A consequent that names no state or variable is a constant: the implication cannot fail through it.
  const constantConsequent = implication && exprRefs(/** @type {any} */ (parsed.ast).b).length === 0;
  for (const c of configs) {
    const r = evalBool(parsed.ast, c.config);
    if (!r.ok) return { verdict: 'inconclusive', explanation: `The expression could not be evaluated in ${c.text}: ${r.message}` };
    if (!r.value) return { verdict: 'violated', stepIndex: c.index, entities: c.entities, explanation: `Invariant \`${ev.expr}\` is false in ${c.text}: ${valuesText(parsed.ast, c.config)}.` };
    // The initial configuration does not count: an antecedent true only before any step exercised nothing.
    if (implication && c.index >= 0) {
      const a = evalBool(/** @type {any} */ (parsed.ast).a, c.config);
      if (a.ok && a.value) antecedentTrue = true;
    }
  }
  // A trace without steps contributes nothing; an implication counts as exercised only once its antecedent was true
  // after some step and its consequent mentions something that can change.
  const exercised = trace.steps.length > 0 && (!implication || (antecedentTrue && !constantConsequent));
  const vacuous = implication && antecedentTrue && constantConsequent ? 'its consequent names no state or variable, so it is decided whatever happens' : undefined;
  return { verdict: 'holds', exercised, ...(vacuous ? { vacuous } : {}), explanation: `Invariant \`${ev.expr}\` held in the initial configuration and after each of ${plural(configs.length - 1, 'step', 'steps')}.` };
}

/**
 * Indices of the steps in which a matcher occurs.
 * @param {any} trace @param {any} matcher
 */
function occurrences(trace, matcher) {
  /** @type {number[]} */
  const out = [];
  trace.steps.forEach((/** @type {any} */ s, /** @type {number} */ i) => {
    const hit = matcher.event !== undefined
      ? s.kind === 'deliver' && s.event.id === matcher.event
      : Array.isArray(s.fired) && s.fired.some((/** @type {any} */ f) => f.transition === matcher.transition);
    if (hit) out.push(i);
  });
  return out;
}

/**
 * Source text of the antecedent when the expression's top-level operator is "=>", else null.
 * The first "=>" outside parentheses and string literals is the top-level one (lowest precedence, right associative).
 * @param {any} src @returns {string|null}
 */
function antecedentText(src) {
  if (typeof src !== 'string') return null;
  const parsed = parseExpr(src);
  if (!parsed.ok || parsed.ast.t !== 'bin' || parsed.ast.op !== '=>') return null;
  let depth = 0;
  for (let i = 0; i < src.length; i++) {
    const c = src[i];
    if (c === '"' || c === "'") { const end = src.indexOf(c, i + 1); if (end < 0) break; i = end; continue; }
    if (c === '(') depth++;
    else if (c === ')') depth--;
    else if (depth === 0 && c === '=' && src[i + 1] === '>') return src.slice(0, i).trim();
  }
  return null;
}

/**
 * The unguarded transitions that fired although another enabled, unguarded transition of the same behavior on the same
 * event and state was declared after them: the engine takes the first in declaration order, so the order
 * decided. A later transition with a guard is not reported: whether its guard held is not examined here.
 * @param {Model} model @param {any} trace @returns {string[]}
 */
function orderDecisions(model, trace) {
  /** @type {Set<string>} */
  const out = new Set();
  const faults = (Array.isArray(trace.faults) ? trace.faults : []).map((/** @type {string} */ id) => model.entities.get(id)?.data).filter(Boolean);
  const targeted = (/** @type {string} */ kind, /** @type {string} */ tid) => faults.some((/** @type {any} */ f) => f.kind === kind && f.transition === tid);
  for (const step of trace.steps) {
    for (const f of Array.isArray(step.fired) ? step.fired : []) {
      const siblings = (model.byKind.transition ?? []).filter((t) => t.owner === f.behavior);
      const at = siblings.findIndex((t) => t.id === f.transition);
      // A fired transition with a guard is a priority rule (its guard decided); only an unguarded winner leaves the order alone deciding.
      if (f.guard !== null && f.guard !== undefined && String(f.guard).trim() !== '') continue;
      for (const s of at < 0 ? [] : siblings.slice(at + 1)) {
        if (s.data.from !== f.from || s.data.on !== step.event?.id) continue;
        if (typeof s.data.guard === 'string' && s.data.guard.trim() !== '') continue;
        if (s.data.faultOnly === true && !targeted('enable-transition', s.id)) continue;
        if (targeted('disable-transition', s.id)) continue;
        out.add(`"${f.transition}" fired where "${s.id}" (unguarded, also enabled) is declared after it on event "${step.event.id}" in behavior "${f.behavior}"`);
      }
    }
  }
  return [...out];
}

/**
 * The faultOnly transitions that are the only way a matcher's occurrence can be produced, or [] when anything
 * else (a non-faultOnly transition, a scripted step, an injected event) can also produce it.
 * @param {Model} model @param {any} matcher @param {Entity[]} scenarios @returns {string[]}
 */
function faultOnlyProducers(model, matcher, scenarios) {
  if (matcher.transition !== undefined) {
    const t = model.entities.get(matcher.transition);
    return t && t.kind === 'transition' && t.data.faultOnly === true ? [t.id] : [];
  }
  if (matcher.event === undefined) return [];
  const behaviors = new Set(scenarios.flatMap((s) => (Array.isArray(s.data.behaviors) ? s.data.behaviors : [])));
  const scripted = scenarios.some((s) => (Array.isArray(s.data.steps) ? s.data.steps : []).some((/** @type {any} */ st) => st?.event === matcher.event)
    || (Array.isArray(s.data.faults) ? s.data.faults : []).some((/** @type {string} */ id) => { const f = model.entities.get(id)?.data; return f?.kind === 'inject-event' && f.event === matcher.event; }));
  if (scripted) return [];
  const emitters = (model.byKind.transition ?? []).filter((t) => behaviors.has(/** @type {string} */ (t.owner))
    && (Array.isArray(t.data.effects) ? t.data.effects : []).some((/** @type {any} */ fx) => fx && typeof fx === 'object' && (fx.emit === matcher.event || fx.then === matcher.event || fx.refused === matcher.event)));
  return emitters.length && emitters.every((t) => t.data.faultOnly === true) ? emitters.map((t) => t.id) : [];
}

/** Whether any of the faults enables one of the transitions. @param {Model} model @param {string[]} faultIds @param {string[]} transitionIds */
function enablesAny(model, faultIds, transitionIds) {
  return faultIds.some((id) => { const f = model.entities.get(id)?.data; return f?.kind === 'enable-transition' && transitionIds.includes(f.transition); });
}

/** @param {any} m */
const matcherText = (m) => (m.event !== undefined ? `event "${m.event}"` : `transition "${m.transition}"`);
/** @param {any} m */
const matcherId = (m) => m.event ?? m.transition;

/** @param {any} ev @param {any} trace @returns {ReturnType<typeof evalTraceProperty>} */
function tracePrecedes(ev, trace) {
  const firsts = occurrences(trace, ev.first);
  const thens = occurrences(trace, ev.then);
  // An event is delivered before the transitions it triggers fire, so a
  // delivery of the "first" event in the same step counts as earlier.
  const sameStepOk = ev.first.event !== undefined && ev.then.transition !== undefined;
  // An occurrence is the system's when a transition fired it or emitted its event; a scripted delivery is the
  // scenario's own input, so an order the script itself dictates shows nothing about the system.
  /** @param {any} m @param {number} i */
  const bySystem = (m, i) => m.event === undefined || trace.steps[i].event?.source?.kind !== 'scenario';
  for (const t of thens) {
    if (!firsts.some((f) => f < t || (sameStepOk && f === t))) {
      const step = trace.steps[t];
      return { verdict: 'violated', stepIndex: step.index ?? t, entities: unique([...(step.responsible ?? []), matcherId(ev.first)]), exercised: true, explanation: `The ${matcherText(ev.then)} occurs in ${stepText(step)} with no earlier occurrence of the ${matcherText(ev.first)}.` };
    }
  }
  const witnessed = thens.some((t) => bySystem(ev.then, t) || firsts.some((f) => (f < t || (sameStepOk && f === t)) && bySystem(ev.first, f)));
  const vacuous = thens.length && !witnessed ? `every occurrence of the ${matcherText(ev.then)} and of the ${matcherText(ev.first)} is a delivery from the scenario script, so the order is the script's, not the system's` : undefined;
  return { verdict: 'holds', exercised: witnessed, ...(vacuous ? { vacuous } : {}), explanation: thens.length ? `Each of the ${plural(thens.length, 'occurrence', 'occurrences')} of the ${matcherText(ev.then)} had an earlier occurrence of the ${matcherText(ev.first)}.` : `The ${matcherText(ev.then)} did not occur, so the ordering was not exercised.` };
}

/**
 * Why a matcher cannot occur in the scenario of a trace, or null when it can.
 * @param {Model} model @param {any} matcher @param {any} trace
 * @returns {string|null}
 */
function cannotOccur(model, matcher, trace) {
  const sc = model.entities.get(trace.scenarioId);
  /** @type {string[]} */
  const behaviorIds = Array.isArray(sc?.data.behaviors) ? sc.data.behaviors : [];
  const behaviors = new Set(behaviorIds);
  if (matcher.transition !== undefined) {
    const t = model.entities.get(matcher.transition);
    if (t && t.kind === 'transition' && !behaviors.has(/** @type {string} */ (t.owner))) {
      return `belongs to behavior "${t.owner}", which is not part of scenario "${trace.scenarioId}"; it cannot occur in this scenario`;
    }
    return null;
  }
  if (matcher.event === undefined) return null;
  const transitions = (model.byKind.transition ?? []).filter((t) => behaviors.has(/** @type {string} */ (t.owner)));
  if (transitions.some((t) => t.data.on === matcher.event)) return null;
  if (transitions.some((t) => (Array.isArray(t.data.effects) ? t.data.effects : []).some((/** @type {any} */ fx) => fx && typeof fx === 'object' && fx.emit === matcher.event))) return null;
  if ((Array.isArray(sc?.data.steps) ? sc.data.steps : []).some((/** @type {any} */ st) => st?.event === matcher.event)) return null;
  const faultIds = Array.isArray(trace.faults) ? trace.faults : [];
  if (faultIds.some((/** @type {string} */ id) => { const fl = model.entities.get(id); return fl?.data.kind === 'inject-event' && fl.data.event === matcher.event; })) return null;
  return "is triggered by no transition of this scenario's behaviors and is neither a step event, emitted by those behaviors, nor injected by a declared fault; it cannot occur in this scenario";
}

/** @param {Model} model @param {any} ev @param {any} trace @returns {ReturnType<typeof evalTraceProperty>} */
function traceNever(model, ev, trace) {
  const hits = occurrences(trace, ev.occurs);
  if (hits.length) {
    const step = trace.steps[hits[0]];
    return { verdict: 'violated', stepIndex: step.index ?? hits[0], entities: unique([...(step.responsible ?? []), matcherId(ev.occurs)]), explanation: `The ${matcherText(ev.occurs)} occurs in ${stepText(step)}, but it was never to occur.` };
  }
  const cannot = cannotOccur(model, ev.occurs, trace);
  if (cannot) return { verdict: 'inconclusive', explanation: `The ${matcherText(ev.occurs)} ${cannot}, so its absence shows nothing.` };
  return { verdict: 'holds', explanation: `The ${matcherText(ev.occurs)} did not occur in the ${plural(trace.steps.length, 'step', 'steps')} of the trace.` };
}

/** @param {any} ev @param {any} trace @returns {ReturnType<typeof evalTraceProperty>} */
function traceEventually(ev, trace) {
  /** @type {string[]} */
  const held = [];
  if (ev.occurs !== undefined) {
    const hits = occurrences(trace, ev.occurs);
    if (!hits.length) return { verdict: 'violated', absence: true, entities: [matcherId(ev.occurs)], explanation: `The ${matcherText(ev.occurs)} never occurs in the ${plural(trace.steps.length, 'step', 'steps')} of the trace.` };
    // A delivery of an event the scenario script itself delivers is the environment's input, not a
    // reaction of the system: it cannot witness "eventually". Only deliveries that a transition emitted
    // (or that the system produced in some other way than the script) count.
    const reactions = ev.occurs.event === undefined ? hits : hits.filter((i) => trace.steps[i].event?.source?.kind !== 'scenario');
    if (!reactions.length) {
      return { verdict: 'inconclusive', explanation: `The ${matcherText(ev.occurs)} occurs only as the scenario's own scripted input (step ${trace.steps[hits[0]].index ?? hits[0]}), which shows nothing about the system's reaction, so the claim is not reported as verified. Wait for a reaction of the system to that input, or state the claim with a transition as the occurrence.` };
    }
    held.push(`The ${matcherText(ev.occurs)} occurs first in step ${trace.steps[reactions[0]].index ?? reactions[0]}.`);
  }
  if (ev.expr !== undefined) {
    const parsed = parseExpr(ev.expr);
    if (!parsed.ok) return { verdict: 'inconclusive', explanation: `The expression does not parse: ${parsed.error.message}` };
    const r = evalBool(parsed.ast, trace.final);
    if (!r.ok) return { verdict: 'inconclusive', explanation: `The expression could not be evaluated in the final configuration: ${r.message}` };
    if (!r.value) return { verdict: 'violated', absence: true, entities: unique(exprRefs(parsed.ast).map((p) => p[0]).filter((n) => n !== 'time')), explanation: `\`${ev.expr}\` is false in the final configuration of the trace: ${valuesText(parsed.ast, trace.final)}.` };
    held.push(`\`${ev.expr}\` holds in the final configuration.`);
  }
  return { verdict: 'holds', explanation: held.join(' ') || 'Nothing was required.' };
}

/**
 * Whether a trace-method claim only refers to behaviors of the given scenario.
 * @param {Model} model @param {any} ev @param {Set<string>} behaviors
 */
function applicable(model, ev, behaviors) {
  /** @param {any} m */
  const matcherOk = (m) => {
    if (!m || typeof m !== 'object') return false;
    if (typeof m.event === 'string') return true;
    const t = typeof m.transition === 'string' ? model.entities.get(m.transition) : undefined;
    return !!t && t.kind === 'transition' && behaviors.has(/** @type {string} */ (t.owner));
  };
  /** @param {any} src */
  const exprOk = (src) => {
    if (typeof src !== 'string') return false;
    const p = parseExpr(src);
    if (!p.ok) return false;
    return exprRefs(p.ast).every((path) => (path.length === 1 ? path[0] === 'time' : behaviors.has(path[0])));
  };
  switch (ev.method) {
    case 'state-invariant': return exprOk(ev.expr);
    case 'precedes': return matcherOk(ev.first) && matcherOk(ev.then);
    case 'never': return matcherOk(ev.occurs);
    case 'eventually': return (ev.occurs !== undefined || ev.expr !== undefined) && (ev.occurs === undefined || matcherOk(ev.occurs)) && (ev.expr === undefined || exprOk(ev.expr));
  }
  return false;
}

/** @param {any} trace */
const describeOutcome = (trace) => (trace.outcome === 'running' ? 'not finished' : trace.outcome === 'step-limit' ? 'cut off at its step limit' : trace.outcome === 'error' ? 'ended by an error' : trace.outcome);

// ---------------------------------------------------------------------------
// Small helpers
// ---------------------------------------------------------------------------

/** @param {string[]} xs */
function unique(xs) {
  return [...new Set(xs)];
}

/** "a", "a and b", "a, b and c". @param {string[]} xs */
function list(xs) {
  if (xs.length <= 1) return xs.join('');
  return `${xs.slice(0, -1).join(', ')} and ${xs[xs.length - 1]}`;
}

/** @param {string} s */
function capitalise(s) {
  return s ? s[0].toUpperCase() + s.slice(1) : s;
}
