// Claim evaluation. The one rule of this module: never confuse "declared" with
// "true". This module runs the checks Exegra can run itself (structural, trace,
// refinement and metric checks over the model), reads the recorded results of
// evidence and Lean theorem checks, and turns each into a fact in the schema
// formal/Exegra/Verdict.lean defines. The status of every claim is decided in
// Lean from those facts (src/core/verdict.js); here it is only worded: every
// result says precisely what was and was not checked (`scope`).
//
// Deterministic: no DOM, no clocks, no randomness.

import { faultModelOf, faultModelScope, faultCoverage } from './fault-model.js';
import { CLAIM_METHODS } from './claim-methods.js';
import { own } from './own.js';
import { DEPENDENCY_CLASSES, kindInfo } from './interactions.js';
import { componentGraph, selectComponents, hierarchyIds, hierarchyOf, cutMap, elementsOf, selectorNames } from './query.js';
import { deriveModel, blockAt, restrictInteraction, abstractionInvariants, ABSTRACTION_INVARIANTS } from './abstraction.js';
import { parseExpr, evalExpr, exprRefs, ExprError } from './expr.js';
import { semanticHash } from './hash.js';
import { runScenario, runEngineText } from './engine.js';
import { evaluateMetricClaim, metricVerdictInput, quantileKey } from './metric-claims.js';
import { decideStatuses } from './verdict.js';
import { extractionOf, reconcile, claimBasis, STATIC_ONLY } from './extraction.js';
import { stampsOf, testFact, documentFact, theoremFact, checkFact, assumptionFact } from './facts.js';
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
 *   claim.not-expressible: a claim stated at a cut names an element hidden inside a block of that cut, or selects part of a block;
 *   claim.stale-evidence, claim.stale-theorem: a recorded fact was recorded for other files than the current ones;
 *   claim.fact-refused: a fact did not meet the Lean fact schema and was left out;
 *   claim.freshness-unverifiable: recorded facts were read with no current stamp to compare (the browser bundle)
 * @typedef {{
 *   claimId: string, kind: string, method: string|null,
 *   status: 'proved'|'verified'|'supported'|'model-holds'|'asserted'|'violated'|'inconclusive'|'not-evaluated',
 *   evaluator: string, semanticHash: string, scope: string, explanation: string,
 *   assumptions: string[], involved: string[], counterexample?: Counterexample,
 *   evidence: EvidenceItem[], negatives?: NegativeRun[], modelledBy?: {claimId: string, status: string}[],
 *   freshness?: 'fresh'|'stale'|'unverifiable', diagnostics?: ClaimDiagnostic[],
 *   verdict?: import('./verdict.js').Status & {established: boolean}
 *   footprint?: import('./footprints.js').Footprint, level?: {hierarchy: string, cut: string}, basis?: {counts: Record<string, number>, basis: string, text: string}
 * }} ClaimResult
 *   status: the word the Lean verdict is shown with (Exegra.Verdict.label); verdict: the status tuple Lean decided
 *   (formal/Exegra/Verdict.lean), and whether it is shown established (proved, fresh, no open assumption);
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
 * @property {Record<string, {outcome: 'pass'|'fail'|'not-run', stamp?: string, kind?: import('./verdict.js').FactKind, detail?: string}>} [assumptions]
 *   facts about assumptions (an import scan), keyed by assumption id, with the records stamp they were recorded on
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
const TRACE_METHODS = ['state-invariant', 'precedes', 'eventually', 'never'];

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/**
 * Evaluate every claim in declaration order. `stamps` are the current stamps recorded facts are compared with
 * (tools/tree-stamp.js currentStamps): a fact recorded on other stamps is stale and never makes a claim positive.
 * Without stamps (absent, or null as in the browser bundle) the freshness of every recorded fact is unverifiable,
 * and an unverifiable fact establishes nothing (Exegra.Verdict.strength_le_kind counts fresh facts only).
 * `assumptionFacts` are facts about assumptions (an import scan, a test) beside those `recorded.assumptions` holds.
 * The statuses are decided in Lean (src/core/verdict.js); this module produces the facts and formats the result.
 * @param {Model} model @param {EvalOptions} [opts]
 * @returns {ClaimResult[]}
 */
export function evaluateClaims(model, opts = {}) {
  const hash = semanticHash(model);
  const outer = passRuns;
  passRuns = new Map();
  try {
    const results = decide(model, model.byKind.claim ?? [], hash, opts);
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
 * Evaluate one claim (and, for a requirement, the claims that model it, for `modelledBy`).
 * @param {Model} model @param {string} claimId @param {EvalOptions} [opts]
 * @returns {ClaimResult}
 */
export function evaluateClaim(model, claimId, opts = {}) {
  const claim = model.entities.get(claimId);
  if (!claim || claim.kind !== 'claim') throw new Error(`Unknown claim "${claimId}".`);
  const hash = semanticHash(model);
  const outer = passRuns;
  passRuns = new Map();
  try {
    const claims = claim.data.kind === 'requirement' ? [claim, ...modellingClaims(model, claim.id).filter((c) => c.id !== claim.id)] : [claim];
    const results = decide(model, claims, hash, opts);
    if (claim.data.kind === 'requirement') attachModelledBy(model, results);
    return results[0];
  } finally {
    passRuns = outer;
  }
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
// Facts and the Lean verdict
// ---------------------------------------------------------------------------

/**
 * @typedef {{recorded?: Recorded|null, stamps?: Stamps|null, assumptionFacts?: AssumptionFact[], atCut?: string|{hierarchy: string, blocks: string[]}|null}} EvalOptions
 *   atCut: evaluate every claim stated at a cut at this cut instead (a declared cut id, or a hierarchy and the blocks of an
 *   interactive cut): what a view shows for a level-bound claim at the cut it draws (WG-5695). Other claims are unaffected.
 * @typedef {{assumption: string, outcome: 'pass'|'fail'|'not-run', kind?: import('./verdict.js').FactKind,
 *   stamp?: string|null, detail?: string}} AssumptionFact
 *   a fact about an assumption: the assumption holds (pass) or is refuted (fail), with the stamp it was recorded on
 * @typedef {{role: 'check'|'evidence'|'pending'|'derived'|'external'|'theorem'|'assumption'|'metric', id: string}} FactRole
 *   which source a fact sent to Lean came from (evidence id, assumption id, or the claim id)
 * @typedef {{
 *   entity: Entity, method: string|null, ev: any, family: 'none'|'model'|'metric'|'evidence'|'lean',
 *   r: any, evidence: (EvidenceItem & {raw?: string, stamp?: string|null})[], claim: import('./verdict.js').VerdictClaim,
 *   facts: import('./verdict.js').Fact[], roles: FactRole[], outside?: any, theorem?: string, about?: string[],
 *   assumptionFacts: AssumptionFact[], metricParts?: {id: string, role: string, index: number}[]
 * }} Prepared
 */

/**
 * Prepare every claim's facts, have Lean decide all statuses in one call, and format the results.
 * @param {Model} model @param {Entity[]} claims @param {string} hash @param {EvalOptions} opts
 * @returns {ClaimResult[]}
 */
function decide(model, claims, hash, opts) {
  const ctx = { model, hash, recorded: opts.recorded ?? undefined, stamps: opts.stamps ?? null, assumptionFacts: opts.assumptionFacts ?? [], atCut: opts.atCut ?? null };
  const prepared = claims.map((c) => prepare(ctx, c));
  const verdicts = decideStatuses(prepared.map((p) => ({ claim: p.claim, facts: p.facts })));
  return prepared.map((p, i) => present(ctx, p, verdicts[i]));
}

/** @typedef {{model: Model, hash: string, recorded: Recorded|undefined, stamps: Stamps|null, assumptionFacts: AssumptionFact[], atCut?: EvalOptions['atCut']}} Ctx */

/**
 * The subject a claim is about: the model for the checks Exegra runs over it; reality for a requirement realised
 * operationally (measured on a running deployment); the implementation otherwise, including a `measured` claim,
 * whose evidence (a load test, a benchmark) runs the implementation.
 * @param {Entity} claim @param {string} family @returns {import('./verdict.js').Subject}
 */
function subjectOf(claim, family) {
  if (family === 'model' || family === 'metric') return 'model';
  if (claim.data.kind === 'requirement' && claim.data.realisation === 'operational') return 'reality';
  return 'implementation';
}

/** The facts about the assumptions a claim declares: recorded (recorded.assumptions) and given. @param {Ctx} ctx @param {string[]} assumptions */
function assumptionFactsOf(ctx, assumptions) {
  /** @type {AssumptionFact[]} */
  const out = [];
  const rec = ctx.recorded?.assumptions ?? {};
  for (const a of assumptions) {
    const r = Object.hasOwn(rec, a) ? rec[a] : undefined;
    if (r && (r.outcome === 'pass' || r.outcome === 'fail' || r.outcome === 'not-run')) out.push({ assumption: a, outcome: r.outcome, kind: r.kind, stamp: r.stamp ?? null, ...(r.detail ? { detail: r.detail } : {}) });
    for (const f of ctx.assumptionFacts) if (f.assumption === a) out.push(f);
  }
  return out;
}

/**
 * The facts a claim rests on, and its structure for the verdict.
 * @param {Ctx} ctx @param {Entity} claim @returns {Prepared}
 */
function prepare(ctx, claim) {
  const { model, hash, recorded, stamps } = ctx;
  const declaredEv = claim.data.evaluate && typeof claim.data.evaluate === 'object' ? claim.data.evaluate : null;
  // A claim stated at a cut is evaluated at the cut a caller asks for (EvalOptions.atCut), with everything else kept.
  const ev = declaredEv && declaredEv.cut !== undefined && ctx.atCut ? { ...declaredEv, cut: ctx.atCut } : declaredEv;
  const method = ev && typeof ev.method === 'string' ? ev.method : null;
  const evidence = collectEvidence(model, claim.id, recorded);
  const assumptions = Array.isArray(claim.data.assumptions) ? claim.data.assumptions.filter((/** @type {any} */ a) => typeof a === 'string') : [];
  const modelStamps = stampsOf(hash, hash);
  /** @type {import('./verdict.js').Fact[]} */
  const facts = [];
  /** @type {FactRole[]} */
  const roles = [];
  /** @param {import('./verdict.js').Fact} f @param {FactRole} role */
  const add = (f, role) => { facts.push(f); roles.push(role); };

  /** @type {'none'|'model'|'metric'|'evidence'|'lean'} */
  let family = 'none';
  /** @type {any} */
  let r;
  if (!ev || !method) {
    r = { evaluator: 'none', scope: 'Nothing was checked: the claim declares no evaluation method.', explanation: 'The claim has no "evaluate.method", so Exegra has nothing to run and does not report a result.', selected: [] };
  } else if (own(model.meta.verificationMethods, method) || method === 'external-evidence') {
    family = 'evidence';
    const label = own(model.meta.verificationMethods, method)?.label;
    r = method === 'external-evidence'
      ? { evaluator: EVIDENCE, scope: '', explanation: '', selected: evidence.map((e) => e.id) }
      : { evaluator: `external:${method}`, scope: `Exegra ran nothing. "${label}" verification is carried out outside Exegra; only recorded evidence is reported.`, explanation: '', selected: evidence.map((e) => e.id), label };
  } else if (!Object.hasOwn(CLAIM_METHODS, method)) {
    r = { evaluator: 'none', scope: `Nothing was checked: this build of Exegra has no evaluator for method "${method}".`, explanation: `Method "${method}" is not supported, so the claim stays not evaluated. It is declared, not established.`, selected: [] };
  } else if (method === 'metric-bound') {
    family = 'metric';
    try {
      r = evaluateMetricBound(model, ev);
    } catch (e) {
      r = { evaluator: METRIC, scope: 'The metric claim could not be completed.', explanation: `The evaluator failed: ${/** @type {Error} */ (e).message}`, selected: [], failed: true };
    }
  } else if (method === 'lean-theorem') {
    family = 'lean';
    r = { evaluator: LEAN, scope: '', explanation: '', selected: [] };
  } else {
    family = 'model';
    try {
      r = method === 'refines' ? evaluateRefines(model, ev)
        : TRACE_METHODS.includes(method) ? evaluateTraceClaim(model, claim, ev) : { ...evaluateStructural(model, ev), evaluator: STRUCTURAL };
      if (!TRACE_METHODS.includes(method) && method !== 'refines') { const basis = claimBasis(model, ev); if (basis) r.basis = basis; }
    } catch (e) {
      r = { outcome: 'undecided', evaluator: method === 'refines' ? REFINEMENT : TRACE_METHODS.includes(method) ? TRACE : STRUCTURAL, scope: `Method "${method}" could not be completed.`, explanation: `The evaluator failed: ${/** @type {Error} */ (e).message}`, selected: [] };
    }
  }

  const subject = subjectOf(claim, family);
  /** @param {string} id */
  const atom = (id) => ({ part: id, subject, assumptions });
  /** @type {import('./verdict.js').VerdictClaim} */
  let vclaim = atom(claim.id);
  /** @type {Prepared['metricParts']} */
  let metricParts;
  /** @type {string[]} */
  let evidenceTargets = [claim.id];
  let outside;
  let theorem;
  /** @type {string[]|undefined} */
  let about;

  if (family === 'model') {
    if (r.outcome === 'pass' || r.outcome === 'fail' || r.outcome === 'undecided') {
      add(checkFact(claim.id, method === 'refines' || TRACE_METHODS.includes(/** @type {string} */ (method)) ? 'traceCheck' : 'modelCheck', r.outcome, hash), { role: 'check', id: claim.id });
    }
  } else if (family === 'metric') {
    if (r.failed) {
      add(checkFact(claim.id, 'statistical', 'undecided', hash), { role: 'metric', id: claim.id });
    } else {
      const input = metricVerdictInput(r.result, claim.id, assumptions, hash);
      vclaim = input.claim;
      metricParts = input.parts;
      input.facts.forEach((f, i) => add(f, { role: 'metric', id: input.parts[i].id }));
    }
  } else if (family === 'lean') {
    theorem = typeof ev.theorem === 'string' ? ev.theorem : '';
    about = Array.isArray(ev.about) ? ev.about.filter((/** @type {any} */ a) => typeof a === 'string') : [];
    const rec = theorem && recorded?.theorems && Object.hasOwn(recorded.theorems, theorem) ? recorded.theorems[theorem] : undefined;
    if (rec) {
      add(theoremFact(claim.id, rec, about ?? [], stampsOf(rec.formalHash, stamps?.formal)), { role: 'theorem', id: claim.id });
    }
  } else if (family === 'evidence') {
    // The claim is the conjunction of what each piece of executable evidence shows; author-entered items back
    // every part (with no executable evidence they are the one part).
    const parts = evidence.filter((e) => e.kind === 'test').map((e) => e.id);
    outside = recorded?.claims && Object.hasOwn(recorded.claims, claim.id) ? recorded.claims[claim.id] : undefined;
    const withOutside = outside && (outside.outcome === 'pass' || outside.outcome === 'fail');
    const partIds = [...parts, ...(withOutside || !parts.length ? [claim.id] : [])];
    vclaim = partIds.length === 1 ? atom(partIds[0]) : { all: partIds.map(atom) };
    evidenceTargets = partIds;
    if (withOutside) {
      add({ kind: 'externalTool', subject: 'implementation', target: { part: claim.id }, stamps: stampsOf(outside.stamp, stamps?.tree), outcome: outside.outcome }, { role: 'external', id: claim.id });
    }
  }

  // Evidence. For the evidence-based methods each test item is its own part and every other item backs every part;
  // for the model methods and lean-theorem everything targets the claim (only a contradiction can bear on them:
  // Lean considers a fact about another subject only when it fails).
  if (family !== 'none') {
    for (const e of evidence) {
      const targets = family === 'evidence' && e.kind === 'test' ? [e.id] : evidenceTargets;
      for (const t of targets) {
        if (!e.supports) {
          add(e.kind === 'test' ? { ...testFact(t, 'fail', modelStamps), subject } : documentFact(t, subject, false, modelStamps), { role: e.derived ? 'derived' : 'evidence', id: e.id });
        } else if (e.derived) {
          // A Concordance result is applied only when its results file names this specification text or none
          // (src/core/concordance.js); it describes the model as applied.
          if (e.raw === 'pass' || e.raw === 'fail') add(testFact(t, e.raw, modelStamps), { role: 'derived', id: e.id });
        } else if (e.kind === 'test') {
          if (e.raw === 'pass' || e.raw === 'fail' || e.raw === 'not-run') add(testFact(t, e.raw, stampsOf(e.stamp, stamps?.tree)), { role: 'evidence', id: e.id });
          // Attached but with no recorded result: a fact of the current files that the test has not run.
          else add(testFact(t, 'not-run', stampsOf(stamps?.tree, stamps?.tree)), { role: 'pending', id: e.id });
        } else {
          add(documentFact(t, subject, true, modelStamps), { role: 'evidence', id: e.id });
        }
      }
    }
  }

  // Facts about the assumptions the claim rests on.
  const aFacts = assumptionFactsOf(ctx, assumptions);
  for (const a of aFacts) {
    add(assumptionFact(a.assumption, a.kind ?? 'importScan', a.outcome, stampsOf(a.stamp, stamps?.tree)), { role: 'assumption', id: a.assumption });
  }

  return { entity: claim, method, ev, family, r, evidence, claim: vclaim, facts, roles, outside, theorem, about, assumptionFacts: aFacts, metricParts };
}

/**
 * The result of a claim from its prepared facts and the Lean verdict: the status is the verdict's label; the rest
 * is wording.
 * @param {Ctx} ctx @param {Prepared} p @param {import('./verdict.js').Verdict} v
 * @returns {ClaimResult}
 */
function present(ctx, p, v) {
  const { model, hash } = ctx;
  const claim = p.entity;
  const status = /** @type {ClaimResult['status']} */ (v.label);
  // The freshness Lean gave each fact, applied to the evidence items it came from.
  /** @type {Map<string, string[]>} */
  const freshBy = new Map();
  p.roles.forEach((role, i) => {
    const f = v.factFreshness[i];
    if (typeof f !== 'string') return;
    const key = `${role.role}\0${role.id}`;
    freshBy.set(key, [...(freshBy.get(key) ?? []), f]);
  });
  const worst = (/** @type {string} */ role, /** @type {string} */ id) => {
    const fs = freshBy.get(`${role}\0${id}`) ?? [];
    return fs.includes('stale') ? 'stale' : fs.includes('unverifiable') ? 'unverifiable' : fs.length ? 'fresh' : null;
  };
  for (const e of p.evidence) {
    if (e.derived || e.kind !== 'test' || !e.supports || e.recorded === 'none') continue;
    const f = worst('evidence', e.id);
    if (f === 'stale') {
      e.stale = true;
      if (e.recorded === 'pass') e.recorded = 'none';
    } else if (f === 'fresh' || f === 'unverifiable') e.freshness = f;
  }
  const refusedAssumptions = unique(p.assumptionFacts.filter((a) => a.outcome === 'fail').map((a) => a.assumption));

  const text = describe(ctx, p, v);
  /** @type {ClaimResult} */
  const result = {
    claimId: claim.id,
    kind: claim.data.kind,
    method: p.method,
    status,
    evaluator: text.evaluator,
    semanticHash: hash,
    scope: text.scope,
    explanation: text.explanation,
    assumptions: Array.isArray(claim.data.assumptions) ? [...claim.data.assumptions] : [],
    involved: [],
    evidence: p.evidence.map(({ raw, stamp, ...item }) => { void raw; void stamp; return item; }),
    verdict: { strength: v.strength, subject: v.subject, openAssumptions: v.openAssumptions, freshness: v.freshness, established: v.established },
  };
  // What the relationships the check read rest on: declared by authors, extracted from the code, or observed in a run.
  if (p.r?.basis) {
    result.basis = p.r.basis;
    if (p.r.basis.basis !== 'declared-only' && p.r.basis.basis !== 'none') result.scope = `${result.scope} ${p.r.basis.text}`.trim();
  }
  if (refusedAssumptions.length && v.strength === 'undecided') {
    const why = p.assumptionFacts.filter((a) => a.outcome === 'fail' && a.detail).map((a) => a.detail);
    result.explanation += ` However, ${refusedAssumptions.length === 1 ? 'the assumption' : 'the assumptions'} ${list(refusedAssumptions.map((a) => `"${a}"`))} ${refusedAssumptions.length === 1 ? 'is' : 'are'} recorded as refuted${why.length ? ` (${why.join('; ')})` : ''}, so the claim is undecided: it may still hold, but what it rests on does not.`;
  }
  const fm = faultModelOf(model, claim);
  if (fm) {
    result.scope = `${faultModelScope(model, fm)} ${result.scope}`.trim();
    if (p.method && TRACE_METHODS.includes(p.method)) result.explanation = `${result.explanation} ${faultCoverage(model, fm, p.ev)}`.trim();
  }
  if (text.counterexample) result.counterexample = text.counterexample;
  if (p.r?.negatives) result.negatives = p.r.negatives;
  const subjects = Array.isArray(claim.data.subjects) ? claim.data.subjects.filter((/** @type {any} */ s) => typeof s === 'string') : [];
  result.involved = unique([...subjects, ...(p.r?.selected ?? []), ...(result.counterexample?.entities ?? []), ...(result.counterexample?.path ?? [])]);

  // Freshness and its diagnostics, for a status that rests on recorded facts.
  /** @type {ClaimDiagnostic[]} */
  const diagnostics = [];
  const staleEvidence = result.evidence.filter((e) => e.stale);
  if (staleEvidence.length) {
    diagnostics.push({ code: 'claim.stale-evidence', severity: 'warning', entityId: claim.id,
      message: `The recorded result of ${staleEvidence.map((e) => `"${e.id}"`).join(', ')} was recorded on another tree than the current one; it is stale until exegra verify runs again.` });
  }
  if (p.theorem && worst('theorem', claim.id) === 'stale') {
    diagnostics.push({ code: 'claim.stale-theorem', severity: 'warning', entityId: claim.id, message: text.staleTheorem ?? 'The recorded Lean check is stale.' });
  }
  if (worst('external', claim.id) === 'stale' && !staleEvidence.length) {
    diagnostics.push({ code: 'claim.stale-evidence', severity: 'warning', entityId: claim.id, message: 'The outcome an external tool recorded for this claim was recorded on another tree than the current one.' });
  }
  for (const x of v.refused) {
    const role = p.roles[x.index];
    diagnostics.push({ code: 'claim.fact-refused', severity: 'warning', entityId: claim.id, message: `A fact${role ? ` from ${role.role} "${role.id}"` : ''} does not meet the fact schema and was refused: ${x.error}.` });
  }
  const recordedRoles = new Set(['evidence', 'external', 'theorem', 'assumption']);
  const usedRecorded = p.roles.some((role, i) => recordedRoles.has(role.role) && (p.family === 'evidence' || role.role !== 'evidence' || p.facts[i].outcome === 'fail'));
  if (usedRecorded) {
    result.freshness = v.freshness;
    if (v.freshness === 'unverifiable') {
      diagnostics.push({ code: 'claim.freshness-unverifiable', severity: 'info', entityId: claim.id,
        message: 'No stamp of the current files is available here, so whether the recorded facts this status rests on describe them cannot be checked.' });
      result.explanation += ' Freshness unverifiable: no stamp of the current files is available here, so the results recorded for files that may since have changed establish nothing here.';
    }
  }
  if (p.r?.level) result.level = p.r.level;
  if (p.r?.diagnostics?.length) diagnostics.push(...p.r.diagnostics.map((/** @type {any} */ d) => ({ ...d, entityId: claim.id })));
  result.footprint = footprintOf(claim, p.method, p.ev, p.r ?? {});
  if (diagnostics.length) result.diagnostics = diagnostics;
  return result;
}

/** @param {EvidenceItem[]} bad */
function describeContradictions(bad) {
  return bad.map((e) => (e.derived ? `evidence "${e.id}" (Concordance recorded: fail)` : e.recorded === 'fail' ? `evidence "${e.id}" (recorded result: fail)` : `evidence "${e.id}" (declared as contradicting)`)).join(' and ');
}

/** Structural methods whose result reads only the relationship graph and the selected components. */
const GRAPH_METHODS = ['no-relationship', 'reachable', 'only-via', 'acyclic'];

/**
 * The footprint of a claim result (src/core/footprints.js): what it read. A graph method reads the claim, the
 * components its selectors picked, every relationship that passes its kind filter (only those between its source
 * and target components for a direct no-relationship check), every port (ports resolve endpoints) and, stated at a
 * cut, the abstraction structure of that cut. The other model-decided methods read the claim, the selected
 * components and every entity of the kinds they inspect; results resting on runs or recorded facts read everything.
 * @param {Entity} claim @param {string|null} method @param {any} ev @param {any} r
 * @returns {import('./footprints.js').Footprint}
 */
function footprintOf(claim, method, ev, r) {
  const entities = unique([claim.id, ...(r.selected ?? []), ...(typeof ev?.cut === 'string' ? [ev.cut] : [])]);
  if (method && GRAPH_METHODS.includes(method)) {
    const q = r.query ?? { kinds: null, classes: null, where: null, from: null, to: null };
    return { entities, entityKinds: ['port'], selection: true, relationships: q, structure: r.level ? { hierarchy: r.level.hierarchy, cut: r.level.cut } : null };
  }
  if (method === 'has-port') return { entities, entityKinds: ['port'], selection: true };
  if (method === 'property-defined' || method === 'implementation-language') return { entities, entityKinds: ['component'], selection: true };
  if (method === 'abstraction-well-formed') return { entities, entityKinds: ['component', 'hierarchy', 'cut', 'system', 'facet'], selection: true };
  if (method === 'abstraction-invariants') return { entities, entityKinds: ['relationship', 'component', 'port', 'hierarchy', 'cut', 'system', 'event'], selection: true };
  if (method === 'extraction-reconciled') return { entities, entityKinds: ['relationship', 'component', 'event', 'behavior', 'transition'], selection: true };
  if (method === null) return { entities: [claim.id] };
  return { all: true };
}

const POSITIVE = new Set(['proved', 'verified', 'supported', 'model-holds']);

/**
 * The wording of a result: evaluator, scope, explanation and counterexample, for the status Lean decided.
 * @param {Ctx} ctx @param {Prepared} p @param {import('./verdict.js').Verdict} v
 * @returns {{evaluator: string, scope: string, explanation: string, counterexample?: Counterexample, staleTheorem?: string}}
 */
function describe(ctx, p, v) {
  const label = v.label;
  const bad = p.evidence.filter((e) => !e.supports || e.recorded === 'fail');
  const contradicted = (/** @type {string} */ what) => ` However, ${describeContradictions(bad)} contradict${bad.length === 1 ? 's' : ''} ${what}, so the claim is reported as violated.`;
  const badCx = () => ({ summary: `Contradicting evidence: ${bad.map((e) => e.id).join(', ')}.`, entities: bad.map((e) => e.id) });
  const r = p.r;
  if (p.family === 'none') return { evaluator: r.evaluator, scope: r.scope, explanation: r.explanation };
  if (p.family === 'model') {
    const out = { evaluator: r.evaluator, scope: r.scope, explanation: r.explanation, counterexample: r.counterexample };
    if (label === 'violated' && r.outcome !== 'fail' && bad.length) {
      out.explanation += contradicted('this result');
      out.counterexample = badCx();
    }
    return out;
  }
  if (p.family === 'metric') return describeMetric(p, v, bad, contradicted, badCx);
  if (p.family === 'lean') return describeLean(ctx, p, v, bad, contradicted, badCx);
  return describeEvidence(ctx, p, v, bad);
}

/**
 * @param {Prepared} p @param {import('./verdict.js').Verdict} v @param {EvidenceItem[]} bad
 * @param {(what: string) => string} contradicted @param {() => Counterexample} badCx
 */
function describeMetric(p, v, bad, contradicted, badCx) {
  const r = p.r;
  if (r.failed) return { evaluator: r.evaluator, scope: r.scope, explanation: r.explanation };
  const res = r.result;
  const claim = r.claim;
  const failing = res.scenarios.some((/** @type {any} */ s) => s.verdict === 'fails');
  const reason = res.scenarios.some((/** @type {any} */ s) => s.verdict !== 'holds' && s.verdict !== 'fails') ? 'a scenario is inconclusive'
    : res.negatives.some((/** @type {any} */ n) => n.verdict !== 'fails') ? 'a negative does not fail (vacuous)'
      : res.controlNegatives.some((/** @type {any} */ n) => n.verdict !== 'holds') ? 'a control negative does not hold (fails for another reason)' : 'every part holds';
  const head = v.label === 'model-holds'
    ? `Holds in the model at ${claim.confidence} confidence over ${claim.runs} runs per scenario; parameters assumed, unvalidated.`
    : v.label === 'violated' && failing ? `Fails in the model at ${claim.confidence} confidence over ${claim.runs} runs.`
      : v.label === 'violated' ? `The statistical tests hold, but the claim is violated.` : `Inconclusive over ${claim.runs} runs: ${reason}.`;
  /** @type {{evaluator: string, scope: string, explanation: string, counterexample?: Counterexample}} */
  const out = { evaluator: r.evaluator, scope: r.scope, explanation: `${head} ${r.parts.join('; ')}.` };
  if (v.label === 'violated' && failing) {
    const s = res.scenarios.find((/** @type {any} */ x) => x.verdict === 'fails');
    const worst = s?.statistics?.find((/** @type {any} */ x) => x.value === 'inf') ?? s?.statistics?.[0];
    out.counterexample = { summary: `A failing scenario; replay seed ${worst?.seed ?? '?'} as a trace.`, entities: [...r.selected] };
  } else if (v.label === 'violated' && bad.length) {
    out.explanation += contradicted('it');
    out.counterexample = badCx();
  }
  return out;
}

/** The text of a refusal of a theorem check, from the reason Lean gave. @param {string} reason @param {string} detail */
function refusalText(reason, detail) {
  const [a, b] = detail.split(':');
  switch (reason) {
    case 'not-found': return 'no such constant exists in the Lean core.';
    case 'not-a-theorem': return `it is ${detail === 'axiom' ? 'an axiom' : `a ${detail}`}, not a theorem.`;
    case 'kernel': return `the kernel does not accept its proof (${detail}).`;
    case 'axioms': return `it depends on ${detail.split(',').map((x) => {
      const [name, why] = x.split(':');
      return why === 'sorry' ? `${name} (the proof uses sorry)` : why === 'native' ? `${name} (the proof uses native_decide, which trusts compiled code instead of the kernel)` : `${name} (an axiom beyond Lean's standard ones)`;
    }).join(', ')}.`;
    case 'no-about': return 'the claim names no implementation constant ("about"), so the theorem is not shown to be about any code.';
    case 'about-missing': return `the implementation constant "${a}" does not exist.`;
    case 'about-opaque': return `"${a}" is an opaque constant: a theorem about it says nothing about the body that runs (a partial def and an implemented_by opaque compile to one).`;
    case 'about-kind': return `"${a}" is a ${b}, not an implementation constant (a definition).`;
    case 'about-implemented-by': return `"${a}" is implemented_by ${b}: the code that runs is not the definition the theorem is about.`;
    case 'about-extern': return `"${a}" is extern: the code that runs is foreign code, not the definition the theorem is about.`;
    case 'about-partial': return `"${a}" is a partial definition: its compiled body is not the definition the theorem is about.`;
    case 'about-not-in-statement': return `its statement does not mention the implementation constant "${a}", so it is not a theorem about that code.`;
    default: return `${reason} ${detail}`.trim();
  }
}

/**
 * @param {Ctx} ctx @param {Prepared} p @param {import('./verdict.js').Verdict} v @param {EvidenceItem[]} bad
 * @param {(what: string) => string} contradicted @param {() => Counterexample} badCx
 */
function describeLean(ctx, p, v, bad, contradicted, badCx) {
  const thm = p.theorem ?? '';
  const rec = thm && ctx.recorded?.theorems && Object.hasOwn(ctx.recorded.theorems, thm) ? ctx.recorded.theorems[thm] : undefined;
  const lean = rec?.lean ? `Lean ${rec.lean}` : 'Lean';
  const evaluator = rec?.lean ? `${LEAN}/${rec.lean}` : LEAN;
  const scope = `Checked by ${lean}${rec?.checkedAt ? ` at ${rec.checkedAt}` : ''}, as recorded: the theorem's proof re-checked by the kernel and its axioms collected. It establishes the statement about the Lean definitions it names. That the code which runs is those definitions rests on the trusted base: the Lean compiler and runtime, the WebAssembly toolchain and the JS glue (the claim's assumptions).`;
  const notChecked = { evaluator, scope: 'Nothing was checked: there is no recorded Lean check for this claim.' };
  if (!thm) return { ...notChecked, explanation: 'The claim names no theorem.' };
  if (!rec) return { ...notChecked, explanation: `Lean has not checked "${thm}": run "exegra verify" (or "exegra claims" where Lean is installed) to record the check.` };
  const idx = p.roles.findIndex((role) => role.role === 'theorem');
  const t = v.theorems.find((x) => x.index === idx);
  if (!t) return { ...notChecked, explanation: `The recorded check of "${thm}" could not be read.` };
  if (t.outcome === 'fail') {
    const why = refusalText(t.reason, t.detail);
    return { evaluator, scope, explanation: `Lean refuses "${thm}" as a proof of this claim: ${why}`, counterexample: { summary: `Lean refuses ${thm}: ${why}`, entities: [] } };
  }
  if (t.outcome === 'not-run') {
    return { ...notChecked, explanation: `The recorded check of "${thm}" did not cover ${t.detail.split(',').map((a) => `"${a}"`).join(', ')}: run "exegra verify" again.` };
  }
  if (v.factFreshness[idx] === 'stale') {
    const formal = ctx.stamps?.formal ?? '';
    const why = `Stale: the recorded Lean check of "${thm}" ${rec.formalHash ? `ran on formal/ sources with hash ${String(rec.formalHash).slice(0, 12)}` : 'carries no hash of the formal/ sources it ran on'}, not on the current ones (${formal.slice(0, 12)}); run "exegra verify" where Lean is installed to check it again.`;
    return { evaluator, scope: 'Nothing was checked against the current sources: the recorded Lean check is stale.', explanation: why, staleTheorem: why };
  }
  const axioms = Array.isArray(rec.axioms) ? rec.axioms : [];
  const out = {
    evaluator, scope,
    explanation: `"${thm}" is a theorem; the Lean kernel accepted its proof again; it depends only on ${axioms.length ? axioms.join(', ') : 'no axiom'}; its statement is about ${(p.about ?? []).join(', ')}${rec.statementHash ? ` (statement hash ${String(rec.statementHash).slice(0, 12)})` : ''}.`,
  };
  if (v.label === 'violated' && bad.length) return { ...out, explanation: out.explanation + contradicted('it'), counterexample: badCx() };
  return out;
}

/** @param {Ctx} ctx @param {Prepared} p @param {import('./verdict.js').Verdict} v @param {EvidenceItem[]} bad */
function describeEvidence(ctx, p, v, bad) {
  const r = p.r;
  const evidence = p.evidence;
  const label = v.label;
  const outside = p.outside && (p.outside.outcome === 'pass' || p.outside.outcome === 'fail') ? p.outside : null;
  const tool = typeof ctx.recorded?.tool === 'string' && ctx.recorded.tool ? ctx.recorded.tool : 'an external tool';
  const prefix = r.scope ? `${r.scope} ` : '';
  if (!evidence.length && !outside) {
    return { evaluator: r.evaluator, scope: `${prefix}Nothing was checked: the model cannot establish this claim and no evidence is attached to it.`.trim(),
      explanation: `Claim "${p.entity.id}" relies on external evidence, but no evidence entity refers to it. It is declared, not established.` };
  }
  const recordedCount = evidence.filter((e) => e.recorded !== 'none').length;
  const scope = outside
    ? `Exegra ran nothing. The status rests on the outcome ${tool} recorded for this claim${evidence.length ? ` and on ${evidence.length} evidence ${evidence.length === 1 ? 'entity' : 'entities'}` : ''}.`
    : `${prefix}No model evaluation was performed. This rests on ${evidence.length} evidence ${evidence.length === 1 ? 'entity' : 'entities'} (${evidence.map((e) => e.id).join(', ')}), of which ${recordedCount} ${recordedCount === 1 ? 'has' : 'have'} a recorded execution result; the rest is author-entered.`;
  const proofs = outside && Array.isArray(outside.proofs) && outside.proofs.length ? ` Proofs: ${outside.proofs.join(', ')}.` : '';
  const detail = outside && typeof outside.detail === 'string' && outside.detail ? ` ${outside.detail}` : '';
  if (label === 'violated') {
    if (outside?.outcome === 'fail') {
      return { evaluator: r.evaluator, scope, explanation: `Recorded by ${tool} as failing.${detail}${proofs}`, counterexample: { summary: `${tool} reports this requirement as not met.${detail}`, entities: [p.entity.id] } };
    }
    return { evaluator: r.evaluator, scope,
      explanation: `${outside ? `Recorded by ${tool} as passing, but evidence in this specification contradicts it. ` : ''}${capitalise(describeContradictions(bad))} contradict${bad.length === 1 ? 's' : ''} the claim.`,
      counterexample: { summary: `Contradicting evidence: ${bad.map((e) => e.id).join(', ')}.`, entities: bad.map((e) => e.id) } };
  }
  const stale = evidence.filter((e) => e.stale);
  const outsideStale = outside && p.roles.some((role, i) => role.role === 'external' && v.factFreshness[i] === 'stale');
  if (label === 'not-evaluated' && (stale.length || outsideStale)) {
    const parts = [];
    if (stale.length) parts.push(`the recorded result${stale.length === 1 ? '' : 's'} of ${list(stale.map((e) => `"${e.id}"`))} ${stale.length === 1 ? 'was' : 'were'} recorded on another tree than the current one (the stamp differs or is missing), so ${stale.length === 1 ? 'it establishes' : 'they establish'} nothing now`);
    if (outsideStale) parts.push(`${tool} recorded this claim as passing on ${outside.stamp ? `tree stamp ${String(outside.stamp).slice(0, 12)}` : 'a tree it did not stamp'}, not on the current tree (${String(ctx.stamps?.tree ?? '').slice(0, 12)}), so it establishes nothing now`);
    return { evaluator: r.evaluator, scope, explanation: `Stale: ${parts.join('; and ')}; run exegra verify to record ${stale.length + (outsideStale ? 1 : 0) === 1 ? 'it' : 'them'} again.` };
  }
  const passedTests = evidence.filter((e) => e.kind === 'test' && !e.derived && e.recorded === 'pass');
  const passedDerived = evidence.filter((e) => e.derived && e.recorded === 'pass');
  const nonTests = evidence.filter((e) => e.kind !== 'test');
  const pendingTests = evidence.filter((e) => e.kind === 'test' && !e.derived && e.recorded === 'none');
  const notRun = pendingTests.filter((e) => e.raw === 'not-run');
  const parts = [];
  if (outside?.outcome === 'pass') parts.push(`Recorded by ${tool} as established by "${r.label ?? 'external'}" verification.${detail}${proofs} Exegra did not check this itself; the result is as current as the recorded file.`);
  if (passedTests.length) parts.push(`Exegra holds a recorded result of executing ${list(passedTests.map((e) => e.id))}: pass.`);
  for (const e of passedDerived) parts.push(`Concordance recorded "${e.id}" as passing, a result Exegra did not execute.${e.revision === 'unknown' ? ' It was computed for an unknown revision of the specification (the results file names no specSha256), so it may describe an earlier text.' : ''}${e.detail ? ` ${e.detail}` : ''}${e.proofs?.length ? ` Proofs: ${e.proofs.join(', ')}.` : ''}`);
  if (nonTests.length) parts.push(`${capitalise(list(nonTests.map((e) => `${e.kind} "${e.id}"`)))} ${nonTests.length === 1 ? 'is' : 'are'} author-entered only; Exegra did not execute or check ${nonTests.length === 1 ? 'it' : 'them'}.`);
  if (notRun.length) parts.push(`Test evidence ${list(notRun.map((e) => `"${e.id}"`))} did not run (${notRun.map((e) => e.detail ?? 'skipped').join('; ')}).`);
  const unrecorded = pendingTests.filter((e) => e.raw !== 'not-run');
  if (unrecorded.length) parts.push(`Test evidence ${list(unrecorded.map((e) => `"${e.id}"`))} has no recorded result.`);
  if (!passedTests.length && !outside) parts.unshift('Exegra executed nothing for this claim.');
  if (label === 'asserted') parts.push('Asserted: what is written down is not established by anything Exegra checked.');
  if ((label === 'inconclusive' || label === 'not-evaluated') && (passedTests.length || passedDerived.length || nonTests.length || outside)) {
    parts.push('A claim is as strong as its weakest part, so it is not established.');
  }
  if (label === 'inconclusive' && !passedTests.length && !passedDerived.length && !nonTests.length && !outside && pendingTests.length) {
    return { evaluator: r.evaluator, scope, explanation: `Only test evidence (${list(pendingTests.map((e) => `"${e.id}"`))}) is attached and no result of running it ${notRun.length ? 'counts (it did not run)' : 'is recorded'}, so Exegra cannot tell whether the test passes.` };
  }
  return { evaluator: r.evaluator, scope, explanation: parts.join(' ') };
}

// ---------------------------------------------------------------------------
// Lean theorems
// ---------------------------------------------------------------------------

/**
 * The theorems the lean-theorem claims of a model name, with the implementation constants each must
 * be about and the theorem that supersedes it (`supersedes`, when a claim names one): what
 * tools/lean-theorems.js is asked to check.
 * @param {Model} model
 * @returns {{theorem: string, about: string[], supersedes?: string}[]}
 */
export function theoremRequests(model) {
  /** @type {Map<string, {about: Set<string>, supersedes?: string}>} */
  const by = new Map();
  for (const c of model.byKind.claim ?? []) {
    const ev = c.data.evaluate;
    if (!ev || ev.method !== 'lean-theorem' || typeof ev.theorem !== 'string' || !ev.theorem) continue;
    const entry = by.get(ev.theorem) ?? { about: new Set() };
    for (const a of Array.isArray(ev.about) ? ev.about : []) if (typeof a === 'string') entry.about.add(a);
    if (typeof ev.supersedes === 'string' && ev.supersedes && !entry.supersedes) entry.supersedes = ev.supersedes;
    by.set(ev.theorem, entry);
  }
  return [...by].map(([theorem, e]) => ({ theorem, about: [...e.about].sort(), ...(e.supersedes ? { supersedes: e.supersedes } : {}) }));
}

// ---------------------------------------------------------------------------
// Metric claims (docs/simulation.md, "Claims over metrics")
// ---------------------------------------------------------------------------

/**
 * A metric-bound claim: each listed scenario (a format-2 scenario) runs N times with the run
 * seeds of the claim's seed, through the engine, and the per-run statistic is tested by the exact
 * binomial test or the sign-test interval (src/core/metric-claims.js). A bound written as a
 * duration is converted to the base unit of the first scenario. The results become statistical
 * facts (metricVerdictInput); Lean decides `model-holds`, `violated` or `inconclusive`, never verified.
 * @param {Model} model @param {any} ev
 */
function evaluateMetricBound(model, ev) {
  const sids = Array.isArray(ev.scenarios) ? ev.scenarios : [ev.scenarios];
  /** @param {string} sid @param {string[]} extra */
  const inputOf = (sid, extra) => {
    const sc = /** @type {any} */ (model.entities.get(sid));
    const own = Array.isArray(sc?.data?.faults) ? sc.data.faults : [];
    const d = sc?.data ?? {};
    if (!((Array.isArray(d.workloads) && d.workloads.length) || d.seed !== undefined || d.horizon !== undefined)) {
      throw new Error(`Scenario "${sid}" is not a format-2 scenario: it declares no workloads, seed or horizon.`);
    }
    const input = /** @type {any} */ (simulationInput(model, sid, [...own, ...extra]));
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
  return {
    evaluator: METRIC, result: res, claim, parts,
    scope: `Model only; parameters as stated. Seeded runs: N = ${claim.runs}, β = ${claim.fraction}, confidence ${claim.confidence}, base seed ${claim.seed}${ev.asOf ? `, as of ${ev.asOf}` : ''}. Never verified, never counted as evidence.`,
    selected: [...sids],
  };
}

/**
 * The evidence entities of a claim with their recorded results, as recorded (freshness is decided in Lean and
 * applied by `present`). `raw` and `stamp` carry the record into the fact and are not part of the result.
 * @param {Model} model @param {string} claimId @param {Recorded|undefined} recorded
 * @returns {(EvidenceItem & {raw?: string, stamp?: string|null})[]}
 */
function collectEvidence(model, claimId, recorded) {
  /** @type {(EvidenceItem & {raw?: string, stamp?: string|null})[]} */
  const out = [];
  for (const e of model.byKind.evidence ?? []) {
    if (e.data.claim !== claimId) continue;
    const rec = recorded?.results && Object.hasOwn(recorded.results, e.id) ? recorded.results[e.id] : undefined;
    const outcome = rec && (rec.outcome === 'pass' || rec.outcome === 'fail') ? rec.outcome : 'none';
    /** @type {EvidenceItem & {raw?: string, stamp?: string|null}} */
    const item = {
      id: e.id,
      kind: e.data.kind,
      ref: typeof e.data.ref === 'string' ? e.data.ref : '',
      supports: e.data.supports !== false,
      recorded: outcome,
      raw: rec?.outcome,
      stamp: rec?.stamp ?? null,
    };
    const detail = rec?.detail ?? (typeof e.data.observed === 'string' ? e.data.observed : undefined);
    if (detail !== undefined) item.detail = detail;
    out.push(item);
  }
  for (const d of recorded?.derived ?? []) {
    if (d.claim !== claimId) continue;
    /** @type {EvidenceItem & {raw?: string}} */
    const item = { id: d.id, kind: 'test', ref: d.ref, supports: true, recorded: d.outcome, title: d.title, derived: true, revision: d.revision, raw: d.outcome };
    if (d.detail !== undefined) item.detail = d.detail;
    if (d.proofs !== undefined) item.proofs = d.proofs;
    out.push(item);
  }
  return out;
}

// ---------------------------------------------------------------------------
// Structural evaluators
// ---------------------------------------------------------------------------

/** @typedef {{ outcome: string, scope: string, explanation: string, selected: string[], counterexample?: Counterexample, negatives?: NegativeRun[] }} Outcome */

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
    case 'abstraction-well-formed': return abstractionWellFormed(model, ev);
    case 'abstraction-invariants': return invariantsHold(model, ev);
    case 'extraction-reconciled': return extractionReconciled(model, ev);
  }
  throw new Error(`No structural evaluator for "${ev.method}".`);
}

/**
 * The declared relationships agree with the extracted facts attached to the model (src/core/extraction.js): no
 * declared static dependency inside the extraction surface that extraction also finds (redundant), misses
 * (unwitnessed), finds the other way (direction) or finds only dynamically (kind), and no file of the facts
 * belongs to no module element. An extracted dependency with no declared counterpart is not a discrepancy: it is the
 * dependency. Decided by the model and the facts; the facts' own freshness against the tree is the assumption
 * extracted-facts-current, recorded by verify.
 * @param {Model} model @param {any} ev @returns {Outcome}
 */
function extractionReconciled(model, ev) {
  void ev;
  const x = extractionOf(model);
  if (!x) return inconclusive('Nothing was checked: no extracted facts are attached to this model.', 'No fact file (specs/<project>/extracted/facts.json, written by tools/extract.js) is attached, so there is nothing to reconcile the declarations with. It is not reported as verified.');
  const rec = reconcile(model);
  const bad = rec.diagnostics.filter((d) => d.severity === 'warning' && d.code !== 'reconcile.observed-undeclared');
  const files = x.facts.files.length;
  const scope = `Reconciled ${plural(x.edges.length, 'extracted relationship', 'extracted relationships')} between module elements (${plural(files, 'file', 'files')} read by ${x.facts.extractor.id} ${x.facts.extractor.version}) with the ${plural(rec.summary.declaredRelationships, 'declared relationship', 'declared relationships')} at this model revision. ${STATIC_ONLY} Runtime wiring (invokes, notifies, composes, ...) is declared and is not compared with it.`;
  if (!bad.length) return { outcome: 'pass', scope, selected: [], explanation: `No declared static dependency inside the extraction surface is redundant, unwitnessed, reversed or of another kind than extraction finds, and every extracted file belongs to a module element (${rec.summary.declaredStaticInSurface} declared static dependencies inside the surface).` };
  return { outcome: 'fail', scope, selected: [], explanation: `${bad[0].message}${bad.length > 1 ? ` ${bad.length - 1} more discrepancies follow.` : ''}`, counterexample: { summary: bad.slice(0, 5).map((d) => d.message).join(' '), entities: bad.map((d) => d.relationship).filter((x) => typeof x === 'string') } };
}

/**
 * Every listed hierarchy is laminar and acyclic and every listed cut is an antichain covering every element,
 * with an abstraction map that sends each element at or below it to exactly one block (query.js).
 * @param {Model} model @param {any} ev @returns {Outcome}
 */
function abstractionWellFormed(model, ev) {
  const hierarchies = Array.isArray(ev.hierarchies) ? ev.hierarchies.filter((/** @type {any} */ h) => typeof h === 'string') : hierarchyIds(model);
  const cuts = Array.isArray(ev.cuts) ? ev.cuts.filter((/** @type {any} */ c) => typeof c === 'string') : (model.byKind.cut ?? []).map((c) => c.id);
  const elements = elementsOf(model);
  /** @type {string[]} */
  const faults = [];
  /** @type {Set<string>} */
  const offending = new Set();
  for (const hid of hierarchies) {
    const h = hierarchyOf(model, hid);
    if (!h) { faults.push(`"${hid}" is not a hierarchy`); continue; }
    for (const p of h.problems) { faults.push(p.message); offending.add(p.element); }
    // A parent relation that is a forest: every element at most one parent, every parent an element.
    for (const [e, p] of h.parent) if (!elements.has(p)) { faults.push(`"${e}" has parent "${p}", which is not an element`); offending.add(e); }
  }
  for (const cid of cuts) {
    const m = cutMap(model, cid);
    if (!m) { faults.push(`"${cid}" is not a cut of a known hierarchy`); continue; }
    for (const p of m.problems) { faults.push(`cut "${cid}": ${p.message}`); offending.add(p.element); }
    // alpha_C is total on every element at or below the cut, onto the blocks, and fixes each block.
    const blocks = new Set(m.blocks);
    const opened = new Set(m.expanded);
    for (const e of elements.keys()) {
      const b = m.map.get(e);
      if (opened.has(e)) { if (b !== undefined) { faults.push(`cut "${cid}" maps "${e}", which it opens`); offending.add(e); } continue; }
      if (b === undefined || !blocks.has(b)) { faults.push(`cut "${cid}" maps "${e}" to no block`); offending.add(e); }
    }
    for (const b of blocks) if (m.map.get(b) !== b) { faults.push(`cut "${cid}" does not fix its block "${b}"`); offending.add(b); }
  }
  const scope = `Checked ${plural(hierarchies.length, 'hierarchy', 'hierarchies')} (${hierarchies.join(', ')}) over ${plural(elements.size, 'element', 'elements')} and ${plural(cuts.length, 'cut', 'cuts')}${cuts.length ? ` (${cuts.join(', ')})` : ''} at this model revision, module elements derived from implementation.modules.`;
  const selected = [...hierarchies.filter((h) => model.entities.has(h)), ...cuts];
  if (!faults.length) return { outcome: 'pass', scope, selected, explanation: `Every hierarchy is laminar and acyclic, every module element has exactly one owner, and each cut is an antichain covering every element whose abstraction map sends each element at or below it to exactly one block.` };
  const entities = [...offending].filter((e) => model.entities.has(e));
  return { outcome: 'fail', scope, selected, explanation: `${faults.length} ${faults.length === 1 ? 'fault' : 'faults'}: ${faults.slice(0, 5).join('; ')}${faults.length > 5 ? '; ...' : ''}.`, counterexample: { summary: faults.slice(0, 3).join('; '), entities } };
}

/**
 * The invariants of an abstraction hold on the derived models of the listed cuts (abstraction.js).
 * @param {Model} model @param {any} ev @returns {Outcome}
 */
function invariantsHold(model, ev) {
  const cuts = Array.isArray(ev.cuts) ? ev.cuts.filter((/** @type {any} */ c) => typeof c === 'string') : typeof ev.cuts === 'string' ? [ev.cuts] : (model.byKind.cut ?? []).map((c) => c.id);
  const names = Array.isArray(ev.invariants) ? ev.invariants : Object.keys(ABSTRACTION_INVARIANTS);
  const unknown = names.filter((/** @type {any} */ n) => !Object.hasOwn(ABSTRACTION_INVARIANTS, n));
  if (unknown.length) return inconclusive('Nothing was checked.', `Unknown invariant${unknown.length === 1 ? '' : 's'} ${list(unknown.map((/** @type {string} */ n) => `"${n}"`))}; the invariants are ${Object.keys(ABSTRACTION_INVARIANTS).join(', ')}.`, cuts);
  if (!cuts.length) return inconclusive('Nothing was checked: no cut is listed or declared.', 'Without a cut there is no derived model to check, so the invariants would hold vacuously. It is not reported as verified.');
  const r = abstractionInvariants(model, cuts, names);
  const selected = cuts.filter((c) => model.entities.has(c));
  const pairs = names.includes('functoriality') ? `, over ${plural(r.pairs.length, 'comparable pair', 'comparable pairs')} of cuts` : '';
  const scope = `Checked ${list(names.map((/** @type {string} */ n) => `"${n}"`))} on the derived models of ${plural(cuts.length, 'cut', 'cuts')} (${cuts.join(', ')}), with kinds as declared and coarsened to the top kinds (${r.interactions} derived interactions in all)${pairs}, recomputed from the relationships at this model revision.`;
  if (names.includes('functoriality') && !r.pairs.length) return inconclusive(scope, 'No two of the listed cuts are comparable (one refining the other), so functoriality had nothing to compare. It is not reported as verified.', selected);
  const bad = Object.entries(r.faults).filter(([, f]) => f.length);
  if (!bad.length) return { outcome: 'pass', scope, selected, explanation: names.map((/** @type {string} */ n) => /** @type {any} */ (ABSTRACTION_INVARIANTS)[n]).join(' ') };
  const all = bad.flatMap(([n, f]) => f.map((x) => `${n}: ${x}`));
  return { outcome: 'fail', scope, selected, explanation: `${plural(all.length, 'fault', 'faults')}: ${all.slice(0, 5).join('; ')}${all.length > 5 ? '; ...' : ''}.`, counterexample: { summary: all.slice(0, 3).join('; '), entities: selected } };
}

/** @param {string} scope @param {string} explanation @param {string[]} [selected] @returns {Outcome} */
function inconclusive(scope, explanation, selected = []) {
  return { outcome: 'undecided', scope, explanation, selected };
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
 * @returns {{kinds: string[]|null, classes: string[]|null, where: {property: string, values: string[]}|null} | {error: string}}
 */
function checkKinds(model, ev) {
  const w = checkWhere(model, ev.where);
  if ('error' in w) return w;
  const cl = checkClasses(ev.classes);
  if ('error' in cl) return cl;
  const kinds = ev.kinds;
  if (kinds === undefined) return { kinds: null, classes: cl.classes, where: w.where };
  if (!Array.isArray(kinds) || !kinds.every((k) => typeof k === 'string')) return { error: 'The "kinds" parameter is not a list of relationship kind names.' };
  if (!kinds.length) return { error: 'The "kinds" parameter lists no relationship kind, so nothing can be followed.' };
  const unknown = kinds.filter((k) => !Object.hasOwn(model.meta.relationshipKinds, k));
  if (unknown.length) return { error: `Unknown relationship kind${unknown.length === 1 ? '' : 's'} ${list(unknown.map((k) => `"${k}"`))}; a misspelt kind would make the check pass vacuously.` };
  return { kinds, classes: cl.classes, where: w.where };
}

/**
 * Validate the `classes` parameter: dependency classes (static, runtime, none) the followed relationships' kinds
 * must have. An unknown class is an error: a misspelt class would empty the graph and pass vacuously.
 * @param {any} classes
 * @returns {{classes: string[]|null} | {error: string}}
 */
function checkClasses(classes) {
  if (classes === undefined) return { classes: null };
  if (!Array.isArray(classes) || !classes.length || !classes.every((c) => typeof c === 'string')) return { error: 'The "classes" parameter is not a list of one or more dependency classes (static, runtime, none).' };
  const unknown = classes.filter((c) => !DEPENDENCY_CLASSES.includes(/** @type {any} */ (c)));
  if (unknown.length) return { error: `Unknown dependency class${unknown.length === 1 ? '' : 'es'} ${list(unknown.map((c) => `"${c}"`))}; the classes are ${DEPENDENCY_CLASSES.join(', ')}.` };
  return { classes };
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

/** @param {string[]|null} kinds @param {{property: string, values: string[]}|null} [where] @param {string[]|null} [classes] */
const kindsText = (kinds, where, classes) => (kinds ? `kinds ${kinds.join(', ')}` : 'all kinds') + (classes ? ` of class ${classes.join(' or ')}` : '') + (where ? ` with ${where.property} ${where.values.join(' or ')}` : '');

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
  if (ev.cut !== undefined && !('error' in k)) return atLevel(model, ev, k, levelNoRelationship);
  const from = select(model, ev.from);
  const to = select(model, ev.to);
  if ('error' in k) return inconclusive('Nothing was checked.', k.error, [...from, ...to]);
  if (!from.length || !to.length) return inconclusive('Nothing was checked: a selector selected no component.', `The "${from.length ? 'to' : 'from'}" selector selects no component, so "no relationship" would hold vacuously. It is not reported as verified.`, [...from, ...to]);
  // The scope counts every relationship of the filtered kinds, so the result reads all of them, not only those
  // between the selections.
  return withQuery(noRelationshipLeaf(model, ev, k, from, to), { kinds: k.kinds, classes: k.classes, where: k.where, from: null, to: null });
}

/**
 * A result with the relationship query footprint it read.
 * @param {Outcome} r @param {import('./footprints.js').RelationshipQuery} query
 */
function withQuery(r, query) {
  return /** @type {Outcome} */ ({ ...r, query });
}

/** @param {Model} model @param {any} ev @param {any} k @param {string[]} from @param {string[]} to @returns {Outcome} */
function noRelationshipLeaf(model, ev, k, from, to) {
  const g = componentGraph(model, { kinds: k.kinds, classes: k.classes, where: k.where });
  const toSet = new Set(to);
  const transitive = ev.transitive === true;
  const scope = `Checked the ${plural(edgeCount(g), 'relationship', 'relationships')} of ${kindsText(k.kinds, k.where, k.classes)} between ${plural(from.length, 'source component', 'source components')} and ${plural(to.length, 'target component', 'target components')}${transitive ? ', following multi-hop paths too,' : ' (direct relationships only)'} at this model revision.`;
  const selected = [...from, ...to];

  /** @type {{rel: string, from: string, to: string}[]} */
  const direct = [];
  for (const f of from) for (const e of g.get(f) ?? []) if (toSet.has(e.to)) direct.push({ rel: e.rel, from: f, to: e.to });
  if (direct.length) {
    const first = direct[0];
    return {
      outcome: 'fail', scope, selected,
      explanation: `Relationship "${first.rel}" leads from "${first.from}" to "${first.to}"${direct.length > 1 ? `, and ${direct.length - 1} more do` : ''}, although no relationship was to exist.`,
      counterexample: { summary: `${plural(direct.length, 'relationship', 'relationships')} from the source to the target set: ${direct.map((d) => d.rel).join(', ')}.`, entities: direct.map((d) => d.rel), path: [first.from, first.rel, first.to] },
    };
  }
  if (transitive) {
    for (const f of from) {
      const path = findPath(g, f, (id) => toSet.has(id));
      if (path) {
        return {
          outcome: 'fail', scope, selected,
          explanation: `A path of ${plural(pathRels(path).length, 'relationship', 'relationships')} leads from "${path[0]}" to "${path[path.length - 1]}": ${path.join(' -> ')}.`,
          counterexample: { summary: `Path ${path.join(' -> ')}.`, entities: pathRels(path), path },
        };
      }
    }
  }
  return { outcome: 'pass', scope, selected, explanation: `No ${transitive ? 'directed path' : 'relationship'} of ${kindsText(k.kinds, k.where, k.classes)} leads from any of the ${from.length} source components to any of the ${to.length} target components.` };
}

/** @param {Model} model @param {any} ev @returns {Outcome} */
function reachable(model, ev) {
  const k = checkKinds(model, ev);
  if (ev.cut !== undefined && !('error' in k)) return atLevel(model, ev, k, levelReachable);
  return withQuery(reachableLeaf(model, ev, k), { kinds: 'error' in k ? null : k.kinds, classes: 'error' in k ? null : k.classes, where: 'error' in k ? null : k.where, from: null, to: null });
}

/** @param {Model} model @param {any} ev @param {any} k @returns {Outcome} */
function reachableLeaf(model, ev, k) {
  const from = select(model, ev.from);
  const to = select(model, ev.to);
  if ('error' in k) return inconclusive('Nothing was checked.', k.error, [...from, ...to]);
  if (!from.length || !to.length) return inconclusive('Nothing was checked: a selector selected no component.', `The "${from.length ? 'to' : 'from'}" selector selects no component, so reachability cannot be decided. It is not reported as verified.`, [...from, ...to]);
  const g = componentGraph(model, { kinds: k.kinds, classes: k.classes, where: k.where });
  const toSet = new Set(to);
  const scope = `Checked directed reachability over the ${plural(edgeCount(g), 'relationship', 'relationships')} of ${kindsText(k.kinds, k.where, k.classes)} from ${plural(from.length, 'source component', 'source components')} to ${plural(to.length, 'target component', 'target components')} at this model revision.`;
  const selected = [...from, ...to];
  const unreachable = from.filter((f) => !findPath(g, f, (id) => toSet.has(id)));
  if (!unreachable.length) return { outcome: 'pass', scope, selected, explanation: `Each of the ${from.length} source components reaches a target component along at least one directed relationship (being a target itself does not count).` };
  return {
    outcome: 'fail', scope, selected,
    explanation: `${list(unreachable.map((c) => `"${c}"`))} ${unreachable.length === 1 ? 'does' : 'do'} not reach any target component along directed relationships of ${kindsText(k.kinds, k.where, k.classes)}.`,
    counterexample: { summary: `Unreachable source ${unreachable.length === 1 ? 'component' : 'components'}: ${unreachable.join(', ')}.`, entities: unreachable },
  };
}

/** @param {Model} model @param {any} ev @returns {Outcome} */
function onlyVia(model, ev) {
  const k = checkKinds(model, ev);
  if (ev.cut !== undefined && !('error' in k)) return atLevel(model, ev, k, levelOnlyVia);
  return withQuery(onlyViaLeaf(model, ev, k), { kinds: 'error' in k ? null : k.kinds, classes: 'error' in k ? null : k.classes, where: 'error' in k ? null : k.where, from: null, to: null });
}

/** @param {Model} model @param {any} ev @param {any} k @returns {Outcome} */
function onlyViaLeaf(model, ev, k) {
  const from = select(model, ev.from);
  const to = select(model, ev.to);
  const via = select(model, ev.via);
  if ('error' in k) return inconclusive('Nothing was checked.', k.error, [...from, ...to, ...via]);
  const empty = !from.length ? 'from' : !to.length ? 'to' : !via.length ? 'via' : null;
  if (empty) return inconclusive('Nothing was checked: a selector selected no component.', `The "${empty}" selector selects no component, so the check would be vacuous. It is not reported as verified.`, [...from, ...to, ...via]);
  const g = componentGraph(model, { kinds: k.kinds, classes: k.classes, where: k.where });
  const viaSet = new Set(via);
  const toSet = new Set(to);
  const scope = `Checked the ${plural(edgeCount(g), 'relationship', 'relationships')} of ${kindsText(k.kinds, k.where, k.classes)} for directed paths from ${plural(from.length, 'source component', 'source components')} to ${plural(to.length, 'target component', 'target components')} that avoid ${plural(via.length, 'via component', 'via components')} at this model revision.`;
  const selected = [...from, ...to, ...via];
  // A source that is itself a via component starts its paths on the via component: that passes by
  // construction. Only the other sources can show anything, and only if a path exists at all.
  const open = from.filter((f) => !viaSet.has(f));
  if (!open.length) {
    return inconclusive(scope, 'Every source component is also a via component, so every path from them passes through a via component by construction. That shows nothing about the model, and the claim is not reported as verified.', selected);
  }
  if (!open.some((f) => findPath(g, f, (id) => toSet.has(id)))) {
    return inconclusive(scope, `No directed path of ${kindsText(k.kinds, null, k.classes)} leads from the source components to any target component, so "every path passes through a via component" holds vacuously. The claim is not reported as verified.`, selected);
  }
  for (const f of from) {
    if (viaSet.has(f)) continue;
    const path = findPath(g, f, (id) => toSet.has(id), (id) => viaSet.has(id));
    if (path) {
      return {
        outcome: 'fail', scope, selected,
        explanation: `A path reaches "${path[path.length - 1]}" from "${path[0]}" without passing through any via component: ${path.join(' -> ')}.`,
        counterexample: { summary: `Bypassing path ${path.join(' -> ')}.`, entities: pathRels(path), path },
      };
    }
  }
  return { outcome: 'pass', scope, selected, explanation: `With the ${via.length} via components removed, no source component reaches a target component, so every path from source to target passes through a via component.` };
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
  if (!lacking.length) return { outcome: 'pass', scope, selected: sel, explanation: `Each of the ${sel.length} selected components declares ${what}.` };
  return {
    outcome: 'fail', scope, selected: sel,
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
  if (!missing.length) return { outcome: 'pass', scope, selected, explanation: `Each of the ${comps.length} selected components has a non-empty "${prop}".` };
  return {
    outcome: 'fail', scope, selected,
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
      outcome: 'fail', scope, selected,
      explanation: `${done} of ${comps.length} implemented components are ${lang}; ${other.length} are not yet (${parts.join('; ')})${unknown.length ? `, and ${unknown.length} record no language (${unknown.join(', ')})` : ''}.${plan}`,
      counterexample: { summary: `Not yet ${lang}: ${other.map((c) => c.id).join(', ')}.`, entities: other.map((c) => c.id) },
    };
  }
  if (unknown.length) return inconclusive(scope, `${unknown.length} selected components record no implementation.language: ${unknown.join(', ')}.`, selected);
  return { outcome: 'pass', scope, selected, explanation: `All ${comps.length} selected implemented components are ${lang}.` };
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
  const query = { kinds: k.kinds, classes: k.classes, dependencyOnly: !(k.kinds || k.classes), where: k.where, from: null, to: null };
  if (ev.cut !== undefined) return withQuery(atLevel(model, ev, k, levelAcyclic), query);
  return withQuery(acyclicLeaf(model, ev, k), query);
}

/** @param {Model} model @param {any} ev @param {any} k @returns {Outcome} */
function acyclicLeaf(model, ev, k) {
  const full = componentGraph(model, k.kinds || k.classes ? { kinds: k.kinds, classes: k.classes, where: k.where } : { dependencyOnly: true, where: k.where });
  const depKinds = Object.entries(model.meta.relationshipKinds).filter(([, v]) => /** @type {any} */ (v).dependency).map(([id]) => id);
  const kindsDesc = k.kinds || k.classes ? kindsText(k.kinds, k.where, k.classes) : `dependency kinds (${depKinds.join(', ')})`;
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
  if (!cycle) return { outcome: 'pass', scope, selected, explanation: `The directed graph of ${kindsDesc} has no cycle.` };
  return {
    outcome: 'fail', scope, selected,
    explanation: `The relationships ${list(pathRels(cycle).map((r) => `"${r}"`))} form a directed cycle: ${cycle.join(' -> ')}.`,
    counterexample: { summary: `Cycle ${cycle.join(' -> ')}.`, entities: unique(cycle), path: cycle },
  };
}

// ---------------------------------------------------------------------------
// Claims stated at a cut (WG-5694; docs/assessment/2026-11-27/multiscale.md, section 3.3)
//
// A graph claim with `cut` is evaluated on the derived model of that cut (src/core/abstraction.js): its selectors
// pick blocks, its graph is the lifted interactions, and its verdict reaches the base only through the transfer
// rules. Absence transfers exactly (no derived interaction, no path: none between any members either). Presence
// transfers upward (a derived interaction is witnessed by relationships between members). A coarse path is a
// may-path: it is reported as a base fact only when a chain of relationships between members witnesses it, and
// otherwise the claim is inconclusive. Acyclicity is a statement about blocks: a cycle of blocks is a violation at
// that level even when no base cycle exists. A claim that names an element hidden inside a block of its cut, or
// selects only part of a block, is not expressible at that level.

/** @typedef {NonNullable<ReturnType<typeof deriveModel>>} DerivedModel */

/**
 * Evaluate a graph claim at the cut it states.
 * @param {Model} model @param {any} ev @param {any} k
 * @param {(model: Model, ev: any, k: any, d: DerivedModel) => any} fn
 * @returns {Outcome}
 */
function atLevel(model, ev, k, fn) {
  // A declared cut by id, or (EvalOptions.atCut) the blocks of an interactive cut of a hierarchy.
  const adHoc = ev.cut && typeof ev.cut === 'object' && typeof ev.cut.hierarchy === 'string' && Array.isArray(ev.cut.blocks) ? ev.cut : null;
  if (typeof ev.cut !== 'string' && !adHoc) return inconclusive('Nothing was checked.', 'The "cut" parameter must name one declared cut.');
  const d = deriveModel(model, adHoc ? { hierarchy: adHoc.hierarchy, blocks: adHoc.blocks } : ev.cut);
  if (!d) return inconclusive('Nothing was checked.', adHoc ? `"${adHoc.hierarchy}" is not a known hierarchy.` : `"${ev.cut}" is not a declared cut of a known hierarchy.`);
  const name = adHoc ? `the cut of ${adHoc.hierarchy} with ${adHoc.blocks.length} blocks` : `cut "${ev.cut}"`;
  const level = adHoc ? { hierarchy: d.hierarchy, cut: null, blocks: [...d.level.blocks] } : { hierarchy: d.hierarchy, cut: ev.cut };
  const invalid = d.diagnostics.filter((x) => x.condition === 'V1' && x.severity === 'error');
  if (invalid.length) {
    return /** @type {Outcome} */ ({ ...inconclusive(`Nothing was checked at ${name}.`, `The cut is not a valid abstraction (V1): ${invalid.slice(0, 3).map((x) => x.message).join(' ')}`), level });
  }
  return { ...fn(model, ev, k, d), level };
}

/** @type {WeakMap<object, Map<string, string[]>>} */
const blockMembers = new WeakMap();
/** The components each block of a derived model holds. @param {Model} model @param {DerivedModel} d */
function membersOfBlocks(model, d) {
  let m = blockMembers.get(d);
  if (!m) {
    m = new Map();
    for (const c of model.byKind.component ?? []) {
      const b = blockAt(d.level, c.id);
      if (b === null) continue;
      if (!m.has(b)) m.set(b, []);
      /** @type {string[]} */ (m.get(b)).push(c.id);
    }
    blockMembers.set(d, m);
  }
  return m;
}

/**
 * What a selector picks at a cut: blocks, and the components they hold. A problem when the selector names an
 * element strictly inside a block, or picks some but not all of the components a block holds.
 * @param {Model} model @param {DerivedModel} d @param {any} selector @param {string} name
 * @returns {{blocks: string[], members: string[]} | {problem: string}}
 */
function selectAt(model, d, selector, name) {
  for (const n of selectorNames(selector)) {
    if (!d.level.h.depth.has(n)) continue;
    const b = blockAt(d.level, n);
    if (b !== null && b !== n) return { problem: `the "${name}" selector names "${n}", which is hidden inside block "${b}" at ${cutName(d)}` };
  }
  const members = select(model, selector);
  const set = new Set(members);
  /** @type {Set<string>} */
  const blocks = new Set();
  for (const c of members) { const b = blockAt(d.level, c); if (b !== null) blocks.add(b); }
  const held = membersOfBlocks(model, d);
  for (const b of blocks) {
    const missing = (held.get(b) ?? []).filter((c) => !set.has(c));
    if (missing.length) return { problem: `the "${name}" selector picks only part of block "${b}" at ${cutName(d)} (${missing.slice(0, 3).map((c) => `"${c}"`).join(', ')}${missing.length > 3 ? ', ...' : ''} ${missing.length === 1 ? 'lies' : 'lie'} in it unselected)` };
  }
  return { blocks: [...blocks].sort(), members };
}

/** How a derived model's cut is named in a result: its id, or the size of an interactive cut. @param {DerivedModel} d */
function cutName(d) {
  return d.cut ? `cut "${d.cut}"` : `the current cut (${d.level.blocks.length} blocks of hierarchy ${d.hierarchy})`;
}

/**
 * The outcome of a claim that cannot be stated at its cut.
 * @param {DerivedModel} d @param {string} problem @param {string[]} selected @returns {Outcome}
 */
function notExpressible(d, problem, selected) {
  const message = `Not expressible at this level: ${problem}.`;
  return /** @type {Outcome} */ ({
    outcome: 'undecided', scope: `Nothing was checked at ${cutName(d)}.`, selected,
    explanation: `${message} A claim stated at a cut speaks of that cut's blocks; it is not quietly re-scoped to the elements inside them.`,
    diagnostics: [{ code: 'claim.not-expressible', severity: 'warning', message }],
  });
}

/**
 * The block graph of a derived model for a claim's kind filter: one edge per derived interaction that keeps at
 * least one witness, named by its first witness and carrying all of them.
 * @param {Model} model @param {DerivedModel} d @param {any} k @param {boolean} dependencyOnly
 * @returns {Map<string, {to: string, rel: string, witnesses: string[]}[]>}
 */
function blockGraph(model, d, k, dependencyOnly) {
  const keep = (/** @type {import('./abstraction.js').BaseFact} */ f) =>
    (!k.kinds || k.kinds.includes(f.kind)) &&
    (!k.classes || k.classes.includes(kindInfo(model.meta, f.kind).class)) &&
    (!dependencyOnly || !!(/** @type {any} */ (own(model.meta.relationshipKinds, f.kind)))?.dependency) &&
    (!k.where || k.where.values.includes(model.entities.get(f.id)?.data[k.where.property]));
  /** @type {Map<string, {to: string, rel: string, witnesses: string[]}[]>} */
  const g = new Map(d.blocks.map((b) => [b.id, []]));
  for (const i of d.interactions) {
    const r = restrictInteraction(model, i, keep);
    if (r) /** @type {any[]} */ (g.get(i.from)).push({ to: i.to, rel: r.witnesses[0], witnesses: r.witnesses });
  }
  return g;
}

/** The witnesses of the hops of a block path. @param {Map<string, {to: string, rel: string, witnesses: string[]}[]>} g @param {string[]} path */
function pathWitnesses(g, path) {
  /** @type {string[]} */
  const out = [];
  for (let i = 0; i + 2 < path.length; i += 2) {
    const e = (g.get(path[i]) ?? []).find((x) => x.to === path[i + 2] && x.rel === path[i + 1]);
    if (e) out.push(...e.witnesses);
  }
  return unique(out);
}

/**
 * A chain of relationships between members that witnesses a coarse path: from any of `from` to any of `to`,
 * avoiding `blocked` components. Null when there is none.
 * @param {Model} model @param {any} k @param {boolean} dependencyOnly @param {string[]} from @param {string[]} to @param {Set<string>} [blocked]
 */
function memberPath(model, k, dependencyOnly, from, to, blocked) {
  const g = componentGraph(model, dependencyOnly ? { dependencyOnly: true, where: k.where } : { kinds: k.kinds, classes: k.classes, where: k.where });
  const targets = new Set(to);
  for (const f of from) {
    if (blocked?.has(f)) continue;
    const p = findPath(g, f, (id) => targets.has(id), blocked ? (id) => blocked.has(id) : undefined);
    if (p) return p;
  }
  return null;
}

/** @param {any} d @param {any} k @param {Map<string, any[]>} g the block graph after the kind filter */
const levelText = (d, k, g) => `the ${plural(edgeCount(g), 'derived interaction', 'derived interactions')} of ${cutName(d)} (${plural(d.blocks.length, 'block', 'blocks')}, hierarchy ${d.hierarchy}) of ${kindsText(k.kinds, k.where, k.classes)}`;

/** @param {Model} model @param {any} ev @param {any} k @param {DerivedModel} d */
function levelNoRelationship(model, ev, k, d) {
  const F = selectAt(model, d, ev.from, 'from');
  const T = selectAt(model, d, ev.to, 'to');
  const named = [...selectorNames(ev.from), ...selectorNames(ev.to)].filter((x) => model.entities.has(x));
  if ('problem' in F) return notExpressible(d, F.problem, named);
  if ('problem' in T) return notExpressible(d, T.problem, named);
  const selected = unique([...F.members, ...T.members]);
  const query = { kinds: k.kinds, classes: k.classes, where: k.where, from: null, to: null };
  if (!F.blocks.length || !T.blocks.length) return { ...inconclusive('Nothing was checked: a selector selected no block.', `The "${F.blocks.length ? 'to' : 'from'}" selector selects nothing at ${cutName(d)}, so "no relationship" would hold vacuously. It is not reported as verified.`, selected), query };
  const shared = F.blocks.filter((b) => T.blocks.includes(b));
  if (shared.length) return { ...inconclusive(`Nothing was checked at ${cutName(d)}.`, `The source and target selections share ${list(shared.map((b) => `"${b}"`))}; relationships inside a block are internal at this level, so the claim cannot be decided there.`, selected), query };
  const g = blockGraph(model, d, k, false);
  const toSet = new Set(T.blocks);
  const transitive = ev.transitive === true;
  const scope = `Checked ${levelText(d, k, g)}, from ${plural(F.blocks.length, 'source block', 'source blocks')} (${F.members.length} components) to ${plural(T.blocks.length, 'target block', 'target blocks')} (${T.members.length} components)${transitive ? ', following multi-hop paths too' : ' (direct interactions only)'}, at this model revision.`;
  /** @type {{from: string, to: string, rel: string, witnesses: string[]}[]} */
  const direct = [];
  for (const f of F.blocks) for (const e of g.get(f) ?? []) if (toSet.has(e.to)) direct.push({ from: f, ...e });
  if (direct.length) {
    const first = direct[0];
    const ws = unique(direct.flatMap((x) => x.witnesses));
    return {
      outcome: 'fail', scope, selected, query,
      explanation: `The derived interaction "${first.from}" -> "${first.to}" exists at ${cutName(d)}${direct.length > 1 ? `, and ${direct.length - 1} more do` : ''}; presence transfers to the base: ${plural(ws.length, 'relationship', 'relationships')} between their members witness ${direct.length > 1 ? 'them' : 'it'} (${ws.slice(0, 5).join(', ')}${ws.length > 5 ? ', ...' : ''}).`,
      counterexample: { summary: `Derived interactions from the source to the target blocks, witnessed by ${ws.join(', ')}.`, entities: ws, path: [first.from, first.rel, first.to] },
    };
  }
  if (transitive) {
    for (const f of F.blocks) {
      const path = findPath(g, f, (id) => toSet.has(id));
      if (!path) continue;
      const base = memberPath(model, k, false, F.members, T.members);
      if (base) {
        return {
          outcome: 'fail', scope, selected, query,
          explanation: `A path of derived interactions leads from "${path[0]}" to "${path[path.length - 1]}" at ${cutName(d)} (${path.join(' -> ')}), and a chain of relationships between members witnesses it: ${base.join(' -> ')}.`,
          counterexample: { summary: `Path ${base.join(' -> ')}.`, entities: pathRels(base), path: base },
        };
      }
      return {
        outcome: 'undecided', scope, selected, query,
        explanation: `A path of derived interactions leads from "${path[0]}" to "${path[path.length - 1]}" at ${cutName(d)} (${path.join(' -> ')}), but no chain of relationships between members witnesses it: a coarse path is a may-path (it can join a relationship into a block with another out of it that no path inside the block connects), so neither absence nor presence of a path is established.`,
        counterexample: { summary: `May-path ${path.join(' -> ')}.`, entities: pathWitnesses(g, path), path },
      };
    }
  }
  return {
    outcome: 'pass', scope, selected, query,
    explanation: `No ${transitive ? 'path of derived interactions' : 'derived interaction'} of ${kindsText(k.kinds, k.where, k.classes)} leads from the ${plural(F.blocks.length, 'source block', 'source blocks')} to the ${plural(T.blocks.length, 'target block', 'target blocks')} at ${cutName(d)}. Absence transfers exactly: no ${transitive ? 'chain of relationships' : 'relationship'} leads from any of the ${F.members.length} source components to any of the ${T.members.length} target components.`,
  };
}

/** @param {Model} model @param {any} ev @param {any} k @param {DerivedModel} d */
function levelReachable(model, ev, k, d) {
  const F = selectAt(model, d, ev.from, 'from');
  const T = selectAt(model, d, ev.to, 'to');
  const named = [...selectorNames(ev.from), ...selectorNames(ev.to)].filter((x) => model.entities.has(x));
  if ('problem' in F) return notExpressible(d, F.problem, named);
  if ('problem' in T) return notExpressible(d, T.problem, named);
  const selected = unique([...F.members, ...T.members]);
  const query = { kinds: k.kinds, classes: k.classes, where: k.where, from: null, to: null };
  if (!F.blocks.length || !T.blocks.length) return { ...inconclusive('Nothing was checked: a selector selected no block.', `The "${F.blocks.length ? 'to' : 'from'}" selector selects nothing at ${cutName(d)}, so reachability cannot be decided. It is not reported as verified.`, selected), query };
  const g = blockGraph(model, d, k, false);
  const toSet = new Set(T.blocks);
  const held = membersOfBlocks(model, d);
  const scope = `Checked directed reachability over ${levelText(d, k, g)}, from ${plural(F.blocks.length, 'source block', 'source blocks')} to ${plural(T.blocks.length, 'target block', 'target blocks')}, with each coarse path checked for a witnessing chain of relationships between members, at this model revision.`;
  /** @type {string[]} */
  const unreachable = [];
  /** @type {{block: string, path: string[]}[]} */
  const may = [];
  for (const f of F.blocks) {
    const path = findPath(g, f, (id) => toSet.has(id));
    if (!path) { unreachable.push(f); continue; }
    if (!memberPath(model, k, false, held.get(f) ?? [f], T.members)) may.push({ block: f, path });
  }
  if (unreachable.length) {
    return {
      outcome: 'fail', scope, selected, query,
      explanation: `${list(unreachable.map((b) => `"${b}"`))} ${unreachable.length === 1 ? 'reaches' : 'reach'} no target block along derived interactions at ${cutName(d)}; absence transfers exactly, so none of ${unreachable.length === 1 ? 'its' : 'their'} members reaches a target component either.`,
      counterexample: { summary: `Unreachable source ${unreachable.length === 1 ? 'block' : 'blocks'}: ${unreachable.join(', ')}.`, entities: unreachable },
    };
  }
  if (may.length) {
    const m = may[0];
    return {
      outcome: 'undecided', scope, selected, query,
      explanation: `May-reachable only: "${m.block}" reaches a target block along derived interactions at ${cutName(d)} (${m.path.join(' -> ')}), but no chain of relationships from its members to a target component witnesses that path. A coarse path can be spurious (a relationship into a block and another out of it that nothing inside the block connects), so reachability is not established.`,
      counterexample: { summary: `Spurious or unwitnessed coarse path ${m.path.join(' -> ')}.`, entities: pathWitnesses(g, m.path), path: m.path },
    };
  }
  return { outcome: 'pass', scope, selected, query, explanation: `Each of the ${plural(F.blocks.length, 'source block', 'source blocks')} reaches a target block along derived interactions at ${cutName(d)}, and each such path is witnessed by a chain of relationships from one of its members to a target component (path-witnessed, so it is a must-path).` };
}

/** @param {Model} model @param {any} ev @param {any} k @param {DerivedModel} d */
function levelOnlyVia(model, ev, k, d) {
  const F = selectAt(model, d, ev.from, 'from');
  const T = selectAt(model, d, ev.to, 'to');
  const V = selectAt(model, d, ev.via, 'via');
  const named = [...selectorNames(ev.from), ...selectorNames(ev.to), ...selectorNames(ev.via)].filter((x) => model.entities.has(x));
  for (const x of [F, T, V]) if ('problem' in x) return notExpressible(d, x.problem, named);
  const f = /** @type {{blocks: string[], members: string[]}} */ (F), t = /** @type {{blocks: string[], members: string[]}} */ (T), v = /** @type {{blocks: string[], members: string[]}} */ (V);
  const selected = unique([...f.members, ...t.members, ...v.members]);
  const query = { kinds: k.kinds, classes: k.classes, where: k.where, from: null, to: null };
  const empty = !f.blocks.length ? 'from' : !t.blocks.length ? 'to' : !v.blocks.length ? 'via' : null;
  if (empty) return { ...inconclusive('Nothing was checked: a selector selected no block.', `The "${empty}" selector selects nothing at ${cutName(d)}, so the check would be vacuous. It is not reported as verified.`, selected), query };
  const g = blockGraph(model, d, k, false);
  const viaSet = new Set(v.blocks), toSet = new Set(t.blocks);
  const scope = `Checked ${levelText(d, k, g)} for paths from ${plural(f.blocks.length, 'source block', 'source blocks')} to ${plural(t.blocks.length, 'target block', 'target blocks')} that avoid ${plural(v.blocks.length, 'via block', 'via blocks')}, at this model revision.`;
  const open = f.blocks.filter((b) => !viaSet.has(b));
  if (!open.length) return { ...inconclusive(scope, 'Every source block is also a via block, so every path from them passes through a via block by construction. That shows nothing, and the claim is not reported as verified.', selected), query };
  if (!open.some((b) => findPath(g, b, (id) => toSet.has(id)))) return { ...inconclusive(scope, `No path of derived interactions leads from the source blocks to a target block at ${cutName(d)}, so "every path passes through a via block" holds vacuously. The claim is not reported as verified.`, selected), query };
  for (const b of open) {
    const path = findPath(g, b, (id) => toSet.has(id), (id) => viaSet.has(id));
    if (!path) continue;
    const base = memberPath(model, k, false, f.members, t.members, new Set(v.members));
    if (base) {
      return {
        outcome: 'fail', scope, selected, query,
        explanation: `A path of derived interactions bypasses every via block at ${cutName(d)} (${path.join(' -> ')}), and a chain of relationships between members witnesses the bypass: ${base.join(' -> ')}.`,
        counterexample: { summary: `Bypassing path ${base.join(' -> ')}.`, entities: pathRels(base), path: base },
      };
    }
    return {
      outcome: 'undecided', scope, selected, query,
      explanation: `A path of derived interactions bypasses every via block at ${cutName(d)} (${path.join(' -> ')}), but no chain of relationships between members witnesses it; the coarse bypass may be spurious, so the claim is neither established nor refuted at this level.`,
      counterexample: { summary: `May-bypass ${path.join(' -> ')}.`, entities: pathWitnesses(g, path), path },
    };
  }
  return { outcome: 'pass', scope, selected, query, explanation: `With the ${plural(v.blocks.length, 'via block', 'via blocks')} removed, no source block reaches a target block at ${cutName(d)}; absence transfers, so every chain of relationships from a source component to a target component passes through a component of a via block.` };
}

/** @param {Model} model @param {any} ev @param {any} k @param {DerivedModel} d */
function levelAcyclic(model, ev, k, d) {
  const dependencyOnly = !(k.kinds || k.classes);
  const full = blockGraph(model, d, k, dependencyOnly);
  const depKinds = Object.entries(model.meta.relationshipKinds).filter(([, x]) => /** @type {any} */ (x).dependency).map(([id]) => id);
  const kindsDesc = dependencyOnly ? `dependency kinds (${depKinds.join(', ')})` : kindsText(k.kinds, k.where, k.classes);
  /** @type {string[]} */
  let selected = [];
  let g = full;
  let within = '';
  if (ev.within !== undefined) {
    const W = selectAt(model, d, ev.within, 'within');
    if ('problem' in W) return notExpressible(d, W.problem, selectorNames(ev.within).filter((x) => model.entities.has(x)));
    selected = W.members;
    if (!W.blocks.length) return inconclusive('Nothing was checked: the "within" selector selected no block.', `The "within" selector selects nothing at ${cutName(d)}, so there is no graph to check. It is not reported as verified.`);
    const set = new Set(W.blocks);
    g = new Map([...full].filter(([id]) => set.has(id)).map(([id, es]) => [id, es.filter((e) => set.has(e.to))]));
    within = ` restricted to ${plural(W.blocks.length, 'block', 'blocks')}`;
  }
  const n = edgeCount(g);
  const scope = `Checked the ${plural(n, 'derived interaction', 'derived interactions')} of ${kindsDesc} at ${cutName(d)} (${plural(d.blocks.length, 'block', 'blocks')}, hierarchy ${d.hierarchy})${within} for directed cycles of blocks, at this model revision.`;
  if (n === 0) return inconclusive(scope, `No derived interaction of ${kindsDesc} exists at ${cutName(d)}${within ? ' within the selected blocks' : ''}, so there was nothing to check. It is not reported as verified.`, selected);
  const cycle = findCycle(g);
  if (!cycle) return { outcome: 'pass', scope, selected, explanation: `The blocks of ${cutName(d)} form no directed cycle under ${kindsDesc}: a layering statement about blocks, so every cycle among the base relationships lies inside a single block.` };
  const ws = pathWitnesses(g, cycle);
  const blocks = unique(cycle.filter((_, i) => i % 2 === 0));
  return {
    outcome: 'fail', scope, selected,
    explanation: `The blocks ${list(blocks.map((b) => `"${b}"`))} form a directed cycle at ${cutName(d)}: ${cycle.join(' -> ')}. Acyclicity at a level is a statement about blocks, so this is a violation at this level whether or not any single chain of relationships between members closes a cycle; the cycle is witnessed by ${ws.join(', ')}.`,
    counterexample: { summary: `Cycle of blocks ${cycle.join(' -> ')}, witnessed by ${ws.join(', ')}.`, entities: unique([...blocks.filter((b) => model.entities.has(b)), ...ws]), path: cycle },
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
    return { outcome: 'undecided', evaluator: REFINEMENT, scope: 'Nothing was checked: the claim names no behavior.', explanation: `"behavior" must name one implementation behavior; ${id ? `"${id}" is not a behavior` : 'it names none or several'}.`, selected: [] };
  }
  const ref = refinementOf(model, impl);
  if (!ref) {
    return { outcome: 'undecided', evaluator: REFINEMENT, scope: 'Nothing was checked: the behavior declares no refinement.', explanation: `Behavior "${impl.id}" does not declare "refines" naming a behavior together with a "refinement" mapping.`, selected: [impl.id] };
  }
  const A = ref.model;
  const listed = typeof ev.scenarios === 'string' ? [ev.scenarios] : Array.isArray(ev.scenarios) ? ev.scenarios : null;
  const scenarios = listed
    ? listed.map((/** @type {string} */ s) => model.entities.get(s)).filter((/** @type {any} */ s) => s && s.kind === 'scenario')
    : (model.byKind.scenario ?? []).filter((s) => Array.isArray(s.data.behaviors) && s.data.behaviors.includes(impl.id));
  const selected = unique([impl.id, A.id, ...scenarios.map((/** @type {Entity} */ s) => s.id)]);
  const what = `every step of "${impl.id}" against "${A.id}" through its refinement mapping`;
  if (!scenarios.length) {
    return { outcome: 'undecided', evaluator: REFINEMENT, scope: `Nothing was checked: ${listed ? 'no listed scenario exists' : `no scenario runs "${impl.id}"`}.`, explanation: 'There is no trace of the implementation behavior to check, so the refinement is not established.', selected };
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
        outcome: 'fail', evaluator: REFINEMENT, scope, selected: unique([...selected, ...f.entities]),
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
  if (reasons.length) return { outcome: 'undecided', evaluator: REFINEMENT, scope, selected, explanation: reasons.join(' ') };
  if (!moving) {
    return { outcome: 'undecided', evaluator: REFINEMENT, scope, selected, explanation: checked ? `Every one of the ${plural(checked, 'step', 'steps')} of "${impl.id}" is a stutter, so no step of the model was matched. It is not reported as verified.` : `"${impl.id}" fired no transition in any trace, so only initial configurations were compared. It is not reported as verified.` };
  }
  return {
    outcome: 'pass', evaluator: REFINEMENT, scope, selected,
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
  if (!ids.length) return { outcome: 'undecided', evaluator: TRACE, scope: 'Nothing was checked: the claim lists no scenario.', explanation: 'No scenario is listed, so there is no trace to check.', selected };

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
    return { outcome: 'fail', evaluator: TRACE, scope, selected: unique([...selected, ...counter.entities]), counterexample: counter, explanation: `${counter.summary} (scenario "${counter.scenario}"${counter.stepIndex !== undefined ? `, ${counter.stepIndex < 0 ? 'initial configuration' : `step ${counter.stepIndex}`}` : ''}).` };
  }
  if (reasons.length) return { outcome: 'undecided', evaluator: TRACE, scope, selected, explanation: reasons.join(' ') };
  if (ev.method === 'precedes' && !exercised) {
    const why = vacuousWhy.length ? `The ordering was never witnessed by the system: ${vacuousWhy.join('; ')}.` : 'The "then" occurrence never happens in any listed trace, so the ordering was never exercised and the check is vacuous.';
    return { outcome: 'undecided', evaluator: TRACE, scope, selected, explanation: `${why} It is not reported as verified.` };
  }
  if (ev.method === 'state-invariant') {
    if (!totalSteps) {
      return { outcome: 'undecided', evaluator: TRACE, scope, selected, explanation: 'Every listed trace has zero steps, so the invariant was only looked at in initial configurations and nothing was exercised. It is not reported as verified.' };
    }
    const ante = antecedentText(ev.expr);
    if (ante !== null && !exercised) {
      const why = vacuousWhy.length ? `The antecedent \`${ante}\` was true, but ${vacuousWhy.join('; ')}, so the implication was never exercised and the check is vacuous.` : `The antecedent \`${ante}\` was never true in any configuration reached by a step of any listed trace, so the implication was never exercised and the check is vacuous.`;
      return { outcome: 'undecided', evaluator: TRACE, scope, selected, explanation: `${why} It is not reported as verified.` };
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
    return { outcome: 'undecided', evaluator: TRACE, scope, selected, negatives: [], explanation: `${holdsText}, but the claim declares no negative, so nothing shows this check can fail. A trace claim is verified only when one of its scenarios, run with a fault that removes the protection, violates it (evaluate.negatives).` };
  }
  const failedNeg = neg.runs.filter((n) => !n.violated);
  if (failedNeg.length) {
    return { outcome: 'undecided', evaluator: TRACE, scope, selected, negatives: neg.runs, explanation: `${holdsText}, but ${failedNeg.map((n) => `the negative "${n.scenario}" with ${n.faults.join(', ')} did not violate it (${n.explanation})`).join('; and ')}. A check its negatives cannot break is not told apart from one that always passes.` };
  }
  const negText = ` Each of its ${plural(neg.runs.length, 'negative', 'negatives')} violated it: ${neg.runs.map((n) => `"${n.scenario}" with ${n.faults.join(', ')}${n.stepIndex !== undefined ? ` at step ${n.stepIndex}` : ''}`).join('; ')}.`;
  const what = {
    'state-invariant': `The expression held in the initial configuration and after every step of`,
    precedes: 'Every occurrence of the "then" matcher had an earlier occurrence of the "first" matcher in',
    eventually: 'The expected occurrence or final state was observed in',
    never: 'The forbidden occurrence did not happen in',
  }[/** @type {'state-invariant'} */ (ev.method)];
  return { outcome: 'pass', evaluator: TRACE, scope, selected, negatives: neg.runs, explanation: `${what} each of the ${plural(ran.length, 'trace', 'traces')} of ${list(ran.map((t) => `"${t.id}"`))}.${notes.length ? ` ${notes.join(' ')}` : ''}${negText} Other executions, faults or inputs were not examined.` };
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
