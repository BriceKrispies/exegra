// The verdict boundary: claim statuses are decided in Lean (formal/Exegra/Verdict.lean), never here.
//
// The shell produces facts (a test result, a model check, a Lean theorem check, a document) in the schema
// Exegra.Verdict.Fact defines, encodes each claim as Exegra.Verdict.Claim (an atomic part, or a conjunction of
// parts), and sends them to the registered Lean function `claims.status`. What comes back is the status tuple
// (strength, subject, open assumptions, freshness), whether it is shown established, and the word it is shown
// with. Regressions are decided by `verdict.isRegression`. This module only transports.

import { call } from './lean.js';

/**
 * @typedef {'test'|'boundedExploration'|'leanTheorem'|'document'|'modelCheck'|'traceCheck'|'statistical'|'externalTool'|'importScan'} FactKind
 * @typedef {'model'|'implementation'|'reality'} Subject
 * @typedef {'pass'|'fail'|'not-run'|'undecided'} FactOutcome
 * @typedef {{kind: FactKind, subject: Subject, target: {part: string}|{assumption: string},
 *   stamps: {recorded: string|null, current: string|null}, outcome?: FactOutcome, check?: any, about?: string[]}} Fact
 *   a leanTheorem fact may carry the recorded check and the claim's `about` instead of `outcome`: Lean decides it
 * @typedef {{part: string, subject: Subject, assumptions: string[]} | {all: VerdictClaim[]}} VerdictClaim
 * @typedef {'refuted'|'undecided'|'asserted'|'checkedOnInstances'|'exploredToBound'|'proved'} Strength
 * @typedef {{strength: Strength, subject: Subject, openAssumptions: string[], freshness: 'fresh'|'stale'|'unverifiable'}} Status
 * @typedef {Status & {established: boolean, label: string, refused: {index: number, error: string}[],
 *   theorems: {index: number, outcome: FactOutcome, reason: string, detail: string}[],
 *   factFreshness: (string|null)[]}} Verdict
 */

/**
 * Decide the status of each claim from its facts, in Lean.
 * @param {{claim: VerdictClaim, facts: Fact[]}[]} items
 * @returns {Verdict[]}
 */
export function decideStatuses(items) {
  if (!items.length) return [];
  const r = call('claims.status', { claims: items });
  if (!r.ok) throw new Error(`The Lean verdict could not be computed: ${r.error}`);
  return r.value;
}

/**
 * Whether each move from an old status to a new one (null: the claim was removed) is a regression, decided by
 * Exegra.Verdict.isRegression.
 * @param {{old: Status, new: Status|null}[]} pairs
 * @returns {boolean[]}
 */
export function isRegression(pairs) {
  if (!pairs.length) return [];
  const r = call('verdict.isRegression', { pairs });
  if (!r.ok) throw new Error(`The Lean regression check could not be computed: ${r.error}`);
  return r.value;
}

/**
 * Check facts against the Lean schema: each is `{ok: true}` or `{error}` (the reason it is refused).
 * @param {any[]} facts
 * @returns {({ok: true}|{error: string})[]}
 */
export function decodeFacts(facts) {
  if (!facts.length) return [];
  const r = call('facts.decode', { facts });
  if (!r.ok) throw new Error(`The Lean fact schema could not be checked: ${r.error}`);
  return r.value;
}

/** The status part of a verdict, as stored in baselines and compared for regressions. @param {Status} v @returns {Status} */
export function statusOf(v) {
  return { strength: v.strength, subject: v.subject, openAssumptions: [...v.openAssumptions], freshness: v.freshness };
}
