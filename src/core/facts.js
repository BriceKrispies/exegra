// Fact constructors: the one place that writes facts in the schema formal/Exegra/Verdict.lean defines
// (Exegra.Verdict.Fact: kind, subject, target, stamps, outcome). The trusted fact producers use these: the
// test-runner adapters (cli/outcomes.js, tools/realisation-roots.js through verify's recorded results), the tree
// stamp (tools/tree-stamp.js), the Lean theorem checker (tools/lean-theorems.js), the import scan
// (tools/import-scan.js), and the claim evaluator for the checks it runs over the model. Lean decodes every fact
// and refuses one that does not meet the schema (facts.decode, and claims.status per claim).

/** @typedef {import('./verdict.js').Fact} Fact */
/** @typedef {import('./verdict.js').Subject} Subject */
/** @typedef {{recorded: string|null, current: string|null}} FactStamps */

/**
 * The stamps of a fact: the stamp it was recorded on, and the current one (null where none can be computed).
 * @param {string|null|undefined} recorded @param {string|null|undefined} current
 * @returns {FactStamps}
 */
export function stampsOf(recorded, current) {
  return { recorded: typeof recorded === 'string' ? recorded : null, current: typeof current === 'string' ? current : null };
}

/**
 * The fact a test reference's recorded outcome makes about a part of a claim.
 * @param {string} part @param {'pass'|'fail'|'not-run'} outcome @param {FactStamps} stamps
 * @returns {Fact}
 */
export function testFact(part, outcome, stamps) {
  return { kind: 'test', subject: 'implementation', target: { part }, stamps, outcome };
}

/**
 * The fact an author-entered item (a document, a review) makes: asserted, never more; `supports: false` makes it a
 * contradiction.
 * @param {string} part @param {Subject} subject @param {boolean} supports @param {FactStamps} stamps
 * @returns {Fact}
 */
export function documentFact(part, subject, supports, stamps) {
  return { kind: 'document', subject, target: { part }, stamps, outcome: supports ? 'pass' : 'fail' };
}

/**
 * The fact a recorded Lean theorem check makes: Lean decides its outcome from the check and the claim's `about`
 * constants (Exegra.Verdict.theoremOutcome).
 * @param {string} part @param {any} check @param {string[]} about @param {FactStamps} stamps
 * @returns {Fact}
 */
export function theoremFact(part, check, about, stamps) {
  return { kind: 'leanTheorem', subject: 'implementation', target: { part }, stamps, check, about };
}

/**
 * The fact a check Exegra ran over its own model makes.
 * @param {string} part @param {'modelCheck'|'traceCheck'|'statistical'|'boundedExploration'} kind
 * @param {'pass'|'fail'|'undecided'} outcome @param {string} modelHash
 * @returns {Fact}
 */
export function checkFact(part, kind, outcome, modelHash) {
  return { kind, subject: 'model', target: { part }, stamps: stampsOf(modelHash, modelHash), outcome };
}

/**
 * A fact about an assumption: it holds (pass), is refuted (fail) or was not checked (not-run).
 * @param {string} assumption @param {import('./verdict.js').FactKind} kind @param {'pass'|'fail'|'not-run'} outcome
 * @param {FactStamps} stamps
 * @returns {Fact}
 */
export function assumptionFact(assumption, kind, outcome, stamps) {
  return { kind, subject: 'implementation', target: { assumption }, stamps, outcome };
}
