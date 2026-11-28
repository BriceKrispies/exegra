// Staged conformance (WG-5685, criterion 11): each stage is a claim method whose result names its stage. The
// Lean verdict's maxStrength gives every stage but verified-refinement at most checkedOnInstances (they rest on
// test evidence), and verified-refinement proved with subject implementation (it rests on a Lean theorem).

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { evaluateClaims } from '../../src/core/claims.js';
import { CONFORMANCE_STAGES, CLAIM_METHODS } from '../../src/core/claim-methods.js';

const STAMPS = { tree: 'TREE', formal: 'FORMAL' };

/** @param {string} kind @param {string} id @param {any} data */
const ent = (kind, id, data) => ({ kind, id, data: { id, ...data }, owner: null, path: [], loc: { line: 1, column: 1, offset: 0, length: 1 } });
/** @param {any[]} entities */
function modelOf(entities) {
  /** @type {Record<string, any[]>} */
  const byKind = {};
  for (const e of entities) (byKind[e.kind] ??= []).push(e);
  return /** @type {any} */ ({
    semanticHash: 'stages', entities: new Map(entities.map((e) => [e.id, e])), byKind, refs: [], exprs: [],
    meta: { relationshipKinds: {}, categories: {}, verificationMethods: {}, entities: {}, sections: {} },
  });
}

/** A claim of one evidence-backed stage with a passing test and a document, both fresh. @param {string} stage */
function evidenceStage(stage) {
  const model = modelOf([
    ent('claim', 'c', { kind: 'invariant', statement: `The implementation conforms at stage ${stage}.`, evaluate: { method: `conformance-${stage}` } }),
    ent('evidence', 'ev-t', { claim: 'c', kind: 'test', ref: 'tests/core/x.test.js#conforms' }),
    ent('evidence', 'ev-d', { claim: 'c', kind: 'document', ref: 'docs/review.md' }),
  ]);
  return evaluateClaims(model, { recorded: { results: { 'ev-t': { outcome: 'pass', stamp: 'TREE' } } }, stamps: STAMPS })[0];
}

// The six stages are registered methods, weakest first.
// @evidence conformance-stages-graded # the six conformance stages are claim methods
// A fresh passing test and a document give the structural stage checkedOnInstances, subject implementation, not established.
// @evidence conformance-stages-graded # the structural stage names its stage and gives at most checkedOnInstances
// A fresh passing test and a document give the interface stage checkedOnInstances, subject implementation, not established.
// @evidence conformance-stages-graded # the interface stage names its stage and gives at most checkedOnInstances
// A fresh passing test and a document give the transition stage checkedOnInstances, subject implementation, not established.
// @evidence conformance-stages-graded # the transition stage names its stage and gives at most checkedOnInstances
// A fresh passing test and a document give the trace stage checkedOnInstances, subject implementation, not established.
// @evidence conformance-stages-graded # the trace stage names its stage and gives at most checkedOnInstances
// A fresh passing test and a document give the runtime-monitor stage checkedOnInstances, subject implementation, not established.
// @evidence conformance-stages-graded # the runtime-monitor stage names its stage and gives at most checkedOnInstances
test('the six conformance stages are claim methods, weakest first', () => {
  assert.deepEqual(CONFORMANCE_STAGES, ['structural', 'interface', 'transition', 'trace', 'runtime-monitor', 'verified-refinement']);
  for (const s of CONFORMANCE_STAGES) assert.ok(Object.hasOwn(CLAIM_METHODS, `conformance-${s}`), s);
});

for (const stage of ['structural', 'interface', 'transition', 'trace', 'runtime-monitor']) {
  test(`the ${stage} stage names its stage and gives at most checkedOnInstances`, () => {
    const r = evidenceStage(stage);
    assert.equal(r.stage, stage);
    assert.equal(r.status, 'supported', r.explanation);
    assert.equal(r.verdict?.strength, 'checkedOnInstances');
    assert.equal(r.verdict?.subject, 'implementation');
    assert.equal(r.verdict?.established, false);
  });
}

// A fresh accepted theorem check gives the verified-refinement stage proved, subject implementation.
// @evidence conformance-stages-graded
test('the verified-refinement stage names its stage and is proved with subject implementation', () => {
  const model = modelOf([
    ent('claim', 'c', { kind: 'invariant', statement: 'The implementation refines its specification.', evaluate: { method: 'conformance-verified-refinement', theorem: 'Exegra.Core.LTS.refines_traces', about: ['Exegra.Core.LTS.Simulates'] } }),
  ]);
  const recorded = { theorems: { 'Exegra.Core.LTS.refines_traces': { found: true, kind: 'theorem', kernel: 'ok', axioms: ['propext', 'Quot.sound'], lean: '4.35.0', checkedAt: '2026-11-28T00:00:00Z', formalHash: 'FORMAL', about: { 'Exegra.Core.LTS.Simulates': { kind: 'definition', inStatement: true } } } } };
  const r = evaluateClaims(model, { recorded, stamps: STAMPS })[0];
  assert.equal(r.stage, 'verified-refinement');
  assert.equal(r.status, 'proved', r.explanation);
  assert.equal(r.verdict?.strength, 'proved');
  assert.equal(r.verdict?.subject, 'implementation');
});
