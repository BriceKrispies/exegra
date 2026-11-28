// Model-defined vocabulary: a specification can introduce its own entity
// kinds, reference-typed properties and external verification methods, and
// they take part in validation, renames, deletes and claim evaluation without
// any code knowing about them.
import test from 'node:test';
import assert from 'node:assert/strict';
import { analyzeSpec } from '../../src/core/analyze.js';
import { Project } from '../../src/core/project.js';
import { evaluateClaims } from '../../src/core/claims.js';
import { initEngine } from '../../src/core/engine.js';

// Claims over scenarios run the simulation engine.
initEngine();

const SPEC = `{
  "exegra": "0.1",
  "system": { "id": "sys", "name": "Sys" },
  "vocabulary": {
    "entityKinds": {
      "goal": { "label": "Goal", "section": "goals", "shape": "diamond", "color": "green",
        "properties": { "statement": { "type": "text", "required": true }, "stage": { "type": "enum", "values": ["r1", "r2"] } } },
      "boundary": { "label": "Boundary", "section": "boundaries", "shape": "hex", "color": "teal",
        "properties": { "name": { "type": "string", "required": true }, "providedBy": { "type": "list", "items": { "type": "ref", "ref": ["component"] } } } }
    },
    "properties": [
      { "entity": "claim", "name": "traces", "type": "list", "items": { "type": "ref", "ref": ["goal"] }, "label": "Traces to" },
      { "entity": "claim", "name": "boundary", "type": "ref", "ref": "boundary", "label": "Stated at" }
    ],
    "verificationMethods": { "property": { "label": "Property test", "description": "Checked by a property-based test outside Exegra." } }
  },
  "components": [ { "id": "kernel", "name": "Kernel", "category": "logical", "purpose": "Decides." } ],
  "goals": [ { "id": "g-1", "statement": "Decisions are deterministic.", "stage": "r1" } ],
  "boundaries": [ { "id": "b-17", "name": "Kernel API", "providedBy": ["kernel"] } ],
  "claims": [
    { "id": "krn-002", "kind": "requirement", "statement": "Same input, same output.", "subjects": ["kernel"],
      "traces": ["g-1"], "boundary": "b-17", "evaluate": { "method": "property" } }
  ]
}`;

test('declared entity kinds parse into entities with their own sections and properties', () => {
  const { model, diagnostics, errorCount } = analyzeSpec(SPEC);
  assert.equal(errorCount, 0, JSON.stringify(diagnostics.filter((d) => d.severity === 'error')));
  assert.ok(model);
  assert.equal(model.entities.get('g-1')?.kind, 'goal');
  assert.equal(model.byKind.boundary.length, 1);
  assert.equal(model.meta.entities.goal.declared, true);
  assert.equal(model.meta.sections.goals.entity, 'goal');
  assert.deepEqual(diagnostics.filter((d) => d.severity === 'warning'), [], 'a declared verification method is not "unsupported"');
});

test('declared kinds are validated like built-in ones', () => {
  const codes = (/** @type {string} */ t) => analyzeSpec(t).diagnostics.filter((d) => d.severity === 'error').map((d) => d.code);
  assert.deepEqual(codes(SPEC.replace('"stage": "r1"', '"stage": "r9"')), ['property.enum']);
  assert.deepEqual(codes(SPEC.replace('"statement": "Decisions are deterministic.", ', '')), ['property.required']);
  assert.deepEqual(codes(SPEC.replace('"traces": ["g-1"]', '"traces": ["nope"]')), ['ref.unresolved']);
  assert.deepEqual(codes(SPEC.replace('"traces": ["g-1"]', '"traces": ["kernel"]')), ['ref.kind']);
  assert.deepEqual(codes(SPEC.replace('"goals": [', '"aims": [], "goals": [')), ['spec.unknown-section']);
  assert.ok(codes(SPEC.replace('"section": "goals"', '"section": "components"')).includes('vocabulary.duplicate'));
  assert.ok(codes(SPEC.replace('"ref": ["component"]', '"ref": ["widget"]')).includes('vocabulary.entity'));
});

test('references through model-defined properties follow renames and block deletes', () => {
  const p = new Project({ specText: SPEC });
  assert.equal(p.errorCount, 0);
  assert.equal(p.apply({ type: 'RenameEntity', id: 'g-1', newId: 'g-determinism' }).ok, true);
  assert.deepEqual(p.model?.entities.get('krn-002')?.data.traces, ['g-determinism']);
  const refused = p.apply({ type: 'DeleteEntity', id: 'b-17' });
  assert.equal(refused.code, 'delete.referenced');
  assert.equal(p.apply({ type: 'DeleteEntity', id: 'b-17', cascade: true }).ok, true);
  assert.equal(p.model?.entities.get('krn-002')?.data.boundary, undefined);
  assert.equal(p.errorCount, 0);
  const created = p.apply({ type: 'CreateEntity', kind: 'goal', data: { id: 'g-2', statement: 'Another goal.' } });
  assert.equal(created.ok, true, created.message);
  assert.equal(p.model?.byKind.goal.length, 2);
});

test('a claim verified by an external method is never reported as verified by Exegra', () => {
  const { model } = analyzeSpec(SPEC);
  assert.ok(model);
  const [r] = evaluateClaims(model);
  assert.equal(r.status, 'not-evaluated');
  assert.equal(r.evaluator, 'external:property');
  assert.match(r.scope, /outside Exegra/);
  // With recorded evidence of an executed test it becomes "supported", still not "verified".
  const withEvidence = SPEC.replace('"claims": [', '"evidence": [ { "id": "ev-krn-002", "claim": "krn-002", "kind": "test", "ref": "tests/kernel.rs#krn_002" } ],\n  "claims": [');
  const m2 = analyzeSpec(withEvidence).model;
  assert.ok(m2);
  assert.equal(evaluateClaims(m2)[0].status, 'inconclusive');
  assert.equal(evaluateClaims(m2, { recorded: { results: { 'ev-krn-002': { outcome: 'pass', stamp: 'T' } } }, stamps: { tree: 'T', formal: 'F' } })[0].status, 'supported');
  assert.equal(evaluateClaims(m2, { recorded: { results: { 'ev-krn-002': { outcome: 'fail' } } } })[0].status, 'violated');
});

test('an outcome recorded per claim by an external tool decides supported or violated, never verified', () => {
  const { model } = analyzeSpec(SPEC);
  assert.ok(model);
  const pass = evaluateClaims(model, { recorded: { tool: 'concordance', claims: { 'krn-002': { outcome: 'pass', detail: 'Proved by kernel::tests::determinism.', proofs: ['kernel::tests::determinism'], stamp: 'T' } } }, stamps: { tree: 'T', formal: 'F' } })[0];
  assert.equal(pass.status, 'supported');
  assert.equal(pass.evaluator, 'external:property');
  assert.match(pass.explanation, /Recorded by concordance/);
  assert.match(pass.explanation, /Exegra did not check this itself/);
  const fail = evaluateClaims(model, { recorded: { tool: 'concordance', claims: { 'krn-002': { outcome: 'fail', detail: 'A proof contradicts it.' } } } })[0];
  assert.equal(fail.status, 'violated');
  assert.ok(fail.counterexample);
  // A recorded outcome for some other claim, or a malformed one, changes nothing.
  assert.equal(evaluateClaims(model, { recorded: { claims: { other: { outcome: 'pass' } } } })[0].status, 'not-evaluated');
  assert.equal(evaluateClaims(model, { recorded: { claims: { 'krn-002': { outcome: 'maybe' } } } })[0].status, 'not-evaluated');
  assert.equal(evaluateClaims(model, { recorded: { claims: { constructor: { outcome: 'pass' } } } })[0].status, 'not-evaluated');
});
