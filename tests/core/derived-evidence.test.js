// Test evidence derived from the tests themselves (WG-5705): a test names the claims it evidences with an @evidence
// marker (tools/extract.js reads it into the fact file), and the model derives the evidence entities from the markers
// (src/core/extraction.js). Declared evidence stays for what a test cannot carry, and validation refuses a declared
// test evidence that duplicates a derived one.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { analyzeSpec } from '../../src/core/analyze.js';
import { initEngine } from '../../src/core/engine.js';
import { Project } from '../../src/core/project.js';
import { evaluateClaim } from '../../src/core/claims.js';
import { attachExtracted, derivedEvidenceId, derivedEvidenceDiagnostics, isDerivedEvidence, stripExtracted } from '../../src/core/extraction.js';
import { markersOf, testEvidence, FACTS_PATH } from '../../tools/extract.js';
import { readSpecFile } from '../../tools/spec-manifest.js';
import { claimSubjects } from '../../src/core/query.js';
import { CLAIM_METHODS } from '../../src/core/claim-methods.js';

initEngine();
const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');

const SPEC = JSON.stringify({
  exegra: '0.1',
  system: { id: 'markers', name: 'Markers' },
  components: [{ id: 'a', name: 'A', category: 'logical', purpose: 'A.' }],
  claims: [
    { id: 'c1', kind: 'invariant', statement: 'One.', subjects: ['a'], evaluate: { method: 'external-evidence' } },
    { id: 'c2', kind: 'invariant', statement: 'Two.', subjects: ['a'], evaluate: { method: 'external-evidence' } },
  ],
}, null, 2);
const facts = (/** @type {any[]} */ evidence, /** @type {any[]} */ evidenceProblems = []) => ({ format: 'exegra-extracted-facts/1', provenance: 'extracted', extractor: { id: 'x', version: '2' }, files: [], evidence, ...(evidenceProblems.length ? { evidenceProblems } : {}) });

// @evidence test-evidence-derived-from-markers
test('the extractor reads a marker above a test as its title, a marker with a pattern as that pattern, and one with an empty pattern as the whole file', () => {
  const text = [
    "import { test } from 'node:test';",
    '// @evidence c1 c2',
    '// a comment between the marker and its test',
    "test('does one thing', () => {});",
    '// @evidence c2 # generated case [0-9]+',
    '// @evidence c1 #',
    "for (const n of [1, 2]) test(`generated case ${n}`, () => {});",
    '// @evidence c1',
    'const notATest = 1;',
    '// @evidence Not-An-Id',
  ].join('\n');
  const r = markersOf('tests/core/x.test.js', text);
  assert.deepEqual(r.evidence.map((e) => [e.claim, e.ref, e.line]), [
    ['c1', 'tests/core/x.test.js#does one thing', 2],
    ['c2', 'tests/core/x.test.js#does one thing', 2],
    ['c2', 'tests/core/x.test.js#generated case [0-9]+', 5],
    ['c1', 'tests/core/x.test.js', 6],
  ]);
  assert.deepEqual(r.problems.map((p) => p.line), [8, 10], 'a marker above no test, and a marker naming no claim id, are problems');
});

// @evidence test-evidence-derived-from-markers
test('the model derives one test evidence per marked claim and reference, which a claim reads like a declared one', () => {
  const project = new Project({ name: 'markers', specText: SPEC, extracted: facts([
    { claim: 'c1', ref: 'tests/core/x.test.js#does one thing', file: 'tests/core/x.test.js', line: 2 },
    { claim: 'c1', ref: 'tests/core/x.test.js#does one thing', file: 'tests/core/x.test.js', line: 9 },
    { claim: 'c2', ref: 'tests/core/x.test.js', file: 'tests/core/x.test.js', line: 6 },
  ]) });
  const model = /** @type {any} */ (project.model);
  const derived = model.byKind.evidence.filter(isDerivedEvidence);
  assert.deepEqual(derived.map((/** @type {any} */ e) => [e.data.claim, e.data.kind, e.data.ref]), [
    ['c1', 'test', 'tests/core/x.test.js#does one thing'],
    ['c2', 'test', 'tests/core/x.test.js'],
  ], 'the same marker twice derives one evidence');
  const id = derivedEvidenceId('c1', 'tests/core/x.test.js#does one thing');
  assert.equal(derived[0].id, id);
  const STAMP = { tree: 'T', formal: 'F' };
  const pass = evaluateClaim(model, 'c1', { recorded: { results: { [id]: { outcome: 'pass', stamp: 'T' } } }, stamps: STAMP });
  assert.equal(pass.status, 'supported');
  const fail = evaluateClaim(model, 'c1', { recorded: { results: { [id]: { outcome: 'fail', stamp: 'T' } } }, stamps: STAMP });
  assert.equal(fail.status, 'violated');
  assert.equal(project.errorCount, 0);
  // Without the facts the derived evidence is gone again.
  assert.equal(stripExtracted(model).byKind.evidence.filter(isDerivedEvidence).length, 0);
});

// @evidence test-evidence-derived-from-markers
test('validation refuses a declared test evidence that duplicates a derived one, a marker naming no claim, a marker it cannot read and a tested claim with no subjects, and keeps contradicting evidence', () => {
  const declared = JSON.parse(SPEC);
  declared.claims.push({ id: 'c5', kind: 'invariant', statement: 'Five.', evaluate: { method: 'external-evidence' } });
  declared.evidence = [
    { id: 'ev-dup', claim: 'c1', kind: 'test', ref: 'tests/core/x.test.js#does one thing' },
    { id: 'ev-against', claim: 'c1', kind: 'test', ref: 'tests/core/x.test.js#does one thing', supports: false },
    { id: 'ev-doc', claim: 'c2', kind: 'document', ref: 'docs/review.md' },
  ];
  const project = new Project({ name: 'markers', specText: JSON.stringify(declared, null, 2), extracted: facts([
    { claim: 'c1', ref: 'tests/core/x.test.js#does one thing', file: 'tests/core/x.test.js', line: 2 },
    { claim: 'nope', ref: 'tests/core/x.test.js#does one thing', file: 'tests/core/x.test.js', line: 3 },
    { claim: 'c5', ref: 'tests/core/x.test.js#does one thing', file: 'tests/core/x.test.js', line: 3 },
  ], [{ file: 'tests/core/y.test.js', line: 4, message: 'an @evidence marker names no claim.' }]) });
  const codes = derivedEvidenceDiagnostics(project.model).map((d) => [d.code, d.entityId ?? null]);
  assert.deepEqual(codes, [
    ['evidence.marker-unknown-claim', derivedEvidenceId('nope', 'tests/core/x.test.js#does one thing')],
    ['evidence.claim-without-subjects', 'c5'],
    ['evidence.marker-invalid', null],
    ['evidence.duplicates-derived', 'ev-dup'],
  ]);
  assert.equal(project.errorCount, 4, 'the project counts them as errors');
  assert.ok(project.diagnostics.some((d) => d.code === 'evidence.duplicates-derived'));
});

// @evidence test-evidence-derived-from-markers
test('the self-specification declares no test evidence: every one is derived from a marker, and every marker names a claim', () => {
  const stored = JSON.parse(fs.readFileSync(path.join(ROOT, FACTS_PATH), 'utf8'));
  assert.deepEqual(stored.evidence, testEvidence(ROOT).evidence, 'the fact file records the markers of the tree');
  const { model } = analyzeSpec(readSpecFile(path.join(ROOT, 'specs/exegra/spec.jsonc')));
  const declared = /** @type {any} */ (model).byKind.evidence ?? [];
  assert.deepEqual(declared.filter((/** @type {any} */ e) => e.data.kind === 'test' && e.data.supports !== false).map((/** @type {any} */ e) => e.id), [], 'no declared test evidence');
  const attached = /** @type {any} */ (attachExtracted(/** @type {any} */ (model), stored));
  const derived = attached.byKind.evidence.filter(isDerivedEvidence);
  assert.ok(derived.length >= 800, `${derived.length} derived test evidence`);
  assert.deepEqual(derivedEvidenceDiagnostics(attached), []);
});

// @evidence claim-subjects-derived-from-parameters
test('a claim that declares no subjects takes the entities its evaluation parameters name, and the removed declarations still equal them', () => {
  const doc = JSON.parse(SPEC);
  doc.components.push({ id: 'b', name: 'B', category: 'logical', purpose: 'B.' }, { id: 'store', name: 'Store', category: 'storage', purpose: 'S.' });
  doc.claims.push({ id: 'c3', kind: 'structural', statement: 'A never reaches B.', evaluate: { method: 'no-relationship', from: 'a', to: ['b', 'store'] } });
  doc.claims.push({ id: 'c4', kind: 'structural', statement: 'Stores have owners.', evaluate: { method: 'property-defined', select: { category: 'storage' }, property: 'owner' } });
  const model = /** @type {any} */ (analyzeSpec(JSON.stringify(doc, null, 2)).model);
  const params = (/** @type {string} */ m) => CLAIM_METHODS[m].params;
  assert.deepEqual(claimSubjects(model, model.entities.get('c3'), params('no-relationship')), ['a', 'b', 'store'], 'selectors give their components, in parameter order');
  assert.deepEqual(claimSubjects(model, model.entities.get('c4'), params('property-defined')), ['store'], 'an object selector gives what it selects');
  assert.deepEqual(claimSubjects(model, model.entities.get('c1'), params('external-evidence')), ['a'], 'declared subjects win');
  // The self-specification's claims whose subjects were removed derive exactly what they declared at removal time.
  const removed = JSON.parse(fs.readFileSync(path.join(ROOT, 'tests/fixtures/derived-declarations/claim-subjects.json'), 'utf8')).claims;
  assert.equal(removed.length, 5);
  const self = /** @type {any} */ (analyzeSpec(readSpecFile(path.join(ROOT, 'specs/exegra/spec.jsonc'))).model);
  for (const r of removed) {
    const c = self.entities.get(r.claim);
    assert.equal(c.data.subjects, undefined, `${r.claim} declares no subjects`);
    assert.deepEqual([...claimSubjects(self, c, params(c.data.evaluate.method))].sort(), [...r.declared].sort(), r.claim);
  }
});
