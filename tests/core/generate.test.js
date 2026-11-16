// Tests for the deterministic artifact generators (src/core/generate).
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { analyzeSpec } from '../../src/core/analyze.js';
import { evaluateClaims } from '../../src/core/claims.js';
import { initEngine } from '../../src/core/engine.js';
import { semanticHash } from '../../src/core/hash.js';
import {
  generateAll,
  generateManifest,
  generateArchitectureDoc,
  generateClaimsReportJson,
} from '../../src/core/generate/index.js';

// Claims over scenarios run the simulation engine.
initEngine();

// Two components, one calls relationship, and a claim the model violates.
const SPEC = `{
  "exegra": "0.1",
  "system": { "id": "sample", "name": "Sample", "description": "A two-part sample." },
  "components": [
    { "id": "alpha", "name": "Alpha", "category": "logical", "purpose": "Does alpha things." },
    { "id": "beta", "name": "Beta", "category": "logical", "purpose": "Holds beta state.", "unknowns": ["Retention period is not decided."] }
  ],
  "relationships": [
    { "id": "alpha-calls-beta", "kind": "calls", "from": "alpha", "to": "beta", "description": "Alpha calls beta directly." }
  ],
  "claims": [
    { "id": "alpha-never-calls-beta", "kind": "structural", "statement": "Alpha never calls Beta.", "evaluate": { "method": "no-relationship", "from": "alpha", "to": "beta" } }
  ]
}`;

// The same specification with comments, different whitespace and different key order.
const SPEC_REFORMATTED = `// A reformatted copy of the same specification.
{ "claims": [ { "evaluate": { "to": "beta", "from": "alpha", "method": "no-relationship" },
      "statement": "Alpha never calls Beta.", "kind": "structural", "id": "alpha-never-calls-beta" } ],
  "relationships": [ { "description": "Alpha calls beta directly.", "to": "beta", "from": "alpha", "kind": "calls", "id": "alpha-calls-beta" } ],
  /* components below */
  "components": [
    { "category": "logical", "purpose": "Does alpha things.", "name": "Alpha", "id": "alpha" },
    { "unknowns": ["Retention period is not decided."], "id": "beta", "category": "logical", "name": "Beta", "purpose": "Holds beta state." }
  ],
  "system": { "name": "Sample", "id": "sample", "description": "A two-part sample." },
  "exegra": "0.1"
}`;

/** @param {string} text */
function build(text) {
  const { model, errorCount, diagnostics } = analyzeSpec(text);
  assert.equal(errorCount, 0);
  assert.ok(model);
  return { model, diagnostics, claimResults: evaluateClaims(model) };
}

/** @param {string} text */
function outputs(text) {
  const { model, diagnostics, claimResults } = build(text);
  return generateAll(model, { claimResults, diagnostics });
}

/** @param {{id: string, data: any}[]} entities */
function dataById(entities) {
  return Object.fromEntries(entities.map((e) => [e.id, e.data]));
}

test('generateAll returns exactly the five artifacts', () => {
  const out = outputs(SPEC);
  assert.deepEqual(Object.keys(out).sort(), [
    'ARCHITECTURE.md', 'claims-report.json', 'claims-report.md', 'manifest.json', 'tasks.json',
  ]);
  for (const value of Object.values(out)) assert.equal(typeof value, 'string');
});

test('two runs over the same model are byte-identical', () => {
  const a = outputs(SPEC);
  const b = outputs(SPEC);
  assert.deepEqual(a, b);
  for (const [name, body] of Object.entries(a)) {
    assert.ok(body.endsWith('\n') && !body.endsWith('\n\n'), `${name} ends with one newline`);
    assert.ok(!body.includes('\r'), `${name} uses \\n line endings`);
  }
});

test('comments, whitespace and key order do not change the semantic content', () => {
  const a = JSON.parse(generateManifest(build(SPEC).model));
  const b = JSON.parse(generateManifest(build(SPEC_REFORMATTED).model));
  assert.equal(a.semanticHash, b.semanticHash);
  // Source positions differ between the two texts, so compare declarations only.
  assert.deepEqual(dataById(a.entities), dataById(b.entities));
});

test('every JSON artifact parses and carries the semantic hash', () => {
  const { model, claimResults } = build(SPEC);
  const hash = semanticHash(model);
  const out = generateAll(model, { claimResults, diagnostics: [] });
  for (const name of ['manifest.json', 'claims-report.json', 'tasks.json']) {
    assert.equal(JSON.parse(out[name]).semanticHash, hash, name);
  }
});

test('a violated claim is a high-severity task and a violated report entry', () => {
  const out = outputs(SPEC);
  const tasks = JSON.parse(out['tasks.json']).tasks;
  const task = tasks.find((t) => t.id === 'claim:alpha-never-calls-beta:violated');
  assert.ok(task, 'violated-claim task present');
  assert.equal(task.type, 'violated-claim');
  assert.equal(task.severity, 'high');
  assert.ok(task.entities.includes('alpha-never-calls-beta'));

  const report = JSON.parse(out['claims-report.json']);
  const claim = report.claims.find((c) => c.id === 'alpha-never-calls-beta');
  assert.equal(claim.status, 'violated');
  assert.equal(report.summary.violated, 1);
  assert.ok(claim.counterexample);
});

test('a claim without a supplied result is reported as not evaluated', () => {
  const { model } = build(SPEC);
  const report = JSON.parse(generateClaimsReportJson(model, { claimResults: [], diagnostics: [] }));
  const claim = report.claims[0];
  assert.equal(claim.status, 'not-evaluated');
  assert.equal(claim.evaluator, 'none');
  assert.equal(claim.explanation, 'No evaluation result was supplied.');
});

test('the architecture document names every component', () => {
  const { model, claimResults } = build(SPEC);
  const doc = generateArchitectureDoc(model, { claimResults, diagnostics: [] });
  for (const c of model.byKind.component) {
    assert.ok(doc.includes(c.data.name), `architecture doc names ${c.data.name}`);
  }
});

test('no artifact contains undefined or object placeholders', () => {
  for (const text of [SPEC, SPEC_REFORMATTED]) {
    for (const [name, body] of Object.entries(outputs(text))) {
      assert.ok(!body.includes('undefined'), `${name} contains "undefined"`);
      assert.ok(!body.includes('[object Object]'), `${name} contains "[object Object]"`);
    }
  }
});
