// The import scan (WG-5684, criterion 12; epistemics defect D5; reworked by WG-5696): the fact producer for the
// assumption extracted-facts-current. Imports between files of the surface are extracted facts now, so the scan checks
// what extraction cannot vouch for itself: that the fact file describes the tree, and that the file-system imports
// no extracted element stands for have a declared relationship. On the current tree it finds
// src/core/derivation-cache.js importing node:fs with no declared relationship, so the assumption is refuted and
// core-independent-of-ui, a claim resting on it, reads undecided instead of verified.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { analyzeSpec } from '../../src/core/analyze.js';
import { evaluateClaim } from '../../src/core/claims.js';
import { attachExtracted } from '../../src/core/extraction.js';
import { scanImports, importScanFacts, importScanRecord, importsOf, IMPORT_ASSUMPTION } from '../../tools/import-scan.js';
import { readSpecFile } from '../../tools/spec-manifest.js';
import { readFacts, FACTS_PATH } from '../../tools/extract.js';

const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');

function exegraModel() {
  const { model, errorCount } = analyzeSpec(readSpecFile(path.join(repoRoot, 'specs', 'exegra', 'spec.jsonc')));
  assert.equal(errorCount, 0);
  assert.ok(model);
  return attachExtracted(model, readFacts(path.join(repoRoot, FACTS_PATH)));
}

test('the import scan reads static, dynamic and builtin imports and ignores comments', () => {
  const text = [
    "import fs from 'node:fs';",
    "import { a, b } from './a.js';",
    "export { c } from '../c.js';",
    "const m = await import('./lazy.js');",
    "const p = process.getBuiltinModule('node:fs/promises');",
    "// import x from './commented.js';",
    "/* import y from './blocked.js'; */",
    "const url = 'https://example.org/x.js';",
  ].join('\n');
  assert.deepEqual(importsOf(text), ['node:fs', './a.js', '../c.js', './lazy.js', 'node:fs/promises']);
});

test('the assumption is the freshness of the extracted facts, no longer the hand-declared relationships', () => {
  assert.equal(IMPORT_ASSUMPTION, 'extracted-facts-current');
  const model = exegraModel();
  assert.ok(model.entities.has(IMPORT_ASSUMPTION));
  assert.ok(!model.entities.has('relationships-match-imports'));
});

test('on the current tree the scan finds derivation-cache importing node:fs with no declared relationship', () => {
  const model = exegraModel();
  const scan = scanImports(model, repoRoot);
  assert.ok(scan.checked > 0);
  assert.deepEqual(scan.stale, [], 'the fact file describes the tree');
  const hit = scan.undeclared.find((u) => u.from === 'src/core/derivation-cache.js' && u.imports === 'node:fs');
  assert.ok(hit, JSON.stringify(scan.undeclared.slice(0, 10)));
  assert.equal(hit.component, 'derivation-cache');
  assert.equal(hit.target, 'filesystem');
  const [fact] = importScanFacts(scan, 'TREE', { tree: 'TREE', formal: 'F' });
  assert.deepEqual(fact.target, { assumption: IMPORT_ASSUMPTION });
  assert.equal(fact.outcome, 'fail');
  assert.equal(importScanRecord(scan, 'TREE').outcome, 'fail');
});

test('a stale fact file refutes the assumption, whatever the imports', () => {
  const model = exegraModel();
  const facts = /** @type {any} */ (readFacts(path.join(repoRoot, FACTS_PATH)));
  const stale = { ...facts, files: facts.files.map((/** @type {any} */ f, /** @type {number} */ i) => (i === 0 ? { ...f, digest: 'sha256:0' } : f)) };
  const scan = scanImports(model, repoRoot, stale);
  assert.deepEqual(scan.stale, [facts.files[0].path]);
  const rec = importScanRecord(scan, 'TREE');
  assert.equal(rec.outcome, 'fail');
  assert.match(rec.detail, /fact file is stale/);
});

test('with the scan recorded, core-independent-of-ui is undecided, not verified', () => {
  const model = exegraModel();
  const claim = model.entities.get('core-independent-of-ui');
  assert.ok(claim?.data.assumptions.includes(IMPORT_ASSUMPTION), 'the claim rests on the assumption');
  assert.ok(claim?.data.assumptions.includes('static-extractor-sound'));
  const stamps = { tree: 'TREE', formal: 'F' };
  // Without the scan the model check alone holds: no relationship leads to the file system from the core.
  const without = evaluateClaim(model, 'core-independent-of-ui', { stamps });
  assert.equal(without.status, 'verified', without.explanation);
  assert.equal(without.basis?.basis, 'extracted');
  assert.match(without.scope, /static imports only/);
  // The scan as verify records it (results.json, assumptions), read on the tree it ran on.
  const scan = scanImports(model, repoRoot);
  const recorded = { assumptions: { [IMPORT_ASSUMPTION]: importScanRecord(scan, 'TREE') } };
  const r = evaluateClaim(model, 'core-independent-of-ui', { recorded, stamps });
  assert.notEqual(r.status, 'verified');
  assert.equal(r.verdict?.strength, 'undecided');
  assert.equal(r.verdict?.established, false);
  assert.match(r.explanation, /extracted-facts-current/);
  assert.match(r.explanation, /derivation-cache/);
});

test('the claim that replaces the assumption is evaluated from the extracted facts and holds on the current tree', () => {
  const model = exegraModel();
  const r = evaluateClaim(model, 'extraction-reconciles-with-declarations');
  assert.equal(r.status, 'verified', r.explanation);
  assert.match(r.scope, /static imports only/);
  // Without the fact file there is nothing to reconcile: undecided, not verified.
  const bare = /** @type {any} */ (analyzeSpec(readSpecFile(path.join(repoRoot, 'specs', 'exegra', 'spec.jsonc'))).model);
  assert.notEqual(evaluateClaim(bare, 'extraction-reconciles-with-declarations').status, 'verified');
});
