// The verified kernel's model derivation and semantic hash (formal/Exegra/Model.lean and
// Hash.lean, called through src/core/parse.js and src/core/hash.js) against the JavaScript they
// replaced (tests/oracle/parse-reference.js): identical diagnostics, model and hash on
// - every specification the tests read: specs/exegra, specs/benchmark and tests/fixtures/**;
// - every specification text the core tests parse (tests/fixtures/parse-corpus/cases.json.gz:
//   the distinct texts parseSpec received while tests/core/{model,vocabulary,roundtrip,references,
//   data-model,contract-trace,fault-model,metric-spec,projections,flows,generate,claims,sim,replay,
//   import-markdown,cli,workspace}.test.js ran, the invalid-spec cases among them; 81 of the 206
//   have diagnostics);
// - the edge cases below (repeated keys, array-index keys, non-ASCII keys, unusual numbers).
// This file holds the two sweeps over every specification the tests read; the edge cases are in
// tests/core/model-kernel.test.js. Both sweeps run outside the routine suite: npm run test:proofs, npm run verify
// and the Check workflow.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import zlib from 'node:zlib';
import { fileURLToPath } from 'node:url';
import { SpecManifestError, readSpecFile } from '../../tools/spec-manifest.js';
import { same, jsoncFiles } from '../oracle/same-model.js';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');

// specs/exegra, specs/benchmark and every tests/fixtures .jsonc: identical diagnostics, model, normal form and hash.
// @evidence model-derivation-matches-javascript
test('the specifications and fixtures the tests read derive identically', () => {
  const files = ['specs/exegra/spec.jsonc', 'specs/benchmark/spec.jsonc', ...jsoncFiles(path.join(ROOT, 'tests/fixtures')).map((f) => path.relative(ROOT, f))];
  assert.ok(files.length >= 6);
  for (const f of files) {
    /** @type {string} */
    let text;
    try {
      text = readSpecFile(path.join(ROOT, f));
    } catch (e) {
      // A fixture that is a deliberately invalid manifest (tests/fixtures/spec-manifest) has no specification text to derive.
      if (e instanceof SpecManifestError) continue;
      throw e;
    }
    same(text, f);
  }
});

// The 206 texts the core tests parse (81 with diagnostics): identical diagnostics, model, normal form and hash.
// @evidence model-derivation-matches-javascript
test('every specification text the core tests parse derives identically', () => {
  /** @type {string[]} */
  const cases = JSON.parse(zlib.gunzipSync(fs.readFileSync(path.join(ROOT, 'tests/fixtures/parse-corpus/cases.json.gz'))).toString('utf8'));
  let invalid = 0;
  cases.forEach((text, i) => { if (same(text, `case ${i}`)) invalid++; });
  assert.equal(cases.length, 206);
  assert.ok(invalid >= 80, `only ${invalid} cases have diagnostics`);
});

