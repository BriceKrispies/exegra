// The platform half of a layered analysis is computed once per process (src/core/layers.js, WG-5411):
// validating several layer sets over one platform text gives exactly what validating each alone gives.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { analyzeLayers, baseAnalysisCount, clearBaseAnalysisCache } from '../../src/core/layers.js';
import { Project } from '../../src/core/project.js';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const FIXTURES = path.join(HERE, '..', 'fixtures', 'layers');
const read = (/** @type {string} */ f) => fs.readFileSync(f, 'utf8');
const PLATFORM = read(path.join(FIXTURES, 'platform.jsonc'));
const layer = (/** @type {string} */ file) => ({ file: path.basename(file), text: read(file), platform: { declared: '../platform.jsonc', matches: true, expected: '../platform.jsonc' } });
const BADGES = [layer(path.join(FIXTURES, 'products', 'badges.jsonc'))];
const REFUSED = [layer(path.join(FIXTURES, 'refused', 'import-unknown.jsonc'))];

/** Everything an analysis reports, as plain text: models, diagnostics, hashes, counts. @param {any} a */
const shown = (a) => JSON.stringify(a, (_k, v) => (v instanceof Map ? [...v.entries()] : v));

test('layer sets over one platform give the output of independent validations and the platform is analysed once', () => {
  clearBaseAnalysisCache();
  const alone = [BADGES, REFUSED].map((layers) => { clearBaseAnalysisCache(); return shown(analyzeLayers(PLATFORM, layers)); });
  clearBaseAnalysisCache();
  const before = baseAnalysisCount();
  const together = [BADGES, REFUSED, BADGES, []].map((layers) => shown(analyzeLayers(PLATFORM, layers)));
  assert.equal(baseAnalysisCount() - before, 1, 'the platform text is parsed once for all four validations');
  assert.equal(together[0], alone[0]);
  assert.equal(together[1], alone[1]);
  assert.equal(together[2], alone[0], 'a repeated layer set gives the same output again');
  assert.notEqual(together[0], together[1]);
  const a = analyzeLayers(PLATFORM, BADGES);
  const b = analyzeLayers(PLATFORM, REFUSED);
  assert.equal(a.baseHash, b.baseHash);
  assert.ok(b.errorCount > 0 && a.errorCount === 0);
});

test('the shared platform analysis cannot be corrupted by a caller', () => {
  clearBaseAnalysisCache();
  const a = analyzeLayers(PLATFORM, BADGES);
  const base = /** @type {any} */ (a.baseModel);
  assert.throws(() => { base.entities.set('x', {}); }, TypeError);
  assert.throws(() => { base.semanticHash = 'changed'; }, TypeError);
  const first = base.byKind[Object.keys(base.byKind)[0]];
  assert.throws(() => { first.push({}); }, TypeError);
  // The combined model is rebuilt for every call and stays the caller's to change.
  const m = /** @type {any} */ (a.model);
  m.entities.set('x', {});
  assert.equal(/** @type {any} */ (analyzeLayers(PLATFORM, BADGES).model).entities.has('x'), false);
});

test('a layered project derives and edits on top of the shared platform analysis', () => {
  clearBaseAnalysisCache();
  const one = new Project({ specText: PLATFORM, layers: BADGES });
  const two = new Project({ specText: PLATFORM, layers: BADGES });
  assert.equal(shown(one.diagnostics), shown(two.diagnostics));
  assert.equal(one.semanticHash, two.semanticHash);
  assert.equal(one.layeredHash, two.layeredHash);
  const text = one.specText;
  const r = two.apply({ type: 'SetProperty', id: 'runtime', property: 'name', value: 'Tenant runtime' });
  assert.equal(r.ok, true, JSON.stringify(r));
  assert.equal(one.specText, text);
});
