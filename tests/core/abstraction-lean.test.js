// The Lean grounding of the structural abstraction semantics (WG-5699, formal/Exegra/Multiscale.lean) agrees with
// M3's executable derivation (src/core/abstraction.js) on every golden cut of the self-specification
// (tests/fixtures/abstraction/*.json): structure.derive, the definitions P1-P7 and P13 are proved about, gives the
// same lifted interactions with their witness sets, the same fibres and the same boundaries as deriveModel and as the
// recorded golden. The resolution of relationship endpoints to elements (a port to its owner, extracted imports to
// module elements) stays in the trusted JavaScript shell and is the input of both.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { analyzeSpec } from '../../src/core/analyze.js';
import { initEngine } from '../../src/core/engine.js';
import { call } from '../../src/core/lean.js';
import { levelOf, baseFacts, deriveModel } from '../../src/core/abstraction.js';
import { attachExtracted } from '../../src/core/extraction.js';
import { readSpecFile } from '../../tools/spec-manifest.js';

initEngine();
const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const GOLDENS = path.join(ROOT, 'tests/fixtures/abstraction');
const CUTS = ['l0', 'l1', 'persistence-expanded', 'semantic-core-expanded', 'module-level'];

// @evidence structure-lean-agrees-with-derivation # the Lean structural derivation equals M3.s derivation and its golden on every golden cut of the self-specification
test('the Lean structural derivation equals M3\'s derivation and its golden on every golden cut of the self-specification', () => {
  const facts = JSON.parse(fs.readFileSync(path.join(ROOT, 'specs/exegra/extracted/facts.json'), 'utf8'));
  const model = /** @type {any} */ (attachExtracted(/** @type {any} */ (analyzeSpec(readSpecFile(path.join(ROOT, 'specs/exegra/spec.jsonc'))).model), facts));
  const base = baseFacts(model).facts.map((f) => ({ id: f.id, from: f.from, to: f.to, kind: f.kind }));
  assert.deepEqual(fs.readdirSync(GOLDENS).filter((f) => f.endsWith('.json')).map((f) => f.slice(0, -5)).sort(), [...CUTS].sort(), 'every golden cut is compared');
  for (const cut of CUTS) {
    const golden = JSON.parse(fs.readFileSync(path.join(GOLDENS, `${cut}.json`), 'utf8'));
    const level = /** @type {any} */ (levelOf(model, cut));
    const elements = [...level.h.depth.keys()].map((id) => ({ id, parent: level.h.parent.get(id) ?? null }));
    const r = call('structure.derive', { elements, blocks: level.blocks, facts: base });
    assert.ok(r.ok, `${cut}: ${r.error}`);
    const lean = r.value;
    const js = /** @type {any} */ (deriveModel(model, cut));
    const shape = (/** @type {any[]} */ xs) => xs.map((i) => ({ from: i.from, to: i.to, kind: i.kind, witnesses: i.witnesses }));
    assert.ok(lean.interactions.length > 0, cut);
    assert.deepEqual(lean.interactions, shape(js.interactions), `${cut}: interactions against deriveModel`);
    assert.deepEqual(lean.interactions, shape(golden.interactions), `${cut}: interactions against the golden`);
    assert.deepEqual(lean.fibres, js.fibres, `${cut}: fibres against deriveModel`);
    assert.deepEqual(lean.fibres, golden.fibres, `${cut}: fibres against the golden`);
    assert.deepEqual(lean.boundaries, js.boundaries, `${cut}: boundaries against deriveModel`);
    assert.deepEqual(lean.boundaries, golden.boundaries, `${cut}: boundaries against the golden`);
    assert.deepEqual(lean.unplaced, js.diagnostics.filter((/** @type {any} */ d) => d.code === 'abstraction.unplaced').map((/** @type {any} */ d) => d.relationship).sort(), `${cut}: unplaced facts`);
  }
});

// @evidence structure-lean-agrees-with-derivation # the Lean structural derivation places a composite.s own fact in its implicit block
test('the Lean structural derivation places a composite\'s own fact in its implicit block, coarsens kinds and reports an unplaced fact', () => {
  const r = call('structure.derive', {
    elements: [{ id: 's', parent: null }, { id: 'a', parent: 's' }, { id: 'a1', parent: 'a' }, { id: 'b', parent: 's' }],
    blocks: ['a', 'b'],
    facts: [{ id: 'r1', from: 'a1', to: 'b', kind: 'invokes' }, { id: 'r2', from: 's', to: 'b', kind: 'notifies' }, { id: 'r3', from: 'a1', to: 'a', kind: 'imports' }, { id: 'r4', from: 'zz', to: 'b', kind: 'imports' }],
    coarsen: [['invokes', 'interacts-with'], ['notifies', 'interacts-with']],
  });
  assert.ok(r.ok, r.error);
  assert.deepEqual(r.value.interactions, [
    { from: 'a', to: 'b', kind: 'interacts-with', witnesses: ['r1'] },
    { from: 's', to: 'b', kind: 'interacts-with', witnesses: ['r2'] },
  ]);
  assert.deepEqual(r.value.fibres, { a: ['r3'], b: [], s: [] });
  assert.deepEqual(r.value.boundaries.b, { out: [], in: ['r1', 'r2'] });
  assert.deepEqual(r.value.unplaced, ['r4']);
});
