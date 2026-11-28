// The lowering of a scenario to its engine input is in Lean (formal/Exegra/Lower.lean, WG-5683) and
// derives exactly what the JavaScript lowering it replaced (src/core/sim-input.js, pools.js and
// distributions.js, deleted) derived: the distribution tables byte for byte (tests/fixtures/lowering/tables.json,
// recorded from distributions.js before the deletion), and the engine input or the refusal of every
// scenario of the repository's specifications outside the golden sources (tests/fixtures/lowering/inputs.json;
// the golden inputs are checked by tests/core/conformance.test.js), tests/fixtures/lowering/timed.jsonc
// covering every branch of the timed lowering.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { call, initLean } from '../../src/core/lean.js';
import { engineInput } from '../../src/core/engine.js';
import { parseSpec } from '../../src/core/parse.js';
import { REPO_ROOT } from '../../tools/conformance.js';

initLean();

const fixture = (/** @type {string} */ name) => JSON.parse(fs.readFileSync(path.join(REPO_ROOT, 'tests', 'fixtures', 'lowering', name), 'utf8'));

// The Lean lowering (lower.tables) gives the pinned tables' canonical text, the unitExponential table and every recorded family's table or refusal exactly as tests/fixtures/lowering/tables.json holds them, compared as JSON text.
// @evidence lowering-in-lean-reproduces-recorded-inputs
test('tables unchanged', () => {
  const fx = fixture('tables.json');
  const r = call('lower.tables', { families: fx.families.map((/** @type {any} */ f) => ({ path: f.path, family: f.family })) });
  assert.ok(r.ok, r.ok ? '' : r.error);
  const out = r.value;
  assert.equal(out.canonical, fx.canonical, 'the pinned tables');
  assert.equal(JSON.stringify(out.unitExponential), JSON.stringify(fx.unitExponential), 'the unitExponential table');
  assert.equal(out.families.length, fx.families.length);
  fx.families.forEach((/** @type {any} */ f, /** @type {number} */ i) => {
    assert.equal(JSON.stringify(out.families[i]), JSON.stringify(f.table ?? { error: f.error }), `${f.path}: ${JSON.stringify(f.family)}`);
  });
});

// engineInput (the Lean lowering) derives the recorded engine input, or throws the recorded refusal message, for every entry of tests/fixtures/lowering/inputs.json.
// @evidence lowering-in-lean-reproduces-recorded-inputs
test('engine inputs unchanged', () => {
  const fx = fixture('inputs.json');
  /** @type {Map<string, any>} */
  const models = new Map();
  for (const e of fx.entries) {
    if (!models.has(e.spec)) models.set(e.spec, parseSpec(fs.readFileSync(path.join(REPO_ROOT, e.spec), 'utf8')).model);
    const model = models.get(e.spec);
    const what = `${e.spec} ${e.scenario} ${JSON.stringify(e.faults)}`;
    if (e.error !== undefined) {
      assert.throws(() => engineInput(model, e.scenario, e.faults), (err) => /** @type {Error} */ (err).message === e.error, what);
    } else {
      assert.deepEqual(engineInput(model, e.scenario, e.faults), e.input, what);
    }
  }
  assert.ok(fx.entries.length >= 40);
});
