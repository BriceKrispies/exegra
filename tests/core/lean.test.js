// The Lean call boundary (src/core/lean.js over formal/Exegra/Api.lean compiled to WebAssembly):
// the registry lists its functions; errors are values (an unknown function, a malformed request and
// arguments the function refuses each come back as {ok: false, error}); and engine.run returns the
// trace that src/core/engine.js returns for the same input. Needs `npm run build:formal-wasm`.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { call, callText, initLean, leanFunctions, leanReady } from '../../src/core/lean.js';
import { runEngineText } from '../../src/core/engine.js';
import { GOLDENS_DIR } from '../../tools/conformance.js';

initLean();

// Calls through src/core/lean.js: the registry lists engine.run, an unknown function, a malformed request and refused arguments come back as errors, and a run returns the trace the engine returns.
// @evidence lean-boundary-errors-are-values #
test('the Lean core loads synchronously in Node and lists its registered functions', () => {
  assert.equal(leanReady(), true);
  const names = leanFunctions().map((f) => f.name);
  for (const n of ['engine.run', 'engine.explore', 'engine.temporal', 'api.functions']) assert.ok(names.includes(n), n);
  assert.equal(new Set(names).size, names.length);
});

test('errors are values: unknown function, malformed arguments, refused input', () => {
  assert.deepEqual(call('no.such.function', {}), { ok: false, error: 'unknown function "no.such.function"' });
  const notJson = callText('engine.run', '{"version": ');
  assert.equal(notJson.ok, false);
  assert.match(/** @type {any} */ (notJson).error, /^the input is not JSON/);
  const refused = call('engine.run', { format: 'exegra-sim-input', version: 1 });
  assert.equal(refused.ok, false);
  assert.ok(/** @type {any} */ (refused).error.length > 0);
  const explore = call('engine.explore', []);
  assert.deepEqual(explore, { ok: false, error: 'explore: the request must be an object' });
  // The boundary still answers after errors.
  assert.ok(leanFunctions().length >= 4);
});

test('engine.run returns the trace of the engine facade, and a call with parsed arguments the same', () => {
  const input = fs.readFileSync(path.join(GOLDENS_DIR, 'fixture', 'core-flow.input.json'), 'utf8');
  const viaText = callText('engine.run', input);
  assert.ok(viaText.ok);
  assert.equal(/** @type {any} */ (viaText).text, runEngineText(input));
  const viaValue = call('engine.run', JSON.parse(input));
  assert.ok(viaValue.ok);
  assert.deepEqual(/** @type {any} */ (viaValue).value, JSON.parse(runEngineText(input)));
});
