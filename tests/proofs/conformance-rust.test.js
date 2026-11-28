// The Rust engine, kept as a differential oracle, reproduces every golden trace of tests/conformance and gives
// byte-identical traces to the Lean engine, as WebAssembly (src/engine/pkg) and as the native binary
// engine/target/release/exegra-sim when they are built, except the goldens of tests/conformance/expected-differences.json
// (WG-5683). These runs re-check one engine against another, so they live with the proof re-checks (npm run test:proofs,
// npm run verify, the Check workflow), not in the routine suite.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { initEngine, runEngineText } from '../../src/core/engine.js';
import { rustEngineBuilt, runRustEngineText } from '../../tools/rust-engine.js';
import { expectedDifferences } from '../../tools/differential.js';
import { REPO_ROOT, describeFailure, listGoldens, runConformance, runEngineCommand } from '../../tools/conformance.js';

initEngine();

/** The native engine binary, when it has been built (cargo build --release in engine/). */
const NATIVE = path.join(REPO_ROOT, 'engine', 'target', 'release', process.platform === 'win32' ? 'exegra-sim.exe' : 'exegra-sim');

/** The goldens the Rust oracle is held to: not refused, and not an expected difference. */
const rustGoldens = () => {
  const exp = expectedDifferences();
  return listGoldens().filter((g) => !g.refused && !exp[`golden ${g.source}/${g.name}`]);
};

test('the Rust WebAssembly engine reproduces every golden trace and agrees with the Lean engine byte for byte', (t) => {
  if (!rustEngineBuilt()) {
    t.skip('src/engine/pkg is not built (npm run build:engine)');
    return;
  }
  // The Rust engine does not mirror static typing: the goldens the Lean engine refuses are left out.
  const results = runConformance({ goldens: rustGoldens(), engine: (text) => JSON.parse(runRustEngineText(text)) });
  assert.ok(results.length >= 50);
  assert.deepEqual(results.filter((r) => r.status !== 'ok').map(describeFailure), []);
  const differ = [];
  for (const g of rustGoldens()) {
    const text = fs.readFileSync(g.inputPath, 'utf8');
    if (runRustEngineText(text) !== runEngineText(text)) differ.push(g.name);
  }
  assert.deepEqual(differ, []);
});

test('the native Rust engine binary reproduces every golden trace', (t) => {
  if (!fs.existsSync(NATIVE)) {
    t.skip(`${path.relative(REPO_ROOT, NATIVE)} is not built (cargo build --release in engine/)`);
    return;
  }
  const command = `"${NATIVE}"`;
  const results = runConformance({ goldens: rustGoldens(), engine: (text) => runEngineCommand(command, text) });
  assert.ok(results.length >= 50);
  assert.deepEqual(results.filter((r) => r.status !== 'ok').map(describeFailure), []);
});

test('the Lean WebAssembly engine reproduces every golden trace from the input file alone', () => {
  // Only the input files are read: no specification, no model.
  const results = runConformance();
  assert.ok(results.length >= 50);
  assert.deepEqual(results.filter((r) => r.status !== 'ok').map(describeFailure), []);
});
