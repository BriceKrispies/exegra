// The simulation contract: the engine Exegra runs, the Lean core compiled to WebAssembly (through
// src/core/engine.js and src/core/lean.js), reproduces every golden trace of tests/conformance exactly,
// from the model and from the committed engine input alone; the Rust engine, kept as a differential
// oracle, reproduces them too and gives byte-identical traces, as WebAssembly (src/engine/pkg) and as
// the native binary engine/target/release/exegra-sim when they are built, except the goldens of
// tests/conformance/expected-differences.json (the Rust oracle computes untyped numbers as doubles, the
// Lean engine as exact rationals, WG-5683); the committed engine inputs are what engineInput derives;
// and the conformance runner reports a difference at the right step and path.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { initEngine, runEngineText, runScenario } from '../../src/core/engine.js';
import { rustEngineBuilt, runRustEngineText } from '../../tools/rust-engine.js';
import { engineInput } from '../../src/core/engine.js';
import { SOURCES, loadModel, variantsOf } from '../../tools/record-goldens.js';
import { expectedDifferences } from '../../tools/differential.js';
import { ELAB_REFUSAL, GOLDENS_DIR, REPO_ROOT, compareTraces, describeFailure, goldenChanges, listGoldens, runConformance, runEngineCommand } from '../../tools/conformance.js';

initEngine();

/** The native engine binary, when it has been built (cargo build --release in engine/). */
const NATIVE = path.join(REPO_ROOT, 'engine', 'target', 'release', process.platform === 'win32' ? 'exegra-sim.exe' : 'exegra-sim');

/** The goldens the Rust oracle is held to: not refused, and not an expected difference. */
const rustGoldens = () => {
  const exp = expectedDifferences();
  return listGoldens().filter((g) => !g.refused && !exp[`golden ${g.source}/${g.name}`]);
};

/** @param {any} v */
const viaJson = (v) => JSON.parse(JSON.stringify(v));
/** @param {string} p */
const readJson = (p) => JSON.parse(fs.readFileSync(p, 'utf8'));

test('the Lean WebAssembly engine reproduces every golden trace when run from the model', () => {
  let checked = 0;
  for (const [source, file] of SOURCES) {
    const model = loadModel(source, file);
    const goldens = new Map(listGoldens().filter((g) => g.source === source).map((g) => [g.name, g]));
    for (const scenario of model.byKind.scenario ?? []) {
      for (const v of variantsOf(model, scenario.id)) {
        const golden = goldens.get(v.name);
        assert.ok(golden, `no golden for ${source}/${v.name}; run node tools/record-goldens.js`);
        goldens.delete(v.name);
        const run = () => runScenario(model, v.scenarioId, v.faults === undefined ? undefined : { faults: v.faults });
        // A golden without a trace is an input the engine refuses as ill-typed or non-integer (WG-5681).
        if (golden.refused) assert.throws(run, (/** @type {any} */ e) => ELAB_REFUSAL.test(e.message), `${source}/${v.name} is refused`);
        else assert.equal(compareTraces(readJson(golden.tracePath), run()), null, `${source}/${v.name}`);
        assert.deepEqual(viaJson(engineInput(model, v.scenarioId, v.faults)), readJson(golden.inputPath), `${source}/${v.name} input`);
        checked++;
      }
    }
    assert.deepEqual([...goldens.keys()], [], `goldens of ${source} that no scenario produces`);
  }
  assert.ok(checked >= 50, `only ${checked} goldens checked`);
});

test('the Lean WebAssembly engine reproduces every golden trace from the input file alone', () => {
  // Only the input files are read: no specification, no model.
  const results = runConformance();
  assert.ok(results.length >= 50);
  assert.deepEqual(results.filter((r) => r.status !== 'ok').map(describeFailure), []);
});

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

test('the runner reports an altered trace as a mismatch with the right step and path', () => {
  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-conformance-'));
  try {
    const dir = path.join(tmp, 'fixture');
    fs.mkdirSync(dir);
    for (const f of ['core-flow.input.json', 'core-flow.trace.json']) fs.copyFileSync(path.join(GOLDENS_DIR, 'fixture', f), path.join(dir, f));
    const tracePath = path.join(dir, 'core-flow.trace.json');
    const trace = readJson(tracePath);
    trace.steps[1].fired[0].emitted[0].time += 1;
    trace.steps[5].time += 1; // a later difference is not the first
    fs.writeFileSync(tracePath, JSON.stringify(trace));

    const [result] = runConformance({ goldens: listGoldens(tmp) });
    assert.equal(result.status, 'mismatch');
    assert.equal(result.difference?.step, 1);
    assert.equal(result.difference?.path, '$.steps[1].fired[0].emitted[0].time');
    assert.match(describeFailure(result), /core-flow: first difference at step 1, \$\.steps\[1\]\.fired\[0\]\.emitted\[0\]\.time/);

    // A difference outside the steps has no step index.
    trace.steps = readJson(path.join(GOLDENS_DIR, 'fixture', 'core-flow.trace.json')).steps;
    trace.outcome = 'error';
    fs.writeFileSync(tracePath, JSON.stringify(trace));
    const [other] = runConformance({ goldens: listGoldens(tmp) });
    assert.equal(other.difference?.step, null);
    assert.equal(other.difference?.path, '$.outcome');

    // An engine that fails is an error, not a pass.
    const [failing] = runConformance({ goldens: listGoldens(tmp), engine: () => { throw new Error('boom'); } });
    assert.equal(failing.status, 'error');
  } finally {
    fs.rmSync(tmp, { recursive: true, force: true });
  }
});

test('golden changes are exactly the manifest', (t) => {
  // tests/conformance/golden-changes.json (WG-5681, criterion 22): every golden that differs from its
  // version at the base commit, with its class; strip(version-2 trace) = version-1 trace for the shape change.
  const manifest = readJson(path.join(REPO_ROOT, 'tests', 'conformance', 'golden-changes.json'));
  let changes;
  try {
    changes = goldenChanges(manifest.base);
  } catch (e) {
    t.skip(`${/** @type {Error} */ (e).message} (a shallow checkout; the Check workflow fetches the history)`);
    return;
  }
  assert.deepEqual(changes, manifest.changes);
  const counts = /** @type {Record<string, number>} */ ({});
  for (const c of Object.values(changes)) counts[c] = (counts[c] ?? 0) + 1;
  assert.equal(Object.keys(changes).length, listGoldens().length, 'every golden changed (version 1 to version 2)');
  // The exegra goldens changed again on purpose after WG-5681: the composition root of the multiscale work (WG-5692)
  // re-addressed behaviours, and the two-session-write event (WG-5720) joined every exegra input; the two-session
  // edit race is a new golden. Re-subjecting workspace-flow (WG-5728) edited the source-edit-flow input as well, and the
  // save path speaking the persistence client's interface (WG-5729) re-recorded write-with-stale-base-hash.
  assert.deepEqual(counts, { 'version 2': 43, 'input re-recorded, trace equal under strip': 31, 'trace removed (refused)': 2, 'input edited, trace re-recorded': 12, added: 1 });
});
