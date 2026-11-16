// The simulation contract: the Rust engine reproduces every golden trace of tests/conformance
// exactly, compiled to WebAssembly (through src/core/engine.js, from the model and from the committed
// engine input alone) and as the native binary engine/target/release/exegra-sim when it is built;
// the committed engine inputs are what simulationInput derives; and the conformance runner reports a
// difference at the right step and path.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { initEngine, runScenario } from '../../src/core/engine.js';
import { simulationInput } from '../../src/core/sim-input.js';
import { SOURCES, loadModel, variantsOf } from '../../tools/record-goldens.js';
import { GOLDENS_DIR, REPO_ROOT, compareTraces, describeFailure, listGoldens, runConformance, runEngineCommand } from '../../tools/conformance.js';

initEngine();

/** The native engine binary, when it has been built (cargo build --release in engine/). */
const NATIVE = path.join(REPO_ROOT, 'engine', 'target', 'release', process.platform === 'win32' ? 'exegra-sim.exe' : 'exegra-sim');

/** @param {any} v */
const viaJson = (v) => JSON.parse(JSON.stringify(v));
/** @param {string} p */
const readJson = (p) => JSON.parse(fs.readFileSync(p, 'utf8'));

test('the WebAssembly engine reproduces every golden trace when run from the model', () => {
  let checked = 0;
  for (const [source, file] of SOURCES) {
    const model = loadModel(source, file);
    const goldens = new Map(listGoldens().filter((g) => g.source === source).map((g) => [g.name, g]));
    for (const scenario of model.byKind.scenario ?? []) {
      for (const v of variantsOf(model, scenario.id)) {
        const golden = goldens.get(v.name);
        assert.ok(golden, `no golden for ${source}/${v.name}; run node tools/record-goldens.js`);
        goldens.delete(v.name);
        const trace = runScenario(model, v.scenarioId, v.faults === undefined ? undefined : { faults: v.faults });
        assert.equal(compareTraces(readJson(golden.tracePath), trace), null, `${source}/${v.name}`);
        assert.deepEqual(viaJson(simulationInput(model, v.scenarioId, v.faults)), readJson(golden.inputPath), `${source}/${v.name} input`);
        checked++;
      }
    }
    assert.deepEqual([...goldens.keys()], [], `goldens of ${source} that no scenario produces`);
  }
  assert.ok(checked >= 50, `only ${checked} goldens checked`);
});

test('the WebAssembly engine reproduces every golden trace from the input file alone', () => {
  // Only the input files are read: no specification, no model.
  const results = runConformance();
  assert.ok(results.length >= 50);
  assert.deepEqual(results.filter((r) => r.status !== 'ok').map(describeFailure), []);
});

test('the native engine binary reproduces every golden trace', (t) => {
  if (!fs.existsSync(NATIVE)) {
    t.skip(`${path.relative(REPO_ROOT, NATIVE)} is not built (cargo build --release in engine/)`);
    return;
  }
  const command = `"${NATIVE}"`;
  const results = runConformance({ engine: (text) => runEngineCommand(command, text) });
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
