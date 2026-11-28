// The simulation contract: the engine Exegra runs, the Lean core compiled to WebAssembly (through
// src/core/engine.js and src/core/lean.js), reproduces every golden trace of tests/conformance exactly,
// from the model and from the committed engine input alone (the Rust differential oracle runs in
// tests/proofs/conformance-rust.test.js); the committed engine inputs are what engineInput derives; and the conformance
// runner reports a difference at the right step and path.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { initEngine, runScenario, engineInput } from '../../src/core/engine.js';
import { SOURCES, loadModel, variantsOf } from '../../tools/record-goldens.js';
import { ELAB_REFUSAL, GOLDENS_DIR, REPO_ROOT, compareTraces, describeFailure, goldenChanges, listGoldens, runConformance } from '../../tools/conformance.js';

initEngine();

/** @param {any} v */
const viaJson = (v) => JSON.parse(JSON.stringify(v));
/** @param {string} p */
const readJson = (p) => JSON.parse(fs.readFileSync(p, 'utf8'));

// The WebAssembly engine reproduces every golden trace from the model and from the committed engine input alone, simulationInput derives the committed inputs, and the conformance runner reports an altered trace at the right step and path.
// @evidence simulation-contract-pinned #
// Every golden input is what engineInput derives from its source specification, and the engine reproduces its trace when run from the model.
// @evidence lowering-in-lean-reproduces-recorded-inputs
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
