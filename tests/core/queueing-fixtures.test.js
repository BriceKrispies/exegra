// Queueing-theory fixtures of format 2 (WG-4715; docs/simulation.md, "Fixtures"): the M/M/1
// fixture of tests/fixtures/queueing/mm1.json reproduces its analytic utilisation and mean waiting
// time by approx metric claims over 59 seeded runs, and each claim's twin, a fault of the base
// input (set-capacity 2: two servers; replace-demand with a constant service: M/D/1), must fail it.
// The results are model results (model-holds), never verified, and test the engine, the metrics
// and the claim method, not any system.
//
// The fixture is stated at the engine-input level. Each claim takes 59 runs of a 90 s horizon at
// 800 arrivals per second for the base and as many for its twin (236 runs, about 150,000 steps
// each), which is beyond the routine suite's budget, so the test runs only with
// EXEGRA_FIXTURES=1. It uses the native Lean engine
// (formal/.lake/build/bin/exegra-lean, npm run build:formal, the same C as the Lean WebAssembly
// engine) when built, else the native Rust engine (engine/target/release/exegra-sim), else the
// WebAssembly engine.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { REPO_ROOT } from '../../tools/conformance.js';
import { LEAN_BIN, RUST_BIN, runBinary } from '../../tools/differential.js';
import { lowerInput, withFaults } from '../fixtures/queueing/inputs.js';
import { evaluateMetricClaim, metricVerdict } from '../../src/core/metric-claims.js';
import { initEngine, runEngineText } from '../../src/core/engine.js';

const FIXTURE = path.join(REPO_ROOT, 'tests', 'fixtures', 'queueing', 'mm1.json');

test('M/M/1 fixture: utilisation and mean wait hold in the model, and their twins fail', { skip: process.env.EXEGRA_FIXTURES !== '1' && 'set EXEGRA_FIXTURES=1 to run the queueing fixtures' }, async (t) => {
  const fx = JSON.parse(fs.readFileSync(FIXTURE, 'utf8'));
  /** @type {(text: string) => any} */
  let run;
  // The native Lean engine is compiled from the same C as the Lean WebAssembly engine and runs it
  // about twice as fast; the native Rust engine is the fallback, the WebAssembly engine the last resort.
  const native = [LEAN_BIN, RUST_BIN].find((bin) => fs.existsSync(bin));
  if (native) {
    run = (text) => {
      const r = runBinary(native, text);
      if (!r.ok) throw new Error(r.refusal);
      return r.trace;
    };
  } else {
    await initEngine();
    run = (text) => JSON.parse(runEngineText(text));
  }
  // The claims share the base scenario and its seeds: a run of an input text already run is
  // answered from the first run (the engine is deterministic), so each distinct run happens once.
  const engineRun = run;
  /** @type {Map<string, any>} */
  const done = new Map();
  run = (text) => {
    if (!done.has(text)) done.set(text, engineRun(text));
    return done.get(text);
  };
  const base = lowerInput(fx.base);
  for (const c of fx.claims) {
    const negatives = c.negatives.map((/** @type {{faults: string[]}} */ v) => withFaults(base, v.faults));
    const result = evaluateMetricClaim(run, { scenarios: [base], negatives }, { ...c, runs: fx.runs, fraction: fx.fraction, confidence: fx.confidence, seed: fx.seed });
    const s = result.scenarios[0];
    const verdict = metricVerdict(result);
    const show = (/** @type {any} */ x) => JSON.stringify(x, (_, v) => (typeof v === 'bigint' ? String(v) : v));
    const dec = (/** @type {any} */ r) => (r && typeof r === 'object' ? (Number(r.n) / Number(r.d)).toFixed(4) : String(r));
    t.diagnostic(`${c.id}: ${verdict.label}; base ${s.verdict} over ${s.kept}/${s.runs} runs, interval [${dec(s.interval?.lo)}, ${dec(s.interval?.hi)}] (ranks ${s.interval?.j}), spread ${dec(s.spread?.min)} / ${dec(s.spread?.median)} / ${dec(s.spread?.max)}; twin ${result.negatives[0].verdict}, interval [${dec(result.negatives[0].interval?.lo)}, ${dec(result.negatives[0].interval?.hi)}]`);
    void show;
    assert.equal(s.runs, 59, `${c.id}: 59 runs`);
    assert.equal(s.truncated, 0, `${c.id}: no truncated run`);
    assert.equal(result.negatives[0].verdict, 'fails', `${c.id}: its twin fails`);
    assert.equal(verdict.label, 'model-holds', `${c.id}: ${verdict.strength}; interval ${JSON.stringify(s.interval, (_, v) => (typeof v === 'bigint' ? String(v) : v))}`);
  }
});
