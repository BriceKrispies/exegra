// The pool-classes-under-flood fixture of format 2 (WG-4729; docs/simulation.md, "Fixtures"):
// tests/fixtures/queueing/pool-flood.json states, at the engine-input level, a database pool with
// request classes in front of shared I/O channels under a page-read flood. The claim (the p99 of
// the database leg of a move within 30 ms over the flood window) must hold in the base (flood) and
// the control (no flood) over 59 seeded runs each; each twin, a fault of the base (collapse-classes
// on the pool; the page-read limit raised to 12), must fail it, and the same fault on the control
// must still hold. The results are model results (model-holds), never verified, and test the
// engine, the metrics and the claim method, not any system.
//
// Six scenario evaluations of 59 runs each are beyond the routine suite's budget, so the test runs
// only with EXEGRA_FIXTURES=1. It uses the native Lean engine (formal/.lake/build/bin/exegra-lean,
// npm run build:formal, the same C as the Lean WebAssembly engine) when built, else the native Rust
// engine (engine/target/release/exegra-sim), else the WebAssembly engine.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { REPO_ROOT } from '../../tools/conformance.js';
import { LEAN_BIN, RUST_BIN, runBinary } from '../../tools/differential.js';
import { evaluateMetricClaim, metricVerdict } from '../../src/core/metric-claims.js';
import { initEngine, runEngineText } from '../../src/core/engine.js';
import { changed, lowerInput, withFaults } from '../fixtures/queueing/inputs.js';

const FIXTURE = path.join(REPO_ROOT, 'tests', 'fixtures', 'queueing', 'pool-flood.json');

test('pool under flood: the move leg holds in base and control, and every twin fails', { skip: process.env.EXEGRA_FIXTURES !== '1' && 'set EXEGRA_FIXTURES=1 to run the pool fixture' }, async (t) => {
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
  const base = lowerInput(fx.base);
  const control = changed(base, fx.control);
  const dec = (/** @type {any} */ r) => (r && typeof r === 'object' ? (Number(r.n) / Number(r.d)).toFixed(0) : String(r));
  const show = (/** @type {string} */ what, /** @type {any} */ s) =>
    `${what} ${s.verdict} (${s.passes ?? s.k ?? '?'}/${s.kept}/${s.runs}), spread ${dec(s.spread?.min)} / ${dec(s.spread?.median)} / ${dec(s.spread?.max)}`;
  for (const c of fx.claims) {
    const negatives = c.negatives.map((/** @type {{faults: string[]}} */ v) => withFaults(base, v.faults));
    const controlNegatives = c.controlNegatives.map((/** @type {{faults: string[]}} */ v) => withFaults(control, v.faults));
    const result = evaluateMetricClaim(run, { scenarios: [base, control], negatives, controlNegatives },
      { ...c, runs: fx.runs, fraction: fx.fraction, confidence: fx.confidence, seed: fx.seed });
    const verdict = metricVerdict(result);
    t.diagnostic(`${c.id}: ${verdict.label} (${verdict.strength})`);
    result.scenarios.forEach((s, i) => t.diagnostic(show(i ? 'control' : 'base', s)));
    result.negatives.forEach((s, i) => t.diagnostic(show(`twin ${c.negatives[i].faults}`, s)));
    result.controlNegatives.forEach((s, i) => t.diagnostic(show(`control with ${c.controlNegatives[i].faults}`, s)));
    for (const s of result.scenarios) assert.equal(s.truncated, 0, `${c.id}: no truncated run`);
    for (const s of result.negatives) assert.equal(s.verdict, 'fails', `${c.id}: every twin fails`);
    for (const s of result.controlNegatives) assert.equal(s.verdict, 'holds', `${c.id}: every twin's fault holds on the control`);
    assert.equal(verdict.label, 'model-holds', `${c.id}: ${verdict.strength}`);
  }
});
