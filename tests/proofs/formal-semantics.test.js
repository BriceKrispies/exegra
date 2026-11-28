// The Lean formal semantics (formal/) is the definition of the behavior language. This file checks:
//
// - that its proofs build: `lake build` in formal/ succeeds, which type-checks the semantics and every
//   theorem of formal/Exegra/ (the behaviour calculus in Core/, Elab.lean, Format2B.lean, ProveB.lean),
//   and fails if a theorem depends on `sorryAx` or on an axiom
//   other than Lean's standard ones (the #guard_msgs checks of each file); and that no source
//   file contains `sorry`, `admit` or an `axiom` declaration;
// - that the Rust engine agrees with it: the Lean executable reproduces every golden trace, and the
//   native Rust engine and the Lean executable give identical traces on every golden input and on the
//   inputs of a fixed seed of tools/gen-engine-inputs.js (tools/differential.js); and that the calculus
//   path agrees with the legacy interpreter on them (differential.js --calculus, WG-5681).
//
// Each check skips with a message when what it needs is missing: `lake` on the PATH, the native binary
// engine/target/release/exegra-sim (cargo build --release in engine/), or the Lean executable
// formal/.lake/build/bin/exegra-lean (npm run build:formal).

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { REPO_ROOT, describeFailure, runConformance, runEngineCommand } from '../../tools/conformance.js';
import { LEAN_BIN, RUST_BIN, checkCalculus, checkInputs, fixtureInputsV2, generatedInputsV2, generatedInputsV2Int, goldenInputs, saveMismatches, DEFAULT_OUT } from '../../tools/differential.js';

const FORMAL = path.join(REPO_ROOT, 'formal');
/** The fixed seed and size of the generated part of the differential check. */
const SEED = 4685;
const COUNT = 150;

/** Every Lean source file of the formal semantics. @returns {string[]} */
function leanSources() {
  /** @type {string[]} */
  const out = [];
  /** @param {string} dir */
  const walk = (dir) => {
    for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
      if (e.name === '.lake') continue;
      const p = path.join(dir, e.name);
      if (e.isDirectory()) walk(p);
      else if (e.name.endsWith('.lean')) out.push(p);
    }
  };
  walk(FORMAL);
  return out;
}

/** Lean source with comments and string literals removed. @param {string} src */
function codeOnly(src) {
  return src
    .replace(/\/-[\s\S]*?-\//g, '')
    .replace(/--.*$/gm, '')
    .replace(/"(?:[^"\\]|\\.)*"/g, '""');
}

// Statements whose proof is still open, named so that no other sorry can slip in (none since format 1,
// and lift_agrees with it, was removed, WG-5681).
/** @type {Map<string, number>} */
const OPEN_OBLIGATIONS = new Map();

test('the Lean proofs build with no sorry and only standard axioms', (t) => {
  const probe = spawnSync('lake', ['--version'], { cwd: FORMAL, encoding: 'utf8', shell: process.platform === 'win32', windowsHide: true });
  if (probe.status !== 0) {
    t.skip('lake is not on the PATH (install elan with the toolchain in formal/lean-toolchain)');
    return;
  }
  const sources = leanSources();
  assert.ok(sources.some((p) => p.endsWith(path.join('Exegra', 'Core', 'Behav.lean'))), 'formal/Exegra/Core/Behav.lean exists');
  for (const file of sources) {
    const code = codeOnly(fs.readFileSync(file, 'utf8'));
    const open = [...OPEN_OBLIGATIONS].find(([suffix]) => file.endsWith(suffix));
    const sorries = (code.match(/\bsorry\b/g) ?? []).length;
    assert.equal(sorries, open ? open[1] : 0, `${path.relative(REPO_ROOT, file)} uses sorry ${sorries} time(s)`);
    assert.doesNotMatch(code, /\badmit\b/, `${path.relative(REPO_ROOT, file)} uses admit`);
    assert.doesNotMatch(code, /^\s*(private\s+|noncomputable\s+)*axiom\s/m, `${path.relative(REPO_ROOT, file)} declares an axiom`);
  }
  const build = spawnSync('lake', ['build'], { cwd: FORMAL, encoding: 'utf8', shell: process.platform === 'win32', windowsHide: true, maxBuffer: 1 << 26 });
  assert.equal(build.status, 0, `lake build failed:\n${String(build.stdout ?? '').slice(-4000)}${String(build.stderr ?? '').slice(-2000)}`);
  const warned = (String(build.stdout ?? '').match(/declaration uses 'sorry'/g) ?? []).length;
  assert.ok(warned <= [...OPEN_OBLIGATIONS.values()].reduce((a, b) => a + b, 0), `${warned} declarations use sorry`);
});

test('the Lean semantics reproduces every golden trace', (t) => {
  if (!fs.existsSync(LEAN_BIN)) {
    t.skip(`${path.relative(REPO_ROOT, LEAN_BIN)} is not built (npm run build:formal)`);
    return;
  }
  const command = `"${LEAN_BIN}"`;
  const results = runConformance({ engine: (text) => runEngineCommand(command, text) });
  assert.ok(results.length >= 50);
  assert.deepEqual(results.filter((r) => r.status !== 'ok').map(describeFailure), []);
});

test('the Rust engine and the Lean semantics agree on the goldens and on generated inputs', (t) => {
  for (const [bin, how] of [[RUST_BIN, 'cargo build --release in engine/'], [LEAN_BIN, 'npm run build:formal']]) {
    if (!fs.existsSync(bin)) {
      t.skip(`${path.relative(REPO_ROOT, bin)} is not built (${how})`);
      return;
    }
  }
  const gen = generatedInputsV2Int(SEED, COUNT);
  const result = checkInputs({ inputs: [...goldenInputs(), ...gen.inputs] });
  const files = saveMismatches(result.mismatches, DEFAULT_OUT);
  assert.ok(result.checked >= 50 + COUNT);
  // The generated inputs must exercise every fault kind, timers and replies.
  for (const key of ['calculus fault drop-event', 'calculus fault delay-event', 'calculus fault enable-transition', 'calculus fault disable-transition', 'calculus fault inject-event', 'calculus timer', 'calculus reply']) {
    assert.ok((gen.coverage[key] ?? 0) > 0, `the generated inputs do not cover ${key}`);
  }
  for (const key of ['outcome quiescent', 'step drop', 'step delay', 'fault effect injected']) {
    assert.ok((result.traceCoverage[key] ?? 0) > 0, `the traces do not cover ${key}`);
  }
  assert.deepEqual(result.mismatches.map((m) => `${m.name}: ${m.detail}`), [], files.length ? `mismatching inputs saved under ${DEFAULT_OUT}` : undefined);
});

test('the calculus path agrees with the legacy interpreter and the Rust engine (differential --calculus)', (t) => {
  if (!fs.existsSync(LEAN_BIN)) {
    t.skip(`${path.relative(REPO_ROOT, LEAN_BIN)} is not built (npm run build:formal)`);
    return;
  }
  const inputs = [...goldenInputs(), ...fixtureInputsV2(), ...generatedInputsV2Int(SEED, COUNT).inputs];
  const r = checkCalculus(inputs, LEAN_BIN, fs.existsSync(RUST_BIN) ? RUST_BIN : null);
  process.stdout.write(`calculus: ${inputs.length} inputs, ${r.counts.compared} compared, ${r.counts.refused} refused, ${r.counts.legacy} on the legacy path
`);
  assert.ok(r.counts.compared >= 50 + COUNT / 3, `only ${r.counts.compared} inputs compared`);
  assert.deepEqual(r.mismatches.map((m) => `${m.name}: ${m.detail}`), []);
});

test('the Rust engine and the Lean semantics agree on generated version-2 inputs, workloads and metrics included', (t) => {
  for (const [bin, how] of [[RUST_BIN, 'cargo build --release in engine/'], [LEAN_BIN, 'npm run build:formal']]) {
    if (!fs.existsSync(bin)) {
      t.skip(`${path.relative(REPO_ROOT, bin)} is not built (${how})`);
      return;
    }
  }
  const gen = generatedInputsV2(SEED, 60);
  const result = checkInputs({ inputs: gen.inputs });
  const files = saveMismatches(result.mismatches, DEFAULT_OUT);
  for (const key of ['v2 workload poisson', 'v2 workload constant', 'v2 workload phase ramp', 'v2 workload repeat', 'v2 workload clients uniform', 'v2 workload clients round-robin', 'v2 workload payload', 'v2 workload fault delay', 'v2 workload fault drop', 'v2 workload metrics']) {
    assert.ok((gen.coverage[key] ?? 0) > 0, `the generated inputs do not cover ${key}`);
  }
  assert.ok((result.traceCoverage['trace with metrics'] ?? 0) > 0, 'no trace reports metrics');
  assert.deepEqual(result.mismatches.map((m) => `${m.name}: ${m.detail}`), [], files.length ? `mismatching inputs saved under ${DEFAULT_OUT}` : undefined);
});
