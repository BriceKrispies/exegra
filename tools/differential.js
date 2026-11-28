#!/usr/bin/env node
// Differential check of the Rust engine against the Lean formal semantics. Node-only.
//
//   node tools/differential.js [--seed <n>] [--count <n>] [--goldens] [--out <dir>]
//                              [--lift] [--rust <binary>] [--lean <binary>]
//   node tools/differential.js --calculus [--seed <n>] [--count <n>] [--lean <binary>] [--rust <binary>]
//
// Generates --count version-2 inputs in the integer fragment of the behaviour calculus and --count
// version-2 inputs of every construct from --seed with tools/gen-engine-inputs.js (and, with --goldens,
// adds every golden input of tests/conformance/goldens), runs each through the native Rust engine
// (engine/target/release/exegra-sim) and the Lean executable (formal/.lake/build/bin/exegra-lean), and
// compares the two traces as tools/conformance.js compares a trace with a golden: as JSON values, key
// order ignored, numbers by value. Inputs the Lean elaborator refuses (ill-typed, a number that is not an
// integer) are counted, not compared. With --lift, every golden's version-2 trace, stripped of the
// version-2 fields, is compared with its version-1 trace at the base commit of
// tests/conformance/golden-changes.json (format 1 is gone, WG-5681); the goldens that differ must be
// exactly the manifest's. Two refusals agree when their messages agree (for input that is not
// JSON, only that both say so). Reports the count, the seed, the construct coverage of the generated
// inputs and of the traces, and every mismatch; each mismatching input is saved to --out (default
// test-results/differential/). Exit code 0 when everything agrees, 1 on any mismatch, 2 on a usage error
// or a missing binary.
//
// With --calculus (WG-5681): the inputs are every golden (all version 2), every version-2 fixture under
// tests/fixtures and --count generated version-2 inputs in the integer fragment of the behaviour calculus
// (gen-engine-inputs.js, generateInputsV2Int). Each is run by the Lean engine, which runs inputs the
// elaborator accepts on the calculus scheduler, and by `exegra-lean --legacy`, the legacy interpreter; the
// two traces must agree. When the Rust engine is built, its trace must agree with the Lean engine's too.
// Inputs the elaborator refuses (ill-typed, non-integer) or runs on the legacy path (outside the fragment)
// are counted, not compared. Inputs listed in tests/conformance/expected-differences.json may
// differ and are reported, not failed, when they do.

import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { ELAB_REFUSAL, REPO_ROOT, compareTraces, goldenChanges, listGoldens } from './conformance.js';
import { formatCoverage, generateInputsV2, generateInputsV2Int } from './gen-engine-inputs.js';

const EXE = process.platform === 'win32' ? '.exe' : '';
/** The native engine binary (cargo build --release in engine/). */
export const RUST_BIN = path.join(REPO_ROOT, 'engine', 'target', 'release', `exegra-sim${EXE}`);
/** The Lean executable (npm run build:formal). */
export const LEAN_BIN = path.join(REPO_ROOT, 'formal', '.lake', 'build', 'bin', `exegra-lean${EXE}`);
export const DEFAULT_OUT = path.join(REPO_ROOT, 'test-results', 'differential');

/**
 * @typedef {{ok: true, trace: any} | {ok: false, refusal: string}} EngineResult
 * @typedef {{name: string, inputText: string, rust: EngineResult, lean: EngineResult, detail: string}} Mismatch
 * @typedef {{name: string, text: string}} NamedInput
 */

/**
 * Run an engine binary on one input: the trace, or the refusal message without the program prefix.
 * @param {string} bin @param {string} inputText @param {string[]} [args]
 * @returns {EngineResult}
 */
export function runBinary(bin, inputText, args = []) {
  const r = spawnSync(bin, args, { input: inputText, encoding: 'utf8', maxBuffer: 1 << 29, windowsHide: true });
  if (r.error) throw new Error(`could not run ${bin}: ${r.error.message}`);
  if (r.status !== 0) {
    const msg = String(r.stderr ?? '').trim().replace(/^exegra-(sim|lean): /, '');
    return { ok: false, refusal: msg || `exit status ${r.status}` };
  }
  try {
    return { ok: true, trace: JSON.parse(r.stdout) };
  } catch (e) {
    return { ok: false, refusal: `output is not JSON: ${/** @type {Error} */ (e).message}` };
  }
}

/** Refusals agree when their messages agree; JSON syntax errors only by their common prefix. */
const NOT_JSON = 'the input is not JSON:';
/** @param {string} a @param {string} b */
const sameRefusal = (a, b) => (a.startsWith(NOT_JSON) && b.startsWith(NOT_JSON)) || a === b;

/**
 * Compare the two engines' results on one input; null when they agree.
 * @param {EngineResult} rust @param {EngineResult} lean
 * @returns {string|null}
 */
export function compareResults(rust, lean) {
  if (rust.ok && lean.ok) {
    const d = compareTraces(rust.trace, lean.trace);
    if (!d) return null;
    const show = (/** @type {any} */ v) => (v === undefined ? '(absent)' : JSON.stringify(v).slice(0, 200));
    return `first difference ${d.step === null ? 'outside the steps' : `at step ${d.step}`}, ${d.path}: Rust ${show(d.expected)}, Lean ${show(d.actual)}`;
  }
  if (!rust.ok && !lean.ok) return sameRefusal(rust.refusal, lean.refusal) ? null : `different refusals: Rust "${rust.refusal}", Lean "${lean.refusal}"`;
  if (!rust.ok) return `Rust refused ("${rust.refusal}"), Lean returned a trace`;
  return `Lean refused ("${/** @type {{refusal: string}} */ (lean).refusal}"), Rust returned a trace`;
}

/**
 * Construct coverage observed in a trace: outcomes, step kinds, fault effects, ignored reasons, error
 * messages by kind.
 * @param {any} trace @param {Record<string, number>} cov
 */
export function traceCoverage(trace, cov) {
  const add = (/** @type {string} */ k) => { cov[k] = (cov[k] ?? 0) + 1; };
  add(`outcome ${trace.outcome}`);
  if (trace.metrics) add("trace with metrics");
  for (const st of trace.steps ?? []) {
    add(`step ${st.kind}`);
    if (st.fired.length) add('step with fired transitions');
    if (st.fired.length > 1) add('step with several fired transitions');
    for (const f of st.fired) {
      if (f.sets.length) add('fired with sets');
      if (f.emitted.length) add('fired with emits');
    }
    for (const i of st.ignored) add(`ignored ${i.reason}`);
    for (const f of st.faults) add(`fault effect ${f.effect}`);
    if (st.event.source.kind === 'transition') add('delivered emitted event');
    for (const r of st.resources ?? []) add(`resource ${r.action}${r.reason ? ` ${r.reason}` : ''}`);
    if (st.draws?.length) add('step with draws');
    if (st.event.routes) add('routed entry');
    if (st.error) add(`error ${String(st.error.message).replace(/"[^"]*"/g, '"…"').replace(/'.'/g, "'…'")}`);
  }
}

/**
 * Check a set of inputs on both engines.
 * @param {{inputs: NamedInput[], rustBin?: string, leanBin?: string}} opts
 * @returns {{checked: number, mismatches: Mismatch[], traceCoverage: Record<string, number>}}
 */
export function checkInputs(opts) {
  const rustBin = opts.rustBin ?? RUST_BIN;
  const leanBin = opts.leanBin ?? LEAN_BIN;
  /** @type {Mismatch[]} */
  const mismatches = [];
  /** @type {Record<string, number>} */
  const cov = {};
  for (const { name, text } of opts.inputs) {
    const lean = runBinary(leanBin, text);
    // An input the Lean elaborator refuses (ill-typed, a number that is not an integer) is counted,
    // not compared: the Rust engine does not mirror the static typing (WG-5681).
    if (!lean.ok && ELAB_REFUSAL.test(lean.refusal)) { cov['elaboration refusal'] = (cov['elaboration refusal'] ?? 0) + 1; continue; }
    const rust = runBinary(rustBin, text);
    if (rust.ok) traceCoverage(rust.trace, cov);
    else cov.refusal = (cov.refusal ?? 0) + 1;
    const detail = compareResults(rust, lean);
    if (detail) mismatches.push({ name, inputText: text, rust, lean, detail });
  }
  return { checked: opts.inputs.length, mismatches, traceCoverage: cov };
}

/**
 * The golden inputs as named inputs.
 * @returns {NamedInput[]}
 */
export function goldenInputs() {
  return listGoldens().map((g) => ({ name: `golden ${g.source}/${g.name}`, text: fs.readFileSync(g.inputPath, 'utf8') }));
}

/**
 * Generated version-2 inputs in the integer fragment of the behaviour calculus, as named inputs.
 * @param {number} seed @param {number} count
 * @returns {{inputs: NamedInput[], coverage: Record<string, number>}}
 */
export function generatedInputsV2Int(seed, count) {
  const { inputs, coverage } = generateInputsV2Int(seed, count);
  return { inputs: inputs.map((input, i) => ({ name: `seed ${seed} integer input ${i}`, text: JSON.stringify(input) })), coverage };
}

/**
 * Generated version-2 inputs as named inputs.
 * @param {number} seed @param {number} count
 * @returns {{inputs: NamedInput[], coverage: Record<string, number>}}
 */
export function generatedInputsV2(seed, count) {
  const { inputs, coverage } = generateInputsV2(seed, count);
  return { inputs: inputs.map((input, i) => ({ name: `seed ${seed} v2 input ${i}`, text: JSON.stringify(input) })), coverage };
}

/**
 * Save each mismatching input (and both results) to a directory. Returns the files written.
 * @param {Mismatch[]} mismatches @param {string} dir
 * @returns {string[]}
 */
export function saveMismatches(mismatches, dir) {
  if (!mismatches.length) return [];
  fs.mkdirSync(dir, { recursive: true });
  return mismatches.map((m) => {
    const base = m.name.replace(/[^A-Za-z0-9_-]+/g, '-');
    const file = path.join(dir, `${base}.input.json`);
    fs.writeFileSync(file, m.inputText.endsWith('\n') ? m.inputText : `${m.inputText}\n`);
    fs.writeFileSync(path.join(dir, `${base}.result.json`), `${JSON.stringify({ detail: m.detail, rust: m.rust, lean: m.lean }, null, 1)}\n`);
    return file;
  });
}

/** The version-2 fixtures under tests/fixtures (a file holding an engine input, or one under `base`). @returns {NamedInput[]} */
export function fixtureInputsV2() {
  /** @type {NamedInput[]} */
  const out = [];
  const walk = (/** @type {string} */ dir) => {
    for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
      const p = path.join(dir, e.name);
      if (e.isDirectory()) walk(p);
      else if (e.name.endsWith('.json')) {
        let j;
        try { j = JSON.parse(fs.readFileSync(p, 'utf8')); } catch { continue; }
        const input = j?.format === 'exegra-sim-input' ? j : j?.base?.format === 'exegra-sim-input' ? j.base : null;
        if (input?.version === 2) out.push({ name: `fixture ${path.relative(REPO_ROOT, p).split(path.sep).join('/')}`, text: JSON.stringify(input) });
      }
    }
  };
  walk(path.join(REPO_ROOT, 'tests', 'fixtures'));
  return out;
}

/** The expected differences of the calculus path (tests/conformance/expected-differences.json), by input name. */
export function expectedDifferences() {
  const file = path.join(REPO_ROOT, 'tests', 'conformance', 'expected-differences.json');
  if (!fs.existsSync(file)) return {};
  return JSON.parse(fs.readFileSync(file, 'utf8')).differences ?? {};
}

/**
 * The calculus check: the Lean engine (the calculus scheduler for elaborated inputs) against the legacy
 * interpreter, and against the Rust engine when given.
 * @param {NamedInput[]} inputs @param {string} leanBin @param {string|null} rustBin
 */
export function checkCalculus(inputs, leanBin, rustBin) {
  /** @type {Mismatch[]} */
  const mismatches = [];
  /** @type {string[]} */
  const expected = [];
  const counts = { compared: 0, refused: 0, legacy: 0 };
  const exp = expectedDifferences();
  for (const { name, text } of inputs) {
    const lean = runBinary(leanBin, text);
    if (lean.ok && lean.trace.semantics === 'legacy') { counts.legacy++; continue; }
    if (!lean.ok && ELAB_REFUSAL.test(lean.refusal)) {
      counts.refused++;
      if (exp[name]) expected.push(name);
      continue;
    }
    counts.compared++;
    const legacy = runBinary(leanBin, text, ['--legacy']);
    let detail = compareResults(legacy, lean);
    if (detail) detail = detail.replace(/Rust/g, 'legacy').replace(/Lean/g, 'calculus');
    else if (rustBin) {
      const rust = runBinary(rustBin, text);
      detail = compareResults(rust, lean);
    }
    if (detail) {
      if (exp[name]) expected.push(name);
      else mismatches.push({ name, inputText: text, rust: legacy, lean, detail });
    }
  }
  const unlisted = Object.keys(exp).filter((k) => !expected.includes(k));
  return { counts, mismatches, expected, unlisted };
}
/** @param {string[]} argv */
function main(argv) {
  let seed = 1;
  let count = 200;
  let goldens = false;
  let out = DEFAULT_OUT;
  let rustBin = RUST_BIN;
  let leanBin = LEAN_BIN;
  let lift = false;
  let calculus = false;
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    const v = argv[i + 1];
    if (a === '--goldens') goldens = true;
    else if (a === '--lift') lift = true;
    else if (a === '--calculus') calculus = true;
    else if (a === '--seed' && v !== undefined) { seed = Number(v); i++; }
    else if (a === '--count' && v !== undefined) { count = Number(v); i++; }
    else if (a === '--out' && v !== undefined) { out = path.resolve(v); i++; }
    else if (a === '--rust' && v !== undefined) { rustBin = path.resolve(v); i++; }
    else if (a === '--lean' && v !== undefined) { leanBin = path.resolve(v); i++; }
    else {
      process.stderr.write('Usage: node tools/differential.js [--seed <n>] [--count <n>] [--goldens] [--out <dir>] [--rust <binary>] [--lean <binary>]\n');
      return 2;
    }
  }
  if (!Number.isInteger(seed) || !Number.isInteger(count) || count < 0) { process.stderr.write('--seed and --count must be integers\n'); return 2; }
  if (calculus) {
    if (!fs.existsSync(leanBin)) { process.stderr.write(`The Lean engine is not built: ${leanBin} (npm run build:formal).
`); return 2; }
    const inputs = [...goldenInputs(), ...fixtureInputsV2(), ...generatedInputsV2Int(seed, count).inputs];
    const rust = fs.existsSync(rustBin) ? rustBin : null;
    if (!rust) process.stdout.write(`calculus: the Rust engine is not built (${rustBin}); only the legacy comparison runs
`);
    const r = checkCalculus(inputs, leanBin, rust);
    saveMismatches(r.mismatches, path.join(out, 'calculus'));
    for (const m of r.mismatches) process.stdout.write(`MISMATCH ${m.name}: ${m.detail}
`);
    for (const n of r.expected) process.stdout.write(`expected difference: ${n}
`);
    process.stdout.write(`calculus: ${inputs.length} inputs (goldens, fixtures, seed ${seed} with ${count} integer inputs): ${r.counts.compared} compared, ${r.counts.refused} refused, ${r.counts.legacy} on the legacy path; ${r.mismatches.length} mismatch, ${r.expected.length} expected differences
`);
    return r.mismatches.length ? 1 : 0;
  }
  if (lift) {
    // Format 1 is gone (WG-5681): the lift check compares each golden's version-2 trace, stripped of the
    // version-2 fields, with its version-1 trace at the base commit of tests/conformance/golden-changes.json.
    const manifest = JSON.parse(fs.readFileSync(path.join(REPO_ROOT, 'tests', 'conformance', 'golden-changes.json'), 'utf8'));
    const changes = goldenChanges(manifest.base);
    const bad = Object.entries(changes).filter(([name, c]) => manifest.changes[name] !== c);
    for (const [name, c] of bad) process.stdout.write(`MISMATCH lift ${name}: ${c} (the manifest says ${manifest.changes[name] ?? 'unchanged'})
`);
    const counts = /** @type {Record<string, number>} */ ({});
    for (const c of Object.values(changes)) counts[c] = (counts[c] ?? 0) + 1;
    process.stdout.write(`lift: ${Object.keys(changes).length} goldens against ${manifest.base.slice(0, 7)}: ${Object.entries(counts).map(([k, n]) => `${n} ${k}`).join(', ')}; ${bad.length} outside the manifest
`);
    return bad.length ? 1 : 0;
  }
  for (const [what, bin, how] of [['Rust engine', rustBin, 'cargo build --release in engine/'], ['Lean semantics', leanBin, 'npm run build:formal']]) {
    if (!fs.existsSync(bin)) { process.stderr.write(`The ${what} is not built: ${bin} (${how}).\n`); return 2; }
  }
  const gen1 = generatedInputsV2Int(seed, count);
  const gen2 = generatedInputsV2(seed, count);
  /** @type {Record<string, number>} */
  const genCoverage = { ...gen1.coverage };
  for (const [k, v] of Object.entries(gen2.coverage)) genCoverage[k] = v;
  const gen = { coverage: genCoverage };
  const inputs = [...(goldens ? goldenInputs() : []), ...gen1.inputs, ...gen2.inputs];
  const result = checkInputs({ inputs, rustBin, leanBin });
  const files = saveMismatches(result.mismatches, out);
  for (const m of result.mismatches) process.stdout.write(`MISMATCH ${m.name}: ${m.detail}\n`);
  process.stdout.write(`generated input coverage (seed ${seed}, ${count} version-1 and ${count} version-2 inputs):\n${formatCoverage(gen.coverage)}\n`);
  process.stdout.write(`trace coverage (Rust traces):\n${formatCoverage(result.traceCoverage)}\n`);
  process.stdout.write(`differential: ${result.checked} inputs (${goldens ? 'goldens and ' : ''}seed ${seed}, ${count} generated of each version), ${result.checked - result.mismatches.length} agree, ${result.mismatches.length} mismatch${files.length ? `; inputs saved under ${out}` : ''}\n`);
  return result.mismatches.length ? 1 : 0;
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) process.exitCode = main(process.argv.slice(2));
