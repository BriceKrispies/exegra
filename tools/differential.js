#!/usr/bin/env node
// Differential check of the Rust engine against the Lean formal semantics. Node-only.
//
//   node tools/differential.js [--seed <n>] [--count <n>] [--goldens] [--out <dir>]
//                              [--lift] [--rust <binary>] [--lean <binary>]
//
// Generates --count version-1 and --count version-2 inputs from --seed with tools/gen-engine-inputs.js (and, with --goldens, adds every
// golden input of tests/conformance/goldens), runs each through the native Rust engine
// (engine/target/release/exegra-sim) and the Lean executable (formal/.lake/build/bin/exegra-lean), and
// compares the two traces as tools/conformance.js compares a trace with a golden: as JSON values, key
// order ignored, numbers by value. With --lift, each engine instead runs every liftable version-1 input
// both as it is and lifted to version 2, and the version-2 trace without its version-2 fields must
// equal the version-1 trace (lift_agrees, formal/Exegra/Lift.lean). Two refusals agree when their messages agree (for input that is not
// JSON, only that both say so). Reports the count, the seed, the construct coverage of the generated
// inputs and of the traces, and every mismatch; each mismatching input is saved to --out (default
// test-results/differential/). Exit code 0 when everything agrees, 1 on any mismatch, 2 on a usage error
// or a missing binary.

import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { REPO_ROOT, compareTraces, listGoldens } from './conformance.js';
import { formatCoverage, generateInputs, generateInputsV2 } from './gen-engine-inputs.js';

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
 * @param {string} bin @param {string} inputText
 * @returns {EngineResult}
 */
export function runBinary(bin, inputText) {
  const r = spawnSync(bin, [], { input: inputText, encoding: 'utf8', maxBuffer: 1 << 29, windowsHide: true });
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
    const rust = runBinary(rustBin, text);
    const lean = runBinary(leanBin, text);
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
 * Generated inputs as named inputs.
 * @param {number} seed @param {number} count
 * @returns {{inputs: NamedInput[], coverage: Record<string, number>}}
 */
export function generatedInputs(seed, count) {
  const { inputs, coverage } = generateInputs(seed, count);
  return { inputs: inputs.map((input, i) => ({ name: `seed ${seed} input ${i}`, text: JSON.stringify(input) })), coverage };
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

const TWO53 = 2 ** 53;
/** @param {unknown} x */
const isTime = (x) => x === undefined || x === null || (Number.isInteger(x) && /** @type {number} */ (x) >= 0 && /** @type {number} */ (x) < TWO53);

/**
 * Whether a version-1 input meets the side conditions of lift_agrees (formal/Exegra/Lift.lean) that
 * can be checked on the input: integer times, durations and step limit; no variable named `instance`
 * and no reference format 2 resolves anew; distinct ids and no empty event id.
 * @param {any} input
 */
export function liftable(input) {
  if (!input || input.version !== 1 || !Array.isArray(input.behaviors) || !Array.isArray(input.events)) return false;
  const sc = input.scenario ?? {};
  if (!(sc.steps ?? []).every((/** @type {any} */ st) => Number.isInteger(st?.at) && isTime(st.at))) return false;
  if (sc.stepLimit !== undefined && sc.stepLimit !== null && !(isTime(sc.stepLimit) && sc.stepLimit >= 1)) return false;
  if (!(input.faults ?? []).every((/** @type {any} */ f) => isTime(f?.by) && isTime(f?.at))) return false;
  const ids = [...input.behaviors.map((/** @type {any} */ b) => b?.id), ...input.events.map((/** @type {any} */ e) => e?.id), ...(input.faults ?? []).map((/** @type {any} */ f) => f?.id), sc.id];
  if (new Set(ids).size !== ids.length || ids.includes('')) return false;
  const newRef = /(^|[^\w.])instance([^\w]|$)|[A-Za-z_]\w*\.(count|sum|min|max|instances)\.[A-Za-z_]/;
  for (const b of input.behaviors) {
    if ((b.variables ?? []).some((/** @type {any} */ v) => v?.name === 'instance')) return false;
    for (const t of b.transitions ?? []) {
      const srcs = [typeof t.guard === 'string' ? t.guard : ''];
      for (const e of t.effects ?? []) {
        if (e && typeof e === 'object' && 'emit' in e && !isTime(e.after)) return false;
        if (e && typeof e.to === 'string') srcs.push(e.to);
        for (const v of Object.values(e?.payload ?? {})) if (typeof v === 'string') srcs.push(v);
      }
      if (srcs.some((s) => newRef.test(s))) return false;
    }
  }
  return true;
}

/** `lift(I)`: version 2, unit tick, no seed, nothing else changed. @param {any} input */
export const liftInput = (input) => ({ ...input, version: 2, time: { unit: 'tick', perSecond: null } });

/**
 * Remove the version-2 fields from a version-2 trace (the strip of lift_agrees).
 * @param {any} t
 */
export function stripTrace(t) {
  const drop = (/** @type {any} */ o, /** @type {string[]} */ keys) => { if (o && typeof o === 'object') for (const k of keys) delete o[k]; return o; };
  const config = (/** @type {any} */ c) => {
    drop(c, ['resources', 'links', 'timers', 'workloads', 'meters', 'routeCounters', 'streams', 'down', 'incarnations', 'activeFaults']);
    for (const p of c?.pending ?? []) drop(p, ['scheduledAt', 'routes', 'from', 'target', 'copyOf']);
    return c;
  };
  const out = structuredClone(t);
  drop(out, ['version', 'timeUnit', 'seed', 'truncated', 'initialDraws', 'stepsTaken']);
  config(out.initial);
  config(out.final);
  for (const st of out.steps ?? []) {
    drop(st, ['resources', 'draws', 'links']);
    drop(st.event, ['scheduledAt', 'routes', 'from', 'target', 'copyOf']);
    for (const f of st.fired ?? []) drop(f, ['instance']);
    for (const i of st.ignored ?? []) drop(i, ['instance']);
    config(st.config);
  }
  return out;
}

/**
 * The lift check: every liftable input is run as version 1 and lifted to version 2 on one engine,
 * and the stripped version-2 result must equal the version-1 result.
 * @param {NamedInput[]} inputs @param {string} bin
 * @returns {{checked: number, mismatches: Mismatch[]}}
 */
export function checkLift(inputs, bin) {
  /** @type {Mismatch[]} */
  const mismatches = [];
  let checked = 0;
  for (const { name, text } of inputs) {
    let input;
    try { input = JSON.parse(text); } catch { continue; }
    if (!liftable(input)) continue;
    checked++;
    const v1 = runBinary(bin, text);
    const lifted = JSON.stringify(liftInput(input));
    const v2 = runBinary(bin, lifted);
    const stripped = v2.ok ? { ok: true, trace: stripTrace(v2.trace) } : v2;
    const detail = compareResults(/** @type {EngineResult} */ (v1), /** @type {EngineResult} */ (stripped));
    if (detail) mismatches.push({ name: `lift ${name}`, inputText: lifted, rust: v1, lean: v2, detail: detail.replace(/Rust/g, 'version 1').replace(/Lean/g, 'version 2') });
  }
  return { checked, mismatches };
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
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    const v = argv[i + 1];
    if (a === '--goldens') goldens = true;
    else if (a === '--lift') lift = true;
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
  if (lift) {
    if (!fs.existsSync(leanBin)) { process.stderr.write(`The Lean semantics is not built: ${leanBin} (npm run build:formal).
`); return 2; }
    const inputs = [...(goldens ? goldenInputs() : []), ...generatedInputs(seed, count).inputs];
    let failed = 0;
    for (const [what, bin] of [['Lean', leanBin], ['Rust', rustBin]]) {
      if (!fs.existsSync(bin)) { process.stdout.write(`lift: ${what} engine not built, skipped
`); continue; }
      const r = checkLift(inputs, bin);
      saveMismatches(r.mismatches, path.join(out, `lift-${what.toLowerCase()}`));
      for (const m of r.mismatches) process.stdout.write(`MISMATCH ${what} ${m.name}: ${m.detail}
`);
      process.stdout.write(`lift (${what}): ${r.checked} liftable inputs of ${inputs.length}, ${r.checked - r.mismatches.length} agree, ${r.mismatches.length} mismatch
`);
      failed += r.mismatches.length;
    }
    return failed ? 1 : 0;
  }
  for (const [what, bin, how] of [['Rust engine', rustBin, 'cargo build --release in engine/'], ['Lean semantics', leanBin, 'npm run build:formal']]) {
    if (!fs.existsSync(bin)) { process.stderr.write(`The ${what} is not built: ${bin} (${how}).\n`); return 2; }
  }
  const gen1 = generatedInputs(seed, count);
  const gen2 = generatedInputsV2(seed, count);
  /** @type {Record<string, number>} */
  const genCoverage = { ...gen1.coverage };
  for (const [k, v] of Object.entries(gen2.coverage)) if (k.startsWith('v2 ')) genCoverage[k] = v;
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
