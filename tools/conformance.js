#!/usr/bin/env node
// Conformance runner: checks a simulation engine against every golden of tests/conformance/goldens.
// Node-only.
//
//   node tools/conformance.js                       the WebAssembly engine through src/core/engine.js, in-process,
//                                                   from the input file alone (build it first: npm run build:engine)
//   node tools/conformance.js --engine "<command>"  spawn the command once per golden: the engine input JSON on
//                                                   its stdin, the trace JSON on its stdout
//   options: --goldens <dir>   other goldens directory;  --filter <text>   only goldens whose name contains text
//
// Each mismatch is reported with the golden, the first differing step index and the JSON path of the first
// differing field. Exit code 0 when every golden matches, 1 on any mismatch or error, 2 on a usage error.

import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { isDeepStrictEqual } from 'node:util';
import { fileURLToPath } from 'node:url';
import { initEngine, runEngineText } from '../src/core/engine.js';

const here = path.dirname(fileURLToPath(import.meta.url));
export const REPO_ROOT = path.resolve(here, '..');
export const GOLDENS_DIR = path.join(REPO_ROOT, 'tests', 'conformance', 'goldens');

/**
 * The refusals of the Lean elaborator (formal/Exegra/Elab.lean, `Refusal.message`): an ill-typed input or
 * one with a number that is not an integer. A golden the engine refuses so has an input file and no trace
 * (WG-5681); the Rust engine does not mirror static typing and is not run on it.
 */
export const ELAB_REFUSAL = /^(exegra-lean: )?(The input (is ill-typed|uses)|The number at )/;

/** Top-level trace fields in the order a difference is looked for. */
const TRACE_FIELDS = ['scenarioId', 'faults', 'initial', 'steps', 'outcome', 'final'];

/**
 * @typedef {{source:string, name:string, inputPath:string, tracePath:string, refused:boolean}} GoldenFile
 * @typedef {{path:string, step:number|null, expected:any, actual:any}} Difference
 */

/**
 * Every golden under a goldens directory, sorted by source then name.
 * @param {string} [dir]
 * @returns {GoldenFile[]}
 */
export function listGoldens(dir = GOLDENS_DIR) {
  /** @type {GoldenFile[]} */
  const out = [];
  if (!fs.existsSync(dir)) return out;
  for (const source of fs.readdirSync(dir).sort()) {
    const sub = path.join(dir, source);
    if (!fs.statSync(sub).isDirectory()) continue;
    for (const file of fs.readdirSync(sub).sort()) {
      if (!file.endsWith('.input.json')) continue;
      const name = file.slice(0, -'.input.json'.length);
      const tracePath = path.join(sub, `${name}.trace.json`);
      out.push({ source, name, inputPath: path.join(sub, file), tracePath, refused: !fs.existsSync(tracePath) });
    }
  }
  return out;
}

/** @param {any} v */
const kindOf = (v) => (v === null ? 'null' : Array.isArray(v) ? 'array' : typeof v);

/**
 * First difference between two JSON values: arrays in index order, objects by sorted key, the
 * top level of a trace in the order of its fields. Returns null when they are equal.
 * @param {any} expected @param {any} actual @param {string} [at] @returns {{path:string, expected:any, actual:any}|null}
 */
function firstDifference(expected, actual, at = '$') {
  const ke = kindOf(expected);
  if (ke !== kindOf(actual)) return { path: at, expected, actual };
  if (ke === 'array') {
    const n = Math.min(expected.length, actual.length);
    for (let i = 0; i < n; i++) {
      const d = firstDifference(expected[i], actual[i], `${at}[${i}]`);
      if (d) return d;
    }
    if (expected.length !== actual.length) {
      const i = n;
      return { path: `${at}[${i}]`, expected: expected[i], actual: actual[i] };
    }
    return null;
  }
  if (ke === 'object') {
    const keys = [...new Set([...Object.keys(expected), ...Object.keys(actual)])].sort();
    if (at === '$') keys.sort((a, b) => (TRACE_FIELDS.indexOf(a) + 1 || 99) - (TRACE_FIELDS.indexOf(b) + 1 || 99) || (a < b ? -1 : 1));
    for (const k of keys) {
      const inE = Object.prototype.hasOwnProperty.call(expected, k);
      const inA = Object.prototype.hasOwnProperty.call(actual, k);
      if (inE !== inA) return { path: `${at}.${k}`, expected: inE ? expected[k] : undefined, actual: inA ? actual[k] : undefined };
      const d = firstDifference(expected[k], actual[k], `${at}.${k}`);
      if (d) return d;
    }
    return null;
  }
  return expected === actual ? null : { path: at, expected, actual };
}

/**
 * Compare an actual trace with the expected one, as JSON values.
 * @param {any} expected @param {any} actual
 * @returns {Difference|null} null when equal; `step` is the index in `steps` the path lies in, else null
 */
export function compareTraces(expected, actual) {
  const d = firstDifference(expected, actual);
  if (!d) return null;
  const m = /^\$\.steps\[(\d+)\]/.exec(d.path);
  return { ...d, step: m ? Number(m[1]) : null };
}

/**
 * Run a command as an engine: input JSON on stdin, trace JSON on stdout.
 * @param {string} command @param {string} inputText
 * @returns {any} the trace
 */
export function runEngineCommand(command, inputText) {
  const r = spawnSync(command, { shell: true, input: inputText, encoding: 'utf8', maxBuffer: 1 << 29 });
  if (r.error) throw new Error(`could not run the engine: ${r.error.message}`);
  if (r.status !== 0) throw new Error(`the engine exited with status ${r.status}${r.stderr ? `: ${r.stderr.trim().slice(0, 400)}` : ''}`);
  try {
    return JSON.parse(r.stdout);
  } catch (e) {
    throw new Error(`the engine's output is not JSON: ${/** @type {Error} */ (e).message}`);
  }
}

/**
 * @typedef {{golden:GoldenFile, status:'ok'|'mismatch'|'error', difference?:Difference, error?:string}} GoldenResult
 *
 * A golden with no trace file (`refused`) is one the engine refuses: it passes when the engine refuses it
 * with an elaboration refusal. `skipRefused` leaves such goldens out (for an engine without static typing).
 */

/**
 * Check an engine against goldens. The engine is a function from the input text to a trace;
 * by default the WebAssembly engine (src/core/engine.js), run from the input alone.
 * @param {{goldens?: GoldenFile[], engine?: (inputText:string) => any, skipRefused?: boolean}} [opts]
 * @returns {GoldenResult[]}
 */
export function runConformance(opts = {}) {
  const goldens = (opts.goldens ?? listGoldens()).filter((g) => !(opts.skipRefused && g.refused));
  const engine = opts.engine ?? ((/** @type {string} */ text) => JSON.parse(runEngineText(text)));
  return goldens.map((golden) => {
    if (golden.refused) {
      try {
        engine(fs.readFileSync(golden.inputPath, 'utf8'));
        return { golden, status: 'error', error: 'the engine returned a trace for an input it should refuse (the golden has no trace)' };
      } catch (e) {
        const msg = /** @type {Error} */ (e).message;
        return ELAB_REFUSAL.test(msg) || ELAB_REFUSAL.test(msg.replace(/^the engine exited with status \d+: /, ''))
          ? { golden, status: 'ok' } : { golden, status: 'error', error: msg };
      }
    }
    try {
      const expected = JSON.parse(fs.readFileSync(golden.tracePath, 'utf8'));
      const actual = engine(fs.readFileSync(golden.inputPath, 'utf8'));
      const difference = compareTraces(expected, actual);
      return difference ? { golden, status: 'mismatch', difference } : { golden, status: 'ok' };
    } catch (e) {
      return { golden, status: 'error', error: /** @type {Error} */ (e).message };
    }
  });
}


/** The version-1 trace fields a version-2 trace adds, removed by `strip` (WG-5681: format 1 is gone). */
const V2_ONLY = ['resources', 'links', 'timers', 'workloads', 'meters', 'routeCounters', 'streams', 'down', 'incarnations', 'activeFaults'];
const ENTRY_V2_ONLY = ['scheduledAt', 'routes', 'from', 'target', 'copyOf'];

/**
 * A version-2 trace without the fields version 2 adds: what a version-1 trace of the same run holds.
 * @param {any} t
 */
export function strip(t) {
  const drop = (/** @type {any} */ o, /** @type {string[]} */ keys) => { if (o && typeof o === 'object') for (const k of keys) delete o[k]; return o; };
  const config = (/** @type {any} */ c) => {
    drop(c, V2_ONLY);
    for (const e of c?.pending ?? []) drop(e, ENTRY_V2_ONLY);
    return c;
  };
  const out = structuredClone(t);
  drop(out, ['version', 'timeUnit', 'seed', 'truncated', 'initialDraws', 'stepsTaken', 'semantics']);
  config(out.initial);
  config(out.final);
  for (const st of out.steps ?? []) {
    drop(st, ['resources', 'draws', 'links']);
    drop(st.event, ENTRY_V2_ONLY);
    for (const f of st.fired ?? []) drop(f, ['instance']);
    for (const i of st.ignored ?? []) drop(i, ['instance']);
    config(st.config);
  }
  return out;
}

/**
 * How every golden changed since commit `base` (WG-5681, tests/conformance/golden-changes.json): by
 * `<source>/<name>`, one of "version 2" (a version-1 golden whose input is the lifted version-1 input and
 * whose trace, stripped of the version-2 fields, is the version-1 trace), "input re-recorded, trace equal
 * under strip", "input edited, trace re-recorded", "trace removed (refused)", "trace changed", "added",
 * "deleted", or nothing when it is unchanged. Throws when the base commit is not available.
 * @param {string} base
 * @returns {Record<string, string>}
 */
export function goldenChanges(base) {
  const show = (/** @type {string} */ rel) => {
    const r = spawnSync('git', ['-C', REPO_ROOT, 'show', `${base}:${rel}`], { encoding: 'utf8', maxBuffer: 1 << 28 });
    return r.status === 0 ? JSON.parse(r.stdout) : null;
  };
  const tree = spawnSync('git', ['-C', REPO_ROOT, 'ls-tree', '-r', '--name-only', base, 'tests/conformance/goldens'], { encoding: 'utf8', maxBuffer: 1 << 26 });
  if (tree.status !== 0) throw new Error(`the base commit ${base} is not available: ${tree.stderr.trim()}`);
  const names = new Set(tree.stdout.split(/\r?\n/).filter((f) => f.endsWith('.input.json')).map((f) => f.slice('tests/conformance/goldens/'.length, -'.input.json'.length)));
  for (const g of listGoldens()) names.add(`${g.source}/${g.name}`);
  /** @type {Record<string, string>} */
  const out = {};
  for (const name of [...names].sort()) {
    const rel = `tests/conformance/goldens/${name}`;
    const oldIn = show(`${rel}.input.json`);
    const oldTr = show(`${rel}.trace.json`);
    const inPath = path.join(REPO_ROOT, `${rel}.input.json`);
    const trPath = path.join(REPO_ROOT, `${rel}.trace.json`);
    const newIn = fs.existsSync(inPath) ? JSON.parse(fs.readFileSync(inPath, 'utf8')) : null;
    const newTr = fs.existsSync(trPath) ? JSON.parse(fs.readFileSync(trPath, 'utf8')) : null;
    if (!oldIn) { out[name] = 'added'; continue; }
    if (!newIn) { out[name] = 'deleted'; continue; }
    if (isDeepStrictEqual(oldIn, newIn) && isDeepStrictEqual(oldTr, newTr)) continue;
    if (oldTr && !newTr) { out[name] = 'trace removed (refused)'; continue; }
    const lifted = oldIn.version === 1 && isDeepStrictEqual({ ...oldIn, version: 2, time: { unit: 'tick', perSecond: null } }, newIn);
    const traceEqual = oldTr && newTr && compareTraces(oldTr, strip(newTr)) === null;
    if (traceEqual) out[name] = lifted ? 'version 2' : 'input re-recorded, trace equal under strip';
    else out[name] = lifted ? 'trace changed' : 'input edited, trace re-recorded';
  }
  return out;
}

/** @param {any} v */
function show(v) {
  if (v === undefined) return '(absent)';
  const s = JSON.stringify(v);
  return s.length > 120 ? `${s.slice(0, 117)}...` : s;
}

/** One report line per failing golden. @param {GoldenResult} r */
export function describeFailure(r) {
  const id = `${r.golden.source}/${r.golden.name}`;
  if (r.status === 'error') return `ERROR    ${id}: ${r.error}`;
  const d = /** @type {Difference} */ (r.difference);
  const where = d.step === null ? 'outside the steps' : `at step ${d.step}`;
  return `MISMATCH ${id}: first difference ${where}, ${d.path}: expected ${show(d.expected)}, got ${show(d.actual)}`;
}

/** @param {string[]} argv */
function main(argv) {
  /** @type {string|undefined} */ let engineCommand;
  /** @type {string|undefined} */ let dir;
  /** @type {string|undefined} */ let filter;
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--engine' || a === '--goldens' || a === '--filter') {
      const v = argv[++i];
      if (v === undefined) { process.stderr.write(`${a} needs a value\n`); return 2; }
      if (a === '--engine') engineCommand = v; else if (a === '--goldens') dir = path.resolve(v); else filter = v;
    } else {
      process.stderr.write(`Unknown argument "${a}". Usage: node tools/conformance.js [--engine "<command>"] [--goldens <dir>] [--filter <text>]\n`);
      return 2;
    }
  }
  let goldens = listGoldens(dir);
  if (filter !== undefined) goldens = goldens.filter((g) => `${g.source}/${g.name}`.includes(/** @type {string} */ (filter)));
  if (!goldens.length) { process.stderr.write('No goldens found.\n'); return 1; }
  const command = engineCommand;
  if (command === undefined) {
    try { initEngine(); } catch (e) { process.stderr.write(`${/** @type {Error} */ (e).message}
`); return 1; }
  }
  const results = runConformance({ goldens, engine: command === undefined ? undefined : (text) => runEngineCommand(command, text) });
  const failed = results.filter((r) => r.status !== 'ok');
  for (const r of failed) process.stdout.write(`${describeFailure(r)}\n`);
  const mismatches = failed.filter((r) => r.status === 'mismatch').length;
  const errors = failed.length - mismatches;
  process.stdout.write(`conformance: ${results.length} goldens, ${results.length - failed.length} passed, ${mismatches} mismatched, ${errors} errors (${command === undefined ? 'WebAssembly engine, from the input alone' : `engine: ${command}`})\n`);
  return failed.length ? 1 : 0;
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) process.exitCode = main(process.argv.slice(2));
