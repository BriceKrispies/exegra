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
import { fileURLToPath } from 'node:url';
import { initEngine, runEngineText } from '../src/core/engine.js';

const here = path.dirname(fileURLToPath(import.meta.url));
export const REPO_ROOT = path.resolve(here, '..');
export const GOLDENS_DIR = path.join(REPO_ROOT, 'tests', 'conformance', 'goldens');

/** Top-level trace fields in the order a difference is looked for. */
const TRACE_FIELDS = ['scenarioId', 'faults', 'initial', 'steps', 'outcome', 'final'];

/**
 * @typedef {{source:string, name:string, inputPath:string, tracePath:string}} GoldenFile
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
      out.push({ source, name, inputPath: path.join(sub, file), tracePath: path.join(sub, `${name}.trace.json`) });
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
 */

/**
 * Check an engine against goldens. The engine is a function from the input text to a trace;
 * by default the WebAssembly engine (src/core/engine.js), run from the input alone.
 * @param {{goldens?: GoldenFile[], engine?: (inputText:string) => any}} [opts]
 * @returns {GoldenResult[]}
 */
export function runConformance(opts = {}) {
  const goldens = opts.goldens ?? listGoldens();
  const engine = opts.engine ?? ((/** @type {string} */ text) => JSON.parse(runEngineText(text)));
  return goldens.map((golden) => {
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
