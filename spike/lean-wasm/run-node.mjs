// Node check and measurement of the Lean engine compiled to wasm.
// Usage: node spike/lean-wasm/run-node.mjs <dir with exegra-lean.mjs/.wasm> [--native <exegra-lean exe>]
// Runs every golden of tests/conformance/goldens through the wasm Lean engine, compares each trace with
// the golden (tools/conformance.js compareTraces), and, given --native, compares the output text byte for
// byte with the native exegra-lean. Prints timings for startup, per-call and the Rust wasm engine.
import fs from 'node:fs';
import path from 'node:path';
import zlib from 'node:zlib';
import { spawnSync } from 'node:child_process';
import { pathToFileURL, fileURLToPath } from 'node:url';
import { performance } from 'node:perf_hooks';
import { listGoldens, compareTraces } from '../../tools/conformance.js';
import { createLeanEngine } from './lean-engine.mjs';

const args = process.argv.slice(2);
const dir = path.resolve(args[0]);
const native = args.includes('--native') ? args[args.indexOf('--native') + 1] : null;
const here = path.dirname(fileURLToPath(import.meta.url));

const wasmPath = path.join(dir, 'exegra-lean.wasm');
const raw = fs.statSync(wasmPath).size;
const gz = zlib.gzipSync(fs.readFileSync(wasmPath), { level: 9 }).length;
const br = zlib.brotliCompressSync(fs.readFileSync(wasmPath)).length;

const t0 = performance.now();
const { default: factory } = await import(pathToFileURL(path.join(dir, 'exegra-lean.mjs')).href);
const t1 = performance.now();
const m = await factory();
const t2 = performance.now();
// createLeanEngine runs the Lean module initializer (exegra_init)
const engine = await createLeanEngine(async () => m);
const t3 = performance.now();
const heapAfterInit = engine.heapBytes();

const goldens = listGoldens(path.join(here, '..', '..', 'tests', 'conformance', 'goldens'));
let ok = 0, mismatch = 0, errors = 0, nativeSame = 0, nativeDiff = 0;
const perCall = [];
for (const g of goldens) {
  const input = fs.readFileSync(g.inputPath, 'utf8');
  const expected = JSON.parse(fs.readFileSync(g.tracePath, 'utf8'));
  let out, err;
  const s = performance.now();
  try { out = engine.run(input); } catch (e) { err = e instanceof Error ? e.message : `${e} (${e?.constructor?.name})`; }
  perCall.push({ name: `${g.source}/${g.name}`, ms: performance.now() - s, bytes: input.length });
  if (err !== undefined) { errors++; console.log(`ERROR ${g.source}/${g.name}: ${err.slice(0, 200)}`); }
  else {
    const d = compareTraces(expected, JSON.parse(out));
    if (d) { mismatch++; console.log(`MISMATCH ${g.source}/${g.name} at ${d.path}`); } else ok++;
  }
  if (native) {
    const r = spawnSync(native, { input, encoding: 'utf8', maxBuffer: 1 << 29 });
    const nat = r.status === 0 ? r.stdout.replace(/\n$/, '') : `ERR ${r.stderr}`;
    const mine = err === undefined ? out : `ERR exegra-lean: ${err}\n`;
    if (nat === mine || (r.status !== 0 && err !== undefined && r.stderr.includes(err))) nativeSame++;
    else { nativeDiff++; console.log(`NATIVE-DIFF ${g.source}/${g.name}`); }
  }
}
const heapAfterRuns = engine.heapBytes();

console.log(`goldens: ${goldens.length}, match ${ok}, mismatch ${mismatch}, error ${errors}`);
if (native) console.log(`byte-identical to native exegra-lean: ${nativeSame}/${goldens.length} (differ ${nativeDiff})`);
console.log(`wasm size: ${raw} B raw, ${gz} B gzip -9, ${br} B brotli`);
console.log(`import glue: ${(t1 - t0).toFixed(1)} ms; compile+instantiate: ${(t2 - t1).toFixed(1)} ms; Lean module init: ${(t3 - t2).toFixed(1)} ms`);
console.log(`wasm heap: ${heapAfterInit} B after init, ${heapAfterRuns} B after all goldens; node rss ${process.memoryUsage().rss} B`);
perCall.sort((a, b) => b.ms - a.ms);
const total = perCall.reduce((a, b) => a + b.ms, 0);
console.log(`first pass over goldens: total ${total.toFixed(1)} ms, median ${perCall[perCall.length >> 1].ms.toFixed(2)} ms, slowest ${perCall[0].name} ${perCall[0].ms.toFixed(1)} ms`);

// Steady-state per-call cost and engine comparison on fixed inputs: the two slowest goldens and a small one.
const { runEngineText } = await import('../../src/core/engine.js');
const spawnMs = (input, n) => {
  const s = performance.now();
  for (let i = 0; i < n; i++) spawnSync(native, { input, encoding: 'utf8', maxBuffer: 1 << 29 });
  return (performance.now() - s) / n;
};
// a native run of an input it refuses at once: process start-up and exit, no engine work
const nativeFloor = native ? spawnMs('{}', 10) : null;
if (native) console.log(`native exegra-lean process start-up (refused '{}' input, mean of 10): ${nativeFloor.toFixed(1)} ms`);
for (const name of ['exegra/live-session', 'exegra/app-start-and-open', 'fixture/faults-combined--delay-tick-3']) {
  const [source, base] = name.split('/');
  const inputPath = path.join(here, '..', '..', 'tests', 'conformance', 'goldens', source, `${base}.input.json`);
  const input = fs.readFileSync(inputPath, 'utf8');
  const time = (f, n) => { f(); const s = performance.now(); for (let i = 0; i < n; i++) f(); return (performance.now() - s) / n; };
  const n = 50;
  const lean = time(() => { try { engine.run(input); } catch {} }, n);
  const rust = time(() => { try { runEngineText(input); } catch {} }, n);
  let nat = '';
  if (native) {
    const t = spawnMs(input, 10);
    nat = `, native exegra-lean process ${t.toFixed(1)} ms (minus start-up: ~${(t - nativeFloor).toFixed(1)} ms)`;
  }
  console.log(`${name} (${input.length} B input, mean of ${n}): Lean wasm ${lean.toFixed(2)} ms, Rust wasm ${rust.toFixed(2)} ms${nat}`);
}
console.log(`wasm heap at end: ${engine.heapBytes()} B; node rss ${process.memoryUsage().rss} B`);
