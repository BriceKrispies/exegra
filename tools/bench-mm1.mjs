// Times one run of a queueing fixture's base input on the native engine, best of 5.
//   node tools/bench-mm1.mjs [binary] [fixture]     fixture: mm1 (default) or pool-flood
import fs from 'node:fs';
import { spawnSync } from 'node:child_process';
import { lowerInput } from '../tests/fixtures/queueing/inputs.js';
const bin = process.argv[2] ?? 'engine/target/release/exegra-sim.exe';
const name = process.argv[3] ?? 'mm1';
const fx = JSON.parse(fs.readFileSync(`tests/fixtures/queueing/${name}.json`, 'utf8'));
const text = JSON.stringify(lowerInput(fx.base));
let best = Infinity, steps = 0, out = '';
for (let k = 0; k < 5; k++) {
  const t = Date.now();
  const r = spawnSync(bin, [], { input: text, maxBuffer: 1 << 30, encoding: 'utf8' });
  const ms = Date.now() - t;
  if (r.status !== 0) throw new Error(r.stderr);
  out = r.stdout;
  steps = JSON.parse(out).stepsTaken;
  best = Math.min(best, ms);
}
console.log(name, 'steps', steps, 'best of 5:', best, 'ms', (best * 1000 / steps).toFixed(2), 'us/step');
