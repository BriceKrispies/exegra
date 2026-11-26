import { runsToDecide, passesToHold, parseRational } from '../../../../src/core/metric-stats.js';
const B = parseRational('0.95'), C = parseRational('0.95');
// exact (BigInt) thresholds from the repository's own code
const M = {}; for (let f = 0; f <= 6; f++) M[f] = runsToDecide(59, 59 - f, B, C);
console.log('decideAt for f failures (repo runsToDecide):', M);
console.log('passesToHold(59)=', passesToHold(59, B, C));
// strategy: run 59 with base seed s; while inconclusive with f failures so far, rerun with N = M[f] (same base seed: first runs identical).
// Monte Carlo with true per-run pass probability p < 0.95 (the claim is false).
let s = 7; const rnd = () => { s = (s * 16807) % 2147483647; return s / 2147483647; };
for (const p of [0.95, 0.945]) {
  const T = 200000; let hold = 0;
  for (let t = 0; t < T; t++) {
    let n = 0, f = 0, N = 59, verdictHold = false;
    for (let round = 0; round < 7; round++) {
      while (n < N) { if (rnd() >= p) f++; n++; }
      if (f <= 6 && M[f] !== null && N >= M[f]) { verdictHold = true; break; }
      if (f > 6) break;          // treat as fail/give up
      N = M[f];
    }
    if (verdictHold) hold++;
  }
  const one = p ** 59;
  console.log(`p=${p}: one-shot P(holds)=${one.toFixed(4)}; seeds to try for 95%: ${Math.ceil(Math.log(0.05)/Math.log(1-one))}; following decideAt advice: P(holds)=${(hold/T).toFixed(4)}`);
}
