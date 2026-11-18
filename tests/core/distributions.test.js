// The integer lowering of distributions (src/core/distributions.js) reproduces, bit for bit, the
// reference outputs of docs/simulation.md ("Lowering distributions"): the fixed-point checks, the
// pinned tables at their reference points, the SHA-256 of their canonical text, and the lowered
// log-normal and exponential tables.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import crypto from 'node:crypto';
import {
  GRID, LN2, S, canonicalTableText, expFp, lnFp, lognormalSigma, lowerDistribution, qexp, qnorm, roundHalfEven, tableMean,
} from '../../src/core/distributions.js';

const TWO32 = 1n << 32n;

test('exp_fp and ln_fp meet their exact checks', () => {
  assert.equal(expFp(LN2), 1n << 97n);
  assert.equal(lnFp(1n << 97n), LN2);
  const e = roundHalfEven(271828182845904523536028747135266249775724709369995n * S, 10n ** 50n);
  assert.equal(lnFp(e), S - 16n);
});

test('the pinned tables give the reference values and the pinned hash', () => {
  assert.equal(GRID.length, 1046);
  const at = [GRID[1], GRID[512], GRID[1023], TWO32 - 2n, TWO32];
  assert.deepEqual(at.map(qexp), [18023200333324837n, 12786308645202655660n, 127863086452026556598n, 396375568001282325453n, 421948185291687636773n]);
  assert.deepEqual(at.map(qnorm), [-57134530012947273077n, 0n, 57134530012947273077n, 112908024744873384702n, 116914684648236608820n]);
  const hash = crypto.createHash('sha256').update(canonicalTableText(), 'ascii').digest('hex');
  assert.equal(hash, 'a23cd2a9566c106701375d5cf75ef982b8db6f3e52c199c47e6239649c840950');
});

test('families lower to the reference tables', () => {
  assert.equal(lognormalSigma({ median: 1000, p99: 4000 }), 47212867929608158508829714117n);
  const ln = lowerDistribution({ lognormal: { median: 1000, p99: 4000 } });
  assert.equal(ln.kind, 'table');
  const lp = /** @type {{points: number[][]}} */ (ln).points;
  assert.deepEqual([lp[1][1], lp[512][1], lp[1023][1], lp[lp.length - 1][1]], [158, 1000, 6332, 43678]);
  const ex = /** @type {{points: number[][]}} */ (lowerDistribution({ exponential: { mean: 1250 } })).points;
  assert.deepEqual([ex[0][1], ex[512][1], ex[1023][1], ex[ex.length - 1][1]], [0, 866, 8664, 28592]);
  assert.deepEqual(lowerDistribution({ constant: '7' }), { kind: 'fixed', value: 7 });
  assert.deepEqual(lowerDistribution({ uniform: { lo: 2, hi: 5 } }), { kind: 'uniform', lo: 2, hi: 5 });
  const emp = /** @type {{points: number[][]}} */ (lowerDistribution({ empirical: { samples: [5, 1, 3] } })).points;
  assert.deepEqual([emp[0][1], emp[1][1], emp[emp.length - 1][1]], [1, 1, 5]);
  const q = /** @type {{points: number[][]}} */ (lowerDistribution({ empirical: { quantiles: [['0', 0], ['0.5', 10], ['1', 40]] } })).points;
  assert.deepEqual(q, [[0, 0], [2147483648, 10], [4294967296, 40]]);
  assert.throws(() => lowerDistribution({ exponential: { mean: String(2 ** 50) } }), /2\^53 base units or more/);
  assert.throws(() => lowerDistribution({ lognormal: { median: 1000, sigma: '9' } }), /sigma above 8/);
  assert.throws(() => lowerDistribution({ lognormal: { median: 1, p99: 1000001 } }), /p99/);
});

test('the exact mean of a table', () => {
  // Brute force on a table whose segments are short enough to enumerate (the sum over u* is
  // scaled: tableMean returns the sum over every u* divided by 2^32).
  const pts = [[0, 3], [7, 10], [12, 10], [20, 25], [4294967296, 25]];
  let brute = 0n;
  for (let i = 0; i + 1 < 4; i++) for (let v = pts[i][0]; v < pts[i + 1][0]; v++) brute += BigInt(pts[i][1] + Math.floor(((v - pts[i][0]) * (pts[i + 1][1] - pts[i][1])) / (pts[i + 1][0] - pts[i][0])));
  brute += 25n * (4294967296n - 20n);
  assert.deepEqual(tableMean(pts), [brute, 4294967296n]);
  const ex = /** @type {{points: number[][]}} */ (lowerDistribution({ exponential: { mean: 1000000 } })).points;
  const [en, ed] = tableMean(ex);
  const rel = Number((en * 10n ** 7n) / ed) / 1e13; // in units of the mean
  assert.ok(Math.abs(rel - 1.000118) < 2e-6, `relative mean ${rel}`);
});
