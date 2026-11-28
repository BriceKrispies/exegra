// The integer lowering of distributions (formal/Exegra/Lower/Dist.lean and Families.lean, the
// registered function "lower.tables", WG-5683) reproduces, bit for bit, the reference outputs of
// docs/simulation.md ("Lowering distributions"): the pinned tables at their reference points, the
// SHA-256 of their canonical text, and the lowered log-normal, exponential, empirical, uniform and
// constant families with their refusals. The fixed-point checks (exp_fp, ln_fp, the log-normal sigma)
// and the reference values of Qexp and Qnorm are #guard checks of Families.lean, and Pinned.lean checks
// the canonical text against the integer algorithms at every grid point, when the Lean core is built.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import crypto from 'node:crypto';
import { call, initLean } from '../../src/core/lean.js';

initLean();

const TWO32 = 1n << 32n;

/** @param {any[]} families @returns {{canonical: string, unitExponential: string[][], families: any[]}} */
function tables(families) {
  const r = call('lower.tables', { families: families.map((family) => ({ path: 'distribution', family })) });
  if (!r.ok) throw new Error(r.error);
  return r.value;
}

/** @param {any} family */
const lower = (family) => tables([family]).families[0];

test('the pinned tables give the reference values and the pinned hash', () => {
  const t = tables([]);
  const rows = t.canonical.trimEnd().split('\n').map((l) => l.split(' ').map(BigInt));
  assert.equal(rows.length, 1045);
  const at = (/** @type {bigint} */ u) => /** @type {bigint[]} */ (rows.find((r) => r[0] === u));
  const points = [1n << 22n, 512n << 22n, 1023n << 22n, TWO32 - 2n, TWO32];
  assert.deepEqual(points.map((u) => at(u)[1]), [18023200333324837n, 12786308645202655660n, 127863086452026556598n, 396375568001282325453n, 421948185291687636773n]);
  assert.deepEqual(points.map((u) => at(u)[2]), [-57134530012947273077n, 0n, 57134530012947273077n, 112908024744873384702n, 116914684648236608820n]);
  const hash = crypto.createHash('sha256').update(t.canonical, 'ascii').digest('hex');
  assert.equal(hash, 'a23cd2a9566c106701375d5cf75ef982b8db6f3e52c199c47e6239649c840950');
  assert.deepEqual(t.unitExponential[0], ['0', '0']);
  assert.deepEqual(t.unitExponential.slice(1).map((r) => r[1]), rows.map((r) => String(r[1])));
});

test('families lower to the reference tables', () => {
  const lp = lower({ lognormal: { median: 1000, p99: 4000 } }).points;
  assert.deepEqual([lp[1][1], lp[512][1], lp[1023][1], lp[lp.length - 1][1]], [158, 1000, 6332, 43678]);
  const ex = lower({ exponential: { mean: 1250 } }).points;
  assert.deepEqual([ex[0][1], ex[512][1], ex[1023][1], ex[ex.length - 1][1]], [0, 866, 8664, 28592]);
  assert.deepEqual(lower({ constant: '7' }), { kind: 'fixed', value: 7 });
  assert.deepEqual(lower({ uniform: { lo: 2, hi: 5 } }), { kind: 'uniform', lo: 2, hi: 5 });
  const emp = lower({ empirical: { samples: [5, 1, 3] } }).points;
  assert.deepEqual([emp[0][1], emp[1][1], emp[emp.length - 1][1]], [1, 1, 5]);
  assert.deepEqual(lower({ empirical: { quantiles: [['0', 0], ['0.5', 10], ['1', 40]] } }).points, [[0, 0], [2147483648, 10], [4294967296, 40]]);
  assert.match(lower({ exponential: { mean: String(2 ** 50) } }).error, /2\^53 base units or more/);
  assert.match(lower({ lognormal: { median: 1000, sigma: '9' } }).error, /sigma above 8/);
  assert.match(lower({ lognormal: { median: 1, p99: 1000001 } }).error, /p99/);
});

/**
 * The exact mean of an engine table, as `[num, den]`: the trapezoid sum less the floor of the
 * interpolation, computed over every `u*` in [0, 2^32).
 * @param {(number|string|bigint)[][]} points
 * @returns {[bigint, bigint]}
 */
function tableMean(points) {
  const gcd = (/** @type {bigint} */ a, /** @type {bigint} */ b) => { while (b) [a, b] = [b, a % b]; return a; };
  let sum = 0n;
  for (let i = 0; i + 1 < points.length; i++) {
    const u0 = BigInt(points[i][0]);
    const x0 = BigInt(points[i][1]);
    const L = BigInt(points[i + 1][0]) - u0;
    const dx = BigInt(points[i + 1][1]) - x0;
    // Σ_{v=0}^{L-1} floor(v · dx / L) = ((L − 1)(dx − 1) + gcd(L, dx) − 1) / 2 for dx ≥ 1.
    const floors = dx > 0n ? ((L - 1n) * (dx - 1n) + gcd(L, dx) - 1n) / 2n : 0n;
    sum += L * x0 + floors;
  }
  return [sum, TWO32];
}

test('the exact mean of a table', () => {
  // Brute force on a table whose segments are short enough to enumerate (the sum over u* is
  // scaled: tableMean returns the sum over every u* divided by 2^32).
  const pts = [[0, 3], [7, 10], [12, 10], [20, 25], [4294967296, 25]];
  let brute = 0n;
  for (let i = 0; i + 1 < 4; i++) for (let v = pts[i][0]; v < pts[i + 1][0]; v++) brute += BigInt(pts[i][1] + Math.floor(((v - pts[i][0]) * (pts[i + 1][1] - pts[i][1])) / (pts[i + 1][0] - pts[i][0])));
  brute += 25n * (4294967296n - 20n);
  assert.deepEqual(tableMean(pts), [brute, 4294967296n]);
  const ex = lower({ exponential: { mean: 1000000 } }).points;
  const [en, ed] = tableMean(ex);
  const rel = Number((en * 10n ** 7n) / ed) / 1e13; // in units of the mean
  assert.ok(Math.abs(rel - 1.000118) < 2e-6, `relative mean ${rel}`);
});
