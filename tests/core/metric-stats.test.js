// The statistics of metric claims (src/core/metric-stats.js) give the figures docs/simulation.md
// states for the exact binomial test, the minimum run count, the sign-test interval, underpowered
// statistics and the run seeds.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { metricVerdict } from '../../src/core/metric-claims.js';
import {
  binomTail, binomialVerdict, cmp, evaluateRuns, minRuns, minSignTestRuns, parseRational, passesToFail,
  passesToHold, rat, runSeed, signTestRank, toDecimal, underpowered,
} from '../../src/core/metric-stats.js';

const B95 = parseRational('0.95');
const C95 = parseRational('0.95');

test('the minimum run count is the smallest N with beta^N <= alpha, compared exactly', () => {
  assert.equal(minRuns(B95, C95), 59);
  assert.equal(minRuns(parseRational('0.99'), C95), 299);
  assert.equal(minSignTestRuns(C95), 6);
  assert.equal(minSignTestRuns(parseRational('0.99')), 8);
});

test('the binomial test at the defaults and the documented run counts', () => {
  assert.equal(toDecimal(binomTail(59, 59, B95, 'ge')), '0.0485');
  assert.equal(binomialVerdict(59, 59, B95, C95), 'holds');
  assert.equal(binomialVerdict(59, 58, B95, C95), 'inconclusive');
  assert.equal(binomialVerdict(59, 53, B95, C95), 'inconclusive');
  assert.equal(binomialVerdict(59, 52, B95, C95), 'fails');
  assert.equal(toDecimal(binomTail(59, 52, B95, 'le'), 3), '0.027');
  assert.equal(toDecimal(binomTail(59, 53, B95, 'le'), 3), '0.074');
  // 93 runs allow one failure and fail at 9 or more; 150 allow two, fail at 13.
  for (const [N, allow, failAt] of [[93, 1, 9], [150, 2, 13]]) {
    assert.equal(N - passesToHold(N, B95, C95), allow, `${N} runs allow ${allow}`);
    assert.equal(N - passesToFail(N, B95, C95), failAt, `${N} runs fail at ${failAt}`);
  }
  // With N' = 58 fails needs 51 or fewer passes; with N' = 55, 48 or fewer; 91 of 92 does not hold.
  assert.equal(passesToFail(58, B95, C95), 51);
  assert.equal(passesToFail(55, B95, C95), 48);
  assert.equal(binomialVerdict(92, 91, B95, C95), 'inconclusive');
  assert.equal(toDecimal(binomTail(92, 91, B95, 'ge'), 3), '0.052');
});

test('the sign-test interval for 59 runs is [T(22), T(38)] with coverage 0.964', () => {
  const r = signTestRank(59, C95);
  assert.ok(r);
  assert.equal(r.j, 22);
  assert.equal(59 + 1 - r.j, 38);
  assert.equal(toDecimal(r.coverage, 3), '0.964');
  assert.equal(signTestRank(5, C95), null);
});

test('evaluating runs: underpowered, truncated, approx and the claim status', () => {
  const ms = (/** @type {number} */ x) => ({ seed: 's', value: rat(BigInt(x)) });
  const all = Array.from({ length: 59 }, (_, i) => ms(10 + (i % 5)));
  const ok = evaluateRuns(all, { op: '<=', bound: rat(30n), fraction: B95, confidence: C95, openStarted: true });
  assert.equal(ok.verdict, 'holds');
  assert.equal(ok.passes, 59);
  assert.ok(ok.margin && cmp(ok.margin, rat(16n, 30n)) === 0, 'margin (30 - 14) / 30 at the largest run');
  // One underpowered run left out of an open-started class makes holds impossible at N = 59.
  const left = evaluateRuns([...all.slice(1), { ...all[0], underpowered: true }], { op: '<=', bound: rat(30n), fraction: B95, confidence: C95, openStarted: true });
  assert.equal(left.kept, 58);
  assert.equal(left.verdict, 'inconclusive');
  // For a class not open-started the underpowered run does not satisfy.
  const closed = evaluateRuns([...all.slice(1), { ...all[0], underpowered: true, value: null }], { op: '<=', bound: rat(30n), fraction: B95, confidence: C95, openStarted: false });
  assert.equal(closed.kept, 59);
  assert.equal(closed.passes, 58);
  // +∞ fails an upper bound; seven failing runs fail the claim.
  const bad = evaluateRuns([...all.slice(7), ...Array.from({ length: 7 }, () => ({ seed: 's', value: /** @type {'inf'} */ ('inf') }))], { op: '<=', bound: rat(30n), fraction: B95, confidence: C95, openStarted: true });
  assert.equal(bad.verdict, 'fails');
  // approx: the interval [T(22), T(38)] against the band.
  const near = Array.from({ length: 59 }, (_, i) => ms(990 + i % 20));
  assert.equal(evaluateRuns(near, { approx: { value: rat(1000n), tolerance: parseRational('0.02') }, fraction: B95, confidence: C95, openStarted: true }).verdict, 'holds');
  assert.equal(evaluateRuns(near, { approx: { value: rat(500n), tolerance: parseRational('0.02') }, fraction: B95, confidence: C95, openStarted: true }).verdict, 'fails');
  assert.equal(evaluateRuns([...near.slice(1), { ...near[0], truncated: true }], { approx: { value: rat(1000n), tolerance: parseRational('0.02') }, fraction: B95, confidence: C95, openStarted: true }).verdict, 'inconclusive');
  // Status (decided in Lean): never verified; negatives must fail and control negatives hold.
  const verdictOf = (/** @type {any[]} */ scenarios, /** @type {any[]} */ negatives = [], /** @type {any[]} */ controlNegatives = []) => metricVerdict({ scenarios, negatives, controlNegatives });
  assert.equal(verdictOf([{ verdict: 'holds' }], [{ verdict: 'fails' }], [{ verdict: 'holds' }]).label, 'model-holds');
  assert.equal(verdictOf([{ verdict: 'holds' }], [{ verdict: 'fails' }], [{ verdict: 'holds' }]).strength, 'checkedOnInstances');
  assert.equal(verdictOf([{ verdict: 'holds' }], [{ verdict: 'holds' }]).label, 'inconclusive');
  assert.equal(verdictOf([{ verdict: 'fails' }]).label, 'violated');
});

test('underpowered statistics and run seeds', () => {
  assert.equal(underpowered({ statistic: 'p99', n: 2999 }), true);
  assert.equal(underpowered({ statistic: 'p99', n: 3000 }), false);
  assert.equal(underpowered({ statistic: 'mean', n: 29 }), true);
  assert.equal(underpowered({ statistic: 'ratio', n: 29999, bound: parseRational('0.001') }), true);
  assert.equal(underpowered({ statistic: 'ratio', n: 30000, bound: parseRational('0.001') }), false);
  assert.equal(underpowered({ statistic: 'max', n: 1 }), false);
  // Run r of base seed 1234567 is the r-th output of Vigna's splitmix64 seeded with 1234567.
  assert.deepEqual([0, 1, 2].map((r) => runSeed('1234567', r)), ['6457827717110365317', '3203168211198807973', '9817491932198370423']);
});
