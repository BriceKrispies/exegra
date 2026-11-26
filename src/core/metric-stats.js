// The statistics of metric claims (format 2, WG-4715; docs/simulation.md, "Claims over metrics"):
// the exact binomial test over independent seeded runs, the minimum run count, the sign-test
// interval of the median for `approx`, the margin, and the verdict with its basis. Every
// probability is an exact rational on BigInt; nothing here uses floating point or randomness.
// Pure; no I/O.

/** @typedef {{n: bigint, d: bigint}} Rational   d > 0, not necessarily reduced */

/** @param {bigint} a @param {bigint} b @returns {bigint} */
function gcd(a, b) {
  if (a < 0n) a = -a;
  while (b) [a, b] = [b, a % b];
  return a;
}

/** @param {bigint} n @param {bigint} [d] @returns {Rational} */
export function rat(n, d = 1n) {
  if (d === 0n) throw new Error('zero denominator');
  if (d < 0n) { n = -n; d = -d; }
  const g = gcd(n, d) || 1n;
  return { n: n / g, d: d / g };
}

/** @param {Rational} a @param {Rational} b */
export const cmp = (a, b) => {
  const l = a.n * b.d;
  const r = b.n * a.d;
  return l < r ? -1 : l > r ? 1 : 0;
};

/**
 * An exact decimal (`"0.95"`, `"30"`, `0.5`) or a `[num, den]` pair as a rational.
 * @param {string|number|bigint|[any, any]|Rational} v
 * @returns {Rational}
 */
export function parseRational(v) {
  if (typeof v === 'object' && v && 'n' in v) return rat(v.n, v.d);
  if (Array.isArray(v)) return rat(BigInt(v[0]), BigInt(v[1]));
  if (typeof v === 'bigint') return rat(v);
  const s = String(v);
  const m = /^(-?)(\d+)(?:\.(\d+))?$/.exec(s);
  if (!m) throw new Error(`"${s}" is not an exact decimal.`);
  const frac = m[3] ?? '';
  const n = BigInt(m[2] + frac);
  return rat(m[1] ? -n : n, 10n ** BigInt(frac.length));
}

/** @param {number} n @param {number} k @returns {bigint} */
function choose(n, k) {
  if (k < 0 || k > n) return 0n;
  k = Math.min(k, n - k);
  let r = 1n;
  for (let i = 1; i <= k; i++) r = (r * BigInt(n - k + i)) / BigInt(i);
  return r;
}

/**
 * P[Bin(N, p) ≥ k] (`upper`) or P[Bin(N, p) ≤ k] (lower), exactly.
 * @param {number} N @param {number} k @param {Rational} p @param {'ge'|'le'} side
 * @returns {Rational}
 */
export function binomTail(N, k, p, side) {
  const q = p.d - p.n;
  let num = 0n;
  const lo = side === 'ge' ? Math.max(0, k) : 0;
  const hi = side === 'ge' ? N : Math.min(N, k);
  for (let i = lo; i <= hi; i++) num += choose(N, i) * p.n ** BigInt(i) * q ** BigInt(N - i);
  return rat(num, p.d ** BigInt(N));
}

/**
 * The smallest N with β^N ≤ α (compared exactly), α = 1 − confidence: the fewest runs with which
 * a claim can ever hold.
 * @param {Rational} beta @param {Rational} confidence
 */
export function minRuns(beta, confidence) {
  const alpha = rat(confidence.d - confidence.n, confidence.d);
  if (cmp(beta, rat(1n)) >= 0) return Infinity;
  if (beta.n === 0n) return 1;
  let N = 1;
  let pw = rat(beta.n, beta.d);
  while (cmp(pw, alpha) > 0) {
    N += 1;
    pw = rat(pw.n * beta.n, pw.d * beta.d);
  }
  return N;
}

/**
 * The binomial test on `k` passes out of `N` kept runs.
 * @param {number} N @param {number} k @param {Rational} beta @param {Rational} confidence
 * @returns {'holds'|'fails'|'inconclusive'}
 */
export function binomialVerdict(N, k, beta, confidence) {
  const alpha = rat(confidence.d - confidence.n, confidence.d);
  if (N > 0 && cmp(binomTail(N, k, beta, 'ge'), alpha) <= 0) return 'holds';
  if (N > 0 && cmp(binomTail(N, k, beta, 'le'), alpha) <= 0) return 'fails';
  return 'inconclusive';
}

/** The smallest number of passes out of N for which the test reads holds (Infinity if none). @param {number} N @param {Rational} beta @param {Rational} confidence */
export function passesToHold(N, beta, confidence) {
  for (let k = 0; k <= N; k++) if (binomialVerdict(N, k, beta, confidence) === 'holds') return k;
  return Infinity;
}

/** The largest number of passes out of N for which the test reads fails (-1 if none). @param {number} N @param {Rational} beta @param {Rational} confidence */
export function passesToFail(N, beta, confidence) {
  for (let k = N; k >= 0; k--) if (binomialVerdict(N, k, beta, confidence) === 'fails') return k;
  return -1;
}

/**
 * About how many runs would decide an inconclusive result: the smallest M ≥ N at which the same
 * number of failing runs still reads holds. Capped at 100,000.
 * @param {number} N @param {number} k @param {Rational} beta @param {Rational} confidence
 */
export function runsToDecide(N, k, beta, confidence) {
  const f = N - k;
  for (let M = Math.max(N, 1); M <= 100000; M++) if (binomialVerdict(M, M - f, beta, confidence) === 'holds') return M;
  return null;
}

/**
 * The sign-test interval of the median: the largest j with P[j ≤ Bin(N, 1/2) ≤ N − j] ≥ 1 − α,
 * so that [T_(j), T_(N+1−j)] covers the median. Null when even j = 1 does not reach 1 − α.
 * @param {number} N @param {Rational} confidence
 * @returns {{j: number, coverage: Rational} | null}
 */
export function signTestRank(N, confidence) {
  const half = rat(1n, 2n);
  /** @type {{j: number, coverage: Rational} | null} */
  let best = null;
  for (let j = 1; 2 * j <= N; j++) {
    // P[j ≤ X ≤ N − j] = 1 − 2 P[X ≤ j − 1]
    const below = binomTail(N, j - 1, half, 'le');
    const cov = rat(below.d - 2n * below.n, below.d);
    if (cmp(cov, confidence) >= 0) best = { j, coverage: cov };
    else break;
  }
  return best;
}

/** The fewest kept runs a calibration needs: the smallest N with 2^(1−N) ≤ α. @param {Rational} confidence */
export function minSignTestRuns(confidence) {
  const alpha = rat(confidence.d - confidence.n, confidence.d);
  let N = 1;
  while (cmp(rat(1n, 1n << BigInt(N - 1)), alpha) > 0) N += 1;
  return N;
}

/**
 * @typedef {{seed: string, value: Rational | null | 'inf', underpowered?: boolean, truncated?: boolean,
 *   samples?: number, infinite?: number, duplicates?: number}} RunStatistic
 *   `value`: the per-run statistic; null when undefined or empty; 'inf' for +∞; `duplicates`: starts of the
 *   class refused as duplicates in the run (its sample count then depends on the system).
 */

/**
 * Whether one run's statistic satisfies `op bound`. Undefined, +∞ against an upper bound, and a
 * truncated run do not.
 * @param {RunStatistic} r @param {string} op @param {Rational} bound
 */
export function satisfies(r, op, bound) {
  if (r.truncated || r.value === null) return false;
  if (r.value === 'inf') return op === '>=' || op === '>';
  const c = cmp(r.value, bound);
  return op === '<=' ? c <= 0 : op === '<' ? c < 0 : op === '>=' ? c >= 0 : c > 0;
}

/** @param {Rational|'inf'} a @param {Rational|'inf'} b */
const cmpStat = (a, b) => (a === 'inf' ? (b === 'inf' ? 0 : 1) : b === 'inf' ? -1 : cmp(a, b));

/**
 * Evaluate one scenario's runs of a metric-bound claim: keep the runs (an underpowered run is
 * left out for an open-started class and fails otherwise), count the passes, and decide.
 * `openStarted` must be stated true to leave anything out (src/core/metric-claims.js computes it from
 * the input); absent, the class is not open-started, so a collapse never turns fails into inconclusive.
 * A run with duplicate starts is never left out: its sample count depended on the system.
 * @param {RunStatistic[]} runs
 * @param {{op?: string, bound?: Rational, approx?: {value: Rational, tolerance: Rational},
 *   fraction: Rational, confidence: Rational, openStarted?: boolean}} spec
 */
export function evaluateRuns(runs, spec) {
  const open = spec.openStarted === true;
  const leaveOut = (/** @type {RunStatistic} */ r) => !!r.underpowered && open && !r.duplicates;
  // A kept underpowered run (a class not open-started, or a run with duplicate starts) does not satisfy.
  const kept = runs.filter((r) => !leaveOut(r)).map((r) => (r.underpowered ? { ...r, value: null } : r));
  const left = runs.length - kept.length;
  const truncated = runs.filter((r) => r.truncated).length;
  const underpowered = runs.filter((r) => r.underpowered).length;
  const finite = /** @type {Rational[]} */ (kept.map((r) => r.value).filter((v) => v !== null && v !== 'inf'));
  const sorted = [...finite].sort(cmp);
  const spread = sorted.length ? { min: sorted[0], median: sorted[Math.floor((sorted.length - 1) / 2)], max: sorted[sorted.length - 1] } : null;
  const base = { runs: runs.length, kept: kept.length, leftOut: left, truncated, underpowered, spread };
  if (spec.approx) {
    const { value: v, tolerance: tol } = spec.approx;
    const rank = signTestRank(kept.length, spec.confidence);
    if (truncated || !rank || kept.some((r) => r.value === null)) return { ...base, verdict: /** @type {const} */ ('inconclusive'), interval: null };
    const vals = /** @type {(Rational|'inf')[]} */ (kept.map((r) => r.value)).sort(cmpStat);
    const lo = vals[rank.j - 1];
    const hi = vals[kept.length - rank.j];
    const bandLo = rat(v.n * (tol.d - tol.n), v.d * tol.d);
    const bandHi = rat(v.n * (tol.d + tol.n), v.d * tol.d);
    let verdict = /** @type {'holds'|'fails'|'inconclusive'} */ ('inconclusive');
    if (lo !== 'inf' && hi !== 'inf' && cmp(lo, bandLo) >= 0 && cmp(hi, bandHi) <= 0) verdict = 'holds';
    else if ((lo === 'inf' || cmp(lo, bandHi) > 0) || (hi !== 'inf' && cmp(hi, bandLo) < 0)) verdict = 'fails';
    /** @type {Rational|null} */
    let margin = null;
    if (verdict === 'holds' && lo !== 'inf' && hi !== 'inf') {
      const a = rat(bandHi.n * hi.d - hi.n * bandHi.d, bandHi.d * hi.d);
      const b = rat(lo.n * bandLo.d - bandLo.n * lo.d, lo.d * bandLo.d);
      const m = cmp(a, b) <= 0 ? a : b;
      margin = rat(m.n * v.d, m.d * v.n);
    }
    return { ...base, verdict, interval: { lo, hi, j: rank.j, coverage: rank.coverage }, margin };
  }
  const op = /** @type {string} */ (spec.op);
  const bound = /** @type {Rational} */ (spec.bound);
  const k = kept.filter((r) => satisfies(r, op, bound)).length;
  const verdict = binomialVerdict(kept.length, k, spec.fraction, spec.confidence);
  // Margin at the rank the test uses (docs/simulation.md, Calibration and sensitivity).
  /** @type {Rational|null} */
  let margin = null;
  const need = passesToHold(kept.length, spec.fraction, spec.confidence);
  if (verdict === 'holds' && bound.n !== 0n && Number.isFinite(need)) {
    const upper = op === '<=' || op === '<';
    const vals = /** @type {(Rational|'inf')[]} */ (kept.map((r) => r.value ?? 'inf')).sort(cmpStat);
    if (!upper) vals.reverse();
    const t = vals[need - 1];
    if (t !== 'inf') margin = upper ? rat((bound.n * t.d - t.n * bound.d) * bound.d, bound.d * t.d * bound.n) : rat((t.n * bound.d - bound.n * t.d) * bound.d, t.d * bound.d * bound.n);
  }
  return { ...base, verdict, passes: k, margin, decideAt: verdict === 'inconclusive' ? runsToDecide(kept.length, k, spec.fraction, spec.confidence) : null };
}

/**
 * Combine the per-scenario results with the negatives into the claim's result: holds only when
 * every scenario holds, every negative fails and every control negative holds; a scenario that
 * fails makes the claim violated. Never `verified` or `supported`.
 * @param {{verdict: string}[]} scenarios
 * @param {{verdict: string}[]} negatives
 * @param {{verdict: string}[]} controlNegatives
 * @returns {{status: 'model-holds'|'violated'|'inconclusive', reason: string}}
 */
export function claimStatus(scenarios, negatives = [], controlNegatives = []) {
  if (scenarios.some((s) => s.verdict === 'fails')) return { status: 'violated', reason: 'a scenario fails' };
  if (scenarios.some((s) => s.verdict !== 'holds')) return { status: 'inconclusive', reason: 'a scenario is inconclusive' };
  if (negatives.some((n) => n.verdict !== 'fails')) return { status: 'inconclusive', reason: 'a negative does not fail (vacuous)' };
  if (controlNegatives.some((n) => n.verdict !== 'holds')) return { status: 'inconclusive', reason: 'a control negative does not hold (fails for another reason)' };
  return { status: 'model-holds', reason: 'model only; parameters as stated' };
}

/**
 * Whether a statistic is underpowered: a quantile q with n·(1 − q) < 30, a mean with n < 30, a
 * ratio with bound b and denominator d with d·min(b, 1 − b) < 30.
 * @param {{statistic: string, n: number, bound?: Rational}} s
 */
export function underpowered(s) {
  const m = /^p(\d+(?:\.\d+)?)$/.exec(s.statistic);
  if (m) {
    const q = parseRational(`0.${m[1].replace('.', '')}`);
    return BigInt(s.n) * (q.d - q.n) < 30n * q.d;
  }
  if (s.statistic === 'mean') return s.n < 30;
  if (s.statistic === 'ratio' && s.bound) {
    const b = s.bound;
    const minb = cmp(b, rat(1n, 2n)) <= 0 ? b : rat(b.d - b.n, b.d);
    return BigInt(s.n) * minb.n < 30n * minb.d;
  }
  return false;
}

/** Seed of run r for base seed s: the r-th SplitMix64 output of s, as a decimal string. @param {string|bigint} s @param {number} r */
export function runSeed(s, r) {
  const M = (1n << 64n) - 1n;
  let z = (BigInt(s) + BigInt(r + 1) * 0x9E3779B97F4A7C15n) & M;
  z = ((z ^ (z >> 30n)) * 0xBF58476D1CE4E5B9n) & M;
  z = ((z ^ (z >> 27n)) * 0x94D049BB133111EBn) & M;
  return String(z ^ (z >> 31n));
}

/** A rational as a decimal string with `digits` places (for display only). @param {Rational} r @param {number} [digits] */
export function toDecimal(r, digits = 4) {
  const scale = 10n ** BigInt(digits);
  const neg = r.n < 0n;
  const v = ((neg ? -r.n : r.n) * scale * 2n + r.d) / (2n * r.d);
  const s = v.toString().padStart(digits + 1, '0');
  return `${neg ? '-' : ''}${s.slice(0, -digits)}.${s.slice(-digits)}`;
}
