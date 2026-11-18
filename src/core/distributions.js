// Lowering of distributions to the integer forms the engine reads (format 2, WG-4715): the pinned
// quantile tables `Qexp` and `Qnorm` on the standard grid, the fixed-point `exp_fp` and `ln_fp`,
// and the families `exponential`, `lognormal`, `empirical`, `uniform` and `constant`. Every step is
// integer arithmetic on BigInt, specified to the bit in docs/simulation.md ("Lowering
// distributions"), so every implementation derives the same engine input; no Math function and
// no Number arithmetic touches a value. Pure; no I/O.

/** Scale of the fixed-point arithmetic, 2^96. */
export const S = 1n << 96n;
/** round(ln 2 · S). */
export const LN2 = 54916777467707473351141471128n;
/** round(Φ⁻¹(0.99) · S). */
export const Z99 = 184312267429221101812985515261n;
/** Scale of the normal CDF evaluation, 2^192, and its constants. */
export const W = 1n << 192n;
export const LN2_W = 4350955369971217654477563090224794165364344896676135745070n;
export const ISQ2PI_W = 2504201280626952864894549311249338563268063356138482501337n;

const TWO32 = 1n << 32n;
const TWO53 = 1n << 53n;
const TWO64 = 1n << 64n;

/** Floor division for b > 0. @param {bigint} a @param {bigint} b */
export function floorDiv(a, b) {
  const q = a / b;
  return a % b !== 0n && a < 0n ? q - 1n : q;
}

/** n / d rounded half to even, d > 0. @param {bigint} n @param {bigint} d */
export function roundHalfEven(n, d) {
  const q = floorDiv(n, d);
  const r2 = 2n * (n - q * d);
  if (r2 > d) return q + 1n;
  if (r2 < d) return q;
  return q % 2n === 0n ? q : q + 1n;
}

/** @param {bigint} x @param {bigint} k */
const shift = (x, k) => (k >= 0n ? x << k : floorDiv(x, 1n << -k));

/** exp at scale `scale` with ln 2 `ln2` at that scale. @param {bigint} x @param {bigint} scale @param {bigint} ln2 */
function expAt(x, scale, ln2) {
  const k = floorDiv(x, ln2);
  const r = x - k * ln2;
  let t = scale;
  let s = 0n;
  let n = 0n;
  do {
    s += t;
    n += 1n;
    t = floorDiv(t * r, n * scale);
  } while (t !== 0n);
  return shift(s, k);
}

/** `exp_fp(x)` for `x` at scale S, of either sign. @param {bigint} x */
export const expFp = (x) => expAt(x, S, LN2);

/** Number of bits of a positive integer. @param {bigint} y */
const bitLength = (y) => BigInt(y.toString(2).length);

/** `ln_fp(y)` for `y > 0` at scale S. @param {bigint} y */
export function lnFp(y) {
  if (y <= 0n) throw new Error('ln_fp needs a positive argument.');
  const k = bitLength(y) - 97n;
  const m = k < 0n ? y << -k : y >> k;
  const s = floorDiv((m - S) * S, m + S);
  const s2 = floorDiv(s * s, S);
  let t = s;
  let acc = 0n;
  let j = 0n;
  do {
    acc += floorDiv(t, 2n * j + 1n);
    j += 1n;
    t = floorDiv(t * s2, S);
  } while (t !== 0n);
  return 2n * acc + k * LN2;
}

/** The standard grid: `k · 2^22` for k = 0 … 1023, `2^32 − 2^(32−j)` for j = 11 … 31, then 2^32. */
export const GRID = (() => {
  /** @type {bigint[]} */
  const g = [];
  for (let k = 0n; k < 1024n; k++) g.push(k << 22n);
  for (let j = 11n; j <= 31n; j++) g.push(TWO32 - (1n << (32n - j)));
  g.push(TWO32);
  return g;
})();

/** `Qexp(u)`: the unit-mean exponential quantile at scale 2^−64, for a grid point `u > 0`. @param {bigint} u */
export function qexp(u) {
  const y = u === TWO32 ? 1n << 63n : (TWO32 - u) << 64n;
  return roundHalfEven(-lnFp(y), TWO32);
}

/** Φ at scale W of `x` at scale W. @param {bigint} x */
export function phiW(x) {
  const a = x < 0n ? -x : x;
  const a2 = floorDiv(a * a, W);
  let term = a;
  let total = 0n;
  let n = 0n;
  do {
    total += term;
    n += 1n;
    term = floorDiv(term * a2, W * (2n * n + 1n));
  } while (term !== 0n);
  const dens = floorDiv(ISQ2PI_W * expAt(-floorDiv(a2, 2n), W, LN2_W), W);
  const half = floorDiv(dens * total, W);
  return x >= 0n ? W / 2n + half : W / 2n - half;
}

/** `Qnorm(u)`: the standard normal quantile at scale 2^−64, for a grid point `u > 0`. @param {bigint} u */
export function qnorm(u) {
  const pW = u === TWO32 ? W - (1n << 159n) : u << 160n;
  let lo = -8n * TWO64;
  let hi = 8n * TWO64;
  while (lo < hi) {
    const mid = floorDiv(lo + hi, 2n);
    if (phiW((2n * mid + 1n) << 127n) >= pW) hi = mid;
    else lo = mid + 1n;
  }
  return lo;
}

/** @type {{u: bigint, qexp: bigint, qnorm: bigint}[] | null} */
let pinned = null;

/** The pinned tables on the grid points with `u > 0`, computed once. */
export function pinnedTables() {
  if (!pinned) pinned = GRID.slice(1).map((u) => ({ u, qexp: qexp(u), qnorm: qnorm(u) }));
  return pinned;
}

/** The canonical text of the pinned tables, whose SHA-256 the specification pins. */
export function canonicalTableText() {
  return pinnedTables().map((r) => `${r.u} ${r.qexp} ${r.qnorm}\n`).join('');
}

/** The engine input's `unitExponential` table, `[[0, 0], [u, Qexp(u)], ...]`, as decimal strings. */
export function unitExponentialTable() {
  return [['0', '0'], ...pinnedTables().map((r) => [String(r.u), String(r.qexp)])];
}

/**
 * Parse an exact non-negative decimal (`"0.59"`, `"12"`, `"1e3"` not accepted) to `[num, den]`.
 * @param {string|number|bigint} v
 * @returns {[bigint, bigint]}
 */
export function exactDecimal(v) {
  if (typeof v === 'bigint') return [v, 1n];
  const s = String(v);
  const m = /^(\d+)(?:\.(\d+))?$/.exec(s);
  if (!m) throw new Error(`"${s}" is not an exact non-negative decimal.`);
  const frac = m[2] ?? '';
  return [BigInt(m[1] + frac), 10n ** BigInt(frac.length)];
}

/** @param {bigint} x @param {string} path */
function bounded(x, path) {
  if (x >= TWO53) throw new Error(`Distribution "${path}" lowers to values of 2^53 base units or more.`);
  return Number(x);
}

/**
 * Lower a family to an engine distribution (`fixed`, `uniform` or `table`). Values are in base
 * units already: `mean`, `median`, `p99`, `lo`, `hi`, `value` and samples are integers or exact
 * decimals of base units.
 * @param {any} d one of `{constant}`, `{uniform: {lo, hi}}`, `{exponential: {mean}}`,
 *   `{lognormal: {median, p99} | {median, sigma}}`, `{empirical: {samples} | {quantiles}}`
 * @param {string} [path]
 * @returns {{kind: 'fixed', value: number} | {kind: 'uniform', lo: number, hi: number} | {kind: 'table', points: number[][]}}
 */
export function lowerDistribution(d, path = 'distribution') {
  if ('constant' in d) {
    const [n, den] = exactDecimal(d.constant);
    if (n % den !== 0n) throw new Error(`Distribution "${path}" is not a whole number of base units.`);
    return { kind: 'fixed', value: bounded(n / den, path) };
  }
  if ('uniform' in d) {
    const lo = BigInt(d.uniform.lo);
    const hi = BigInt(d.uniform.hi);
    if (lo > hi) throw new Error(`Distribution "${path}" has lo above hi.`);
    return { kind: 'uniform', lo: bounded(lo, path), hi: bounded(hi, path) };
  }
  if ('exponential' in d) {
    const [a, b] = exactDecimal(d.exponential.mean);
    const pts = [[0, 0]];
    for (const r of pinnedTables()) pts.push([Number(r.u), bounded(roundHalfEven(a * r.qexp, b * TWO64), path)]);
    return { kind: 'table', points: pts };
  }
  if ('lognormal' in d) {
    const sigma = lognormalSigma(d.lognormal, path);
    const [mn, md] = exactDecimal(d.lognormal.median);
    if (mn % md !== 0n) throw new Error(`Distribution "${path}" has a median that is not a whole number of base units.`);
    const M = mn / md;
    const pts = [[0, 0]];
    for (const r of pinnedTables()) {
      const z = r.qnorm << 32n;
      pts.push([Number(r.u), bounded(roundHalfEven(M * expFp(floorDiv(sigma * z, S)), S), path)]);
    }
    return { kind: 'table', points: pts };
  }
  if ('empirical' in d) {
    const e = d.empirical;
    if (Array.isArray(e.samples)) {
      const s = e.samples.map((/** @type {any} */ x) => BigInt(x)).sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
      if (!s.length) throw new Error(`Distribution "${path}" has no samples.`);
      const n = BigInt(s.length);
      const pts = [[0, bounded(s[0], path)]];
      for (const u of GRID.slice(1)) {
        let rank = (u * n + TWO32 - 1n) / TWO32;
        if (rank < 1n) rank = 1n;
        pts.push([Number(u), bounded(s[Number(rank - 1n)], path)]);
      }
      return { kind: 'table', points: pts };
    }
    if (Array.isArray(e.quantiles)) {
      /** @type {number[][]} */
      const pts = [];
      let prevU = -1n;
      for (const [p, x] of e.quantiles) {
        const [pn, pd] = exactDecimal(p);
        const u = roundHalfEven(pn * TWO32, pd);
        if (u <= prevU) throw new Error(`Distribution "${path}" has two quantiles at the same table point.`);
        prevU = u;
        pts.push([Number(u), bounded(BigInt(x), path)]);
      }
      if (pts[0][0] !== 0 || BigInt(pts[pts.length - 1][0]) !== TWO32) throw new Error(`Distribution "${path}" must give quantiles from 0 to 1.`);
      return { kind: 'table', points: pts };
    }
  }
  throw new Error(`Distribution "${path}" has an unknown family.`);
}

/**
 * σ at scale S of a log-normal: from `{median: M, p99: P}` or `{median, sigma}`.
 * @param {{median: any, p99?: any, sigma?: any}} l @param {string} [path]
 */
export function lognormalSigma(l, path = 'distribution') {
  let sigma;
  if (l.p99 !== undefined) {
    const M = BigInt(l.median);
    const P = BigInt(l.p99);
    if (M < 1n || P <= M || P > 1000000n * M) throw new Error(`Distribution "${path}" needs 1 ≤ median < p99 ≤ 10^6 · median.`);
    sigma = floorDiv(lnFp(floorDiv(P * S, M)) * S, Z99);
  } else {
    const [n, d] = exactDecimal(l.sigma);
    sigma = floorDiv(n * S, d);
  }
  if (sigma > 8n * S) throw new Error(`Distribution "${path}" has sigma above 8.`);
  return sigma;
}

/**
 * The exact mean of an engine table, as `[num, den]`: the trapezoid sum less the floor of the
 * interpolation, computed over every `u*` in [0, 2^32).
 * @param {(number|string|bigint)[][]} points
 * @returns {[bigint, bigint]}
 */
export function tableMean(points) {
  let sum = 0n;
  for (let i = 0; i + 1 < points.length; i++) {
    const u0 = BigInt(points[i][0]);
    const x0 = BigInt(points[i][1]);
    const u1 = BigInt(points[i + 1][0]);
    const x1 = BigInt(points[i + 1][1]);
    const L = u1 - u0;
    const dx = x1 - x0;
    // Σ_{v=0}^{L-1} floor(v · dx / L) = ((L − 1)(dx − 1) + gcd(L, dx) − 1) / 2 for dx ≥ 1.
    let floors = 0n;
    if (dx > 0n) floors = ((L - 1n) * (dx - 1n) + gcd(L, dx) - 1n) / 2n;
    sum += L * x0 + floors;
  }
  return [sum, TWO32];
}

/** @param {bigint} a @param {bigint} b @returns {bigint} */
function gcd(a, b) {
  while (b) [a, b] = [b, a % b];
  return a;
}
