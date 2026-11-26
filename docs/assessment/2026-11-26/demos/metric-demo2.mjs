import { lowerDistribution, tableMean, pinnedTables } from '../../../../src/core/distributions.js';
const mean = (d) => { const t = lowerDistribution(d); const [n, den] = tableMean(t.points); return [Number(n) / Number(den), t]; };
for (const m of [1, 2, 3, 5, 10, 100, 1250]) {
  const [mu] = mean({ exponential: { mean: String(m) } });
  console.log(`exponential mean ${m}: table mean ${mu.toFixed(4)}  rel.err ${((mu - m) / m * 100).toFixed(2)}%`);
}
for (const [M, s] of [[1000, '1'], [1000, '2'], [1000, '3'], [1000, '4'], [1, '5.5']]) {
  try {
    const [mu, t] = mean({ lognormal: { median: M, sigma: s } });
    const truth = M * Math.exp(Number(s) ** 2 / 2);
    const max = t.points[t.points.length - 1][1];
    console.log(`lognormal median ${M} sigma ${s}: table mean ${mu.toExponential(4)} true ${truth.toExponential(4)} ratio ${(mu / truth).toFixed(4)} max ${max}`);
  } catch (e) { console.log(`lognormal ${M} ${s}: ${e.message}`); }
}
// p99 parameterisation: requested p99 vs table quantile at u = 0.99
for (const [M, P] of [[1000, 4000], [10, 40], [3, 5]]) {
  const t = lowerDistribution({ lognormal: { median: M, p99: P } });
  const pts = t.points; const u99 = Math.round(0.99 * 2 ** 32);
  // find segment
  let q; for (let i = 0; i + 1 < pts.length; i++) if (u99 >= pts[i][0] && u99 < pts[i+1][0]) q = pts[i][1] + Math.floor((u99 - pts[i][0]) * (pts[i+1][1] - pts[i][1]) / (pts[i+1][0] - pts[i][0]));
  const [n, d] = tableMean(pts);
  console.log(`lognormal median ${M} p99 ${P}: table p99 ${q}, table median ${pts[513][1]}, table mean ${(Number(n)/Number(d)).toFixed(3)}`);
}
// empirical two-point
const e = lowerDistribution({ empirical: { samples: [0, 1000000] } });
const [en, ed] = tableMean(e.points);
console.log('empirical {0,1e6}: table mean', Number(en) / Number(ed), 'true 500000; values strictly between 0 and 1e6 occur with prob', 1/1024);
