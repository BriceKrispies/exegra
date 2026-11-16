// Radial arranger: the best-connected sibling at the centre, the rest on
// concentric rings by graph distance, ordered on each ring to keep connected
// nodes angularly close; rings are stretched to the target aspect (ellipse).

import { NODE_GAP } from './constants.js';
import { adjacency } from './packed.js';

const TWO_PI = Math.PI * 2;
const ANGLE_SWEEPS = 3;
/** A ring at index r holds at most RING_CAP * r nodes; the overflow starts a new ring. */
const RING_CAP = 6;
/** Angular offset between consecutive rings so spokes do not line up. */
const RING_STAGGER = 0.6;

/** @type {import('./solve.js').Arranger} */
export function arrangeRadial(ids, pairs, size, ctx) {
  const n = ids.length;
  /** @type {Map<string, [number, number]>} */
  const pos = new Map();
  if (!n) return pos;
  const diag = ids.map((id) => { const s = /** @type {[number, number]} */ (size.get(id)); return Math.hypot(s[0], s[1]); });
  const adj = adjacency(ids, pairs);
  const degree = adj.map((m) => { let s = 0; for (const c of m.values()) s += c; return s; });

  let center = 0;
  for (let i = 1; i < n; i++) if (degree[i] > degree[center]) center = i;

  // Breadth-first distance from the centre (undirected), in index order.
  const dist = new Int32Array(n).fill(-1);
  dist[center] = 0;
  const queue = [center];
  let maxDist = 0;
  for (let h = 0; h < queue.length; h++) {
    const v = queue[h];
    for (const u of [...adj[v].keys()].sort((a, b) => a - b)) {
      if (dist[u] < 0) { dist[u] = dist[v] + 1; maxDist = Math.max(maxDist, dist[u]); queue.push(u); }
    }
  }
  /** @type {number[][]} */
  const groups = Array.from({ length: maxDist }, () => []);
  /** @type {number[]} */ const detached = [];
  /** @type {number[]} */ const loose = [];
  for (let i = 0; i < n; i++) {
    if (i === center) continue;
    if (dist[i] > 0) groups[dist[i] - 1].push(i);
    else if (degree[i] > 0) detached.push(i);
    else loose.push(i); // edge-free at this level: outermost rings
  }
  groups.push(detached, loose);

  /** @type {number[][]} rings[0] is ring 1 */
  const rings = [];
  for (const g of groups) {
    for (let k = 0; k < g.length;) {
      const cap = RING_CAP * (rings.length + 1);
      rings.push(g.slice(k, k + cap));
      k += cap;
    }
  }

  const angle = new Float64Array(n);
  const hasAngle = new Uint8Array(n);
  const offset = rings.map((_, r) => (r + 1) * RING_STAGGER);
  const spread = (/** @type {number} */ r) => {
    const ring = rings[r];
    ring.forEach((v, k) => { angle[v] = offset[r] + (TWO_PI * k) / ring.length; hasAngle[v] = 1; });
  };
  rings.forEach((_, r) => spread(r));
  for (let s = 0; s < ANGLE_SWEEPS; s++) {
    for (let r = 0; r < rings.length; r++) {
      const ring = rings[r];
      if (ring.length < 2) continue;
      /** @type {Map<number, number>} */
      const key = new Map();
      for (const v of ring) {
        let sx = 0, sz = 0, cnt = 0;
        for (const [u, c] of adj[v]) {
          if (u === center || !hasAngle[u]) continue;
          sx += c * Math.cos(angle[u]); sz += c * Math.sin(angle[u]); cnt += c;
        }
        let a = cnt && (Math.abs(sx) > 1e-9 || Math.abs(sz) > 1e-9) ? Math.atan2(sz, sx) : angle[v];
        a = ((a % TWO_PI) + TWO_PI) % TWO_PI;
        key.set(v, a);
      }
      ring.sort((a, b) => /** @type {number} */ (key.get(a)) - /** @type {number} */ (key.get(b)) || a - b);
      spread(r);
    }
  }

  // Radii: neighbours on a ring (and nodes of adjacent rings) must not overlap,
  // each node being treated as its circumscribed disc.
  const sx = Math.max(1, ctx.aspect);
  const sz = Math.max(1, 1 / ctx.aspect);
  pos.set(ids[center], [0, 0]);
  let prevR = 0;
  let prevDiag = diag[center];
  rings.forEach((ring, r) => {
    let md = 0;
    for (const v of ring) md = Math.max(md, diag[v]);
    let radius = prevR + (prevDiag + md) / 2 + NODE_GAP;
    if (ring.length > 1) radius = Math.max(radius, (md + NODE_GAP) / (2 * Math.sin(Math.PI / ring.length)));
    for (const v of ring) pos.set(ids[v], [sx * radius * Math.cos(angle[v]), sz * radius * Math.sin(angle[v])]);
    prevR = radius;
    prevDiag = md;
    void r;
  });
  return pos;
}
