// Radial arranger: the best-connected sibling at the centre, the rest on
// concentric rings by graph distance, ordered on each ring to keep connected
// nodes angularly close; rings are stretched to the target aspect (ellipse).
//
// A hub much larger than the nodes around it (an opened system or subsystem with its members inside) is not
// treated as a disc: its neighbours sit on rectangular rings that hug the hub's own rectangle, as many per ring as
// its perimeter holds. A disc around a large rectangle wastes the space between the rectangle and the circle, which
// at a fit zoom shrinks the hub (the subject of the picture) to a small part of the view.

import { NODE_GAP } from './constants.js';
import { adjacency } from './packed.js';

const TWO_PI = Math.PI * 2;
const ANGLE_SWEEPS = 3;
/** A ring at index r holds at most RING_CAP * r nodes; the overflow starts a new ring. */
const RING_CAP = 6;
/** Angular offset between consecutive rings so spokes do not line up. */
const RING_STAGGER = 0.6;
/** A hub whose diagonal is at least this many times the largest other node's is a large hub (rectangular rings). */
const LARGE_HUB = 2.5;

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

  let maxOther = 0;
  for (let i = 0; i < n; i++) if (i !== center) maxOther = Math.max(maxOther, diag[i]);
  const hubSize = /** @type {[number, number]} */ (size.get(ids[center]));
  const large = n > 1 && maxOther > 0 && diag[center] >= LARGE_HUB * maxOther;
  // The slot one node takes on a ring, and the rectangle of ring r (0-based) around a large hub.
  let slotW = 0, slotD = 0;
  for (let i = 0; i < n; i++) if (i !== center) { const s2 = /** @type {[number, number]} */ (size.get(ids[i])); slotW = Math.max(slotW, s2[0]); slotD = Math.max(slotD, s2[1]); }
  // The rings are stretched towards the target aspect, as the elliptic rings are.
  const ringRect = (/** @type {number} */ r) => {
    let w = hubSize[0] / 2 + NODE_GAP + slotW / 2 + r * (slotW + NODE_GAP);
    let d = hubSize[1] / 2 + NODE_GAP + slotD / 2 + r * (slotD + NODE_GAP);
    if (w / d < ctx.aspect) w = d * ctx.aspect; else d = Math.max(d, w / ctx.aspect);
    return [w, d];
  };
  const ringCap = (/** @type {number} */ r) => {
    if (!large) return RING_CAP * (r + 1);
    const [a, b] = ringRect(r);
    return Math.max(4, Math.floor((4 * (a + b)) / (slotW + NODE_GAP)));
  };
  /** @type {number[][]} rings[0] is ring 1 */
  const rings = [];
  // Around a large hub the rings fill in order of graph distance, each as full as its perimeter allows.
  for (const g of large ? [groups.flat()] : groups) {
    for (let k = 0; k < g.length;) {
      const cap = ringCap(rings.length);
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
  if (large) {
    // Rectangular rings: each node at the point of the ring's rectangle in its direction from the hub, then spread
    // along the perimeter in that order with at least one slot between neighbours.
    rings.forEach((ring, r) => {
      const [a, b] = ringRect(r);
      const per = 4 * (a + b);
      /** Perimeter parameter (0 at the right middle, counter-clockwise) of the direction theta. @param {number} theta */
      const param = (theta) => {
        const c = Math.cos(theta), sn = Math.sin(theta);
        const t = Math.min(Math.abs(c) > 1e-12 ? a / Math.abs(c) : Infinity, Math.abs(sn) > 1e-12 ? b / Math.abs(sn) : Infinity);
        const x = c * t, z = sn * t;
        if (Math.abs(x - a) < 1e-9 && z >= 0) return z;
        if (Math.abs(z - b) < 1e-9) return b + (a - x);
        if (Math.abs(x + a) < 1e-9) return b + 2 * a + (b - z);
        if (Math.abs(z + b) < 1e-9) return 3 * b + 2 * a + (x + a);
        return 4 * b + 4 * a + z; // right side, below the middle
      };
      /** A point of the ring at perimeter parameter q. @param {number} q @returns {[number, number]} */
      const point = (q) => {
        let u = ((q % per) + per) % per;
        if (u < b) return [a, u];
        u -= b; if (u < 2 * a) return [a - u, b];
        u -= 2 * a; if (u < 2 * b) return [-a, b - u];
        u -= 2 * b; if (u < 2 * a) return [-a + u, -b];
        u -= 2 * a; return [a, -b + u];
      };
      // Directions as perimeter parameters, unwrapped so that they increase in ring order.
      const want = ring.map((v) => param(angle[v]));
      for (let k = 1; k < want.length; k++) while (want[k] < want[k - 1]) want[k] += per;
      const step = slotW + NODE_GAP;
      // Keep each node near its own direction, at least one slot after the previous one; when that does not close
      // around the ring, space the ring evenly from its first node instead.
      const q = [];
      for (let k = 0; k < ring.length; k++) q.push(k === 0 ? want[0] : Math.max(want[k], q[k - 1] + step));
      if (ring.length > 1 && q[ring.length - 1] + step > q[0] + per) for (let k = 0; k < ring.length; k++) q[k] = want[0] + (k * per) / ring.length;
      ring.forEach((v, k) => pos.set(ids[v], point(q[k])));
    });
    return pos;
  }
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
