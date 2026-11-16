// Placement quality score (lower is better).
//
//   aspect     = |ln((W / D) / opts.aspect)|        W, D: bounding box of every placed rectangle
//   edgeLength = mean centre-to-centre edge length / mean leaf diagonal
//                (all edges whose endpoints are both placed, self edges ignored)
//   crossings  = crossing pairs among straight centre-to-centre segments of
//                leaf-to-leaf edges / number of such edges; above MAX_CROSSING_EDGES
//                edges, every k-th edge (k = ceil(m / MAX_CROSSING_EDGES)) is used
//   area       = bounding-box area / sum of leaf areas   (whitespace factor, >= 1 for non-overlapping leaves)
//   total      = W_ASPECT * aspect + W_EDGE_LENGTH * edgeLength + W_CROSSINGS * crossings + W_AREA * area

import { DEFAULT_ASPECT } from './constants.js';

export const W_ASPECT = 3;
export const W_EDGE_LENGTH = 0.3;
export const W_CROSSINGS = 1;
export const W_AREA = 0.25;
export const MAX_CROSSING_EDGES = 400;

/**
 * @typedef {{ total: number, aspect: number, edgeLength: number, crossings: number, area: number }} Score
 */

/**
 * @param {import('../types.js').SceneModel} scene
 * @param {import('../types.js').Placement} placement
 * @param {{aspect?: number}} [opts]
 * @returns {Score}
 */
export function scorePlacement(scene, placement, opts = {}) {
  const target = opts.aspect && opts.aspect > 0 ? opts.aspect : DEFAULT_ASPECT;
  const parents = new Set();
  for (const n of scene.nodes) if (n.parent != null) parents.add(n.parent);

  let minX = Infinity, maxX = -Infinity, minZ = Infinity, maxZ = -Infinity;
  let leafCount = 0, leafArea = 0, leafDiag = 0;
  for (const n of scene.nodes) {
    const p = placement[n.id];
    if (!p) continue;
    minX = Math.min(minX, p.x - p.w / 2); maxX = Math.max(maxX, p.x + p.w / 2);
    minZ = Math.min(minZ, p.z - p.d / 2); maxZ = Math.max(maxZ, p.z + p.d / 2);
    if (!n.container && !parents.has(n.id)) {
      leafCount++; leafArea += p.w * p.d; leafDiag += Math.hypot(p.w, p.d);
    }
  }
  if (!Number.isFinite(minX) || leafCount === 0) return { total: 0, aspect: 0, edgeLength: 0, crossings: 0, area: 0 };
  const width = maxX - minX, depth = maxZ - minZ;
  const aspect = width > 0 && depth > 0 ? Math.abs(Math.log(width / depth / target)) : 0;
  const area = leafArea > 0 ? (width * depth) / leafArea : 0;

  let lenSum = 0, lenCount = 0;
  /** @type {[string, string][]} */
  const leafEdges = [];
  for (const e of scene.edges) {
    const a = placement[e.from], b = placement[e.to];
    if (!a || !b || e.from === e.to) continue;
    lenSum += Math.hypot(a.x - b.x, a.z - b.z);
    lenCount++;
    if (!parents.has(e.from) && !parents.has(e.to)) leafEdges.push([e.from, e.to]);
  }
  const meanDiag = leafDiag / leafCount;
  const edgeLength = lenCount && meanDiag > 0 ? lenSum / lenCount / meanDiag : 0;

  const step = Math.max(1, Math.ceil(leafEdges.length / MAX_CROSSING_EDGES));
  /** @type {[string, string][]} */
  const sample = [];
  for (let i = 0; i < leafEdges.length; i += step) sample.push(leafEdges[i]);
  const crossings = sample.length ? countCrossings(sample, placement) / sample.length : 0;

  const total = W_ASPECT * aspect + W_EDGE_LENGTH * edgeLength + W_CROSSINGS * crossings + W_AREA * area;
  return { total, aspect, edgeLength, crossings, area };
}

/**
 * Pairs of properly crossing segments; pairs sharing an endpoint node never count.
 * @param {[string, string][]} edges @param {import('../types.js').Placement} pl
 */
function countCrossings(edges, pl) {
  const m = edges.length;
  const ax = new Float64Array(m), az = new Float64Array(m), bx = new Float64Array(m), bz = new Float64Array(m);
  for (let i = 0; i < m; i++) {
    const a = pl[edges[i][0]], b = pl[edges[i][1]];
    ax[i] = a.x; az[i] = a.z; bx[i] = b.x; bz[i] = b.z;
  }
  let count = 0;
  for (let i = 0; i < m; i++) {
    const [fi, ti] = edges[i];
    for (let j = i + 1; j < m; j++) {
      const [fj, tj] = edges[j];
      if (fi === fj || fi === tj || ti === fj || ti === tj) continue;
      const d1 = orient(ax[j], az[j], bx[j], bz[j], ax[i], az[i]);
      const d2 = orient(ax[j], az[j], bx[j], bz[j], bx[i], bz[i]);
      if (d1 * d2 >= 0) continue;
      const d3 = orient(ax[i], az[i], bx[i], bz[i], ax[j], az[j]);
      const d4 = orient(ax[i], az[i], bx[i], bz[i], bx[j], bz[j]);
      if (d3 * d4 < 0) count++;
    }
  }
  return count;
}

/** @param {number} px @param {number} pz @param {number} qx @param {number} qz @param {number} rx @param {number} rz */
function orient(px, pz, qx, qz, rx, rz) {
  return (qx - px) * (rz - pz) - (qz - pz) * (rx - px);
}
