// Placement quality score (lower is better).
//
//   aspect     = |ln((W / D) / opts.aspect)|        W, D: bounding box of every placed rectangle
//   edgeLength = mean centre-to-centre edge length / mean leaf diagonal
//                (all edges whose endpoints are both placed, self edges ignored)
//   crossings  = crossing pairs among straight centre-to-centre segments of
//                leaf-to-leaf edges / number of such segments; edges between the same two
//                leaves are one segment (they are drawn as one fanned bundle); above
//                MAX_CROSSING_EDGES segments, every k-th (k = ceil(m / MAX_CROSSING_EDGES)) is used
//   overlaps   = (segment, leaf) pairs where a segment passes through a leaf that is not one
//                of its ends / number of segments (same segments and sampling as crossings):
//                a line drawn through an unrelated node reads as a connection to it
//   area       = bounding-box area / sum of leaf areas   (whitespace factor, >= 1 for non-overlapping leaves)
//   total      = W_ASPECT * aspect + W_EDGE_LENGTH * edgeLength + W_CROSSINGS * crossings
//                + W_OVERLAPS * overlaps + W_LABELS * labels + W_AREA * ln(max(1, area))
//   labels     = pairs of node labels that overlap when the whole placement is fitted into a nominal
//                viewport (LABEL_VIEW_PX wide, the target aspect), / number of labels. Labels are drawn at
//                a fixed pixel size (LABEL_CHAR_PX per character, LABEL_LINE_PX high) above a leaf and in the
//                top-left corner of a container, so a placement whose members are cramped into a small part
//                of the picture has colliding labels that no zoom-independent term sees.
//
// Crossings and lines through nodes are the defects that make a picture misread. A line through an
// unrelated node is the worse of the two (it reads as a connection to that node, where a crossing still
// reads as a crossing), so it weighs twice as much. The overlap term exists because a hub drawn in a
// tight grid has no crossings at all (every spoke shares the hub) while most spokes pass through other
// nodes. Whitespace and length only make a picture larger: whitespace is scored on a log scale, like the
// aspect, so a picture twice as sparse costs a fixed amount rather than twice as much, and a hub with its
// neighbours on a ring is not outscored by a tight grid that draws its spokes through other nodes.

import { DEFAULT_ASPECT } from './constants.js';

export const W_ASPECT = 3;
export const W_EDGE_LENGTH = 0.3;
export const W_CROSSINGS = 1;
export const W_OVERLAPS = 2;
export const W_LABELS = 1;
/** The nominal viewport a placement is fitted into to judge its labels, and the size of label text in it. */
export const LABEL_VIEW_PX = 1000;
const LABEL_CHAR_PX = 7;
const LABEL_LINE_PX = 18;
const LABEL_PAD_PX = 12;
const MAX_LABELS = 400;
export const W_AREA = 0.5;
export const MAX_CROSSING_EDGES = 400;

/**
 * @typedef {{ total: number, aspect: number, edgeLength: number, crossings: number, overlaps: number, labels: number, area: number }} Score
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
  if (!Number.isFinite(minX) || leafCount === 0) return { total: 0, aspect: 0, edgeLength: 0, crossings: 0, overlaps: 0, labels: 0, area: 0 };
  const width = maxX - minX, depth = maxZ - minZ;
  const aspect = width > 0 && depth > 0 ? Math.abs(Math.log(width / depth / target)) : 0;
  const area = leafArea > 0 ? (width * depth) / leafArea : 0;

  let lenSum = 0, lenCount = 0;
  /** @type {[string, string][]} */
  const leafEdges = [];
  const seenPairs = new Set();
  for (const e of scene.edges) {
    const a = placement[e.from], b = placement[e.to];
    if (!a || !b || e.from === e.to) continue;
    lenSum += Math.hypot(a.x - b.x, a.z - b.z);
    lenCount++;
    if (parents.has(e.from) || parents.has(e.to)) continue;
    const key = e.from < e.to ? `${e.from}|${e.to}` : `${e.to}|${e.from}`;
    if (seenPairs.has(key)) continue;
    seenPairs.add(key);
    leafEdges.push([e.from, e.to]);
  }
  const meanDiag = leafDiag / leafCount;
  const edgeLength = lenCount && meanDiag > 0 ? lenSum / lenCount / meanDiag : 0;

  const step = Math.max(1, Math.ceil(leafEdges.length / MAX_CROSSING_EDGES));
  /** @type {[string, string][]} */
  const sample = [];
  for (let i = 0; i < leafEdges.length; i += step) sample.push(leafEdges[i]);
  const crossings = sample.length ? countCrossings(sample, placement) / sample.length : 0;
  /** @type {string[]} */
  const leaves = [];
  for (const n of scene.nodes) if (placement[n.id] && !n.container && !parents.has(n.id)) leaves.push(n.id);
  const overlaps = sample.length ? countOverlaps(sample, leaves, placement) / sample.length : 0;

  const labels = labelOverlaps(scene, placement, parents, width, depth, target);

  const total = W_ASPECT * aspect + W_EDGE_LENGTH * edgeLength + W_CROSSINGS * crossings + W_OVERLAPS * overlaps + W_LABELS * labels + W_AREA * Math.log(Math.max(1, area));
  return { total, aspect, edgeLength, crossings, overlaps, labels, area };
}

/**
 * Overlapping label pairs per label, with the placement fitted into the nominal viewport.
 * @param {import('../types.js').SceneModel} scene @param {import('../types.js').Placement} pl @param {Set<string>} parents
 * @param {number} width @param {number} depth @param {number} target
 */
function labelOverlaps(scene, pl, parents, width, depth, target) {
  if (!(width > 0 && depth > 0)) return 0;
  const scale = Math.min(LABEL_VIEW_PX / width, LABEL_VIEW_PX / target / depth); // px per ground unit
  /** @type {number[][]} x0, z0, x1, z1 */
  const boxes = [];
  for (const n of scene.nodes) {
    const p = pl[n.id];
    if (!p || boxes.length >= MAX_LABELS) continue;
    const chars = (n.label ?? '').length + (n.badges ?? []).reduce((t, b) => t + b.length + 1, 0) + (n.marks ?? []).reduce((t, m) => t + m.text.length + 1, 0);
    const w = (chars * LABEL_CHAR_PX + LABEL_PAD_PX) / scale;
    const h = LABEL_LINE_PX / scale;
    const top = p.z - p.d / 2;
    if (n.container || parents.has(n.id)) boxes.push([p.x - p.w / 2, top, p.x - p.w / 2 + w, top + h]);
    else boxes.push([p.x - w / 2, top - h, p.x + w / 2, top]);
  }
  if (!boxes.length) return 0;
  let count = 0;
  for (let i = 0; i < boxes.length; i++) {
    const a = boxes[i];
    for (let j = i + 1; j < boxes.length; j++) {
      const b = boxes[j];
      if (a[0] < b[2] && b[0] < a[2] && a[1] < b[3] && b[1] < a[3]) count++;
    }
  }
  return count / boxes.length;
}

/** Fraction of each footprint side ignored, so a segment grazing a corner does not count. */
const OVERLAP_INSET = 0.1;

/**
 * (segment, leaf) pairs where the segment between two leaf centres passes through a third leaf's footprint.
 * @param {[string, string][]} edges @param {string[]} leaves @param {import('../types.js').Placement} pl
 */
function countOverlaps(edges, leaves, pl) {
  let count = 0;
  for (const [f, t] of edges) {
    const a = pl[f], b = pl[t];
    const x0 = Math.min(a.x, b.x), x1 = Math.max(a.x, b.x), z0 = Math.min(a.z, b.z), z1 = Math.max(a.z, b.z);
    for (const id of leaves) {
      if (id === f || id === t) continue;
      const r = pl[id];
      const hw = (r.w / 2) * (1 - OVERLAP_INSET), hd = (r.d / 2) * (1 - OVERLAP_INSET);
      if (r.x + hw < x0 || r.x - hw > x1 || r.z + hd < z0 || r.z - hd > z1) continue;
      if (segmentHitsRect(a.x, a.z, b.x, b.z, r.x - hw, r.z - hd, r.x + hw, r.z + hd)) count++;
    }
  }
  return count;
}

/**
 * Whether the segment (ax, az)-(bx, bz) meets the axis-aligned rectangle [rx0, rx1] x [rz0, rz1] (Liang-Barsky).
 * @param {number} ax @param {number} az @param {number} bx @param {number} bz
 * @param {number} rx0 @param {number} rz0 @param {number} rx1 @param {number} rz1
 */
function segmentHitsRect(ax, az, bx, bz, rx0, rz0, rx1, rz1) {
  const dx = bx - ax, dz = bz - az;
  let t0 = 0, t1 = 1;
  const p = [-dx, dx, -dz, dz];
  const q = [ax - rx0, rx1 - ax, az - rz0, rz1 - az];
  for (let i = 0; i < 4; i++) {
    if (p[i] === 0) { if (q[i] < 0) return false; continue; }
    const r = q[i] / p[i];
    if (p[i] < 0) { if (r > t1) return false; if (r > t0) t0 = r; }
    else { if (r < t0) return false; if (r < t1) t1 = r; }
  }
  return t0 <= t1;
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
