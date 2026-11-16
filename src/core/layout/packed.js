// Packed arranger: no flow direction. Siblings are ordered so strongly
// connected ones are adjacent, then shelf-packed towards the target aspect.

import { NODE_GAP, ROW_GAP } from './constants.js';

/** Row gap used between shelves (a little tighter than the layered row gap). */
const SHELF_GAP = Math.min(NODE_GAP, ROW_GAP);
/** Candidate shelf widths, as multiples of the ideal width sqrt(area * aspect). */
const WIDTH_FACTORS = [0.5, 0.6, 0.7, 0.8, 0.9, 1, 1.1, 1.25, 1.4, 1.6, 1.9, 2.3, 2.8, 3.5];
/** Weight of the whitespace term when comparing candidate packings. */
const WASTE_WEIGHT = 0.7;
/** Small penalty on the depth-sorted packing so adjacency order wins ties. */
const SORTED_PENALTY = 0.12;

/**
 * Deterministic greedy ordering: start from the highest-degree node, then
 * repeatedly append the node most strongly tied to the last one (then to the
 * placed set, then by degree), ties by original order.
 * @param {number} n @param {Map<number, number>[]} adj
 * @returns {number[]}
 */
export function adjacencyOrder(n, adj) {
  const degree = adj.map((m) => { let s = 0; for (const c of m.values()) s += c; return s; });
  const done = new Uint8Array(n);
  const acc = new Float64Array(n);
  /** @type {number[]} */
  const order = [];
  let last = -1;
  for (let step = 0; step < n; step++) {
    let best = -1;
    let bestLast = -1, bestAcc = -1, bestDeg = -1;
    for (let j = 0; j < n; j++) {
      if (done[j]) continue;
      const wl = last >= 0 ? (adj[last].get(j) ?? 0) : 0;
      if (wl > bestLast || (wl === bestLast && (acc[j] > bestAcc || (acc[j] === bestAcc && degree[j] > bestDeg)))) {
        best = j; bestLast = wl; bestAcc = acc[j]; bestDeg = degree[j];
      }
    }
    done[best] = 1;
    order.push(best);
    for (const [j, c] of adj[best]) acc[j] += c;
    last = best;
  }
  return order;
}

/**
 * Undirected edge-count adjacency between sibling indices.
 * @param {string[]} ids @param {[string,string][]} pairs
 * @returns {Map<number, number>[]}
 */
export function adjacency(ids, pairs) {
  const ix = new Map(ids.map((id, i) => [id, i]));
  const adj = ids.map(() => /** @type {Map<number, number>} */ (new Map()));
  for (const [a, b] of pairs) {
    const i = ix.get(a), j = ix.get(b);
    if (i === undefined || j === undefined || i === j) continue;
    adj[i].set(j, (adj[i].get(j) ?? 0) + 1);
    adj[j].set(i, (adj[j].get(i) ?? 0) + 1);
  }
  return adj;
}

/**
 * Shelf-pack items (given in order) into rows no wider than `maxW`.
 * Rows are filled sequentially, or first-fit when `firstFit` is set.
 * @param {number[]} order @param {number[]} w @param {number[]} d @param {number} maxW @param {boolean} firstFit
 */
function shelfPack(order, w, d, maxW, firstFit) {
  /** @type {{items: number[], width: number, height: number}[]} */
  const rows = [];
  for (const v of order) {
    /** @type {typeof rows[number]|undefined} */
    let row;
    if (firstFit) {
      row = rows.find((r) => r.width + NODE_GAP + w[v] <= maxW + 1e-9 && d[v] <= r.height + 1e-9);
    } else {
      const last = rows[rows.length - 1];
      if (last && last.width + NODE_GAP + w[v] <= maxW + 1e-9) row = last;
    }
    if (!row) { row = { items: [], width: 0, height: 0 }; rows.push(row); }
    row.width += (row.items.length ? NODE_GAP : 0) + w[v];
    row.height = Math.max(row.height, d[v]);
    row.items.push(v);
  }
  let width = 0, height = 0;
  for (const r of rows) { width = Math.max(width, r.width); height += r.height; }
  height += SHELF_GAP * Math.max(0, rows.length - 1);
  return { rows, width, height };
}

/** @type {import('./solve.js').Arranger} */
export function arrangePacked(ids, pairs, size, ctx) {
  const n = ids.length;
  /** @type {Map<string, [number, number]>} */
  const pos = new Map();
  if (!n) return pos;
  const w = ids.map((id) => /** @type {[number, number]} */ (size.get(id))[0]);
  const d = ids.map((id) => /** @type {[number, number]} */ (size.get(id))[1]);
  const order = adjacencyOrder(n, adjacency(ids, pairs));
  const orderRank = new Int32Array(n);
  order.forEach((v, k) => { orderRank[v] = k; });
  const byDepth = [...order].sort((a, b) => d[b] - d[a] || orderRank[a] - orderRank[b]);

  let area = 0, maxItemW = 0;
  for (let i = 0; i < n; i++) { area += (w[i] + NODE_GAP) * (d[i] + SHELF_GAP); maxItemW = Math.max(maxItemW, w[i]); }
  const ideal = Math.sqrt(area * ctx.aspect);

  /** @type {any} */
  let best = null;
  let bestCost = Infinity;
  for (const sorted of [false, true]) {
    for (const f of WIDTH_FACTORS) {
      const maxW = Math.max(maxItemW, ideal * f);
      const packed = shelfPack(sorted ? byDepth : order, w, d, maxW, sorted);
      if (packed.width <= 0 || packed.height <= 0) continue;
      const cost = Math.abs(Math.log(packed.width / packed.height / ctx.aspect))
        + WASTE_WEIGHT * Math.log((packed.width * packed.height) / area)
        + (sorted ? SORTED_PENALTY : 0);
      if (cost < bestCost - 1e-9) { bestCost = cost; best = packed; }
    }
  }
  if (!best) best = shelfPack(order, w, d, maxItemW, false);

  let z = 0;
  for (const r of best.rows) {
    let x = 0;
    for (const v of r.items) {
      pos.set(ids[v], [x + w[v] / 2, z + r.height / 2]);
      x += w[v] + NODE_GAP;
    }
    z += r.height + SHELF_GAP;
  }
  return pos;
}
