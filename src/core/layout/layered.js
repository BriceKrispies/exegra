// Layered (Sugiyama-style) arranger: longest-path layers, barycenter ordering,
// flow direction alternating with nesting depth, long root runs wrapped in rows.

import { LAYER_GAP, NODE_GAP, SWEEPS, ROW_GAP } from './constants.js';

/**
 * @param {boolean} rootVertical true when the root flows along z (front to back)
 * @returns {import('./solve.js').Arranger}
 */
export function layeredArranger(rootVertical) {
  return (ids, pairs, size, ctx) => {
    // Root level is level 0; each nesting level flips the direction.
    const vertical = (ctx.level % 2 === 0) === rootVertical;
    return arrangeLayered(ids, pairs, size, vertical, ctx.key === null, ctx.aspect);
  };
}

/**
 * Arrange sibling nodes. Returns local centres.
 * @param {string[]} ids @param {[string,string][]} pairs @param {Map<string,[number,number]>} size
 * @param {boolean} vertical lay layers out along z instead of x
 * @param {boolean} wrap allow wrapping a long run of layers into rows
 * @param {number} aspect target width/depth ratio of the whole result
 * @returns {Map<string, [number, number]>}
 */
function arrangeLayered(ids, pairs, size, vertical, wrap, aspect) {
  const n = ids.length;
  /** @type {Map<string, [number, number]>} */
  const pos = new Map();
  if (!n) return pos;
  const ix = new Map(ids.map((id, i) => [id, i]));
  /** @type {number[][]} */ const out = Array.from({ length: n }, () => []);
  /** @type {number[][]} */ const inn = Array.from({ length: n }, () => []);
  const has = new Array(n).fill(false);
  for (const [a, b] of pairs) {
    const i = /** @type {number} */ (ix.get(a));
    const j = /** @type {number} */ (ix.get(b));
    if (i === undefined || j === undefined || i === j) continue;
    out[i].push(j); inn[j].push(i);
    has[i] = true; has[j] = true;
  }
  // Work in (along-flow, across-flow) coordinates; swap back at the end when vertical.
  const w = ids.map((id) => /** @type {[number, number]} */ (size.get(id))[vertical ? 1 : 0]);
  const d = ids.map((id) => /** @type {[number, number]} */ (size.get(id))[vertical ? 0 : 1]);

  // Break cycles: DFS in node order; edges to a node on the stack are back edges.
  const state = new Int8Array(n);
  const ptr = new Int32Array(n);
  /** @type {number[]} */ const post = [];
  const back = new Set();
  for (let s = 0; s < n; s++) {
    if (!has[s] || state[s]) continue;
    const stack = [s];
    state[s] = 1;
    while (stack.length) {
      const v = stack[stack.length - 1];
      if (ptr[v] < out[v].length) {
        const t = out[v][ptr[v]++];
        if (state[t] === 0) { state[t] = 1; stack.push(t); }
        else if (state[t] === 1) back.add(v * n + t);
      } else { state[v] = 2; post.push(v); stack.pop(); }
    }
  }
  // Longest-path layering in topological (reverse post) order.
  const layer = new Int32Array(n);
  for (let k = post.length - 1; k >= 0; k--) {
    const v = post[k];
    for (const t of out[v]) if (!back.has(v * n + t) && layer[t] < layer[v] + 1) layer[t] = layer[v] + 1;
  }
  let maxLayer = -1;
  for (let i = 0; i < n; i++) if (has[i] && layer[i] > maxLayer) maxLayer = layer[i];
  /** @type {number[][]} */
  const layers = Array.from({ length: maxLayer + 1 }, () => []);
  for (let i = 0; i < n; i++) if (has[i]) layers[layer[i]].push(i);
  const und = Array.from({ length: n }, (_, i) => [...out[i], ...inn[i]]);
  const where = new Int32Array(n);
  const reindex = (/** @type {number[]} */ l) => l.forEach((v, k) => { where[v] = k; });
  layers.forEach(reindex);
  const sweep = (/** @type {number} */ li, /** @type {number} */ nb) => {
    const l = layers[li];
    /** @type {Map<number, number>} */
    const bary = new Map();
    for (const v of l) {
      let sum = 0, cnt = 0;
      for (const u of und[v]) if (layer[u] === nb) { sum += where[u]; cnt++; }
      bary.set(v, cnt ? sum / cnt : where[v]);
    }
    l.sort((a, b) => /** @type {number} */ (bary.get(a)) - /** @type {number} */ (bary.get(b)) || a - b);
    reindex(l);
  };
  for (let s = 0; s < SWEEPS; s++) {
    if (s % 2 === 0) for (let li = 1; li < layers.length; li++) sweep(li, li - 1);
    else for (let li = layers.length - 2; li >= 0; li--) sweep(li, li + 1);
  }

  // Coordinates of the layered part. A long run of layers is wrapped into
  // several rows (root level only) so the scene keeps a usable aspect ratio.
  const colWs = layers.map((l) => l.reduce((m, v) => Math.max(m, w[v]), 0));
  const depths = layers.map((l) => l.reduce((t, v) => t + d[v], 0) + NODE_GAP * Math.max(0, l.length - 1));
  const totalW = colWs.reduce((t, c) => t + c, 0) + LAYER_GAP * Math.max(0, layers.length - 1);
  const maxDepth = depths.reduce((m, x) => Math.max(m, x), 0);
  let rowCount = 1;
  if (wrap && layers.length >= 4 && maxDepth > 0) {
    // In flow coordinates the final width/depth ratio is inverted when vertical.
    const target = vertical ? 1 / aspect : aspect;
    let best = Infinity;
    for (let r = 1; r <= Math.min(4, Math.floor(layers.length / 2)); r++) {
      const flowAspect = (totalW / r) / (maxDepth * r + ROW_GAP * (r - 1));
      const score = Math.abs(Math.log(flowAspect / target));
      if (score < best - 1e-9) { best = score; rowCount = r; }
    }
  }
  const perRow = Math.ceil(layers.length / rowCount);
  let minX = Infinity, maxZ = -Infinity;
  let rowTop = 0;
  for (let r = 0; r < rowCount; r++) {
    const from = r * perRow;
    const to = Math.min(layers.length, from + perRow);
    let rowDepth = 0;
    for (let li = from; li < to; li++) rowDepth = Math.max(rowDepth, depths[li]);
    let x0 = 0;
    for (let li = from; li < to; li++) {
      const l = layers[li];
      let z = rowTop + (rowDepth - depths[li]) / 2;
      for (const v of l) {
        const cx = x0 + colWs[li] / 2;
        const cz = z + d[v] / 2;
        pos.set(ids[v], [cx, cz]);
        minX = Math.min(minX, cx - w[v] / 2);
        maxZ = Math.max(maxZ, cz + d[v] / 2);
        z += d[v] + NODE_GAP;
      }
      x0 += colWs[li] + LAYER_GAP;
    }
    rowTop += rowDepth + ROW_GAP;
  }

  // Components with no edges here: compact grid below the layered part.
  const loose = [];
  for (let i = 0; i < n; i++) if (!has[i]) loose.push(i);
  if (loose.length) {
    const cols = Math.ceil(Math.sqrt(loose.length));
    const rows = Math.ceil(loose.length / cols);
    const colW = new Array(cols).fill(0);
    const rowD = new Array(rows).fill(0);
    loose.forEach((v, k) => {
      colW[k % cols] = Math.max(colW[k % cols], w[v]);
      rowD[Math.floor(k / cols)] = Math.max(rowD[Math.floor(k / cols)], d[v]);
    });
    const left = Number.isFinite(minX) ? minX : 0;
    let top = Number.isFinite(maxZ) ? maxZ + LAYER_GAP : 0;
    const colX = [];
    let cx = left;
    for (let c = 0; c < cols; c++) { colX.push(cx + colW[c] / 2); cx += colW[c] + NODE_GAP; }
    const rowZ = [];
    for (let r = 0; r < rows; r++) { rowZ.push(top + rowD[r] / 2); top += rowD[r] + NODE_GAP; }
    loose.forEach((v, k) => pos.set(ids[v], [colX[k % cols], rowZ[Math.floor(k / cols)]]));
  }
  if (vertical) for (const [id, [a, b]] of pos) pos.set(id, [b, a]);
  return pos;
}
