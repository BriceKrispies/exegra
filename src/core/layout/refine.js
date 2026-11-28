// Slot refinement after any method (WG-5695): leaves that their own level cannot tell apart are assigned to
// the slots the method gave them so that edges leaving containers cross less and pass through fewer nodes.
//
// Each method arranges one level at a time and sees only the edges between siblings, so an edge from a leaf
// inside a container to a leaf outside it plays no part in where either is put. Two leaves are
// interchangeable for the method when they have the same parent, the same footprint and the same edges to
// their siblings (as the method sees them: flow edges, mapped to the sibling that contains the other end).
// Swapping two such leaves gives a placement the method itself could have produced from another input order,
// so its structure (layers, rings, shelves) is kept. Swaps are accepted greedily, in id order, only when they
// strictly lower the number of crossing segment pairs plus segments through unrelated leaves; the result is
// deterministic. Pinned leaves never move.

import { isFlowEdge } from './model.js';

/** Classes larger than this are not refined (their swaps would cost more than they could save). */
const MAX_CLASS = 24;
const PASSES = 2;
/**
 * A bound on the work of one refinement, in segment-against-segment and segment-against-leaf tests. It is counted,
 * not timed, so the result stays deterministic; a dense scene is left as its method arranged it once it is spent.
 */
const BUDGET = 400_000;

/**
 * @param {import('../types.js').SceneModel} scene
 * @param {Map<string, {x: number, z: number, w: number, d: number}>} rect absolute rectangles, changed in place
 * @param {Map<string, string|null>} par @param {Map<string|null, string[]>} children @param {Set<string>} pinned
 */
export function refineSlots(scene, rect, par, children, pinned) {
  const isLeaf = (/** @type {string} */ id) => !(children.get(id)?.length);
  const ancestorsOf = (/** @type {string} */ id) => { const out = []; let c = par.get(id) ?? null; while (c != null) { out.push(c); c = par.get(c) ?? null; } return out; };
  const anc = new Map([...rect.keys()].map((id) => [id, ancestorsOf(id)]));

  // Segments: one per pair of distinct drawn ends that neither contains the other.
  /** @type {[string, string][]} */
  const segs = [];
  const seen = new Set();
  for (const e of scene.edges) {
    if (e.from === e.to || !rect.has(e.from) || !rect.has(e.to)) continue;
    if (anc.get(e.from)?.includes(e.to) || anc.get(e.to)?.includes(e.from)) continue;
    const key = e.from < e.to ? `${e.from}|${e.to}` : `${e.to}|${e.from}`;
    if (seen.has(key)) continue;
    seen.add(key);
    segs.push([e.from, e.to]);
  }
  if (!segs.length) return;
  /** @type {Map<string, number[]>} */
  const segsOf = new Map();
  segs.forEach(([a, b], i) => { for (const x of [a, b]) { if (!segsOf.has(x)) segsOf.set(x, []); /** @type {number[]} */ (segsOf.get(x)).push(i); } });
  const leaves = [...rect.keys()].filter(isLeaf);

  // A segment's ends sit at the centre of each end node; a segment through a leaf that contains neither end counts.
  const centre = (/** @type {string} */ id) => /** @type {{x: number, z: number}} */ (rect.get(id));
  const crosses = (/** @type {number} */ i, /** @type {number} */ j) => {
    const [a, b] = segs[i], [c, d] = segs[j];
    if (a === c || a === d || b === c || b === d) return 0;
    const p = centre(a), q = centre(b), r = centre(c), s = centre(d);
    const o1 = orient(p, q, r), o2 = orient(p, q, s), o3 = orient(r, s, p), o4 = orient(r, s, q);
    return o1 * o2 < 0 && o3 * o4 < 0 ? 1 : 0;
  };
  const through = (/** @type {number} */ i, /** @type {string} */ leaf) => {
    const [a, b] = segs[i];
    if (leaf === a || leaf === b || anc.get(a)?.includes(leaf) || anc.get(b)?.includes(leaf)) return 0;
    const p = centre(a), q = centre(b), r = /** @type {{x: number, z: number, w: number, d: number}} */ (rect.get(leaf));
    const hw = r.w * 0.45, hd = r.d * 0.45;
    if (Math.max(p.x, q.x) < r.x - hw || Math.min(p.x, q.x) > r.x + hw || Math.max(p.z, q.z) < r.z - hd || Math.min(p.z, q.z) > r.z + hd) return 0;
    return hitsRect(p.x, p.z, q.x, q.z, r.x - hw, r.z - hd, r.x + hw, r.z + hd) ? 1 : 0;
  };
  let spent = 0;
  /** The part of the cost that can change when u and v move. @param {string} u @param {string} v */
  const local = (u, v) => {
    const A = new Set([...(segsOf.get(u) ?? []), ...(segsOf.get(v) ?? [])]);
    spent += A.size * (segs.length + leaves.length) + 2 * segs.length;
    let c = 0;
    for (const i of A) {
      for (let j = 0; j < segs.length; j++) if (j !== i && (!A.has(j) || j > i)) c += crosses(i, j);
      for (const l of leaves) c += through(i, l);
    }
    for (let j = 0; j < segs.length; j++) if (!A.has(j)) c += through(j, u) + through(j, v);
    return c;
  };

  // Interchangeable leaves: same parent, footprint and sibling-level flow edges (with direction and multiplicity).
  const siblingOf = (/** @type {string} */ other, /** @type {string|null} */ parent) => {
    if (par.get(other) === parent) return other;
    for (const a of anc.get(other) ?? []) if ((par.get(a) ?? null) === parent) return a;
    return null;
  };
  /** @type {Map<string, string[]>} */
  const classes = new Map();
  for (const id of leaves) {
    if (pinned.has(id) || !segsOf.has(id)) continue;
    const parent = par.get(id) ?? null;
    const r = /** @type {{w: number, d: number}} */ (rect.get(id));
    /** @type {string[]} */
    const sig = [];
    const pairSeen = new Set();
    for (const e of scene.edges) {
      if (!isFlowEdge(e) || (e.from !== id && e.to !== id)) continue;
      const other = e.from === id ? e.to : e.from;
      const s = rect.has(other) ? siblingOf(other, parent) : null;
      if (s === null || s === id) continue;
      const k = `${e.from === id ? '>' : '<'}${s}`;
      if (pairSeen.has(k)) continue;
      pairSeen.add(k);
      sig.push(k);
    }
    const key = `${parent}|${r.w.toFixed(3)}x${r.d.toFixed(3)}|${sig.sort().join(',')}`;
    if (!classes.has(key)) classes.set(key, []);
    /** @type {string[]} */ (classes.get(key)).push(id);
  }

  const swap = (/** @type {string} */ u, /** @type {string} */ v) => {
    const a = /** @type {any} */ (rect.get(u)), b = /** @type {any} */ (rect.get(v));
    [a.x, b.x] = [b.x, a.x];
    [a.z, b.z] = [b.z, a.z];
  };
  for (const ids of [...classes.values()]) {
    if (ids.length < 2 || ids.length > MAX_CLASS) continue;
    ids.sort();
    for (let pass = 0; pass < PASSES; pass++) {
      let improved = false;
      for (let i = 0; i < ids.length; i++) {
        for (let j = i + 1; j < ids.length; j++) {
          if (spent > BUDGET) return;
          const before = local(ids[i], ids[j]);
          swap(ids[i], ids[j]);
          if (local(ids[i], ids[j]) < before) improved = true;
          else swap(ids[i], ids[j]);
        }
      }
      if (!improved) break;
    }
  }
}

/** @param {{x: number, z: number}} p @param {{x: number, z: number}} q @param {{x: number, z: number}} r */
function orient(p, q, r) {
  return (q.x - p.x) * (r.z - p.z) - (q.z - p.z) * (r.x - p.x);
}

/** Liang-Barsky: whether a segment meets an axis-aligned rectangle. @param {number} ax @param {number} az @param {number} bx @param {number} bz @param {number} x0 @param {number} z0 @param {number} x1 @param {number} z1 */
function hitsRect(ax, az, bx, bz, x0, z0, x1, z1) {
  const dx = bx - ax, dz = bz - az;
  let t0 = 0, t1 = 1;
  const p = [-dx, dx, -dz, dz];
  const q = [ax - x0, x1 - ax, az - z0, z1 - az];
  for (let i = 0; i < 4; i++) {
    if (p[i] === 0) { if (q[i] < 0) return false; continue; }
    const r = q[i] / p[i];
    if (p[i] < 0) { if (r > t1) return false; if (r > t0) t0 = r; } else { if (r < t0) return false; if (r < t1) t1 = r; }
  }
  return t0 <= t1;
}
