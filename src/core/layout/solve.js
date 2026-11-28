// Method-independent recursion: size leaves, arrange each level with the given
// arranger, wrap containers around their children, apply pins.

import { LEAF_W, LEAF_D, SMALL_W, SMALL_D, PAD, LABEL_EXTRA, SMALL_KINDS } from './constants.js';
import { buildModel } from './model.js';
import { refineSlots } from './refine.js';

/** @typedef {import('../types.js').SceneModel} SceneModel */
/** @typedef {import('../types.js').Placement} Placement */
/**
 * @typedef {object} LevelContext
 * @property {string|null} key container id (null at the root)
 * @property {number} level 0 at the root, containment depth + 1 inside a container
 * @property {number} aspect target width/depth ratio
 */
/**
 * Arranger: returns local centres of the sibling ids.
 * @typedef {(ids: string[], pairs: [string, string][], size: Map<string,[number,number]>, ctx: LevelContext) => Map<string,[number,number]>} Arranger
 */

/**
 * @param {SceneModel} scene
 * @param {Record<string, [number, number]>} pinned
 * @param {Arranger} arrange
 * @param {{aspect: number}} opts
 * @returns {Placement}
 */
export function solveLayout(scene, pinned, arrange, opts) {
  const { nodes, byId, par, children, depth, edgesAt } = buildModel(scene);

  /** @type {Map<string, [number, number]>} */
  const size = new Map();
  /** @type {Map<string, [number, number]>} offset of a child centre from its parent's centre (root: from origin) */
  const off = new Map();
  /** @type {string[]} containers, children before parents */
  const postOrder = [];

  /** @param {string|null} key */
  const layoutLevel = (key) => {
    const ids = children.get(key) ?? [];
    for (const id of ids) {
      if (children.get(id)?.length) layoutLevel(id);
      else size.set(id, SMALL_KINDS.has(byId.get(id).entityKind) ? [SMALL_W, SMALL_D] : [LEAF_W, LEAF_D]);
    }
    if (!ids.length) return;
    const level = key === null ? 0 : /** @type {number} */ (depth.get(key)) + 1;
    const pos = arrange(ids, edgesAt.get(key) ?? [], size, { key, level, aspect: opts.aspect });
    let minX = Infinity, maxX = -Infinity, minZ = Infinity, maxZ = -Infinity;
    for (const id of ids) {
      const [x, z] = /** @type {[number, number]} */ (pos.get(id));
      const [w, d] = /** @type {[number, number]} */ (size.get(id));
      minX = Math.min(minX, x - w / 2); maxX = Math.max(maxX, x + w / 2);
      minZ = Math.min(minZ, z - d / 2); maxZ = Math.max(maxZ, z + d / 2);
    }
    const cx = (minX + maxX) / 2;
    let cz = (minZ + maxZ) / 2;
    if (key !== null) {
      size.set(key, [maxX - minX + 2 * PAD, maxZ - minZ + 2 * PAD + LABEL_EXTRA]);
      cz -= LABEL_EXTRA / 2;
      postOrder.push(key);
    }
    for (const id of ids) {
      const [x, z] = /** @type {[number, number]} */ (pos.get(id));
      off.set(id, [x - cx, z - cz]);
    }
  };
  layoutLevel(null);

  // Absolute centres, top down.
  /** @type {Map<string, {x:number, z:number, w:number, d:number}>} */
  const rect = new Map();
  /** @param {string|null} key @param {number} px @param {number} pz */
  const place = (key, px, pz) => {
    for (const id of children.get(key) ?? []) {
      const [dx, dz] = /** @type {[number, number]} */ (off.get(id));
      const [w, d] = /** @type {[number, number]} */ (size.get(id));
      rect.set(id, { x: px + dx, z: pz + dz, w, d });
      if (children.get(id)?.length) place(id, px + dx, pz + dz);
    }
  };
  place(null, 0, 0);

  // Interchangeable leaves take the slots that make edges leaving containers cross least (./refine.js).
  refineSlots(scene, rect, par, children, new Set(Object.keys(pinned ?? {})));

  // Pins: leaves only.
  let pinnedAny = false;
  for (const id of Object.keys(pinned ?? {})) {
    const r = rect.get(id);
    const p = pinned[id];
    if (!r || children.get(id)?.length || !Array.isArray(p) || !Number.isFinite(p[0]) || !Number.isFinite(p[1])) continue;
    r.x = p[0]; r.z = p[1];
    pinnedAny = true;
  }
  if (pinnedAny) {
    for (const key of postOrder) {
      let minX = Infinity, maxX = -Infinity, minZ = Infinity, maxZ = -Infinity;
      for (const id of /** @type {string[]} */ (children.get(key))) {
        const r = /** @type {any} */ (rect.get(id));
        minX = Math.min(minX, r.x - r.w / 2); maxX = Math.max(maxX, r.x + r.w / 2);
        minZ = Math.min(minZ, r.z - r.d / 2); maxZ = Math.max(maxZ, r.z + r.d / 2);
      }
      const x0 = minX - PAD, x1 = maxX + PAD, z0 = minZ - PAD - LABEL_EXTRA, z1 = maxZ + PAD;
      rect.set(key, { x: (x0 + x1) / 2, z: (z0 + z1) / 2, w: x1 - x0, d: z1 - z0 });
    }
  }

  /** @type {Placement} */
  const out = {};
  for (const n of nodes) {
    const r = rect.get(n.id);
    if (r) out[n.id] = { x: r.x, z: r.z, w: r.w, d: r.d, level: /** @type {number} */ (depth.get(n.id)) };
  }
  return out;
}
