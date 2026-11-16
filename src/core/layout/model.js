// Containment tree, depths and per-container edge lists derived from a scene.

/** @typedef {import('../types.js').SceneModel} SceneModel */

/**
 * @param {SceneModel} scene
 */
export function buildModel(scene) {
  const nodes = scene.nodes;
  /** @type {Map<string, any>} */
  const byId = new Map(nodes.map((n) => [n.id, n]));

  // Parent links, ignoring unknown parents and parent cycles.
  /** @type {Map<string, string|null>} */
  const par = new Map();
  for (const n of nodes) par.set(n.id, n.parent != null && n.parent !== n.id && byId.has(n.parent) ? n.parent : null);
  for (const n of nodes) {
    const seen = new Set([n.id]);
    let cur = par.get(n.id);
    while (cur != null) {
      if (seen.has(cur)) { par.set(n.id, null); break; }
      seen.add(cur);
      cur = par.get(cur);
    }
  }
  /** @type {Map<string|null, string[]>} */
  const children = new Map();
  for (const n of nodes) {
    const p = par.get(n.id) ?? null;
    if (!children.has(p)) children.set(p, []);
    /** @type {string[]} */ (children.get(p)).push(n.id);
  }
  /** @type {Map<string, number>} */
  const depth = new Map();
  /** @type {(id: string) => number} */
  const depthOf = (id) => {
    let d = depth.get(id);
    if (d !== undefined) return d;
    const p = par.get(id);
    d = p == null ? 0 : depthOf(p) + 1;
    depth.set(id, d);
    return d;
  };
  for (const n of nodes) depthOf(n.id);
  /** @param {string} id */
  const dep = (id) => /** @type {number} */ (depth.get(id));

  // Edges grouped by the container whose children they connect.
  /** @type {Map<string|null, [string, string][]>} */
  const edgesAt = new Map();
  const seenPairs = new Set();
  for (const e of scene.edges) {
    if (!byId.has(e.from) || !byId.has(e.to)) continue;
    /** @type {string|null} */ let a = e.from;
    /** @type {string|null} */ let b = e.to;
    /** @type {string|null} */ let ca = null;
    /** @type {string|null} */ let cb = null;
    while (dep(/** @type {string} */ (a)) > dep(/** @type {string} */ (b))) { ca = a; a = par.get(/** @type {string} */ (a)) ?? null; }
    while (dep(/** @type {string} */ (b)) > dep(/** @type {string} */ (a))) { cb = b; b = par.get(/** @type {string} */ (b)) ?? null; }
    if (a === b) continue; // same node, or one encloses the other
    while (a !== b) {
      ca = a; cb = b;
      a = a == null ? null : (par.get(a) ?? null);
      b = b == null ? null : (par.get(b) ?? null);
    }
    const key = `${a}\u0000${ca}\u0000${cb}`;
    if (seenPairs.has(key)) continue;
    seenPairs.add(key);
    if (!edgesAt.has(a)) edgesAt.set(a, []);
    /** @type {[string, string][]} */ (edgesAt.get(a)).push([/** @type {string} */ (ca), /** @type {string} */ (cb)]);
  }
  return { nodes, byId, par, children, depth, edgesAt };
}
