// Deterministic layouts on the ground plane (x right, z toward the viewer),
// recursive over containers. Position is presentation only; containment is
// always shown as enclosure. Methods live in ./layout/*.js.

import { DEFAULT_ASPECT } from './layout/constants.js';
import { solveLayout } from './layout/solve.js';
import { layeredArranger } from './layout/layered.js';
import { arrangePacked } from './layout/packed.js';
import { arrangeRadial } from './layout/radial.js';
import { scorePlacement } from './layout/score.js';

export { scorePlacement };

/** @typedef {import('./types.js').SceneModel} SceneModel */
/** @typedef {import('./types.js').Placement} Placement */
/** @typedef {{ method?: string, aspect?: number }} LayoutOptions */

/** The concrete methods ('auto' is the selector, not a method). */
export const LAYOUT_METHODS = [
  { id: 'layered', label: 'Layered', description: 'Dependency layers flowing left to right at the top level, alternating direction per nesting level; long runs wrap into rows.' },
  { id: 'layered-down', label: 'Layered (front to back)', description: 'Dependency layers flowing front to back at the top level, alternating direction per nesting level.' },
  { id: 'packed', label: 'Packed', description: 'No flow direction: connected siblings sit next to each other in tight rows shaped to the view.' },
  { id: 'radial', label: 'Radial', description: 'The best-connected node at the centre, the rest on concentric rings that keep neighbours close.' },
];

const ARRANGERS = {
  layered: layeredArranger(false),
  'layered-down': layeredArranger(true),
  packed: arrangePacked,
  radial: arrangeRadial,
};

/** @param {LayoutOptions} opts */
function aspectOf(opts) {
  return typeof opts.aspect === 'number' && Number.isFinite(opts.aspect) && opts.aspect > 0 ? opts.aspect : DEFAULT_ASPECT;
}

/**
 * @param {SceneModel} scene @param {Record<string, [number, number]>} pinned
 * @param {string} method @param {number} aspect
 */
function runMethod(scene, pinned, method, aspect) {
  const arranger = /** @type {Record<string, import('./layout/solve.js').Arranger>} */ (ARRANGERS)[method];
  if (!arranger) throw new Error(`unknown layout method: ${method}`);
  return solveLayout(scene, pinned ?? {}, arranger, { aspect });
}

/**
 * Lay the scene out. `pinned` maps leaf scene ids to absolute [x, z].
 * `opts.method` is a LAYOUT_METHODS id or 'auto' (default 'layered');
 * `opts.aspect` is the target width/depth ratio of the view (default 1.6).
 * @param {SceneModel} scene
 * @param {Record<string, [number, number]>} [pinned]
 * @param {LayoutOptions} [opts]
 * @returns {Placement}
 */
export function layoutScene(scene, pinned = {}, opts = {}) {
  const method = opts?.method ?? 'layered';
  if (method === 'auto') return chooseLayout(scene, pinned, opts).placement;
  return runMethod(scene, pinned, method, aspectOf(opts ?? {}));
}

/**
 * Compute every method, score each and return the best (ties go to the
 * earlier method in LAYOUT_METHODS).
 * @param {SceneModel} scene
 * @param {Record<string, [number, number]>} [pinned]
 * @param {LayoutOptions} [opts]
 * @returns {{ method: string, placement: Placement, scores: Record<string, import('./layout/score.js').Score> }}
 */
export function chooseLayout(scene, pinned = {}, opts = {}) {
  const aspect = aspectOf(opts ?? {});
  /** @type {Record<string, import('./layout/score.js').Score>} */
  const scores = {};
  let bestMethod = LAYOUT_METHODS[0].id;
  /** @type {Placement|null} */
  let best = null;
  for (const { id } of LAYOUT_METHODS) {
    const placement = runMethod(scene, pinned, id, aspect);
    const s = scorePlacement(scene, placement, { aspect });
    scores[id] = s;
    if (!best || s.total < scores[bestMethod].total - 1e-12) { best = placement; bestMethod = id; }
  }
  return { method: bestMethod, placement: /** @type {Placement} */ (best), scores };
}
