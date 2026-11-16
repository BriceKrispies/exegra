// Label DOM construction and screen-space clutter management.
import * as THREE from 'three';

const MIN_LEAF_PX = 18;
const CELL = 96;
const _v = new THREE.Vector3();

/**
 * Build the DOM for a node label.
 * @param {string} entityId
 */
export function createLabelParts(entityId) {
  const el = document.createElement('div');
  el.className = 'scene-label';
  el.dataset.entityId = entityId;
  const nameEl = document.createElement('span');
  nameEl.className = 'scene-label__name';
  const subEl = document.createElement('span');
  subEl.className = 'scene-label__sub';
  el.append(nameEl, subEl);
  return { el, nameEl, subEl, badgeEls: [], text: '' };
}

/**
 * Update label text; returns true when the content changed (size must be re-measured).
 * @param {ReturnType<typeof createLabelParts>} parts
 * @param {{label?:string, sublabel?:string, badges?:string[]}} node
 */
export function setLabelText(parts, node) {
  const badges = node.badges ?? [];
  const text = `${node.label ?? ''}\u0001${node.sublabel ?? ''}\u0001${badges.join('\u0002')}`;
  if (text === parts.text) return false;
  parts.text = text;
  parts.nameEl.textContent = node.label ?? '';
  parts.subEl.textContent = node.sublabel ?? '';
  parts.subEl.hidden = !node.sublabel;
  while (parts.badgeEls.length > badges.length) parts.badgeEls.pop().remove();
  while (parts.badgeEls.length < badges.length) {
    const b = document.createElement('span');
    b.className = 'scene-label__badge';
    parts.el.append(b);
    parts.badgeEls.push(b);
  }
  badges.forEach((t, i) => { parts.badgeEls[i].textContent = t; });
  return true;
}

/**
 * @typedef {Object} LabelItem
 * @property {import('three/addons/renderers/CSS2DRenderer.js').CSS2DObject} obj
 * @property {number} group priority group, lower wins (0 selected, 1 hovered, 2 highlighted, 3 container, 4 other)
 * @property {boolean} force always shown (selected / hovered)
 * @property {boolean} container left-anchored container label
 * @property {number} size world width of the node footprint (leaf size culling)
 * @property {number} w measured label width in px (0 = unknown)
 * @property {number} h measured label height in px
 * @property {boolean} show output
 * @property {number} dist scratch
 */

function overlaps(grid, x0, y0, x1, y1) {
  const cx0 = Math.floor(x0 / CELL);
  const cx1 = Math.floor(x1 / CELL);
  const cy0 = Math.floor(y0 / CELL);
  const cy1 = Math.floor(y1 / CELL);
  for (let cx = cx0; cx <= cx1; cx++) {
    for (let cy = cy0; cy <= cy1; cy++) {
      const list = grid.get(cx * 8192 + cy);
      if (!list) continue;
      for (let i = 0; i < list.length; i += 4) {
        if (x0 < list[i + 2] && x1 > list[i] && y0 < list[i + 3] && y1 > list[i + 1]) return true;
      }
    }
  }
  return false;
}

function insert(grid, x0, y0, x1, y1) {
  const cx0 = Math.floor(x0 / CELL);
  const cx1 = Math.floor(x1 / CELL);
  const cy0 = Math.floor(y0 / CELL);
  const cy1 = Math.floor(y1 / CELL);
  for (let cx = cx0; cx <= cx1; cx++) {
    for (let cy = cy0; cy <= cy1; cy++) {
      const key = cx * 8192 + cy;
      let list = grid.get(key);
      if (!list) { list = []; grid.set(key, list); }
      list.push(x0, y0, x1, y1);
    }
  }
}

/**
 * Decide which labels are shown. Matrices of every label object must be current.
 * @param {LabelItem[]} items
 * @param {THREE.Camera} camera
 * @param {number} width viewport CSS px
 * @param {number} height
 * @returns {number} number of visible labels
 */
export function layoutLabels(items, camera, width, height) {
  const ortho = camera.isOrthographicCamera;
  const pxPerUnitAtUnit = ortho
    ? height / ((camera.top - camera.bottom) / camera.zoom)
    : height / (2 * Math.tan(THREE.MathUtils.degToRad(camera.fov / 2)));
  const order = [];
  for (const it of items) {
    const m = it.obj.matrixWorld.elements;
    _v.set(m[12], m[13], m[14]);
    it.dist = _v.distanceTo(camera.position);
    _v.project(camera);
    it.sx = (_v.x * 0.5 + 0.5) * width;
    it.sy = (-_v.y * 0.5 + 0.5) * height;
    const inView = _v.z >= -1 && _v.z <= 1 && Math.abs(_v.x) < 1.3 && Math.abs(_v.y) < 1.3;
    it.show = false;
    if (inView) order.push(it);
  }
  order.sort((a, b) => (a.group - b.group) || (a.dist - b.dist));
  const grid = new Map();
  let shown = 0;
  for (const it of order) {
    const w = it.w || 70;
    const h = it.h || 18;
    if (!it.force && !it.container) {
      const px = ortho ? it.size * pxPerUnitAtUnit : (it.size * pxPerUnitAtUnit) / Math.max(0.01, it.dist);
      if (px < MIN_LEAF_PX) continue;
    }
    const x0 = it.container ? it.sx : it.sx - w / 2;
    const y0 = it.sy - h;
    const x1 = x0 + w;
    const y1 = it.sy;
    if (!it.force && overlaps(grid, x0, y0, x1, y1)) continue;
    insert(grid, x0, y0, x1, y1);
    it.show = true;
    shown++;
  }
  return shown;
}
