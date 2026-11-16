// Shared, cached geometries for node shapes and edge decoration.
import * as THREE from 'three';
import { LineGeometry } from 'three/addons/lines/LineGeometry.js';

export const SLAB_T = 0.05;     // container slab thickness
export const LEVEL_DY = 0.12;   // vertical step per nesting level

/**
 * Per-shape presentation spec. `dims(w, d)` gives the world scale of the unit
 * (1x1x1, base at y=0) geometry for a footprint w x d.
 * @type {Record<string, {dims:(w:number,d:number)=>number[], lift?:number, tilt?:number, top?:(dims:number[])=>number, edges?:boolean}>}
 */
export const SHAPES = {
  box: { dims: (w, d) => [w * 0.88, 0.9, d * 0.88] },
  chamfer: { dims: (w, d) => [w * 0.88, 0.9, d * 0.88] },
  cylinder: { dims: (w, d) => { const s = Math.min(w, d) * 0.86; return [s, 0.9, s]; } },
  tablet: { dims: (w, d) => [w * 0.8, 0.14, d * 0.8], lift: 0.21, tilt: 0.28, top: () => 0.5 },
  octa: { dims: (w, d) => { const s = Math.min(w, d) * 0.8; return [s, 0.95, s]; } },
  hex: { dims: (w, d) => [w * 0.86, 0.9, d * 0.86] },
  pipe: { dims: (w, d) => { const t = Math.min(d * 0.7, 0.8); return [w * 0.88, t, t]; } },
  sphere: { dims: (w, d) => { const s = Math.min(w, d) * 0.7; return [s, s, s]; }, edges: false },
  diamond: { dims: (w, d) => [w * 0.7, 1.0, d * 0.5] },
  capsule: { dims: (w, d) => [w * 0.86, 0.5, d * 0.62] },
  container: { dims: (w, d) => [w, SLAB_T, d] },
};

/** @param {string} shape */
export function shapeSpec(shape) { return SHAPES[shape] ?? SHAPES.box; }

/** Height of a point on the visible top face (where a click lands), above the node base. */
export function shapePickY(shape, w, d) {
  const spec = shapeSpec(shape);
  const dims = spec.dims(w, d);
  return shape === 'tablet' ? 0.33 : dims[1] + (spec.lift ?? 0);
}

/** Height of the top of a node above its base, for a footprint. */
export function shapeTop(shape, w, d) {
  const spec = shapeSpec(shape);
  const dims = spec.dims(w, d);
  return spec.top ? spec.top(dims) : dims[1] + (spec.lift ?? 0);
}

/** Normalise a geometry into the unit box x,z in [-.5,.5], y in [0,1]. */
function normalize(g) {
  g.computeBoundingBox();
  const b = g.boundingBox;
  const sx = b.max.x - b.min.x || 1;
  const sy = b.max.y - b.min.y || 1;
  const sz = b.max.z - b.min.z || 1;
  g.translate(-(b.min.x + b.max.x) / 2, -b.min.y, -(b.min.z + b.max.z) / 2);
  g.scale(1 / sx, 1 / sy, 1 / sz);
  g.computeBoundingBox();
  g.computeBoundingSphere();
  return g;
}

function extrudeUp(shape) {
  const g = new THREE.ExtrudeGeometry(shape, { depth: 1, bevelEnabled: false });
  g.rotateX(-Math.PI / 2);
  return g;
}

function chamferGeometry() {
  const c = 0.09;
  const s = new THREE.Shape();
  s.moveTo(-0.5 + c, -0.5);
  s.lineTo(0.5 - c, -0.5); s.lineTo(0.5, -0.5 + c);
  s.lineTo(0.5, 0.5 - c); s.lineTo(0.5 - c, 0.5);
  s.lineTo(-0.5 + c, 0.5); s.lineTo(-0.5, 0.5 - c);
  s.lineTo(-0.5, -0.5 + c); s.closePath();
  return extrudeUp(s);
}

function tabletGeometry() {
  const r = 0.12;
  const s = new THREE.Shape();
  s.moveTo(-0.5 + r, -0.5);
  s.lineTo(0.5 - r, -0.5); s.quadraticCurveTo(0.5, -0.5, 0.5, -0.5 + r);
  s.lineTo(0.5, 0.5 - r); s.quadraticCurveTo(0.5, 0.5, 0.5 - r, 0.5);
  s.lineTo(-0.5 + r, 0.5); s.quadraticCurveTo(-0.5, 0.5, -0.5, 0.5 - r);
  s.lineTo(-0.5, -0.5 + r); s.quadraticCurveTo(-0.5, -0.5, -0.5 + r, -0.5);
  return extrudeUp(s);
}

function build(shape) {
  switch (shape) {
    case 'chamfer': return chamferGeometry();
    case 'cylinder': return new THREE.CylinderGeometry(0.5, 0.5, 1, 28);
    case 'tablet': return tabletGeometry();
    case 'octa':
    case 'diamond': return new THREE.OctahedronGeometry(0.5, 0);
    case 'hex': {
      const g = new THREE.CylinderGeometry(0.5, 0.5, 1, 6);
      g.rotateY(Math.PI / 6);
      const flat = g.toNonIndexed();
      g.dispose();
      flat.computeVertexNormals();
      return flat;
    }
    case 'pipe': return new THREE.CylinderGeometry(0.5, 0.5, 1, 20).rotateZ(Math.PI / 2);
    case 'sphere': return new THREE.SphereGeometry(0.5, 20, 14);
    case 'capsule': return new THREE.CapsuleGeometry(0.25, 0.5, 6, 16).rotateZ(Math.PI / 2);
    case 'container':
    case 'box':
    default: return new THREE.BoxGeometry(1, 1, 1);
  }
}

/** Per-view cache so that dispose() frees everything this view created. */
export class GeometryCache {
  constructor() {
    /** @type {Map<string, THREE.BufferGeometry>} */ this.geoms = new Map();
    /** @type {Map<string, THREE.BufferGeometry|null>} */ this.edgeGeoms = new Map();
    this.arrow = new THREE.ConeGeometry(0.1, 0.3, 12).translate(0, -0.15, 0); // tip at origin, pointing +Y
    this.marker = new THREE.SphereGeometry(0.1, 12, 8);
    this.unitRect = new LineGeometry();
    this.unitRect.setPositions([-0.5, 0, -0.5, 0.5, 0, -0.5, 0.5, 0, 0.5, -0.5, 0, 0.5, -0.5, 0, -0.5]);
  }

  /** @param {string} shape */
  shape(shape) {
    const key = SHAPES[shape] ? shape : 'box';
    let g = this.geoms.get(key);
    if (!g) { g = normalize(build(key)); this.geoms.set(key, g); }
    return g;
  }

  /** @param {string} shape @returns {THREE.BufferGeometry|null} */
  edges(shape) {
    const key = SHAPES[shape] ? shape : 'box';
    if (this.edgeGeoms.has(key)) return this.edgeGeoms.get(key) ?? null;
    const e = SHAPES[key].edges === false ? null : new THREE.EdgesGeometry(this.shape(key), 28);
    this.edgeGeoms.set(key, e);
    return e;
  }

  dispose() {
    for (const g of this.geoms.values()) g.dispose();
    for (const g of this.edgeGeoms.values()) g?.dispose();
    this.arrow.dispose(); this.marker.dispose(); this.unitRect.dispose();
    this.geoms.clear(); this.edgeGeoms.clear();
  }
}
