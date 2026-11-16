// Edge curve maths: border clipping, arcs, loops. Pure functions, no allocation per call.

export const SAMPLES = 24;
export const POINTS = SAMPLES + 1;

/**
 * @typedef {{x:number, z:number, w:number, d:number, top:number}} Rect
 */

function exitT(w, d, ux, uz) {
  const tx = Math.abs(ux) > 1e-9 ? (w / 2) / Math.abs(ux) : Infinity;
  const tz = Math.abs(uz) > 1e-9 ? (d / 2) / Math.abs(uz) : Infinity;
  return Math.min(tx, tz);
}

/**
 * Arc between two footprints.
 * @param {Float32Array} out POINTS*3 positions
 * @param {number[]} tan receives the end tangent (unit)
 * @param {Rect} a @param {Rect} b
 * @param {number} lateral signed sideways offset for parallel edges
 * @param {boolean} flip whether the canonical normal is flipped for this direction
 */
export function arcCurve(out, tan, a, b, lateral, flip) {
  let dx = b.x - a.x;
  let dz = b.z - a.z;
  let len = Math.hypot(dx, dz);
  if (len < 1e-6) { dx = 1; dz = 0; len = 1e-6; }
  const ux = dx / len;
  const uz = dz / len;
  let nx = -uz;
  let nz = ux;
  if (flip) { nx = -nx; nz = -nz; }
  const ox = nx * lateral;
  const oz = nz * lateral;
  let ta = exitT(a.w, a.d, ux, uz);
  let tb = exitT(b.w, b.d, ux, uz);
  const cap = len * 0.45;
  if (ta > cap) ta = cap;
  if (tb > cap) tb = cap;
  const p0x = a.x + ox + ux * ta;
  const p0z = a.z + oz + uz * ta;
  const p1x = b.x + ox - ux * tb;
  const p1z = b.z + oz - uz * tb;
  const y0 = a.top + 0.05;
  const y1 = b.top + 0.05;
  const dist = Math.hypot(p1x - p0x, p1z - p0z);
  const apex = 0.25 + 0.06 * dist;
  const cx = (p0x + p1x) / 2;
  const cz = (p0z + p1z) / 2;
  const cy = (y0 + y1) / 2 + 2 * apex;
  for (let i = 0; i <= SAMPLES; i++) {
    const t = i / SAMPLES;
    const m = 1 - t;
    const w0 = m * m;
    const w1 = 2 * m * t;
    const w2 = t * t;
    const o = i * 3;
    out[o] = w0 * p0x + w1 * cx + w2 * p1x;
    out[o + 1] = w0 * y0 + w1 * cy + w2 * y1;
    out[o + 2] = w0 * p0z + w1 * cz + w2 * p1z;
  }
  const tx = p1x - cx;
  const ty = y1 - cy;
  const tz = p1z - cz;
  const tl = Math.hypot(tx, ty, tz) || 1;
  tan[0] = tx / tl; tan[1] = ty / tl; tan[2] = tz / tl;
}

/**
 * Small vertical loop above a node (self edge).
 * @param {Float32Array} out @param {number[]} tan @param {Rect} a @param {number} idx stacking index
 */
export function loopCurve(out, tan, a, idx) {
  const r = 0.36 + idx * 0.14;
  const y0 = a.top + 0.05;
  for (let i = 0; i <= SAMPLES; i++) {
    const phi = (i / SAMPLES) * Math.PI * 2;
    const o = i * 3;
    out[o] = a.x + r * Math.sin(phi);
    out[o + 1] = y0 + r * (1 - Math.cos(phi));
    out[o + 2] = a.z;
  }
  // end tangent: direction of the last segment (arrives at the start point, travelling sideways/down)
  const o = SAMPLES * 3;
  const tx = out[o] - out[o - 3];
  const ty = out[o + 1] - out[o - 2];
  const tl = Math.hypot(tx, ty) || 1;
  tan[0] = tx / tl; tan[1] = ty / tl; tan[2] = 0;
}
