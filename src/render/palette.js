// Colour resolution for the scene: CSS custom properties with fixed fallbacks.
import { Color } from 'three';

export const ROLE_FALLBACK = {
  slate: '#8b98a8', blue: '#5b8fd9', amber: '#d9a441', teal: '#4fb3a5', violet: '#9b7fd4',
  steel: '#7f8ea3', rose: '#d47a8e', green: '#5fb878', red: '#e0605a', neutral: '#9aa3ad',
};

const WHITE = new Color(1, 1, 1);
const _hsl = { h: 0, s: 0, l: 0 };

function readColor(style, name, fallback) {
  const c = new Color(fallback);
  const v = style.getPropertyValue(name).trim();
  if (v) {
    const probe = new Color();
    try {
      probe.setStyle(v);
      c.copy(probe);
    } catch {
      /* keep fallback */
    }
  }
  return c;
}

/**
 * Lighter copy of a colour (mix toward white).
 * @param {Color} c @param {number} f
 */
export function lighten(c, f) {
  return c.clone().lerp(WHITE, f);
}

/** Darker copy of a colour (scale toward black). */
export function darken(c, f) {
  return c.clone().multiplyScalar(1 - f);
}

/** Reduced saturation/brightness variant used for lit surfaces. */
export function calm(c, sat = 0.72, lum = 0.82) {
  c.getHSL(_hsl);
  return new Color().setHSL(_hsl.h, _hsl.s * sat, _hsl.l * lum);
}

/**
 * Read the palette from :root once.
 */
export function readPalette() {
  const style = getComputedStyle(document.documentElement);
  /** @type {Record<string, Color>} */
  const raw = {};
  for (const [role, fb] of Object.entries(ROLE_FALLBACK)) raw[role] = readColor(style, `--c-${role}`, fb);
  const accent = readColor(style, '--accent', '#5cc8d6');
  const surface = readColor(style, '--surface-0', '#131518');
  const grid1 = readColor(style, '--line-1', '#23272d');
  const grid2 = readColor(style, '--line-2', '#2e343b');
  const role = (name) => raw[name] ?? raw.neutral;
  const bodyCache = new Map();
  return {
    raw, accent, surface, grid1, grid2, role,
    /** calm lit colour for a role */
    body(name) {
      let c = bodyCache.get(name);
      if (!c) { c = calm(role(name)); bodyCache.set(name, c); }
      return c;
    },
    /** colour for unlit line work of a role */
    line(name) { return calm(role(name), 0.9, 0.97); },
  };
}
