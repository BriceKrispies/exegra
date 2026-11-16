// Small DOM helpers shared by the UI modules. No state, no framework.

const SVG_NS = 'http://www.w3.org/2000/svg';

/**
 * Apply attributes and children to an element.
 *  - `class` / `className`: string or array of strings (falsy entries dropped)
 *  - `style`: object; keys starting with `--` set custom properties
 *  - `on<event>`: function, added with addEventListener (`onclick` -> 'click')
 *  - `value`, `checked`, `selected`, `indeterminate`: set as properties
 *  - `aria-*`: always stringified (so `false` stays "false"); null/undefined skipped
 *  - other: `true` -> empty attribute, `false`/null/undefined -> omitted
 * @param {Element} node @param {Record<string, any>|null|undefined} attrs @param {any[]} children
 */
function build(node, attrs, children) {
  if (attrs) {
    for (const [k, v] of Object.entries(attrs)) {
      if (k.startsWith('aria-')) {
        if (v != null) node.setAttribute(k, String(v));
        continue;
      }
      if (v == null || v === false) continue;
      if (k === 'class' || k === 'className') {
        node.setAttribute('class', Array.isArray(v) ? v.filter(Boolean).join(' ') : String(v));
      } else if (k === 'style' && typeof v === 'object') {
        for (const [sk, sv] of Object.entries(v)) {
          if (sv == null) continue;
          if (sk.startsWith('--')) /** @type {HTMLElement} */ (node).style.setProperty(sk, String(sv));
          else /** @type {any} */ (node).style[sk] = sv;
        }
      } else if (k.startsWith('on') && typeof v === 'function') {
        node.addEventListener(k.slice(2).toLowerCase(), v);
      } else if (k === 'value' || k === 'checked' || k === 'selected' || k === 'indeterminate') {
        /** @type {any} */ (node)[k] = v;
      } else if (k === 'text') {
        node.textContent = String(v);
      } else {
        node.setAttribute(k, v === true ? '' : String(v));
      }
    }
  }
  append(node, children);
  return node;
}

/** @param {Node} node @param {any[]} children */
function append(node, children) {
  for (const c of children) {
    if (c == null || c === false || c === true) continue;
    if (Array.isArray(c)) append(node, c);
    else node.append(c instanceof Node ? c : document.createTextNode(String(c)));
  }
}

/**
 * Create an HTML element.
 * @param {string} tag @param {Record<string, any>|null} [attrs] @param {...any} children
 * @returns {HTMLElement}
 */
export function h(tag, attrs, ...children) {
  return /** @type {HTMLElement} */ (build(document.createElement(tag), attrs, children));
}

/**
 * Create an SVG element.
 * @param {string} tag @param {Record<string, any>|null} [attrs] @param {...any} children
 * @returns {SVGElement}
 */
export function svg(tag, attrs, ...children) {
  return /** @type {SVGElement} */ (build(document.createElementNS(SVG_NS, tag), attrs, children));
}

/** Remove every child. @param {Element|DocumentFragment} el */
export function clear(el) {
  el.replaceChildren();
  return el;
}

/**
 * addEventListener that returns its own remover.
 * @param {EventTarget} el @param {string} type @param {(e: any) => void} fn @param {AddEventListenerOptions|boolean} [opts]
 * @returns {() => void}
 */
export function on(el, type, fn, opts) {
  el.addEventListener(type, fn, opts);
  return () => el.removeEventListener(type, fn, opts);
}

/** CSS colour for a palette role name (or a literal colour). @param {string|undefined} color */
export function colorVar(color) {
  if (!color) return 'var(--c-neutral)';
  return /^[a-z]+$/.test(color) ? `var(--c-${color})` : color;
}

// ---- icons ----------------------------------------------------------------
// 16x16 grid, 1.5px stroke, currentColor. A string is a path; [cx, cy, r] is a circle.

/** @type {Record<string, (string|number[])[]>} */
const ICONS = {
  'chevron-left': ['M10 3.5 5.5 8 10 12.5'],
  'chevron-right': ['M6 3.5 10.5 8 6 12.5'],
  'chevron-down': ['M3.5 6 8 10.5 12.5 6'],
  eye: ['M1.5 8s2.3-4.5 6.5-4.5S14.5 8 14.5 8 12.2 12.5 8 12.5 1.5 8 1.5 8Z', [8, 8, 2]],
  'eye-off': ['M1.5 8s2.3-4.5 6.5-4.5S14.5 8 14.5 8 12.2 12.5 8 12.5 1.5 8 1.5 8Z', [8, 8, 2], 'M3 13 13 3'],
  collapse: ['M2.5 2.5h11v11h-11Z', 'M5.5 8h5'],
  isolate: [[8, 8, 2.5], 'M8 2v3M8 11v3M2 8h3M11 8h3'],
  undo: ['M5.5 3 2.5 6l3 3', 'M2.5 6H10a3.5 3.5 0 0 1 0 7H6'],
  redo: ['M10.5 3 13.5 6l-3 3', 'M13.5 6H6a3.5 3.5 0 0 0 0 7h4'],
  plus: ['M8 3v10M3 8h10'],
  trash: ['M3 4.5h10M6.5 4.5V3h3v1.5', 'M4.5 4.5l.5 8.5h6l.5-8.5M7 7v4M9 7v4'],
  cursor: ['M3.5 2.5 12 7l-4.2 1.2L6.6 12.5Z'],
  connect: [[3.5, 12.5, 1.8], [12.5, 3.5, 1.8], 'M4.8 11.2 11.2 4.8'],
  fit: ['M2.5 6V2.5H6M10 2.5h3.5V6M13.5 10v3.5H10M6 13.5H2.5V10'],
  restart: ['M3 8a5 5 0 1 0 1.8-3.8', 'M3 2.5v3h3'],
  download: ['M8 2.5v8M4.5 7.5 8 11l3.5-3.5M3 13.5h10'],
  upload: ['M8 10.5v-8M4.5 5.5 8 2l3.5 3.5M3 13.5h10'],
  close: ['M4 4l8 8M12 4l-8 8'],
  'step-back': ['M4 3v10', 'M12.5 3.5 6 8l6.5 4.5Z'],
  step: ['M12 3v10', 'M3.5 3.5 10 8l-6.5 4.5Z'],
  play: ['M4.5 3 12.5 8 4.5 13Z'],
  pause: ['M5.5 3.5v9M10.5 3.5v9'],
  'run-end': ['M2.5 3.5 7.5 8l-5 4.5Z', 'M8 3.5 13 8l-5 4.5Z'],
  perspective: ['M8 2 13.5 5v6L8 14 2.5 11V5Z', 'M2.5 5 8 8l5.5-3M8 8v6'],
  top: ['M2.5 2.5h11v11h-11Z', 'M2.5 8h11M8 2.5v11'],
  warning: ['M8 2.5 14 13H2Z', 'M8 6.5v3M8 11.2v.1'],
  error: [[8, 8, 5.5], 'M5.8 5.8l4.4 4.4M10.2 5.8l-4.4 4.4'],
  info: [[8, 8, 5.5], 'M8 7.5v3.5M8 5v.1'],
  tree: ['M2.5 3h5', 'M5 3v9.5h3.5', 'M5 8h3.5', 'M8.5 6.5h5v3h-5Z', 'M8.5 11h5v3h-5Z'],
  inspect: ['M2.5 2.5h11v11h-11Z', 'M5 6h6', 'M5 8.5h6', 'M5 11h3.5'],
  check: ['M3 8.5 6.5 12 13 4.5'],
  history: [[8, 8, 5.5], 'M8 5v3.2l2.2 1.6'],
  code: ['M5.5 4 2 8l3.5 4', 'M10.5 4 14 8l-3.5 4', 'M9 3 7 13'],
  package: ['M8 1.8 13.8 5v6L8 14.2 2.2 11V5Z', 'M2.2 5 8 8.2 13.8 5', 'M8 8.2v6'],
  more: [[8, 3.5, 0.9], [8, 8, 0.9], [8, 12.5, 0.9]],
  search: [[7, 7, 4.5], 'M10.5 10.5 14 14'],
  'arrow-left': ['M13 8H3', 'M7 4 3 8l4 4'],
  legend: ['M2.5 4h2M2.5 8h2M2.5 12h2', 'M7 4h6.5M7 8h6.5M7 12h6.5'],
  stats: ['M2 13.5h12', 'M4 11V8M7 11V4M10 11V6.5M13 11V9'],
  layout: ['M2.5 2.5h4.5v4.5H2.5Z', 'M9 2.5h4.5v4.5H9Z', 'M2.5 9h4.5v4.5H2.5Z', 'M9 9h4.5v4.5H9Z'],
  dot: [[8, 8, 3]],
};

/**
 * A small inline SVG icon drawn from the table above.
 * @param {string} name @param {number} [size]
 * @returns {SVGElement}
 */
export function icon(name, size = 14) {
  const parts = ICONS[name] ?? [];
  return svg('svg', {
    class: `icon icon--${name}`, viewBox: '0 0 16 16', width: size, height: size,
    fill: 'none', stroke: 'currentColor', 'stroke-width': 1.5, 'stroke-linecap': 'round', 'stroke-linejoin': 'round',
    'aria-hidden': 'true', focusable: 'false',
  }, parts.map((p) => (typeof p === 'string' ? svg('path', { d: p }) : svg('circle', { cx: p[0], cy: p[1], r: p[2] }))));
}

/**
 * A small filled glyph for a node shape in a palette colour. Rough, not exact:
 * it tells categories apart, it does not draw the 3D shape.
 * @param {string|undefined} shape @param {string|undefined} color palette role
 * @param {number} [size]
 * @returns {SVGElement}
 */
export function shapeGlyph(shape, color, size = 12) {
  const c = colorVar(color);
  const fill = { fill: c, stroke: 'none' };
  /** @type {SVGElement[]} */
  let parts;
  switch (shape) {
    case 'chamfer': parts = [svg('polygon', { ...fill, points: '5,1.5 12.5,1.5 12.5,12.5 1.5,12.5 1.5,5' })]; break;
    case 'cylinder': parts = [
      svg('path', { ...fill, d: 'M2.5 4c0-1.4 2.2-2.2 4.5-2.2S11.5 2.6 11.5 4v6c0 1.4-2.2 2.2-4.5 2.2S2.5 11.4 2.5 10Z' }),
      svg('ellipse', { cx: 7, cy: 4, rx: 4.5, ry: 1.7, fill: 'none', stroke: 'var(--surface-1)', 'stroke-width': 1 }),
    ]; break;
    case 'tablet': parts = [svg('rect', { ...fill, x: 1.5, y: 3.5, width: 11, height: 7, rx: 1.5 })]; break;
    case 'octa': parts = [svg('polygon', { ...fill, points: '5,1.5 9,1.5 12.5,5 12.5,9 9,12.5 5,12.5 1.5,9 1.5,5' })]; break;
    case 'hex': parts = [svg('polygon', { ...fill, points: '7,1.5 12.5,4.25 12.5,9.75 7,12.5 1.5,9.75 1.5,4.25' })]; break;
    case 'pipe': parts = [svg('rect', { ...fill, x: 1.5, y: 4.5, width: 11, height: 5, rx: 2.5 })]; break;
    case 'sphere': parts = [svg('circle', { ...fill, cx: 7, cy: 7, r: 5.5 })]; break;
    case 'diamond': parts = [svg('polygon', { ...fill, points: '7,1 13,7 7,13 1,7' })]; break;
    case 'capsule': parts = [svg('rect', { ...fill, x: 3, y: 1.5, width: 8, height: 11, rx: 4 })]; break;
    case 'container': parts = [svg('rect', { x: 1.5, y: 1.5, width: 11, height: 11, rx: 1, fill: 'none', stroke: c, 'stroke-width': 1.25, 'stroke-dasharray': '2.5 2' })]; break;
    default: parts = [svg('rect', { ...fill, x: 2, y: 2, width: 10, height: 10, rx: 1 })];
  }
  return svg('svg', { class: 'glyph', viewBox: '0 0 14 14', width: size, height: size, 'aria-hidden': 'true', focusable: 'false' }, parts);
}

/**
 * A short line swatch for a relationship / edge style.
 * @param {string|undefined} line solid|dashed|dotted @param {string|undefined} color palette role
 * @param {{arrow?: boolean, width?: number}} [opts]
 * @returns {SVGElement}
 */
export function lineSwatch(line, color, opts = {}) {
  const c = colorVar(color);
  const w = opts.width ?? 26;
  const dash = line === 'dashed' ? '4 3' : line === 'dotted' ? '1.5 2.5' : null;
  const end = opts.arrow ? w - 5 : w - 1;
  return svg('svg', { class: 'swatch', viewBox: `0 0 ${w} 10`, width: w, height: 10, 'aria-hidden': 'true', focusable: 'false' },
    svg('line', { x1: 1, y1: 5, x2: end, y2: 5, stroke: c, 'stroke-width': 1.75, 'stroke-dasharray': dash, 'stroke-linecap': line === 'dotted' ? 'round' : 'butt' }),
    opts.arrow ? svg('polygon', { points: `${w - 6},1.5 ${w - 0.5},5 ${w - 6},8.5`, fill: c }) : null);
}

/**
 * Scroll `el` into view inside its nearest scrolling ancestor only. Element.scrollIntoView
 * scrolls every ancestor, including the page frame, which on a phone would push the
 * app bar and the navigation off screen.
 * @param {Element|null|undefined} el
 */
export function revealInScroller(el) {
  if (!el) return;
  let p = el.parentElement;
  while (p && p !== document.body) {
    const cs = getComputedStyle(p);
    if (/(auto|scroll)/.test(cs.overflowY) && p.scrollHeight > p.clientHeight) break;
    p = p.parentElement;
  }
  if (!p || p === document.body) return;
  const r = el.getBoundingClientRect();
  const pr = p.getBoundingClientRect();
  if (r.top < pr.top) p.scrollTop -= pr.top - r.top;
  else if (r.bottom > pr.bottom) p.scrollTop += r.bottom - pr.bottom;
}
