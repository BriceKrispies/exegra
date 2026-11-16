// Bottom-sheet controller: the detents of a panel on a phone (closed, peek, half,
// full), dragged by touch or pointer on the panel's header, snapped on release
// (a flick goes one detent further in its direction), and driven by keyboard
// through the header's handle button. It only sets `data-detent` and, while a
// drag is in progress, an inline transform; layout.css does the placing. It is
// inert while `isActive()` is false (tablet and desktop, where the same panel is
// a side panel or a column).

/** @typedef {'closed'|'peek'|'half'|'full'} Detent */

/** Order from lowest to highest. */
export const DETENTS = /** @type {const} */ (['closed', 'peek', 'half', 'full']);

/** Pixels of movement below which a press on the header is a tap. */
const TAP_SLOP = 6;
/** px per ms; a release faster than this moves one detent in the direction of travel. */
const FLICK = 0.45;

/**
 * Pixel heights of the visible part of a sheet at each detent.
 * peek is 22% of the screen (between 132 and 210 px), half is half the screen,
 * full is the whole sheet (it ends just below the app bar).
 * @param {number} sheetH @param {number} viewportH
 * @returns {Record<Detent, number>}
 */
export function detentHeights(sheetH, viewportH) {
  const peek = Math.round(Math.min(210, Math.max(132, viewportH * 0.22)));
  const half = Math.round(Math.min(sheetH, Math.max(peek + 40, viewportH * 0.5)));
  return { closed: 0, peek: Math.min(peek, sheetH), half, full: sheetH };
}

/**
 * @param {HTMLElement} panel the panel element (`.panel`)
 * @param {{
 *   handle: HTMLElement,
 *   dragZone?: HTMLElement,
 *   isActive: () => boolean,
 *   request: (detent: Detent, reason: 'drag'|'tap'|'key') => void,
 * }} o `request` asks the layout to move to a detent; the layout calls `render` back.
 */
export function createSheet(panel, o) {
  const zone = o.dragZone ?? o.handle;
  /** @type {Detent} */
  let current = 'closed';
  /** @type {{id: number, y0: number, vis0: number, h: number, samples: {t: number, y: number}[], moved: boolean}|null} */
  let drag = null;
  let suppressClick = false;

  const heights = () => detentHeights(panel.offsetHeight, window.innerHeight);

  /** Publish the pixel detents so layout.css and the floating controls agree with the drag. */
  const publish = () => {
    if (!o.isActive()) return;
    const hs = heights();
    const root = /** @type {HTMLElement} */ (panel.closest('.app') ?? document.documentElement);
    root.style.setProperty('--sheet-peek', `${hs.peek}px`);
    root.style.setProperty('--sheet-half', `${hs.half}px`);
  };

  /** The detent whose visible height is nearest to `vis`, allowing closed only when asked. @param {number} vis @param {boolean} allowClosed @returns {Detent} */
  const nearest = (vis, allowClosed) => {
    const hs = heights();
    /** @type {Detent} */
    let best = 'peek';
    let bestD = Infinity;
    for (const d of DETENTS) {
      if (d === 'closed' && !allowClosed) continue;
      const dist = Math.abs(hs[d] - vis);
      if (dist < bestD) { bestD = dist; best = d; }
    }
    return best;
  };

  /** @param {Detent} d @param {1|-1} dir */
  const step = (d, dir) => {
    const i = DETENTS.indexOf(d) + dir;
    return DETENTS[Math.max(0, Math.min(DETENTS.length - 1, i))];
  };

  /** @param {PointerEvent} e */
  const onDown = (e) => {
    if (!o.isActive() || current === 'closed') return;
    if (e.pointerType === 'mouse' && e.button !== 0) return;
    // the header's own buttons (close) keep their clicks
    const t = /** @type {HTMLElement} */ (e.target);
    if (t.closest('button') && !t.closest('.panel__handle')) return;
    const hs = heights();
    drag = { id: e.pointerId, y0: e.clientY, vis0: hs[current], h: hs.full, samples: [{ t: e.timeStamp, y: e.clientY }], moved: false };
    // No pointer capture yet: a tap must still reach the handle as a click.
  };
  /** @param {PointerEvent} e */
  const onMove = (e) => {
    if (!drag || e.pointerId !== drag.id) return;
    const dy = drag.y0 - e.clientY;
    if (!drag.moved && Math.abs(dy) < TAP_SLOP) return;
    if (!drag.moved) {
      drag.moved = true;
      panel.classList.add('panel--dragging');
      try { zone.setPointerCapture(e.pointerId); } catch { /* not capturable */ }
    }
    const vis = Math.max(0, Math.min(drag.h, drag.vis0 + dy));
    panel.style.transform = `translateY(${Math.round(drag.h - vis)}px)`;
    drag.samples.push({ t: e.timeStamp, y: e.clientY });
    if (drag.samples.length > 6) drag.samples.shift();
    e.preventDefault();
  };
  /** @param {PointerEvent} e */
  const onUp = (e) => {
    if (!drag || e.pointerId !== drag.id) return;
    const d = drag;
    drag = null;
    try { zone.releasePointerCapture(e.pointerId); } catch { /* released */ }
    if (!d.moved) return; // a tap: the click handler cycles the detent
    suppressClick = true;
    setTimeout(() => { suppressClick = false; }, 0);
    panel.classList.remove('panel--dragging');
    panel.style.transform = '';
    if (e.type === 'pointercancel') { render(current); return; }
    const vis = Math.max(0, Math.min(d.h, d.vis0 + (d.y0 - e.clientY)));
    // velocity over the last few samples, positive when moving up
    const first = d.samples[0];
    const last = d.samples[d.samples.length - 1];
    const dt = Math.max(1, last.t - first.t);
    const v = (first.y - last.y) / dt;
    /** @type {Detent} */
    let target;
    if (Math.abs(v) > FLICK) {
      // the next detent in the direction of the flick
      const hs = heights();
      if (v > 0) target = DETENTS.find((x) => x !== 'closed' && hs[x] > vis + 1) ?? 'full';
      else target = [...DETENTS].reverse().find((x) => hs[x] < vis - 1) ?? 'closed';
    } else {
      target = nearest(vis, vis < heights().peek * 0.6);
    }
    o.request(target, 'drag');
  };

  zone.addEventListener('pointerdown', onDown);
  zone.addEventListener('pointermove', onMove);
  zone.addEventListener('pointerup', onUp);
  zone.addEventListener('pointercancel', onUp);

  // Tap or Enter on the handle: peek -> half -> full -> peek.
  o.handle.addEventListener('click', (e) => {
    if (suppressClick) { e.preventDefault(); return; }
    if (!o.isActive()) return;
    o.request(current === 'peek' ? 'half' : current === 'half' ? 'full' : 'peek', 'tap');
  });
  o.handle.addEventListener('keydown', (e) => {
    if (!o.isActive()) return;
    if (e.key === 'ArrowUp') { e.preventDefault(); o.request(step(current, 1), 'key'); }
    else if (e.key === 'ArrowDown') { e.preventDefault(); o.request(step(current, -1), 'key'); }
    else if (e.key === 'Home') { e.preventDefault(); o.request('peek', 'key'); }
    else if (e.key === 'End') { e.preventDefault(); o.request('full', 'key'); }
  });

  window.addEventListener('resize', publish);
  new ResizeObserver(publish).observe(panel);

  /** Show a detent (called by the layout). @param {Detent} d */
  function render(d) {
    current = d;
    if (o.isActive()) {
      panel.dataset.detent = d;
      o.handle.setAttribute('aria-expanded', String(d === 'half' || d === 'full'));
      publish();
    }
  }

  return {
    render,
    get detent() { return current; },
    publish,
    /** Escape: one step down; from peek the sheet closes. */
    collapseStep: () => o.request(current === 'full' || current === 'half' ? 'peek' : 'closed', 'key'),
  };
}
