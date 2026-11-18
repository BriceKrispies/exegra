// Responsive layout: the destinations, the navigation (a bottom bar on a phone, a
// rail from tablet width up) and where the two panels go at each size. The
// panels are the same elements everywhere; this module only decides which one is
// shown and in what state, and sets data attributes that layout.css places:
//
//   phone   (< --bp-tablet)   one panel at a time, as a bottom sheet with detents
//                             (sheet.js); the scene fills the screen behind it
//   tablet  (>= --bp-tablet)  one panel at a time, docked beside the scene, with a
//                             collapse control and a draggable width
//   desktop (>= --bp-desktop) the explorer as its own column and the context panel
//                             (inspector, simulation, verification, ...) beside the scene
//
// The context panel holds one tabpanel per destination; the explorer panel holds
// the explorer. Nothing here knows what is inside them.

import { h, clear, icon } from './dom.js';
import { createSheet } from './sheet.js';
import { createMenu } from './menu.js';
import { traffic } from '../app/traffic-recorder.js';

/** @typedef {'phone'|'tablet'|'desktop'} LayoutMode */
/** @typedef {import('./sheet.js').Detent} Detent */
/**
 * @typedef {Object} Destination
 * @property {string} id
 * @property {string} label      navigation label
 * @property {string} title      panel title
 * @property {string} icon
 * @property {boolean} primary   in the phone's bottom bar (the others are under More)
 * @property {boolean} [wide]    tables: the desktop context panel opens wider
 * @property {Detent} [detent]   the sheet detent it opens at on a phone (default half)
 */

/** @type {Destination[]} */
export const DESTINATIONS = [
  { id: 'explorer', label: 'Explore', title: 'Explorer', icon: 'tree', primary: true },
  { id: 'inspector', label: 'Inspect', title: 'Inspector', icon: 'inspect', primary: true },
  { id: 'simulation', label: 'Simulate', title: 'Simulation', icon: 'play', primary: true, wide: true },
  { id: 'verification', label: 'Verify', title: 'Verification', icon: 'check', primary: true, wide: true },
  { id: 'changes', label: 'Changes', title: 'Changes', icon: 'history', primary: false, wide: true },
  { id: 'diagnostics', label: 'Diagnostics', title: 'Diagnostics', icon: 'warning', primary: false, wide: true },
  { id: 'source', label: 'Source', title: 'Source', icon: 'code', primary: false, detent: 'full' },
  { id: 'realisation', label: 'Realisation', title: 'Realisation', icon: 'package', primary: false, wide: true },
];
const BY_ID = new Map(DESTINATIONS.map((d) => [d.id, d]));
const STORE_KEY = 'exegra.layout';

/** @returns {any} */
function loadStored() {
  try { return JSON.parse(localStorage.getItem(STORE_KEY) ?? 'null') ?? {}; } catch { return {}; }
}

/** @param {HTMLElement} el @param {string} name @param {number} fallback */
function tokenPx(el, name, fallback) {
  const v = parseFloat(getComputedStyle(el).getPropertyValue(name));
  return Number.isFinite(v) ? v : fallback;
}

/** @param {EventTarget|null} t */
function isEditable(t) {
  const el = t instanceof HTMLElement ? t : null;
  return !!el && (el.isContentEditable || ['INPUT', 'TEXTAREA', 'SELECT'].includes(el.tagName));
}

/**
 * @param {{app: HTMLElement, nav: HTMLElement, explorer: HTMLElement, context: HTMLElement}} els
 */
export function createLayout(els) {
  const { app, nav } = els;
  const root = document.documentElement;
  const tabletMq = window.matchMedia(`(min-width: ${tokenPx(root, '--bp-tablet', 768)}px)`);
  const desktopMq = window.matchMedia(`(min-width: ${tokenPx(root, '--bp-desktop', 1200)}px)`);
  /** @returns {LayoutMode} */
  const mode = () => (desktopMq.matches ? 'desktop' : tabletMq.matches ? 'tablet' : 'phone');

  const stored = loadStored();
  const state = {
    /** what the phone sheet or the tablet side panel shows */
    dest: BY_ID.has(stored.context) ? String(stored.context) : 'inspector',
    /** the context panel's destination (never the explorer) */
    context: BY_ID.has(stored.context) && stored.context !== 'explorer' ? String(stored.context) : 'inspector',
    /** @type {Detent} phone: always starts closed so the scene is the screen */
    detent: /** @type {Detent} */ ('closed'),
    /** tablet: the side panel is open */
    open: stored.tabletOpen === true,
    /** desktop columns */
    explorerOpen: stored.explorerOpen !== false,
    contextOpen: stored.contextOpen !== false,
    widths: {
      explorer: Number(stored.widths?.explorer) || tokenPx(root, '--explorer-w', 280),
      panel: Number(stored.widths?.panel) || tokenPx(root, '--panel-w', 400),
      wide: Number(stored.widths?.wide) || tokenPx(root, '--panel-w-wide', 680),
    },
  };
  if (stored.tabletDest && BY_ID.has(stored.tabletDest)) state.dest = String(stored.tabletDest);
  // The self-model abstracts this store to whether the explorer is open (responsive-layout-flow): a write
  // that changes it is recorded as panel-toggled and layout-preferences-written; any other write is a stutter step.
  let storedExplorerOpen = state.explorerOpen;
  const persist = () => {
    if (state.explorerOpen !== storedExplorerOpen) {
      storedExplorerOpen = state.explorerOpen;
      traffic.record('panel-toggled', { open: state.explorerOpen });
      traffic.record('layout-preferences-written', { explorerOpen: state.explorerOpen });
    }
    try {
      localStorage.setItem(STORE_KEY, JSON.stringify({
        context: state.context, tabletDest: state.dest, tabletOpen: state.open,
        explorerOpen: state.explorerOpen, contextOpen: state.contextOpen, widths: state.widths,
      }));
    } catch { /* storage unavailable */ }
  };

  /** @type {Record<string, string>} */
  const summaries = {};

  // ---- panels ---------------------------------------------------------------------------
  const panelOf = (/** @type {string} */ dest) => (dest === 'explorer' ? els.explorer : els.context);
  const handleOf = (/** @type {HTMLElement} */ p) => /** @type {HTMLElement} */ (p.querySelector('.panel__handle'));
  const tabs = /** @type {HTMLElement[]} */ ([...els.context.querySelectorAll('.tabpanel[data-dest]')]);
  const contextTitle = /** @type {HTMLElement} */ (els.context.querySelector('[data-title]'));

  const sheets = {
    explorer: createSheet(els.explorer, {
      handle: handleOf(els.explorer),
      dragZone: /** @type {HTMLElement} */ (els.explorer.querySelector('.panel__header')),
      isActive: () => mode() === 'phone',
      request: (d) => setDetent(d),
    }),
    context: createSheet(els.context, {
      handle: handleOf(els.context),
      dragZone: /** @type {HTMLElement} */ (els.context.querySelector('.panel__header')),
      isActive: () => mode() === 'phone',
      request: (d) => setDetent(d),
    }),
  };

  // ---- navigation ---------------------------------------------------------------------------
  /** @type {Map<string, HTMLElement>} */
  const navButtons = new Map();
  const navItem = (/** @type {Destination} */ d) => {
    const b = h('button', {
      type: 'button', class: ['nav__item', !d.primary && 'nav__item--secondary'],
      id: `tab-btn-${d.id}`, 'data-testid': `tab-btn-${d.id}`, 'data-dest': d.id,
      'aria-controls': panelOf(d.id).id, 'aria-expanded': 'false', title: d.title,
      onclick: () => toggle(d.id),
    }, h('span', { class: 'nav__icon', 'aria-hidden': 'true' }, icon(d.icon, 20)), h('span', { class: 'nav__label' }, d.label));
    navButtons.set(d.id, b);
    return b;
  };
  const moreBtn = h('button', {
    type: 'button', class: 'nav__item nav__item--more', id: 'nav-more', 'data-testid': 'nav-more', title: 'More: changes, diagnostics, source, realisation',
  }, h('span', { class: 'nav__icon', 'aria-hidden': 'true' }, icon('more', 20)), h('span', { class: 'nav__label' }, 'More'));
  const moreMenu = h('div', { class: 'menu-sheet menu-sheet--bottom', id: 'more-menu', role: 'menu', 'aria-label': 'More' },
    h('div', { class: 'menu-sheet__title', 'aria-hidden': 'true' }, 'More'),
    DESTINATIONS.filter((d) => !d.primary).map((d) => h('button', {
      type: 'button', class: 'menu-sheet__item', role: 'menuitem', 'data-testid': `more-${d.id}`, 'data-dest': d.id,
      onclick: () => show(d.id),
    }, icon(d.icon, 20), h('span', null, d.title))));
  clear(nav);
  nav.append(
    ...DESTINATIONS.filter((d) => d.primary).map(navItem),
    h('div', { class: 'nav__sep', 'aria-hidden': 'true' }),
    ...DESTINATIONS.filter((d) => !d.primary).map(navItem),
    moreBtn);
  app.append(moreMenu);
  const more = createMenu(moreBtn, moreMenu, { isMenu: () => mode() === 'phone' });

  // ---- render ---------------------------------------------------------------------------------
  const clampWidths = () => {
    const m = mode();
    const rail = tokenPx(root, '--rail-w', 80);
    const sceneMin = tokenPx(root, '--scene-min-w', 360);
    const pMin = tokenPx(root, '--panel-w-min', 320);
    const pMax = tokenPx(root, '--panel-w-max', 760);
    const eMin = tokenPx(root, '--explorer-w-min', 220);
    const eMax = tokenPx(root, '--explorer-w-max', 520);
    const explorerW = m === 'desktop' && state.explorerOpen ? state.widths.explorer : 0;
    const room = Math.max(pMin, window.innerWidth - rail - explorerW - sceneMin);
    const clamp = (/** @type {number} */ v, /** @type {number} */ lo, /** @type {number} */ hi) => Math.round(Math.max(lo, Math.min(hi, v)));
    state.widths.explorer = clamp(state.widths.explorer, eMin, eMax);
    return {
      explorer: m === 'desktop' ? clamp(state.widths.explorer, eMin, Math.max(eMin, window.innerWidth - rail - sceneMin - pMin)) : state.widths.explorer,
      panel: clamp(state.widths.panel, pMin, Math.min(pMax, room)),
      wide: clamp(state.widths.wide, pMin, Math.min(pMax, room)),
    };
  };
  /** Which width the context panel uses now. */
  const contextWidthKey = () => (mode() === 'desktop' && BY_ID.get(state.context)?.wide ? 'wide' : 'panel');

  const COLLAPSE_ICON = { phone: 'close', tablet: 'chevron-right', desktop: 'chevron-right' };

  function apply() {
    const m = mode();
    app.dataset.layout = m;
    app.dataset.dest = state.dest;
    app.dataset.context = state.context;

    for (const t of tabs) t.hidden = t.dataset.dest !== state.context;
    contextTitle.textContent = BY_ID.get(state.context)?.title ?? '';
    for (const p of [els.explorer, els.context]) {
      const s = /** @type {HTMLElement|null} */ (p.querySelector('[data-summary]'));
      if (s) s.textContent = summaries[p === els.explorer ? 'explorer' : state.context] ?? '';
    }

    const w = clampWidths();
    app.style.setProperty('--explorer-w', `${w.explorer}px`);
    app.style.setProperty('--panel-w', `${m === 'tablet' ? w.panel : w[contextWidthKey()]}px`);

    /** @type {Record<'explorer'|'context', boolean>} */
    let shown;
    if (m === 'phone') {
      const active = state.dest === 'explorer' ? 'explorer' : 'context';
      sheets.explorer.render(active === 'explorer' ? state.detent : 'closed');
      sheets.context.render(active === 'context' ? state.detent : 'closed');
      app.dataset.sheet = state.detent;
      shown = { explorer: active === 'explorer' && state.detent !== 'closed', context: active === 'context' && state.detent !== 'closed' };
    } else {
      delete app.dataset.sheet;
      shown = m === 'tablet'
        ? { explorer: state.open && state.dest === 'explorer', context: state.open && state.dest !== 'explorer' }
        : { explorer: state.explorerOpen, context: state.contextOpen };
      els.explorer.dataset.detent = shown.explorer ? 'docked' : 'closed';
      els.context.dataset.detent = shown.context ? 'docked' : 'closed';
    }
    // From tablet width up the transport steps aside while the Simulate panel itself is open.
    app.dataset.simOpen = String(m !== 'phone' && shown.context && state.context === 'simulation');
    for (const p of [els.explorer, els.context]) {
      const handle = handleOf(p);
      handle.tabIndex = m === 'phone' ? 0 : -1;
      if (m !== 'phone') handle.setAttribute('aria-expanded', String(p === els.explorer ? shown.explorer : shown.context));
      const btn = /** @type {HTMLElement} */ (p.querySelector('[data-action="collapse"]'));
      const ic = m === 'desktop' && p === els.explorer ? 'chevron-left' : COLLAPSE_ICON[m];
      if (btn.dataset.icon !== ic) { btn.dataset.icon = ic; clear(btn).append(icon(ic, 18)); }
    }

    // navigation state
    for (const [id, b] of navButtons) {
      let current;
      if (m === 'desktop') current = id === 'explorer' ? state.explorerOpen : state.contextOpen && id === state.context;
      else current = (id === 'explorer' ? shown.explorer : shown.context) && id === state.dest;
      b.setAttribute('aria-current', String(current));
      b.setAttribute('aria-expanded', String(current));
    }
    const moreActive = m === 'phone' && shown.context && !BY_ID.get(state.dest)?.primary;
    moreBtn.setAttribute('aria-current', String(!!moreActive));
    for (const item of moreMenu.querySelectorAll('[data-dest]')) {
      item.setAttribute('aria-current', String(!!moreActive && /** @type {HTMLElement} */ (item).dataset.dest === state.dest));
    }
  }

  // ---- operations ------------------------------------------------------------------------------
  /** @param {HTMLElement} el */
  const focusSoon = (el) => requestAnimationFrame(() => el.focus({ preventScroll: true }));

  /**
   * Bring a destination to the front.
   * @param {string} dest
   * @param {{detent?: Detent, focus?: boolean}} [opts]
   */
  function show(dest, opts = {}) {
    const d = BY_ID.get(dest);
    if (!d) return;
    const m = mode();
    const samePanel = (state.dest === 'explorer') === (dest === 'explorer');
    state.dest = dest;
    if (dest !== 'explorer') state.context = dest;
    if (m === 'phone') {
      const wanted = opts.detent ?? d.detent ?? 'half';
      const order = ['closed', 'peek', 'half', 'full'];
      // switching destinations keeps a taller sheet as tall as it was
      state.detent = opts.detent || state.detent === 'closed' || !samePanel || order.indexOf(wanted) > order.indexOf(state.detent)
        ? wanted : state.detent;
    } else if (m === 'tablet') state.open = true;
    else if (dest === 'explorer') state.explorerOpen = true;
    else state.contextOpen = true;
    more.close();
    apply();
    persist();
    if (opts.focus !== false && m !== 'desktop') focusSoon(handleOf(panelOf(dest)));
  }

  /** The navigation's action: open, or close again when it is already open. @param {string} dest */
  function toggle(dest) {
    const m = mode();
    if (m === 'desktop') {
      if (dest === 'explorer') { state.explorerOpen = !state.explorerOpen; apply(); persist(); return; }
      show(dest);
      return;
    }
    const open = m === 'phone' ? state.detent !== 'closed' : state.open;
    if (open && state.dest === dest) { close(); return; }
    show(dest);
  }

  /** Close whatever panel the phone or tablet shows. @param {boolean} [restoreFocus] */
  function close(restoreFocus = true) {
    const m = mode();
    const panel = panelOf(state.dest);
    const hadFocus = panel.contains(document.activeElement);
    if (m === 'phone') state.detent = 'closed';
    else if (m === 'tablet') state.open = false;
    apply();
    persist();
    if (restoreFocus && hadFocus) navButtons.get(state.dest)?.focus({ preventScroll: true });
  }

  /** @param {Detent} d */
  function setDetent(d) {
    if (d === 'closed') { close(); return; }
    state.detent = d;
    apply();
  }

  // close buttons
  for (const p of [els.explorer, els.context]) {
    p.querySelector('[data-action="collapse"]')?.addEventListener('click', () => {
      const m = mode();
      if (m === 'desktop') {
        if (p === els.explorer) state.explorerOpen = false; else state.contextOpen = false;
        apply();
        persist();
        navButtons.get(p === els.explorer ? 'explorer' : state.context)?.focus({ preventScroll: true });
        return;
      }
      close();
    });
    // Escape steps a sheet down, or closes the tablet panel. Text fields keep their Escape.
    p.addEventListener('keydown', (e) => {
      if (e.key !== 'Escape' || e.defaultPrevented || isEditable(e.target) || document.querySelector('dialog[open]')) return;
      const m = mode();
      if (m === 'phone') { e.preventDefault(); (p === els.explorer ? sheets.explorer : sheets.context).collapseStep(); }
      else if (m === 'tablet') { e.preventDefault(); close(); }
    });
  }

  // ---- resizing (tablet and desktop, pointer and keyboard) ----------------------------------------
  for (const handle of /** @type {HTMLElement[]} */ ([...app.querySelectorAll('[data-resize]')])) {
    const which = handle.dataset.resize;
    /** Is this the explorer column's right edge (desktop) rather than a right-hand panel's left edge? */
    const isLeftColumn = () => which === 'explorer' && mode() === 'desktop';
    const key = () => (isLeftColumn() ? 'explorer' : which === 'context' ? contextWidthKey() : 'panel');
    const set = (/** @type {number} */ px) => {
      state.widths[/** @type {'explorer'|'panel'|'wide'} */ (key())] = px;
      apply();
      const w = clampWidths();
      handle.setAttribute('aria-valuenow', String(w[/** @type {'explorer'|'panel'|'wide'} */ (key())]));
    };
    /** @param {PointerEvent} e */
    const move = (e) => {
      const panel = /** @type {HTMLElement} */ (handle.parentElement);
      const r = panel.getBoundingClientRect();
      set(isLeftColumn() ? e.clientX - r.left : r.right - e.clientX);
    };
    const end = (/** @type {PointerEvent} */ e) => {
      handle.removeEventListener('pointermove', move);
      handle.removeEventListener('pointerup', end);
      handle.removeEventListener('pointercancel', end);
      try { handle.releasePointerCapture(e.pointerId); } catch { /* released */ }
      app.classList.remove('app--resizing');
      handle.classList.remove('panel__resize--active');
      persist();
    };
    handle.addEventListener('pointerdown', (e) => {
      if (mode() === 'phone' || (e.pointerType === 'mouse' && e.button !== 0)) return;
      e.preventDefault();
      handle.setPointerCapture(e.pointerId);
      app.classList.add('app--resizing');
      handle.classList.add('panel__resize--active');
      handle.addEventListener('pointermove', move);
      handle.addEventListener('pointerup', end);
      handle.addEventListener('pointercancel', end);
    });
    handle.addEventListener('keydown', (e) => {
      const grow = isLeftColumn() ? 'ArrowRight' : 'ArrowLeft';
      const shrink = isLeftColumn() ? 'ArrowLeft' : 'ArrowRight';
      const amount = e.shiftKey ? 64 : 16;
      const cur = state.widths[/** @type {'explorer'|'panel'|'wide'} */ (key())];
      if (e.key === grow) set(cur + amount);
      else if (e.key === shrink) set(cur - amount);
      else return;
      e.preventDefault();
      persist();
    });
    handle.addEventListener('dblclick', () => {
      const k = key();
      set(tokenPx(root, k === 'explorer' ? '--explorer-w' : k === 'wide' ? '--panel-w-wide' : '--panel-w', 400));
      persist();
    });
  }

  // The page frame never scrolls (layout.css clips it); should anything still scroll the
  // document, put it back so the app bar and the navigation stay where they belong.
  window.addEventListener('scroll', () => { if (window.scrollX || window.scrollY) window.scrollTo(0, 0); });
  const onModeChange = () => { more.close(); apply(); };
  tabletMq.addEventListener('change', onModeChange);
  desktopMq.addEventListener('change', onModeChange);
  window.addEventListener('resize', () => { if (mode() !== 'phone') apply(); });
  apply();

  return {
    mode,
    show,
    toggle,
    close,
    /** Is a destination on screen right now? @param {string} dest */
    isShown(dest) {
      const m = mode();
      if (m === 'phone') return state.detent !== 'closed' && state.dest === dest;
      if (m === 'tablet') return state.open && state.dest === dest;
      return dest === 'explorer' ? state.explorerOpen : state.contextOpen && state.context === dest;
    },
    get detent() { return state.detent; },
    get dest() { return state.dest; },
    /**
     * A selection, made by any route, brings the inspector forward unless another panel is
     * pinned open: on a phone it opens at peek (name, kind and status; drag up for the rest)
     * when no sheet is open or another sheet only peeks, and leaves a half or full sheet
     * alone; on a tablet it opens the side panel when it is closed. The desktop's context
     * panel keeps whatever it shows.
     */
    revealInspector() {
      const m = mode();
      if (m === 'phone') {
        if (state.dest === 'inspector' && state.detent !== 'closed') return;
        if (state.detent === 'closed' || state.detent === 'peek') show('inspector', { detent: 'peek', focus: false });
      } else if (m === 'tablet') {
        if (!state.open) show('inspector', { focus: false });
      }
    },
    /** Selection cleared from the scene: a peeking inspector sheet goes away. */
    dismissInspectorPeek() {
      if (mode() === 'phone' && state.dest === 'inspector' && state.detent === 'peek') close(false);
    },
    /** One-line summary under a destination's title. @param {string} dest @param {string} text */
    setSummary(dest, text) {
      if (summaries[dest] === text) return;
      summaries[dest] = text;
      const p = dest === 'explorer' ? els.explorer : dest === state.context ? els.context : null;
      const s = /** @type {HTMLElement|null} */ (p?.querySelector('[data-summary]') ?? null);
      if (s) s.textContent = text;
    },
  };
}
