// A menu that opens from a button: the More sheet, the app bar's overflow menu and
// the save-conflict menu. It sets `data-open` on the panel and `aria-expanded` on
// the button (CSS decides what open looks like at each size), closes on Escape,
// on a press outside, and after an item is chosen, and moves focus in and back.

/**
 * @param {HTMLElement} button
 * @param {HTMLElement} panel
 * @param {{
 *   place?: (panel: HTMLElement, button: HTMLElement) => void,
 *   isMenu?: () => boolean,
 *   onToggle?: (open: boolean) => void,
 * }} [o] `isMenu` false means the panel is currently shown inline (desktop) and the
 *   button does nothing; `place` positions the panel next to its button.
 */
export function createMenu(button, panel, o = {}) {
  const isMenu = o.isMenu ?? (() => true);
  if (!panel.id) panel.id = `menu-${Math.random().toString(36).slice(2, 9)}`;
  button.setAttribute('aria-haspopup', 'true');
  button.setAttribute('aria-controls', panel.id);
  button.setAttribute('aria-expanded', 'false');

  const items = () => /** @type {HTMLElement[]} */ ([...panel.querySelectorAll('button:not([disabled]), select:not([disabled]), input:not([disabled]):not([type=hidden])')]
    .filter((n) => /** @type {HTMLElement} */ (n).offsetParent !== null));

  const isOpen = () => panel.hasAttribute('data-open');

  /** @param {boolean} [focus] */
  const open = (focus = true) => {
    if (!isMenu()) return;
    panel.setAttribute('data-open', '');
    button.setAttribute('aria-expanded', 'true');
    o.place?.(panel, button);
    o.onToggle?.(true);
    if (focus) items()[0]?.focus({ preventScroll: true });
  };
  /** @param {boolean} [restore] */
  const close = (restore = false) => {
    if (!isOpen()) return;
    panel.removeAttribute('data-open');
    button.setAttribute('aria-expanded', 'false');
    o.onToggle?.(false);
    if (restore) button.focus({ preventScroll: true });
  };
  const toggle = () => (isOpen() ? close() : open());

  button.addEventListener('click', () => toggle());
  document.addEventListener('pointerdown', (e) => {
    if (!isOpen()) return;
    const t = /** @type {Node} */ (e.target);
    if (!panel.contains(t) && !button.contains(t)) close();
  }, true);
  panel.addEventListener('keydown', (e) => {
    if (!isOpen()) return;
    if (e.key === 'Escape') { e.preventDefault(); e.stopPropagation(); close(true); return; }
    if (e.key !== 'ArrowDown' && e.key !== 'ArrowUp') return;
    const list = items().filter((n) => n.tagName === 'BUTTON');
    const i = list.indexOf(/** @type {HTMLElement} */ (document.activeElement));
    if (i < 0) return;
    e.preventDefault();
    list[(i + (e.key === 'ArrowDown' ? 1 : -1) + list.length) % list.length].focus({ preventScroll: true });
  });
  // Choosing a plain button closes the menu; selects and toggles inside keep it open.
  panel.addEventListener('click', (e) => {
    if (!isOpen()) return;
    const b = /** @type {HTMLElement} */ (e.target).closest('button');
    if (b && !b.hasAttribute('data-keep-open')) close();
  });
  window.addEventListener('resize', () => { if (isOpen()) o.place?.(panel, button); });

  return { open, close, toggle, isOpen };
}

/**
 * Place a fixed panel under its button, right-aligned to it, kept inside the window.
 * @param {HTMLElement} panel @param {HTMLElement} button
 */
export function placeBelow(panel, button) {
  const r = button.getBoundingClientRect();
  panel.style.top = `${Math.round(r.bottom + 6)}px`;
  panel.style.right = `${Math.max(8, Math.round(window.innerWidth - r.right))}px`;
  panel.style.left = 'auto';
}
