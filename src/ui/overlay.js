// Viewport overlay: the view name, an illustrative-example mark, the claims stated at a cut with their result at the
// cut a structural view shows (the hierarchy and cut controls are in the app bar's tools) and notes (top left),
// the legend and the render statistics. The overlay is pointer-transparent except its
// own summaries. On a phone the legend and the statistics start closed and are not
// drawn at all until opened (from the app bar's overflow menu); a closed card never
// covers the scene. On a desktop the legend starts open when it is short, and the
// statistics start open.

import { h, clear, shapeGlyph, lineSwatch } from './dom.js';

const POSITION_NOTE = 'Position on the ground plane is presentation only. Containment and relationships carry the meaning.';

/** @typedef {'legend'|'stats'} CardName */

/**
 * @param {HTMLElement} el
 * @param {any} session
 * @param {() => {fps: number, frameMs: number, drawCalls: number, triangles: number, nodes: number, edges: number, labels: number}|null|undefined} getStats
 * @param {{mode: () => 'phone'|'tablet'|'desktop'}} env
 * @returns {{cards: {isOpen(name: CardName): boolean, toggle(name: CardName): void, onChange(fn: () => void): void}, dispose: () => void}}
 */
export function mountOverlay(el, session, getStats, env) {
  const viewTitle = h('div', { class: 'overlay__view', 'data-testid': 'overlay-view' });
  const notesBody = h('ul', { class: 'overlay__notes' });
  // Claims stated at a cut, with their result at the cut the structural view shows.
  const levelClaims = h('ul', { class: 'overlay__level-claims', 'data-testid': 'level-claims' });
  const levelBar = h('div', { class: 'overlay__level', 'data-testid': 'level-bar' }, levelClaims);
  const notesSummary = h('summary', { class: 'overlay__summary' });
  const notes = h('details', { class: 'overlay__details overlay__details--notes' }, notesSummary, notesBody);

  const legendBody = h('ul', { class: 'overlay__legend' });
  const legendSummary = h('summary', { class: 'overlay__summary' });
  const legend = /** @type {HTMLDetailsElement} */ (h('details', { class: 'overlay__details', 'data-card': 'legend' }, legendSummary, legendBody));

  const statsBody = h('dl', { class: 'overlay__stats', 'data-testid': 'render-stats' });
  const stats = /** @type {HTMLDetailsElement} */ (h('details', { class: 'overlay__details', 'data-card': 'stats' }, h('summary', { class: 'overlay__summary' }, 'Render'), statsBody));

  const legendCard = h('div', { class: 'overlay__card overlay__card--legend' }, legend);
  const statsCard = h('div', { class: 'overlay__card overlay__card--stats' }, stats);
  clear(el);
  el.append(
    h('div', { class: 'overlay__corner overlay__corner--tl' }, h('div', { class: 'overlay__card overlay__card--view' }, viewTitle, levelBar, notes)),
    h('div', { class: 'overlay__corner overlay__corner--bl' }, legendCard),
    h('div', { class: 'overlay__corner overlay__corner--br' }, statsCard));

  // ---- open state ----------------------------------------------------------------
  /** @type {(() => void)[]} */
  const listeners = [];
  // The legend opens by itself only on a desktop and only while the user has not chosen.
  let legendTouched = false;
  const desktopish = () => env.mode() !== 'phone';
  const sync = () => {
    // a closed card is drawn on a desktop (its summary) but not on a phone
    legendCard.dataset.state = legend.open ? 'open' : 'closed';
    statsCard.dataset.state = stats.open ? 'open' : 'closed';
    for (const fn of listeners) fn();
  };
  legendSummary.addEventListener('click', () => { legendTouched = true; });
  legend.addEventListener('toggle', sync);
  stats.addEventListener('toggle', () => { sync(); renderStats(); });
  stats.open = desktopish();

  const cards = {
    /** @param {CardName} name */
    isOpen: (name) => (name === 'legend' ? legend.open : stats.open),
    /** @param {CardName} name */
    toggle: (name) => {
      if (name === 'legend') { legendTouched = true; legend.open = !legend.open; } else stats.open = !stats.open;
      sync();
    },
    /** @param {() => void} fn */
    onChange: (fn) => { listeners.push(fn); },
  };

  // ---- content --------------------------------------------------------------------
  const renderScene = () => {
    const scene = session.scene;
    const view = (session.views ?? []).find((/** @type {any} */ v) => v.id === session.viewId);
    clear(viewTitle);
    if (view) viewTitle.append(h('b', { class: 'overlay__view-name' }, view.name), h('span', { class: 'overlay__view-proj' }, `${view.projection} projection`));
    if (session.model?.system?.data.illustrative === true) viewTitle.append(h('span', { class: 'overlay__illustrative', 'data-testid': 'illustrative-mark', title: 'This system is an illustrative example, not a statement about real software.' }, 'Illustrative example'));

    renderLevel();
    const sceneNotes = /** @type {string[]} */ (scene?.notes ?? []);
    notesSummary.textContent = `Notes (${sceneNotes.length + 1})`;
    clear(notesBody);
    for (const n of sceneNotes) notesBody.append(h('li', null, n));
    notesBody.append(h('li', { class: 'overlay__standing' }, POSITION_NOTE));

    const entries = /** @type {any[]} */ (scene?.legend ?? []);
    legendSummary.textContent = `Legend (${entries.length})`;
    // A long legend starts closed so it does not cover the scene; on a phone every legend does.
    if (!legendTouched) legend.open = desktopish() && entries.length <= 9;
    clear(legendBody);
    if (!entries.length) legendBody.append(h('li', { class: 'overlay__muted' }, 'Nothing to show in this view.'));
    for (const l of entries) {
      legendBody.append(h('li', { class: 'overlay__legend-item', 'data-legend-kind': l.kind },
        l.kind === 'edge' ? lineSwatch(l.line, l.color, { arrow: true, width: 24 }) : l.kind === 'mark' ? h('span', { class: `scene-label__badge scene-label__mark scene-label__mark--${l.mark}` }, l.mark.replace(/-/g, ' ')) : shapeGlyph(l.shape, l.color, 12),
        h('span', { class: 'overlay__legend-label', title: l.label }, l.label)));
    }
    sync();
  };

  const STATUS_TONE = { proved: 'ok', verified: 'ok', supported: 'ok-external', violated: 'bad', inconclusive: 'warn', 'not-evaluated': 'none' };
  function renderLevel() {
    const claims = /** @type {any[]} */ (session.scene?.projection === 'structural' ? session.scene.levelClaims ?? [] : []);
    levelBar.hidden = !claims.length;
    clear(levelClaims);
    for (const c of claims) {
      const text = c.expressible ? `${c.claimId}: ${String(c.status).replace(/-/g, ' ')} at this cut` : `${c.claimId}: not expressible at this level`;
      levelClaims.append(h('li', { class: 'overlay__level-claim', 'data-testid': 'level-claim', 'data-claim': c.claimId, 'data-status': c.status, 'data-expressible': String(c.expressible), title: c.explanation },
        h('span', { class: 'chip', 'data-tone': c.expressible ? /** @type {any} */ (STATUS_TONE)[c.status] ?? 'none' : 'warn' }, h('span', { class: 'chip__dot', 'aria-hidden': 'true' }), text)));
    }
  }

  const fmt = (/** @type {any} */ n, /** @type {number} */ d = 0) => (typeof n === 'number' && Number.isFinite(n) ? n.toFixed(d) : '-');
  const renderStats = () => {
    if (!stats.open) return;
    let s = null;
    try { s = getStats?.() ?? null; } catch { s = null; }
    clear(statsBody);
    if (!s) { statsBody.append(h('dt', null, 'stats'), h('dd', null, 'n/a')); return; }
    const pairs = [['fps', fmt(s.fps)], ['frame ms', fmt(s.frameMs, 1)], ['draw calls', fmt(s.drawCalls)], ['triangles', fmt(s.triangles)], ['nodes', fmt(s.nodes)], ['edges', fmt(s.edges)], ['labels', fmt(s.labels)]];
    for (const [k, v] of pairs) statsBody.append(h('dt', null, k), h('dd', null, v));
  };

  renderScene();
  renderStats();
  const timer = setInterval(renderStats, 1000);
  const offs = [session.on('scene', renderScene), session.on('view', renderScene), session.on('project', renderScene)];
  return { cards, dispose: () => { clearInterval(timer); for (const off of offs) off(); } };
}
