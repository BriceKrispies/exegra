// Application shell: the page frame. Creates the responsive layout (layout.js), mounts
// the modules this file owns (app bar, explorer, diagnostics, changes, overlay,
// simulation transport), keeps each destination's one-line summary current, and owns
// toasts and keyboard shortcuts. Hands back the elements the other panels mount into.

import { h, icon } from './dom.js';
import { detailText } from './detail.js';
import { entityLabel } from '../core/query.js';
import { CLAIM_STATUSES } from '../core/claim-methods.js';
import { mountToolbar } from './toolbar.js';
import { mountExplorer } from './explorer.js';
import { mountDiagnostics, mountChanges } from './activity.js';
import { mountOverlay } from './overlay.js';
import { mountSimTransport } from './sim-transport.js';
import { openDeleteDialog } from './dialogs.js';
import { createLayout } from './layout.js';

/** @param {EventTarget|null} t */
function isEditable(t) {
  const el = /** @type {HTMLElement|null} */ (t instanceof HTMLElement ? t : null);
  if (!el) return false;
  if (el.isContentEditable) return true;
  if (['INPUT', 'TEXTAREA', 'SELECT'].includes(el.tagName)) return true;
  return !!el.closest('[contenteditable=""], [contenteditable="true"], .cm-editor');
}

/** @param {number} n @param {string} one @param {string} [many] */
const plural = (n, one, many) => `${n} ${n === 1 ? one : many ?? `${one}s`}`;

/**
 * @param {any} session
 */
export function mountShell(session) {
  const $ = (/** @type {string} */ id) => /** @type {HTMLElement} */ (document.getElementById(id));
  const app = $('app');

  const layout = createLayout({ app, nav: $('nav'), explorer: $('panel-explorer'), context: $('panel-context') });

  // ---- toasts -------------------------------------------------------------------------------
  const toasts = $('toasts');
  /** @param {string} message @param {any} [rawDetail] */
  const toast = (message, rawDetail) => {
    const detail = detailText(rawDetail);
    const node = h('div', { class: 'toast', role: 'status' },
      h('div', { class: 'toast__text' }, h('b', { class: 'toast__title' }, message), detail ? h('span', { class: 'toast__detail' }, detail) : null),
      h('button', { type: 'button', class: 'toast__close', 'aria-label': 'Dismiss', title: 'Dismiss', onclick: () => node.remove() }, icon('close', 14)));
    toasts.append(node);
    while (toasts.children.length > 3) toasts.firstElementChild?.remove();
    setTimeout(() => node.remove(), 8000);
  };
  let lastLogSeq = (session.log ?? []).reduce((/** @type {number} */ m, /** @type {any} */ l) => Math.max(m, l.seq), -1);
  session.on('log', () => {
    for (const l of session.log ?? []) {
      if (l.seq <= lastLogSeq) continue;
      lastLogSeq = l.seq;
      if (l.kind === 'error') toast(l.message, l.detail);
    }
  });

  // ---- shared api (also handed to the app bar) -------------------------------------------------
  /** @type {() => any} */
  let statsProvider = () => null;
  const overlay = mountOverlay($('viewport-overlay'), session, () => statsProvider(), { mode: layout.mode });
  const api = {
    sceneHost: $('scene-host'),
    sceneControls: $('scene-controls'),
    inspector: $('tab-inspector'),
    source: $('tab-source'),
    simulation: $('tab-simulation'),
    verification: $('tab-verification'),
    realisation: $('tab-realisation'),
    mode: layout.mode,
    /** Bring a destination forward (a sheet on a phone, the side or context panel elsewhere). @param {string} dest @param {any} [opts] */
    show: (dest, opts) => layout.show(dest, opts),
    /** A selection made in the scene or by search shows the inspector (at peek on a phone). */
    revealInspector: () => layout.revealInspector(),
    dismissInspectorPeek: () => layout.dismissInspectorPeek(),
    overlayCards: overlay.cards,
    focusSearch: () => {},
    /** The coordinator supplies the renderer's getStats once the scene view exists. @param {() => any} fn */
    setStatsProvider: (fn) => { statsProvider = fn; },
  };

  mountToolbar($('appbar'), session, api);
  mountExplorer($('explorer'), session);
  mountDiagnostics($('tab-diagnostics'), session);
  mountChanges($('tab-changes'), session);
  mountSimTransport($('transport'), session, {
    show: (dest) => layout.show(dest),
    onVisible: (visible) => app.classList.toggle('app--transport', visible),
  });

  // ---- one-line summaries under each panel title (what a peeking sheet shows) -------------------
  const summarise = () => {
    const model = session.model;
    const ds = session.diagnostics ?? [];
    const count = (/** @type {string} */ s) => ds.filter((/** @type {any} */ d) => d.severity === s).length;
    // inspector: name · kind · status
    const id = session.selection;
    const e = model && id ? model.entities.get(id) : null;
    if (!model) layout.setSummary('inspector', 'No specification loaded');
    else if (!e) layout.setSummary('inspector', `${entityLabel(model.system)} · system · ${plural(count('error'), 'error')}`);
    else {
      const kind = model.meta.entities[e.kind]?.label ?? e.kind;
      let status = '';
      if (e.kind === 'claim') status = CLAIM_STATUSES[/** @type {keyof typeof CLAIM_STATUSES} */ (session.claimResult(e.id)?.status ?? 'not-evaluated')]?.label ?? '';
      else {
        const mine = ds.filter((/** @type {any} */ d) => d.entityId === e.id);
        status = mine.length ? plural(mine.length, 'diagnostic') : 'no diagnostics';
      }
      layout.setSummary('inspector', [entityLabel(e), kind, status].filter(Boolean).join(' · '));
    }
    layout.setSummary('explorer', model ? `${plural(model.byKind.component?.length ?? 0, 'component')} · ${plural(model.byKind.relationship?.length ?? 0, 'relationship')}` : '');
    const results = /** @type {any[]} */ (session.claimResults ?? []);
    const st = (/** @type {string} */ s) => results.filter((r) => r.status === s).length;
    layout.setSummary('verification', results.length ? `${plural(results.length, 'claim')} · ${st('verified')} verified · ${st('supported')} supported · ${st('violated')} violated` : 'No claims');
    layout.setSummary('diagnostics', `${plural(count('error'), 'error')} · ${plural(count('warning'), 'warning')} · ${plural(count('info'), 'gap')}`);
    const commits = session.project?.history?.length ?? 0;
    layout.setSummary('changes', `${plural(commits, 'commit')} this session`);
    layout.setSummary('source', session.project ? `rev ${session.project.revision} · ${session.specLocation ?? 'spec.jsonc'}` : '');
    const comps = model?.byKind.component ?? [];
    const declared = comps.filter((/** @type {any} */ c) => c.data.implementation).length;
    layout.setSummary('realisation', model ? `${declared} of ${plural(comps.length, 'component')} declare their realisation` : '');
    const s = session.sim ?? {};
    const sc = s.scenarioId ? model?.entities.get(s.scenarioId) : null;
    if (!sc) layout.setSummary('simulation', 'No scenario loaded');
    else if (!s.simulation) layout.setSummary('simulation', `${entityLabel(sc)} · running…`);
    else layout.setSummary('simulation', `${entityLabel(sc)} · step ${s.stepIndex + 1}/${s.simulation.steps.length}`);
  };
  for (const ev of ['project', 'model', 'selection', 'claims', 'sim', 'log']) session.on(ev, summarise);
  summarise();

  // ---- keyboard shortcuts ----------------------------------------------------------------------------
  window.addEventListener('keydown', (e) => {
    if (e.defaultPrevented || e.isComposing) return;
    if (isEditable(e.target) || document.querySelector('dialog[open]')) return;
    const mod = e.ctrlKey || e.metaKey;
    const key = e.key.length === 1 ? e.key.toLowerCase() : e.key;
    if (mod && !e.altKey) {
      if (key === 'z') { e.preventDefault(); if (e.shiftKey) session.redo(); else session.undo(); }
      else if (key === 'y') { e.preventDefault(); session.redo(); }
      return;
    }
    if (e.altKey || e.shiftKey && key !== '/') return;
    if (key === 'f') {
      e.preventDefault();
      session.requestFit(session.selection ? [session.selection] : undefined);
    } else if (key === 'Delete') {
      const sel = session.selection;
      if (sel && session.model && session.model.system?.id !== sel) { e.preventDefault(); openDeleteDialog(session, sel); }
    } else if (key === 'Escape') {
      if (session.ui?.mode === 'connect') session.setMode('select');
      else if (session.selection) session.select(null, { source: 'keyboard' });
    } else if (key === '/') {
      e.preventDefault();
      api.focusSearch();
    }
  });

  return api;
}
