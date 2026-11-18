// The app bar and the floating scene controls. Talks only to the session (and to the
// shell for showing destinations and overlay cards); re-renders the affected parts per event.
//
// One set of controls serves every size; toolbar.css places them:
//   phone    mark · project · view · search button · status pill · overflow (⋮)
//            undo/redo float at the bottom left above the sheet's peek height; the
//            overflow menu holds the editing tools, layout, camera, fit, legend,
//            render statistics, export and import
//   tablet   the same, with search inline and undo/redo in the bar
//   desktop  every tool inline (the overflow button disappears)
// Fit and the camera pair float at the right edge of the scene at every size.

import { h, clear, on, icon, revealInScroller } from './dom.js';
import { entityLabel } from '../core/query.js';
import { openCreateDialog, openDeleteDialog } from './dialogs.js';
import { exportProject, importProject } from '../persist/client.js';
import { analyzeSpec } from '../core/analyze.js';
import { sha256Hex } from '../core/sha256.js';
import { createMenu, placeBelow } from './menu.js';

/**
 * @typedef {Object} ShellApi
 * @property {(dest: string, opts?: any) => void} show
 * @property {() => 'phone'|'tablet'|'desktop'} mode
 * @property {HTMLElement} sceneControls
 * @property {{isOpen(name: 'legend'|'stats'): boolean, toggle(name: 'legend'|'stats'): void, onChange(fn: () => void): void}} overlayCards
 * @property {() => void} [focusSearch]
 * @property {() => void} [revealInspector]
 */

const MAX_RESULTS = 20;

/**
 * @param {HTMLElement} el
 * @param {any} session
 * @param {ShellApi} shellApi
 * @returns {() => void} dispose
 */
export function mountToolbar(el, session, shellApi) {
  /** @type {(() => void)[]} */
  const disposers = [];
  /** @type {Record<string, (() => void)[]>} */
  const updaters = {};
  /** @param {string[]} events @param {() => void} fn */
  const track = (events, fn) => {
    for (const ev of events) (updaters[ev] ??= []).push(fn);
    fn();
  };

  /**
   * A tool: an icon and a text label. The label is always the accessible name; toolbar.css
   * shows it beside the icon in the overflow menu and wherever there is room.
   * @param {{testid?: string, label: string, title?: string, icon: string, pressed?: boolean, cls?: string, keepOpen?: boolean, onclick?: (e: Event) => void}} o
   */
  const tool = (o) => h('button', {
    type: 'button', class: ['appbar__tool', o.cls],
    'data-testid': o.testid, title: o.title ?? o.label, 'aria-label': o.label,
    'aria-pressed': o.pressed, 'data-keep-open': o.keepOpen ? '' : null, onclick: o.onclick,
  }, icon(o.icon, 18), h('span', { class: 'appbar__tool-text', 'aria-hidden': 'true' }, o.label));

  /** @param {HTMLElement} b @param {boolean} disabled @param {string} title @param {string} [whyDisabled] */
  const setEnabled = (b, disabled, title, whyDisabled) => {
    /** @type {HTMLButtonElement} */ (b).disabled = disabled;
    b.title = disabled && whyDisabled ? whyDisabled : title;
  };
  const group = (/** @type {string} */ label, /** @type {any[]} */ ...kids) => h('div', { class: 'appbar__group', role: 'group', 'aria-label': label }, ...kids);
  /** Rows that exist only in the overflow menu (their controls also live elsewhere on screen). */
  const menuOnly = (/** @type {string} */ label, /** @type {any[]} */ ...kids) => h('div', { class: 'appbar__group appbar__menu-only', role: 'group', 'aria-label': label }, ...kids);

  // ---- 1. mark, project, view ------------------------------------------------
  const brand = h('span', { class: 'appbar__brand', title: 'Exegra' }, h('span', { class: 'appbar__mark', 'aria-hidden': 'true' }), h('span', { class: 'appbar__name' }, 'Exegra'));

  const projectSelect = h('select', {
    class: 'appbar__picker appbar__picker--project', 'data-testid': 'project-select', 'aria-label': 'Project', title: 'Switch project',
    onchange: () => { void session.open(projectSelect.value); },
  });
  const syncProject = () => {
    clear(projectSelect);
    for (const p of session.projects) projectSelect.append(h('option', { value: p.name, title: p.title }, p.title && p.title !== p.name ? `${p.name} - ${p.title}` : p.name));
    if (session.projectName && !session.projects.some((/** @type {any} */ p) => p.name === session.projectName)) projectSelect.append(h('option', { value: session.projectName }, session.projectName));
    projectSelect.value = session.projectName ?? '';
  };
  track(['project'], syncProject);

  const viewSelect = h('select', {
    class: 'appbar__picker appbar__picker--view', 'data-testid': 'view-select', 'aria-label': 'View', title: 'Switch view',
    onchange: () => session.setView(viewSelect.value),
  });
  let viewSig = '';
  const syncView = () => {
    const views = session.views ?? [];
    const sig = JSON.stringify(views.map((/** @type {any} */ v) => [v.id, v.name, v.projection]));
    if (sig !== viewSig) {
      viewSig = sig;
      clear(viewSelect);
      /** @type {Map<string, HTMLElement>} */
      const groups = new Map();
      for (const v of views) {
        let g = groups.get(v.projection);
        if (!g) { g = h('optgroup', { label: `${v.projection} projection` }); groups.set(v.projection, g); viewSelect.append(g); }
        g.append(h('option', { value: v.id, title: v.description ?? '' }, v.name));
      }
    }
    viewSelect.value = session.viewId ?? '';
  };
  track(['project', 'model', 'view'], syncView);

  // Below desktop width the two selects give way to one title button (project small, view
  // large) that opens a picker sheet listing the views and the projects.
  const titleProject = h('span', { class: 'appbar__title-project' });
  const titleView = h('span', { class: 'appbar__title-view' });
  const titleBtn = h('button', {
    type: 'button', class: 'appbar__title', 'data-testid': 'title-picker', title: 'Switch project or view',
  }, titleProject, h('span', { class: 'appbar__title-row' }, titleView, icon('chevron-down', 14)));
  const pickerSheet = h('div', { class: 'menu-sheet appbar__picker-sheet', id: 'appbar-picker', role: 'group', 'aria-label': 'Project and view' });
  /** @param {string} testid @param {string} text @param {string} sub @param {boolean} current @param {() => void} fn */
  const pickItem = (testid, text, sub, current, fn) => h('button', {
    type: 'button', class: 'menu-sheet__item', 'data-testid': testid, 'aria-current': String(current), onclick: fn,
  }, icon(current ? 'check' : 'dot', 16), h('span', { class: 'menu-sheet__text' }, h('span', null, text), sub ? h('span', { class: 'menu-sheet__hint' }, sub) : null));
  const syncTitle = () => {
    const view = (session.views ?? []).find((/** @type {any} */ v) => v.id === session.viewId);
    const proj = session.projects.find((/** @type {any} */ p) => p.name === session.projectName);
    titleProject.textContent = proj?.title && proj.title !== proj.name ? proj.title : (session.projectName ?? '');
    titleView.textContent = view?.name ?? 'No view';
    titleBtn.setAttribute('aria-label', `Project ${session.projectName ?? 'none'}, view ${view?.name ?? 'none'}. Switch project or view.`);
    clear(pickerSheet);
    pickerSheet.append(h('div', { class: 'menu-sheet__title' }, 'View'));
    for (const v of session.views ?? []) {
      pickerSheet.append(pickItem(`pick-view-${v.id}`, v.name, `${v.projection} projection`, v.id === session.viewId, () => session.setView(v.id)));
    }
    pickerSheet.append(h('div', { class: 'menu-sheet__sep', 'aria-hidden': 'true' }), h('div', { class: 'menu-sheet__title' }, 'Project'));
    const names = session.projects.map((/** @type {any} */ p) => p.name);
    if (session.projectName && !names.includes(session.projectName)) names.push(session.projectName);
    for (const name of names) {
      const p = session.projects.find((/** @type {any} */ x) => x.name === name);
      pickerSheet.append(pickItem(`pick-project-${name}`, name, p?.title && p.title !== name ? p.title : '', name === session.projectName, () => { void session.open(name); }));
    }
  };
  track(['project', 'model', 'view'], syncTitle);
  createMenu(titleBtn, pickerSheet, { isMenu: () => shellApi.mode() !== 'desktop' });

  // ---- 2. search: a button and a full-screen sheet on a phone, inline from tablet width up ----
  const resultsId = 'appbar-search-results';
  const searchInput = h('input', {
    type: 'search', class: 'search__input', placeholder: 'Search entities', 'data-testid': 'search-input',
    'aria-label': 'Search entities by id, name or statement', role: 'combobox', autocomplete: 'off', spellcheck: 'false',
    enterkeyhint: 'search', 'aria-expanded': 'false', 'aria-controls': resultsId, 'aria-autocomplete': 'list',
  });
  const resultsList = h('ul', { class: 'search__results', id: resultsId, role: 'listbox', 'aria-label': 'Search results', hidden: true });
  const searchOpen = h('button', {
    type: 'button', class: 'appbar__icon search__open', 'data-testid': 'search-open', 'aria-label': 'Search', title: 'Search entities  ( / )',
    onclick: () => openSearch(),
  }, icon('search', 20));
  const searchBack = h('button', {
    type: 'button', class: 'appbar__icon search__back', 'aria-label': 'Close search', title: 'Close search',
    onclick: () => closeSearch(true),
  }, icon('arrow-left', 20));
  const search = h('div', { class: 'search', role: 'search' },
    h('div', { class: 'search__bar' }, searchBack, searchInput), resultsList);
  const isPhone = () => shellApi.mode() === 'phone';

  /** @type {any[]} */
  let results = [];
  let active = -1;
  const rank = (/** @type {any} */ e, /** @type {string} */ q) => {
    const id = e.id.toLowerCase();
    const name = typeof e.data?.name === 'string' ? e.data.name.toLowerCase() : '';
    const st = typeof e.data?.statement === 'string' ? e.data.statement.toLowerCase() : '';
    const ref = typeof e.data?.ref === 'string' ? e.data.ref.toLowerCase() : '';
    if (id === q || ref === q) return 0;
    if (id.startsWith(q) || ref.startsWith(q)) return 1;
    if (name.startsWith(q)) return 2;
    if (name.includes(q)) return 3;
    if (id.includes(q)) return 4;
    if (st.includes(q)) return 5;
    return -1;
  };
  const runSearch = () => {
    const q = searchInput.value.trim().toLowerCase();
    results = [];
    if (q && session.model) {
      const scored = [];
      for (const e of session.model.entities.values()) {
        const r = rank(e, q);
        if (r >= 0) scored.push({ r, e });
      }
      scored.sort((a, b) => a.r - b.r);
      results = scored.slice(0, MAX_RESULTS).map((s) => s.e);
    }
    active = results.length ? 0 : -1;
    renderResults(q);
  };
  const setActive = (/** @type {number} */ i) => {
    active = i;
    resultsList.querySelectorAll('.search__option').forEach((o, idx) => {
      o.setAttribute('aria-selected', String(idx === active));
      if (idx === active) { searchInput.setAttribute('aria-activedescendant', o.id); revealInScroller(o); }
    });
  };
  const closeResults = () => { resultsList.hidden = true; searchInput.setAttribute('aria-expanded', 'false'); searchInput.removeAttribute('aria-activedescendant'); };
  const renderResults = (/** @type {string} */ q) => {
    clear(resultsList);
    if (!q) { closeResults(); return; }
    if (!results.length) resultsList.append(h('li', { class: 'search__empty', role: 'presentation' }, 'No matching entity'));
    results.forEach((e, i) => {
      resultsList.append(h('li', {
        class: 'search__option', id: `search-opt-${i}`, role: 'option', 'aria-selected': String(i === active), 'data-entity-id': e.id,
        onmousedown: (/** @type {Event} */ ev) => ev.preventDefault(), // keep focus in the input
        onclick: () => pick(e.id),
        onmousemove: () => { if (active !== i) setActive(i); },
      },
      h('span', { class: 'search__kind' }, e.kind),
      h('span', { class: 'search__label', title: entityLabel(e) }, entityLabel(e)),
      h('span', { class: 'search__id' }, e.id)));
    });
    resultsList.hidden = false;
    searchInput.setAttribute('aria-expanded', 'true');
    if (active >= 0) searchInput.setAttribute('aria-activedescendant', `search-opt-${active}`);
  };
  const pick = (/** @type {string} */ id) => {
    closeResults();
    closeSearch(false);
    session.select(id, { source: 'search' });
    session.requestFit([id]);
    shellApi.revealInspector?.();
  };
  const openSearch = () => {
    search.setAttribute('data-open', '');
    searchOpen.setAttribute('aria-expanded', 'true');
    searchInput.focus({ preventScroll: true });
    searchInput.select();
    if (searchInput.value.trim()) runSearch();
  };
  /** @param {boolean} restore */
  const closeSearch = (restore) => {
    if (!search.hasAttribute('data-open')) return;
    search.removeAttribute('data-open');
    searchOpen.setAttribute('aria-expanded', 'false');
    closeResults();
    if (restore && isPhone()) searchOpen.focus({ preventScroll: true });
  };
  on(searchInput, 'input', runSearch);
  on(searchInput, 'focus', () => { if (searchInput.value.trim()) runSearch(); });
  // The inline search closes its list when focus leaves; the phone's full-screen search stays until closed.
  on(searchInput, 'blur', () => { if (!isPhone()) { closeResults(); search.removeAttribute('data-open'); } });
  on(searchInput, 'keydown', (/** @type {KeyboardEvent} */ e) => {
    if (e.key === 'ArrowDown' || e.key === 'ArrowUp') {
      if (resultsList.hidden) runSearch();
      if (!results.length) return;
      e.preventDefault();
      setActive((active + (e.key === 'ArrowDown' ? 1 : -1) + results.length) % results.length);
    } else if (e.key === 'Enter') {
      if (!resultsList.hidden && results[active]) { e.preventDefault(); pick(results[active].id); }
    } else if (e.key === 'Escape') {
      e.stopPropagation();
      if (!resultsList.hidden && !isPhone()) { closeResults(); e.preventDefault(); }
      else if (searchInput.value) { searchInput.value = ''; runSearch(); }
      else if (isPhone()) closeSearch(true);
      else searchInput.blur();
    }
  });
  shellApi.focusSearch = () => (isPhone() ? openSearch() : (searchInput.focus({ preventScroll: true }), searchInput.select()));

  // ---- 3. status pill: validation counts and save state; opens Diagnostics ---------------
  const overflowBtn = h('button', {
    type: 'button', class: 'appbar__icon appbar__overflow', 'data-testid': 'appbar-overflow', 'aria-label': 'More actions', title: 'More actions',
  }, icon('more', 20));
  const statusBtn = h('button', {
    type: 'button', class: 'appbar__status', 'data-testid': 'validation-state',
    onclick: () => shellApi.show('diagnostics'),
  });
  const SAVE_TEXT = {
    saved: ['Saved', 'All changes are written to disk.'],
    saving: ['Saving…', 'Writing changes to disk.'],
    conflict: ['Conflict', 'The file on disk changed underneath this session. Click to resolve.'],
    error: ['Save error', 'Writing to disk failed. See Changes for details.'],
    readonly: ['Read-only', 'This build has no persistence service. Edits change the in-memory model only and are lost on reload. Run the development server to save to disk.'],
  };
  const saveState = () => /** @type {keyof typeof SAVE_TEXT} */ (session.saveState in SAVE_TEXT ? session.saveState : 'saved');
  const syncStatus = () => {
    const ds = session.diagnostics ?? [];
    const e = ds.filter((/** @type {any} */ d) => d.severity === 'error').length;
    const w = ds.filter((/** @type {any} */ d) => d.severity === 'warning').length;
    const g = ds.filter((/** @type {any} */ d) => d.severity === 'info').length;
    const st = saveState();
    const worst = e ? 'error' : w ? 'warning' : g ? 'gaps' : 'clean';
    clear(statusBtn);
    statusBtn.append(
      // compact (below desktop width): one dot coloured by the worst status, and the total
      h('span', { class: 'appbar__statusdot', 'data-state': worst, 'aria-hidden': 'true' }),
      h('b', { class: 'appbar__total', 'aria-hidden': 'true' }, String(e + w + g)),
      // desktop: the three counts
      h('span', { class: ['appbar__count', e ? 'appbar__count--bad' : 'appbar__count--idle'], 'data-kind': 'error' }, icon('error', 13), h('b', null, String(e)), h('span', { class: 'appbar__count-word' }, ' err')),
      h('span', { class: ['appbar__count', w ? 'appbar__count--warn' : 'appbar__count--idle'], 'data-kind': 'warning' }, icon('warning', 13), h('b', null, String(w)), h('span', { class: 'appbar__count-word' }, ' warn')),
      h('span', { class: ['appbar__count', g ? 'appbar__count--gap' : 'appbar__count--idle'], 'data-kind': 'info' }, icon('info', 13), h('b', null, String(g)), h('span', { class: 'appbar__count-word' }, ' gaps')),
      h('span', { class: 'appbar__savedot', 'data-state': st, 'aria-hidden': 'true' }));
    const saveWords = SAVE_TEXT[st][0];
    statusBtn.setAttribute('aria-label', `${e} errors, ${w} warnings, ${g} gaps; ${saveWords}. Open diagnostics.`);
    statusBtn.title = `${e} error${e === 1 ? '' : 's'}, ${w} warning${w === 1 ? '' : 's'}, ${g} gap${g === 1 ? '' : 's'}. ${saveWords}. Open the diagnostics list.${e === 0 ? ' Zero errors means well-formed, not correct.' : ''}`;
    statusBtn.dataset.state = worst;
  };
  track(['project', 'model', 'save'], syncStatus);

  // Save state. On a desktop a small button appears beside the status when the state needs
  // attention (a conflict opens its menu). Below desktop width the state is a badge on the
  // overflow button and a line at the top of the overflow menu.
  const saveBtn = h('button', { type: 'button', class: 'appbar__save', 'data-testid': 'save-state' });
  const saveLineText = h('span', { class: 'menu-sheet__text' });
  const saveResolve = h('button', { type: 'button', class: 'appbar__tool appbar__resolve', 'data-testid': 'save-resolve', onclick: () => saveMenuCtl.open() },
    icon('warning', 18), h('span', { class: 'appbar__tool-text' }, 'Resolve conflict'));
  saveResolve.setAttribute('aria-label', 'Resolve the save conflict');
  const saveLine = h('div', { class: 'appbar__group appbar__menu-only appbar__saveline', role: 'group', 'aria-label': 'Save state' },
    h('div', { class: 'appbar__saveinfo' }, h('span', { class: 'appbar__savedot', 'aria-hidden': 'true' }), saveLineText), saveResolve);
  const reloadItem = h('button', { type: 'button', role: 'menuitem', class: 'menu-sheet__item', onclick: () => session.resolveConflict('reload') },
    h('span', { class: 'menu-sheet__text' }, h('b', null, 'Reload from disk'), h('span', { class: 'menu-sheet__hint' }, 'Discard the edits made here and adopt the file on disk.')));
  const overwriteItem = h('button', { type: 'button', role: 'menuitem', class: 'menu-sheet__item', onclick: () => session.resolveConflict('overwrite') },
    h('span', { class: 'menu-sheet__text' }, h('b', null, 'Overwrite disk'), h('span', { class: 'menu-sheet__hint' }, 'Keep the edits made here and replace the file on disk.')));
  const saveMenu = h('div', { class: 'menu-sheet', role: 'menu', 'aria-label': 'Resolve save conflict' }, reloadItem, overwriteItem);
  const saveMenuCtl = createMenu(saveBtn, saveMenu, {
    // anchored to the save button on a desktop, to the overflow button where that is hidden
    place: (panel) => placeBelow(panel, saveBtn.offsetParent ? saveBtn : overflowBtn),
    isMenu: () => session.saveState === 'conflict',
  });
  track(['save', 'project'], () => {
    const st = saveState();
    saveBtn.dataset.state = st;
    clear(saveBtn);
    saveBtn.append(icon(st === 'conflict' || st === 'readonly' ? 'warning' : st === 'error' ? 'error' : 'dot', 16), h('span', { class: 'appbar__save-text' }, SAVE_TEXT[st][0]));
    saveBtn.title = SAVE_TEXT[st][1];
    saveBtn.setAttribute('aria-label', SAVE_TEXT[st][0]);
    saveBtn.hidden = st === 'saved' || st === 'saving';
    overflowBtn.dataset.save = st;
    overflowBtn.setAttribute('aria-label', st === 'saved' || st === 'saving' ? 'More actions' : `More actions (${SAVE_TEXT[st][0]})`);
    saveLine.dataset.state = st;
    clear(saveLineText).append(h('b', null, st === 'readonly' ? 'Not saved: read-only build' : SAVE_TEXT[st][0]), h('span', { class: 'menu-sheet__hint' }, SAVE_TEXT[st][1]));
    saveResolve.hidden = st !== 'conflict';
    saveBtn.setAttribute('aria-disabled', String(st !== 'conflict'));
    if (st !== 'conflict') saveMenuCtl.close();
  });

  // ---- 4. history: in the bar from tablet width up, floating at the bottom left on a phone ----
  const undoBtn = tool({ testid: 'undo', icon: 'undo', label: 'Undo', onclick: () => session.undo() });
  const redoBtn = tool({ testid: 'redo', icon: 'redo', label: 'Redo', onclick: () => session.redo() });
  const history = h('div', { class: 'appbar__history', role: 'group', 'aria-label': 'History' }, undoBtn, redoBtn);

  // ---- 5. tools: inline on a desktop, the overflow menu below ---------------------------------
  const modeSelect = tool({ testid: 'mode-select', icon: 'cursor', label: 'Select', title: 'Select and move (drag nodes to pin their position)', onclick: () => session.setMode('select') });
  const modeConnect = tool({ testid: 'mode-connect', icon: 'connect', label: 'Connect', title: 'Connect mode: tap a source node, then a target node to create a relationship', onclick: () => session.setMode('connect') });
  const newBtn = tool({ testid: 'new-component', icon: 'plus', label: 'New', title: 'New component', onclick: () => {
    const sel = session.selection ? session.model?.entities.get(session.selection) : null;
    const parent = sel && sel.kind === 'component' && sel.data.kind === 'subsystem' ? sel.id : null;
    openCreateDialog(session, { parent });
  } });
  const delBtn = tool({ testid: 'delete-entity', icon: 'trash', label: 'Delete', title: 'Delete the selected entity', onclick: () => { if (session.selection) openDeleteDialog(session, session.selection); } });

  // Layout method: a viewer preference per view. 'Auto' compares the methods and
  // picks the best-scoring one for the current scene and viewport shape.
  const layoutSelect = h('select', {
    class: 'appbar__select appbar__select--layout', 'data-testid': 'layout-select', 'aria-label': 'Layout method',
    onchange: () => session.setLayoutMethod(layoutSelect.value),
  });
  track(['project', 'view', 'ui', 'scene'], () => {
    const info = session.layout;
    if (!info) return;
    const used = info.methods.find((/** @type {any} */ m) => m.id === info.used);
    const want = ['auto', ...info.methods.map((/** @type {any} */ m) => m.id)].join('|') + '|' + info.used;
    if (layoutSelect.dataset.sig !== want) {
      layoutSelect.dataset.sig = want;
      clear(layoutSelect);
      layoutSelect.append(h('option', { value: 'auto' }, `Layout: auto (${used?.label ?? info.used})`));
      for (const m of info.methods) layoutSelect.append(h('option', { value: m.id, title: m.description }, `Layout: ${m.label}`));
    }
    layoutSelect.value = info.requested;
    const scores = Object.entries(info.scores ?? {}).map(([id, sc]) => `${id} ${Number(/** @type {any} */ (sc).total).toFixed(2)}`).join(', ');
    layoutSelect.title = info.requested === 'auto'
      ? `Automatic: chose "${used?.label ?? info.used}" for this scene and viewport. Scores (lower is better): ${scores}. Position is presentation only.`
      : `${used?.description ?? ''} Position is presentation only.`;
  });
  const pinnedIds = () => {
    const positions = session.project?.layout?.views?.[session.viewId]?.positions ?? {};
    return Object.keys(positions).filter((id) => session.model?.entities.has(id));
  };
  const resetBtn = tool({ testid: 'reset-layout', icon: 'restart', label: 'Reset layout', title: 'Return every pinned node of this view to automatic layout', onclick: () => {
    const ids = pinnedIds();
    if (!ids.length) return;
    session.apply(ids.map((id) => ({ type: 'MovePresentationNode', view: session.viewId, id, reset: true })), { label: 'Reset layout' });
  } });

  // Overlay cards: the legend and the render statistics.
  const legendBtn = tool({ testid: 'toggle-legend', icon: 'legend', label: 'Legend', keepOpen: false, onclick: () => shellApi.overlayCards.toggle('legend') });
  const statsBtn = tool({ testid: 'toggle-render-stats', icon: 'stats', label: 'Render statistics', onclick: () => shellApi.overlayCards.toggle('stats') });
  const syncCards = () => {
    legendBtn.setAttribute('aria-pressed', String(shellApi.overlayCards.isOpen('legend')));
    statsBtn.setAttribute('aria-pressed', String(shellApi.overlayCards.isOpen('stats')));
  };
  shellApi.overlayCards.onChange(syncCards);
  syncCards();

  // Menu-only copies of controls that sit elsewhere on screen (history, scene controls).
  const fitNow = () => session.requestFit(session.selection ? [session.selection] : undefined);
  const mUndo = tool({ icon: 'undo', label: 'Undo', onclick: () => session.undo() });
  const mRedo = tool({ icon: 'redo', label: 'Redo', onclick: () => session.redo() });
  const mPersp = tool({ icon: 'perspective', label: 'Perspective camera', onclick: () => session.setCameraMode('perspective') });
  const mTop = tool({ icon: 'top', label: 'Top camera', onclick: () => session.setCameraMode('top') });
  const mFit = tool({ icon: 'fit', label: 'Fit', onclick: fitNow });

  // Exchange.
  // Traffic (src/app/traffic-recorder.js, through session.traffic): export and import as the self-model names
  // them; a bundle is recorded as the sha-256 of its specification.
  const rec = (/** @type {string} */ id, /** @type {Record<string, any>} */ payload = {}) => session.traffic?.record(id, payload);
  const exportBtn = tool({ testid: 'export', icon: 'download', label: 'Export', title: 'Download this project as a .exegra.json bundle', onclick: async () => {
    rec('export-clicked');
    const requestId = session.persistent ? session.traffic.nextRequestId() : 0;
    try {
      const name = session.projectName;
      if (session.persistent) rec('export-intent', { name, requestId });
      // Without the persistence service the bundle is built from the in-memory project (same format).
      const bundle = session.persistent
        ? await exportProject(name, { requestId })
        : { format: 'exegra-project', version: 1, name, files: { 'spec.jsonc': session.project.specText, 'layout.jsonc': session.project.layoutText } };
      const specHash = sha256Hex(String(/** @type {any} */ (bundle).files?.['spec.jsonc'] ?? ''));
      if (session.persistent) rec('bundle-received', { files: specHash, requestId });
      rec('bundle-downloaded', { specHash });
      const url = URL.createObjectURL(new Blob([JSON.stringify(bundle, null, 2) + '\n'], { type: 'application/json' }));
      const a = h('a', { href: url, download: `${name}.exegra.json`, hidden: true });
      document.body.append(a); a.click(); a.remove();
      setTimeout(() => URL.revokeObjectURL(url), 2000);
    } catch (err) {
      if (session.persistent) rec('export-refused-received', { requestId });
      session.note('error', 'Export failed', String(/** @type {any} */ (err)?.message ?? err));
    }
  } });
  const fileInput = h('input', { type: 'file', accept: '.json,application/json', hidden: true, 'data-testid': 'import-file', 'aria-label': 'Import project bundle' });
  const importBtn = tool({ testid: 'import', icon: 'upload', label: 'Import', title: 'Import a .exegra.json project bundle', onclick: () => fileInput.click() });
  if (!session.persistent) { importBtn.disabled = true; importBtn.title = 'Importing writes project files, which needs the development server. This build is read-only.'; }
  on(fileInput, 'change', async () => {
    const file = fileInput.files?.[0];
    fileInput.value = '';
    if (!file) return;
    try {
      const bundle = JSON.parse(await file.text());
      if (bundle?.format !== 'exegra-project' || typeof bundle.files !== 'object' || !bundle.files) throw new Error('Not an exegra-project bundle.');
      // An import creates project files outside the transaction pipeline, so refuse text that cannot become a model.
      const specText = String(bundle.files['spec.jsonc'] ?? '');
      const specHash = sha256Hex(specText);
      const check = analyzeSpec(specText);
      if (!check.model) rec('import-file-chosen', { name: String(bundle.name ?? file.name), specHash, syntaxOk: false });
      if (!check.model) throw new Error(`The bundle's spec.jsonc has syntax errors (${check.diagnostics[0]?.message ?? 'unreadable'}).`);
      if (check.errorCount) session.note('info', `The imported specification has ${check.errorCount} validation error(s); it will load with diagnostics and reject edits until they are fixed.`);
      const name = await askProjectName(String(bundle.name ?? file.name.replace(/\.exegra\.json$|\.json$/i, '')));
      if (!name) return;
      rec('import-file-chosen', { name, specHash, syntaxOk: true });
      const requestId = session.traffic.nextRequestId();
      rec('import-intent', { name, bundle: specHash, requestId });
      const res = await importProject(name, bundle, { requestId, bundleHash: specHash });
      rec(res?.ok ? 'import-done' : 'import-refused-received', { requestId });
      if (!res?.ok) { session.note('error', 'Import failed', res?.error ?? 'The server refused the bundle.'); return; }
      await session.refreshProjects();
      await session.open(name);
    } catch (err) {
      session.note('error', 'Import failed', String(/** @type {any} */ (err)?.message ?? err));
    }
  });
  /** @param {string} def @returns {Promise<string|null>} */
  const askProjectName = (def) => new Promise((resolve) => {
    const input = h('input', { type: 'text', class: 'toolbar-dialog__input', name: 'name', required: true, value: def, 'aria-label': 'Project name', autocomplete: 'off', spellcheck: 'false' });
    const hint = h('p', { class: 'toolbar-dialog__hint', 'aria-live': 'polite' });
    const syncHint = () => {
      const exists = session.projects.some((/** @type {any} */ p) => p.name === input.value.trim());
      input.setCustomValidity(!input.value.trim() || /[\\/:*?"<>|]/.test(input.value) ? 'Use a plain name without path characters.' : '');
      hint.textContent = exists ? 'A project with this name exists and will be replaced.' : '';
    };
    on(input, 'input', syncHint);
    syncHint();
    const dlg = /** @type {HTMLDialogElement} */ (h('dialog', { class: 'toolbar-dialog', 'aria-label': 'Import project' },
      h('form', { method: 'dialog', class: 'toolbar-dialog__form' },
        h('h2', { class: 'toolbar-dialog__title' }, 'Import project'),
        h('label', { class: 'toolbar-dialog__label' }, 'Name', input),
        hint,
        h('div', { class: 'toolbar-dialog__actions' },
          h('button', { type: 'submit', value: 'cancel', formnovalidate: true }, 'Cancel'),
          h('button', { type: 'submit', value: 'ok', class: 'toolbar-dialog__primary' }, 'Import')))));
    dlg.addEventListener('close', () => {
      const ok = dlg.returnValue === 'ok';
      const v = input.value.trim();
      dlg.remove();
      resolve(ok && v ? v : null);
    });
    (document.getElementById('dialogs') ?? document.body).append(dlg);
    dlg.showModal();
    input.select();
  });

  const revision = h('output', {
    class: 'appbar__readout', 'data-testid': 'revision',
    title: 'rev counts every commit (edits, undo, redo, reloads). The hash identifies the semantic content of the specification: it does not change when only layout changes.',
  });
  track(['project', 'model'], () => {
    const p = session.project;
    revision.textContent = p ? `rev ${p.revision} · ${String(p.semanticHash).slice(0, 8)}` : 'rev -';
  });

  const tools = h('div', { class: 'appbar__tools', id: 'appbar-tools', role: 'group', 'aria-label': 'Tools' },
    saveLine,
    menuOnly('History', mUndo, mRedo),
    group('Edit', h('div', { class: 'appbar__segment', role: 'group', 'aria-label': 'Interaction mode' }, modeSelect, modeConnect), newBtn, delBtn),
    group('Layout', layoutSelect, resetBtn),
    menuOnly('Camera', mPersp, mTop, mFit),
    group('Overlay', legendBtn, statsBtn),
    group('Exchange', exportBtn, importBtn, fileInput),
    revision);
  createMenu(overflowBtn, tools, { isMenu: () => shellApi.mode() !== 'desktop' });

  // State of the tools, history and menu copies.
  track(['project', 'model', 'view', 'selection', 'ui'], () => {
    const mode = session.ui?.mode;
    modeSelect.setAttribute('aria-pressed', String(mode === 'select'));
    modeConnect.setAttribute('aria-pressed', String(mode === 'connect'));
    const sel = session.selection;
    const isSystem = sel && session.model?.system?.id === sel;
    setEnabled(delBtn, !sel || !!isSystem || !session.model, sel ? `Delete ${sel}` : 'Delete the selected entity', !sel ? 'Select an entity to delete it' : isSystem ? 'The system root cannot be deleted' : 'No valid model');
    setEnabled(newBtn, !session.model, 'New component', 'No valid model: fix the source errors first');
    const n = pinnedIds().length;
    setEnabled(resetBtn, n === 0, `Return ${n} pinned node${n === 1 ? '' : 's'} to automatic layout`, 'Nothing is pinned in this view');
    const cam = session.ui?.cameraMode;
    mPersp.setAttribute('aria-pressed', String(cam === 'perspective'));
    mTop.setAttribute('aria-pressed', String(cam === 'top'));
  });
  track(['project', 'model'], () => {
    const p = session.project;
    const u = p?.undoStack?.at(-1)?.entry?.label;
    const r = p?.redoStack?.at(-1)?.entry?.label;
    for (const b of [undoBtn, mUndo]) setEnabled(b, !p?.canUndo, u ? `Undo: ${u}  ( Ctrl+Z )` : 'Undo', 'Nothing to undo');
    for (const b of [redoBtn, mRedo]) setEnabled(b, !p?.canRedo, r ? `Redo: ${r}  ( Ctrl+Shift+Z )` : 'Redo', 'Nothing to redo');
  });

  // ---- 6. floating scene controls: fit and camera, and the connect-mode indicator --------------
  /** @param {{testid: string, icon: string, label: string, title?: string, onclick: () => void}} o */
  const fab = (o) => h('button', { type: 'button', class: 'fab', 'data-testid': o.testid, 'aria-label': o.label, title: o.title ?? o.label, onclick: o.onclick }, icon(o.icon, 20));
  const fitBtn = fab({ testid: 'fit', icon: 'fit', label: 'Fit', title: 'Fit the selection (or the whole system when nothing is selected)  ( F )', onclick: fitNow });
  const camPersp = fab({ testid: 'camera-perspective', icon: 'perspective', label: 'Perspective camera', onclick: () => session.setCameraMode('perspective') });
  const camTop = fab({ testid: 'camera-top', icon: 'top', label: 'Top camera', title: 'Top-down camera', onclick: () => session.setCameraMode('top') });
  const connectChip = h('button', {
    type: 'button', class: 'fab fab--connect', 'data-testid': 'connect-indicator', title: 'Connect mode: tap a source node, then a target. Tap here to stop.',
    onclick: () => session.setMode('select'),
  }, icon('connect', 18), h('span', { class: 'fab__text' }, 'Connecting'), icon('close', 14));
  connectChip.setAttribute('aria-label', 'Connect mode is on. Stop connecting.');
  const sc = shellApi.sceneControls;
  clear(sc);
  sc.append(connectChip, h('div', { class: 'fab-group', role: 'group', 'aria-label': 'Camera' }, camPersp, camTop), fitBtn);
  track(['project', 'selection', 'ui'], () => {
    const cam = session.ui?.cameraMode;
    camPersp.setAttribute('aria-pressed', String(cam === 'perspective'));
    camTop.setAttribute('aria-pressed', String(cam === 'top'));
    fitBtn.title = session.selection ? `Fit ${session.selection}  ( F )` : 'Fit the whole system  ( F )';
    connectChip.hidden = session.ui?.mode !== 'connect';
  });

  // ---- assemble ----------------------------------------------------------------------
  clear(el);
  el.append(
    brand,
    titleBtn,
    pickerSheet,
    h('div', { class: 'appbar__pickers' }, projectSelect, viewSelect),
    h('span', { class: 'appbar__spacer' }),
    searchOpen,
    search,
    statusBtn,
    saveBtn,
    // right after its button and early in the DOM: the conflict menu's items are the page's
    // first "Reload from disk" and "Overwrite disk" texts
    saveMenu,
    history,
    overflowBtn,
    tools);

  // ---- event wiring: each event re-runs only the parts that listen to it ----------------
  for (const ev of Object.keys(updaters)) {
    disposers.push(session.on(ev, () => { for (const fn of updaters[ev]) fn(); }));
  }
  return () => { for (const d of disposers) d(); };
}
