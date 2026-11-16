// The source editor: a plain textarea over the project's spec.jsonc (or the file its project.jsonc names) with a
// line-number gutter. The committed text is the project's; whatever the user
// types is a *draft* that is never lost: it is only replaced when the user
// discards it or the model accepts it (ReplaceSource).

import { h, clear, on } from './dom.js';
import { analyzeSpec } from '../core/analyze.js';
import { parseSpec } from '../core/parse.js';

/** @typedef {import('../core/types.js').Diagnostic} Diagnostic */

const DEBOUNCE_MS = 250;

/** 0-based offset of a 1-based line/column. @param {string} text @param {number} line @param {number} column */
function offsetOf(text, line, column) {
  let off = 0;
  for (let l = 1; l < line; l++) {
    const nl = text.indexOf('\n', off);
    if (nl < 0) return text.length;
    off = nl + 1;
  }
  return Math.min(text.length, off + Math.max(0, column - 1));
}

/** Map a caret position across a text replacement using the common prefix/suffix. @param {string} a @param {string} b @param {number} pos */
function mapOffset(a, b, pos) {
  let p = 0;
  const max = Math.min(a.length, b.length);
  while (p < max && a.charCodeAt(p) === b.charCodeAt(p)) p++;
  let s = 0;
  while (s < max - p && a.charCodeAt(a.length - 1 - s) === b.charCodeAt(b.length - 1 - s)) s++;
  if (pos <= p) return pos;
  if (pos >= a.length - s) return Math.min(b.length, pos + (b.length - a.length));
  return Math.min(p, b.length);
}

/**
 * @param {HTMLElement} el
 * @param {any} session
 * @param {{show?: () => void}} [opts] `show()` brings the Source tab to the front
 * @returns {() => void} unmount
 */
export function mountSourceEditor(el, session, opts = {}) {
  /** @type {string|null} */
  let draft = null;
  let baseRev = 0;
  let ackRev = 0;
  let applying = false;
  /** @type {any} */
  let timer = 0;
  /** @type {Diagnostic[]} */
  let diags = [];
  let bareLineCount = -1;
  /** @type {Set<number>} */
  let errorLines = new Set();
  /** @type {Set<number>} */
  let warnLines = new Set();

  const file = h('span', { class: 'source__file mono' });
  const state = h('output', { class: 'source__state', 'data-testid': 'source-state' });
  const apply = h('button', { type: 'button', class: 'btn btn--primary', 'data-testid': 'source-apply', title: 'Apply the draft to the model (Ctrl+S or Ctrl+Enter)' }, 'Apply');
  const discard = h('button', { type: 'button', class: 'btn', 'data-testid': 'source-discard', title: 'Throw the draft away and show the current source' }, 'Discard draft');
  const banner = h('div', { class: 'source__banner', role: 'status', 'data-testid': 'source-banner' });
  banner.hidden = true;
  const notice = h('div', { class: 'source__notice', role: 'status', 'data-testid': 'source-notice' });
  notice.hidden = true;
  const rejection = h('div', { class: 'source__rejection', role: 'alert', 'data-testid': 'source-rejection' });
  rejection.hidden = true;
  const gutter = h('div', { class: 'source__gutter mono', 'aria-hidden': 'true', 'data-testid': 'source-gutter' });
  const ta = h('textarea', {
    class: 'source__text mono', 'data-testid': 'source-text', spellcheck: 'false', wrap: 'off',
    autocapitalize: 'off', autocomplete: 'off', autocorrect: 'off', 'aria-label': 'Specification source', 'aria-describedby': 'source-state-out',
  });
  state.id = 'source-state-out';
  const diagHead = h('h3', { class: 'source__diag-head' }, 'Diagnostics');
  const diagList = h('ul', { class: 'source__diag-list' });
  const diagBox = h('section', { class: 'source__diagnostics', 'data-testid': 'source-diagnostics', 'aria-label': 'Source diagnostics' }, diagHead, diagList);

  const root = h('div', { class: 'source' },
    h('header', { class: 'source__head' }, file, state, h('span', { class: 'source__actions' }, apply, discard)),
    banner, notice, rejection,
    h('div', { class: 'source__editor' }, gutter, ta),
    diagBox);
  clear(el);
  el.append(root);

  // ---- helpers -----------------------------------------------------------

  const lineHeight = () => parseFloat(getComputedStyle(ta).lineHeight) || 20;
  const committed = () => session.project?.specText ?? '';

  function drawGutter() {
    const n = ta.value.split('\n').length;
    const key = `${n}|${[...errorLines].join(',')}|${[...warnLines].join(',')}`;
    if (key !== drawGutter.last) {
      drawGutter.last = key;
      const frag = document.createDocumentFragment();
      for (let i = 1; i <= n; i++) {
        const cls = errorLines.has(i) ? 'source__ln source__ln--error' : warnLines.has(i) ? 'source__ln source__ln--warn' : 'source__ln';
        const d = h('div', { class: cls }, String(i));
        if (errorLines.has(i)) d.title = 'Error in the draft on this line';
        else if (warnLines.has(i)) d.title = 'Warning in the draft on this line';
        frag.append(d);
      }
      gutter.replaceChildren(frag);
      gutter.style.minWidth = `${String(n).length + 2}ch`;
    }
    bareLineCount = n;
    syncScroll();
  }
  /** @type {any} */ (drawGutter).last = '';

  function syncScroll() {
    // The horizontal scrollbar of the textarea takes height the gutter does not have.
    const bar = ta.offsetHeight - ta.clientHeight;
    gutter.style.paddingBottom = `calc(var(--source-pad, 8px) + ${Math.max(0, bar)}px)`;
    gutter.scrollTop = ta.scrollTop;
  }

  function scrollToLine(line) {
    const lh = lineHeight();
    const target = (line - 1) * lh - ta.clientHeight / 3;
    ta.scrollTop = Math.max(0, target);
    syncScroll();
  }

  /** @param {number} line @param {number} column */
  function goTo(line, column) {
    const off = offsetOf(ta.value, line, column);
    ta.focus({ preventScroll: true });
    ta.setSelectionRange(off, off);
    scrollToLine(line);
  }

  function renderState() {
    const clean = draft === null;
    state.textContent = clean ? `In sync with model rev ${session.project?.revision ?? '?'}` : 'Draft — not applied';
    state.dataset.state = clean ? 'clean' : 'draft';
    apply.disabled = clean;
    discard.disabled = clean;
    file.textContent = session.specLocation ?? `specs/${session.projectName ?? ''}/spec.jsonc`;
  }

  /** @param {HTMLElement} list @param {Diagnostic[]} ds @param {number} [limit] */
  function fillDiagnostics(list, ds, limit = 500) {
    clear(list);
    for (const d of ds.slice(0, limit)) {
      const where = d.loc ? `${d.loc.line}:${d.loc.column}` : '';
      const row = h('li', { class: `source__diag source__diag--${d.severity}` });
      const text = [h('span', { class: `source__sev source__sev--${d.severity}` }, h('span', { class: 'source__dot', 'aria-hidden': 'true' }), d.severity), where ? h('span', { class: 'source__where mono' }, where) : null, h('span', { class: 'source__msg' }, d.message)];
      if (d.loc) {
        const b = h('button', { type: 'button', class: 'source__diag-btn', title: 'Put the caret here' }, text);
        on(b, 'click', () => goTo(/** @type {any} */ (d.loc).line, /** @type {any} */ (d.loc).column));
        row.append(b);
      } else row.append(h('span', { class: 'source__diag-btn source__diag-btn--static' }, text));
      list.append(row);
    }
    if (ds.length > limit) list.append(h('li', { class: 'source__diag source__diag--more' }, `… and ${ds.length - limit} more`));
  }

  function renderDiagnostics() {
    if (draft === null) {
      diagBox.hidden = true;
      errorLines = new Set(); warnLines = new Set();
      return;
    }
    diagBox.hidden = false;
    const errors = diags.filter((d) => d.severity === 'error').length;
    const warnings = diags.filter((d) => d.severity === 'warning').length;
    const infos = diags.length - errors - warnings;
    diagHead.textContent = `Diagnostics of the draft — ${errors} ${errors === 1 ? 'error' : 'errors'}, ${warnings} ${warnings === 1 ? 'warning' : 'warnings'}, ${infos} ${infos === 1 ? 'gap' : 'gaps'}`;
    diagBox.dataset.errors = String(errors);
    errorLines = new Set(diags.filter((d) => d.severity === 'error' && d.loc).map((d) => /** @type {any} */ (d.loc).line));
    warnLines = new Set(diags.filter((d) => d.severity === 'warning' && d.loc).map((d) => /** @type {any} */ (d.loc).line));
    if (!diags.length) clear(diagList), diagList.append(h('li', { class: 'source__diag source__diag--none' }, 'The draft parses and validates without diagnostics.'));
    else fillDiagnostics(diagList, diags);
  }

  function analyse() {
    clearTimeout(timer);
    timer = 0;
    if (draft === null) { diags = []; renderDiagnostics(); drawGutter(); return; }
    diags = analyzeSpec(draft).diagnostics;
    renderDiagnostics();
    drawGutter();
  }

  function scheduleAnalysis() {
    clearTimeout(timer);
    timer = setTimeout(analyse, DEBOUNCE_MS);
  }

  function renderBanner() {
    const rev = session.project?.revision ?? 0;
    const stale = draft !== null && rev !== baseRev && rev !== ackRev;
    banner.hidden = !stale;
    if (!stale) return;
    clear(banner);
    const keep = h('button', { type: 'button', class: 'btn btn--small', 'data-testid': 'source-keep' }, 'Keep editing my draft');
    const drop = h('button', { type: 'button', class: 'btn btn--small', 'data-testid': 'source-drop' }, 'Discard draft and show current source');
    on(keep, 'click', () => { ackRev = session.project?.revision ?? 0; renderBanner(); ta.focus({ preventScroll: true }); });
    on(drop, 'click', discardDraft);
    banner.append(
      h('p', { class: 'source__banner-text' }, `The model changed (now rev ${rev}) since this draft was started.`, h('span', { class: 'source__banner-sub' }, ' If you keep editing, Apply will overwrite those changes with your draft.')),
      h('span', { class: 'source__banner-actions' }, keep, drop));
  }

  /** Put `text` in the textarea, keeping scroll and mapping the caret. @param {string} text */
  function setText(text) {
    if (ta.value === text) return;
    const old = ta.value;
    const top = ta.scrollTop, left = ta.scrollLeft;
    const a = ta.selectionStart, b = ta.selectionEnd;
    ta.value = text;
    ta.setSelectionRange(mapOffset(old, text, a), mapOffset(old, text, b));
    ta.scrollTop = top;
    ta.scrollLeft = left;
  }

  function showCommitted() {
    draft = null;
    ackRev = 0;
    diags = [];
    rejection.hidden = true;
    notice.hidden = true;
    clearTimeout(timer);
    setText(committed());
    renderState(); renderBanner(); renderDiagnostics(); drawGutter();
  }

  function discardDraft() { showCommitted(); }

  function applyDraft() {
    if (draft === null) return;
    const text = draft;
    applying = true;
    /** @type {any} */
    let r;
    try { r = session.apply({ type: 'ReplaceSource', text }, { label: 'Edit source' }); } finally { applying = false; }
    if (r.ok) { showCommitted(); return; }
    // Rejected: the draft stays exactly as typed.
    clear(rejection);
    rejection.hidden = false;
    rejection.append(h('p', { class: 'source__rejection-msg' }, r.message ?? 'The model rejected the source.', ' The draft is kept as typed; the model is unchanged.'));
    const ds = /** @type {Diagnostic[]} */ (r.diagnostics ?? []);
    const list = h('ul', { class: 'source__diag-list' });
    fillDiagnostics(list, ds.filter((d) => d.severity === 'error').length ? ds.filter((d) => d.severity === 'error') : ds, 50);
    rejection.append(list);
    analyse();
  }

  // ---- events ------------------------------------------------------------

  on(ta, 'input', () => {
    if (ta.value === committed()) { showCommitted(); return; }
    if (draft === null) { baseRev = session.project?.revision ?? 0; ackRev = 0; }
    draft = ta.value;
    rejection.hidden = true;
    notice.hidden = true;
    renderState();
    renderBanner();
    drawGutter();
    scheduleAnalysis();
  });
  on(ta, 'scroll', syncScroll);
  on(ta, 'keydown', (/** @type {KeyboardEvent} */ e) => {
    if ((e.ctrlKey || e.metaKey) && (e.key === 's' || e.key === 'S' || e.key === 'Enter')) { e.preventDefault(); applyDraft(); }
  });
  on(apply, 'click', applyDraft);
  on(discard, 'click', discardDraft);
  if (typeof ResizeObserver === 'function') new ResizeObserver(syncScroll).observe(ta);

  /** @param {{id?: string}|undefined} ev */
  function reveal(ev) {
    const id = ev?.id ?? /** @type {any} */ (ev)?.detail?.id;
    if (!id) return;
    opts.show?.();
    requestAnimationFrame(() => {
      /** @type {{offset: number, length: number, line: number}|undefined} */
      let loc;
      if (draft === null) loc = session.model?.entities.get(id)?.loc;
      else loc = parseSpec(draft).model?.entities.get(id)?.loc;
      if (!loc) {
        notice.hidden = false;
        notice.textContent = `"${id}" cannot be found in the draft. Apply or fix the draft first.`;
        return;
      }
      notice.hidden = true;
      ta.focus({ preventScroll: true });
      ta.setSelectionRange(loc.offset, loc.offset + loc.length);
      scrollToLine(loc.line);
    });
  }

  const unsubs = [
    session.on('model', () => {
      if (applying) return;
      if (draft === null) { setText(committed()); renderState(); drawGutter(); }
      else { renderState(); renderBanner(); }
    }),
    session.on('project', () => showCommitted()),
    session.on('reveal-source', reveal),
  ];

  showCommitted();

  return () => { clearTimeout(timer); for (const u of unsubs) u(); clear(el); };
}
