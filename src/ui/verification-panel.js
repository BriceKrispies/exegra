// Verification panel: inventory of claims and their evaluated results.
// A positive tone appears only for ClaimResults that are verified or supported.

import { h, clear } from './dom.js';
import { entityLabel } from '../core/query.js';
import { CLAIM_STATUSES } from '../core/claim-methods.js';

const ORDER = /** @type {const} */ (['proved', 'verified', 'supported', 'violated', 'inconclusive', 'not-evaluated']);

/** @param {HTMLElement} el @param {any} session */
export function mountVerificationPanel(el, session) {
  el.classList.add('ver');
  el.setAttribute('data-testid', 'verification-panel');

  /** UI-only filter state (not semantic). */
  const filter = { statuses: /** @type {Set<string>} */ (new Set()), kind: '', method: '', text: '' };
  /** Most rows the table renders; the rest are reached by filtering. */
  const LIMIT = 200;

  /** @param {any} c the declared evaluation method of a claim */
  const methodOf = (c) => (typeof c.data.evaluate?.method === 'string' ? c.data.evaluate.method : '');
  /** @param {string} m */
  const methodLabel = (m) => session.model?.meta.verificationMethods?.[m]?.label ?? m;

  /** @param {string} status */
  const statusChip = (status) => {
    const def = CLAIM_STATUSES[/** @type {keyof typeof CLAIM_STATUSES} */ (status)];
    return h('span', { class: ['ver__chip', `ver__chip--${def?.tone ?? 'none'}`], 'data-status': status },
      h('span', { class: 'ver__dot', 'aria-hidden': 'true' }), def?.label ?? status);
  };

  const header = h('header', { class: 'ver__head' });
  const filterBar = h('div', { class: 'ver__filters', role: 'group', 'aria-label': 'Filter claims' });
  const body = h('div', { class: 'ver__body' });
  el.append(header, filterBar, body);

  /** @param {string} id */
  const rowFor = (id) => /** @type {HTMLElement|null} */ (body.querySelector(`tr[data-entity-id="${CSS.escape(id)}"]`));

  function renderHeader() {
    clear(header);
    const model = session.model;
    const claims = model?.byKind.claim ?? [];
    /** @type {Record<string, number>} */
    const counts = Object.fromEntries(ORDER.map((s) => [s, 0]));
    for (const c of claims) {
      const r = session.claimResult(c.id);
      counts[r?.status ?? 'not-evaluated']++;
    }
    const ul = h('ul', { class: 'ver__counts', 'data-testid': 'claim-counts' });
    for (const s of ORDER) ul.append(h('li', { 'data-status': s }, statusChip(s), h('span', { class: 'ver__count' }, String(counts[s]))));
    header.append(
      h('h3', { class: 'ver__h' }, 'Claims'),
      ul,
      h('p', { class: 'ver__legend' }, 'Verified = checked by Exegra against this model revision under the stated assumptions. Supported = rests on external evidence. Neither says anything beyond the stated scope.'),
    );
    const external = Object.values(model?.meta.verificationMethods ?? {}).map((m) => /** @type {any} */ (m).label).filter(Boolean);
    if (external.length) {
      header.append(h('p', { class: 'ver__legend ver__external', 'data-testid': 'external-methods-line' },
        `Requirements verified by ${external.join(', ')} are checked by tools outside Exegra; without recorded evidence they are reported as not evaluated.`));
    }
    const rec = session.recorded;
    if (rec) {
      const n = Object.keys(rec.results ?? {}).length;
      header.append(h('p', { class: 'ver__recorded', 'data-testid': 'recorded-line' },
        `Recorded results for ${n} evidence item${n === 1 ? '' : 's'} loaded from `, h('code', null, 'evidence/results.json'),
        '. Their freshness is unverifiable here: the page cannot stamp the files they were recorded for, so a result may describe an earlier tree. ',
        h('code', null, 'exegra claims'), ' compares the stamps and reports stale results as not evaluated.'));
    } else {
      header.append(h('p', { class: 'ver__recorded', 'data-testid': 'recorded-line' },
        'No recorded results. Test evidence shows as not executed. Run ', h('code', null, 'npm run verify'), ' to execute and record it.'));
    }
  }

  function renderFilters() {
    clear(filterBar);
    const claims = session.model?.byKind.claim ?? [];
    for (const s of ORDER) {
      const on = filter.statuses.has(s);
      filterBar.append(h('button', {
        type: 'button', class: ['ver__toggle', on && 'ver__toggle--on'], 'aria-pressed': String(on), 'data-testid': `claim-filter-${s}`,
        onclick: () => { if (on) filter.statuses.delete(s); else filter.statuses.add(s); renderFilters(); renderTable(); },
      }, CLAIM_STATUSES[s].label));
    }
    const kinds = [...new Set(claims.map((/** @type {any} */ c) => session.claimResult(c.id)?.kind ?? c.data.kind).filter(Boolean))].sort();
    if (filter.kind && !kinds.includes(filter.kind)) filter.kind = '';
    const sel = h('select', {
      'data-testid': 'claim-filter-kind', 'aria-label': 'Filter by claim kind',
      onchange: (/** @type {any} */ e) => { filter.kind = e.target.value; renderTable(); },
    }, h('option', { value: '' }, 'All kinds'), kinds.map((k) => h('option', { value: k }, k)));
    sel.value = filter.kind;
    filterBar.append(sel);
    const methods = [...new Set(claims.map(methodOf).filter(Boolean))].sort();
    if (filter.method && !methods.includes(filter.method)) filter.method = '';
    const msel = h('select', {
      'data-testid': 'claim-filter-method', 'aria-label': 'Filter by verification method',
      onchange: (/** @type {any} */ e) => { filter.method = e.target.value; renderTable(); },
    }, h('option', { value: '' }, 'All methods'), methods.map((m) => h('option', { value: m }, methodLabel(m))));
    msel.value = filter.method;
    filterBar.append(msel);
    filterBar.append(h('input', {
      type: 'search', class: 'ver__text', 'data-testid': 'claim-filter-text', placeholder: 'Filter by id, reference or statement',
      'aria-label': 'Filter claims by id, reference or statement', autocomplete: 'off', spellcheck: 'false', value: filter.text,
      oninput: (/** @type {any} */ e) => { filter.text = e.target.value; renderTable(); },
    }));
  }

  function renderTable() {
    clear(body);
    const model = session.model;
    const claims = model?.byKind.claim ?? [];
    if (!claims.length) { body.append(h('p', { class: 'ver__empty' }, 'This specification declares no claims.')); return; }
    const q = filter.text.trim().toLowerCase();
    const all = claims.filter((/** @type {any} */ c) => {
      const r = session.claimResult(c.id);
      if (filter.statuses.size && !filter.statuses.has(r?.status ?? 'not-evaluated')) return false;
      if (filter.kind && (r?.kind ?? c.data.kind) !== filter.kind) return false;
      if (filter.method && methodOf(c) !== filter.method) return false;
      if (q && ![c.id, c.data.ref, c.data.statement].some((/** @type {any} */ v) => typeof v === 'string' && v.toLowerCase().includes(q))) return false;
      return true;
    });
    const shown = all.slice(0, LIMIT);
    if (!shown.length) { body.append(h('p', { class: 'ver__empty' }, 'No claim matches the filter.')); return; }

    const tbody = h('tbody');
    const claimsView = session.views.find((/** @type {any} */ v) => v.projection === 'claims');
    for (const c of shown) {
      const r = session.claimResult(c.id);
      const status = r?.status ?? 'not-evaluated';
      const ev = r?.evidence ?? [];
      const rc = { pass: 0, fail: 0, none: 0 };
      for (const e of ev) rc[/** @type {'pass'|'fail'|'none'} */ (e.recorded)]++;
      const statementCell = h('td', { class: 'ver__statement', 'data-label': 'Statement' }, h('div', null, c.data.statement ?? entityLabel(c)));
      if (status === 'violated' && r?.counterexample) {
        statementCell.append(h('div', { class: 'ver__cex', 'data-testid': 'claim-counterexample' }, h('strong', null, 'Counterexample: '), r.counterexample.summary));
      }
      const tr = h('tr', {
        class: ['ver__row', session.selection === c.id && 'ver__row--selected'],
        tabindex: 0, 'data-entity-id': c.id, 'data-status': status,
        'aria-selected': String(session.selection === c.id),
        onclick: () => session.select(c.id),
        onkeydown: (/** @type {KeyboardEvent} */ e) => {
          if (e.target !== e.currentTarget) return;
          if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); session.select(c.id); }
        },
      },
        h('td', { class: 'ver__status', 'data-label': 'Status' }, statusChip(status)),
        h('td', { class: 'ver__mono ver__id', 'data-label': 'Claim', title: c.data.ref ? c.id : undefined }, typeof c.data.ref === 'string' && c.data.ref ? c.data.ref : c.id),
        h('td', { 'data-label': 'Kind' }, r?.kind ?? c.data.kind ?? ''),
        h('td', { class: 'ver__mono', 'data-label': 'Method' }, typeof r?.evaluator === 'string' && r.evaluator.startsWith('external:') ? methodLabel(r.evaluator.slice('external:'.length)) : (r?.method ?? '—')),
        statementCell,
        h('td', { class: 'ver__scope', 'data-label': 'Scope', title: r?.explanation ?? '' }, r?.scope ?? ''),
        h('td', { class: 'ver__num', 'data-label': 'Evidence', title: 'recorded results of this claim\'s evidence' },
          String(ev.length), ev.length ? h('span', { class: 'ver__muted' }, ` (${rc.pass} pass, ${rc.fail} fail, ${rc.none} none)`) : null),
        h('td', { class: 'ver__num', 'data-label': 'Assumptions' }, String(r?.assumptions?.length ?? 0)),
        h('td', { class: 'ver__actions' }, h('button', {
          type: 'button', 'data-testid': `claim-show-${c.id}`, disabled: !claimsView,
          title: claimsView ? 'Select this claim and switch to the claims view' : 'This model has no claims view',
          onclick: (/** @type {Event} */ e) => { e.stopPropagation(); session.select(c.id); if (claimsView) session.setView(claimsView.id); },
          onkeydown: (/** @type {Event} */ e) => e.stopPropagation(),
        }, 'Show in claims view')));
      tbody.append(tr);
    }
    const th = (/** @type {string} */ t) => h('th', { scope: 'col' }, t);
    body.append(h('table', { class: 'ver__table cardtable', 'data-testid': 'claims-table' },
      h('thead', null, h('tr', null, th('Status'), th('Claim'), th('Kind'), th('Method'), th('Statement'), th('Scope'), th('Evidence'), th('Assumptions'), h('th', { scope: 'col' }, h('span', { class: 'ver__sr' }, 'Actions')))),
      tbody));
    if (all.length > shown.length) {
      body.append(h('p', { class: 'ver__more', 'data-testid': 'claims-more' }, `Showing ${shown.length} of ${all.length} — filter by status, kind, method or text to narrow`));
    }
  }

  function renderAll() {
    const active = document.activeElement;
    const focusedId = active && el.contains(active) ? active.closest('tr')?.getAttribute('data-entity-id') : null;
    const scroll = el.scrollTop;
    renderHeader(); renderFilters(); renderTable();
    el.scrollTop = scroll;
    if (focusedId && active?.tagName === 'TR') rowFor(focusedId)?.focus({ preventScroll: true });
  }

  function updateSelection() {
    for (const tr of body.querySelectorAll('tr.ver__row')) {
      const on = tr.getAttribute('data-entity-id') === session.selection;
      tr.classList.toggle('ver__row--selected', on);
      tr.setAttribute('aria-selected', String(on));
    }
  }

  const offs = [
    session.on('claims', renderAll), session.on('model', renderAll), session.on('project', renderAll),
    session.on('selection', updateSelection),
  ];
  renderAll();
  return () => { for (const off of offs) off(); };
}
