// Realisation panel: how the specified system is implemented, generated and
// verified, and where the model and the implementation disagree.

import { h, clear } from './dom.js';
import { entityLabel } from '../core/query.js';
import { generateAll } from '../core/generate/index.js';
import { writeGenerated } from '../persist/client.js';
import { sha256Hex } from '../core/sha256.js';

/** sha-256 of the generated files with sorted keys: how the self-model names one set of generated documents (the dev server computes the same, tools/vite-plugin-exegra.js hashFiles). @param {Record<string, string>} files */
function filesHash(files) {
  return sha256Hex(JSON.stringify(Object.fromEntries(Object.keys(files).sort().map((k) => [k, files[k]]))));
}

const STATUSES = ['generated', 'partially-generated', 'model-configured', 'manual', 'not-implemented', 'undeclared'];
const STATUS_LABEL = {
  generated: 'Generated',
  'partially-generated': 'Partially generated',
  'model-configured': 'Model-configured',
  manual: 'Manual',
  'not-implemented': 'Not implemented',
  undeclared: 'Undeclared',
};
const PREVIEW_LINES = 200;

/** @param {HTMLElement} el @param {any} session */
export function mountRealisationPanel(el, session) {
  el.classList.add('real');
  el.setAttribute('data-testid', 'realisation-panel');

  const filter = { statuses: /** @type {Set<string>} */ (new Set()) };
  /** @type {{busy: boolean, files: Record<string, string>|null, written: string[]|null, note: string, error: string}} */
  let gen = { busy: false, files: null, written: null, note: '', error: '' };

  /** @param {string} s */
  const chip = (s) => h('span', { class: ['real__chip', `real__chip--${s}`] }, h('span', { class: 'real__dot', 'aria-hidden': 'true' }), STATUS_LABEL[/** @type {keyof typeof STATUS_LABEL} */ (s)] ?? s);

  const main = h('div', { class: 'real__main' });
  const genBox = h('section', { class: 'real__section', 'data-testid': 'realisation-generated' });
  el.append(main, genBox);

  /** @param {string} id */
  const link = (id) => h('button', {
    type: 'button', class: 'real__link', 'data-entity-id': id, title: id, onclick: () => session.select(id),
  }, (() => { const e = session.model?.entities.get(id); return e ? entityLabel(e) : id; })());

  function renderMain() {
    clear(main);
    const model = session.model;
    const comps = model?.byKind.component ?? [];
    const statusOf = (/** @type {any} */ c) => c.data.implementation?.status ?? 'undeclared';
    const anyDeclared = comps.some((/** @type {any} */ c) => c.data.implementation);
    main.append(h('h3', { class: 'real__h' }, 'Realisation'));

    if (!anyDeclared) {
      main.append(h('p', { class: 'real__empty', 'data-testid': 'realisation-empty' }, 'This specification does not record how its components are realised.',
        model?.system?.data?.illustrative ? ' It is an illustrative example.' : ''));
      return;
    }

    // summary
    /** @type {Record<string, number>} */
    const counts = Object.fromEntries(STATUSES.map((s) => [s, 0]));
    for (const c of comps) counts[statusOf(c)] = (counts[statusOf(c)] ?? 0) + 1;
    const total = comps.length || 1;
    const bar = h('div', { class: 'real__bar', role: 'img', 'aria-label': STATUSES.filter((s) => counts[s]).map((s) => `${counts[s]} ${STATUS_LABEL[/** @type {keyof typeof STATUS_LABEL} */ (s)].toLowerCase()}`).join(', ') });
    for (const s of STATUSES) if (counts[s]) bar.append(h('span', { class: `real__seg real__seg--${s}`, style: { width: `${(counts[s] / total) * 100}%` }, title: `${STATUS_LABEL[/** @type {keyof typeof STATUS_LABEL} */ (s)]}: ${counts[s]}` }));
    const legend = h('ul', { class: 'real__legend', 'data-testid': 'realisation-summary' });
    for (const s of STATUSES) if (counts[s]) legend.append(h('li', null, chip(s), h('span', { class: 'real__num' }, ` ${counts[s]} (${Math.round((counts[s] / total) * 100)}%)`)));
    main.append(bar, legend);

    // filter
    const bnd = h('div', { class: 'real__filters', role: 'group', 'aria-label': 'Filter by realisation status' });
    for (const s of STATUSES) {
      if (!counts[s]) continue;
      const on = filter.statuses.has(s);
      bnd.append(h('button', {
        type: 'button', class: ['real__toggle', on && 'real__toggle--on'], 'aria-pressed': String(on), 'data-testid': `realisation-filter-${s}`,
        onclick: () => { if (on) filter.statuses.delete(s); else filter.statuses.add(s); renderMain(); },
      }, STATUS_LABEL[/** @type {keyof typeof STATUS_LABEL} */ (s)]));
    }
    main.append(bnd);

    const trace = session.recorded?.traceability ?? null;
    /** @type {Set<string>} */
    const missing = new Set((trace?.missingModules ?? []).map((/** @type {any} */ m) => `${m.component}\u0000${m.module}`));

    const ordered = [...comps.filter((/** @type {any} */ c) => c.data.kind === 'subsystem'), ...comps.filter((/** @type {any} */ c) => c.data.kind !== 'subsystem')];
    const rows = ordered.filter((/** @type {any} */ c) => !filter.statuses.size || filter.statuses.has(statusOf(c)));
    const tbody = h('tbody');
    for (const c of rows) {
      const st = statusOf(c);
      const impl = c.data.implementation;
      const results = session.claimResults.filter((/** @type {any} */ r) => r.involved.includes(c.id));
      const n = (/** @type {string} */ s) => results.filter((/** @type {any} */ r) => r.status === s).length;
      const other = results.length - n('proved') - n('verified') - n('supported') - n('violated');
      const verif = !results.length
        ? h('span', { class: 'real__muted' }, 'no claims')
        : h('span', null, `${n('proved') ? `${n('proved')} proved, ` : ''}${n('verified')} verified, ${n('supported')} supported, `,
          h('span', { class: n('violated') ? 'real__bad' : '' }, `${n('violated')} violated`), `, ${other} other`);
      const mods = h('td', { class: 'real__mono', 'data-label': 'Modules' });
      for (const m of impl?.modules ?? []) {
        const gone = missing.has(`${c.id}\u0000${m}`);
        mods.append(h('div', { class: gone ? 'real__gone' : '' }, gone ? h('s', null, m) : m,
          gone ? h('span', { class: 'real__bad' }, ' missing on disk') : null));
      }
      tbody.append(h('tr', { 'data-entity-id': c.id, 'data-status': st },
        h('td', { class: 'real__name cardtable__title' }, link(c.id), c.data.kind === 'subsystem' ? h('span', { class: 'real__muted' }, ' (subsystem)') : null),
        h('td', { 'data-label': 'Realisation' }, chip(st)),
        mods,
        h('td', { 'data-label': 'Verification' }, verif),
        h('td', { class: 'real__notes', 'data-label': 'Notes' }, impl?.notes ?? '')));
    }
    const th = (/** @type {string} */ t) => h('th', { scope: 'col' }, t);
    main.append(rows.length
      ? h('table', { class: 'real__table cardtable', 'data-testid': 'realisation-table' },
        h('thead', null, h('tr', null, th('Component'), th('Realisation'), th('Modules'), th('Verification'), th('Notes'))), tbody)
      : h('p', { class: 'real__muted' }, 'No component matches the filter.'));

    // bootstrap boundary
    const manual = comps.filter((/** @type {any} */ c) => statusOf(c) === 'manual');
    const boundary = h('section', { class: 'real__section', 'data-testid': 'realisation-bootstrap' },
      h('h4', { class: 'real__sub' }, 'Bootstrap boundary'),
      h('p', { class: 'real__muted' }, 'Hand-written foundation that Exegra cannot yet generate from its own model.'));
    if (!manual.length) boundary.append(h('p', { class: 'real__muted' }, 'No component is recorded as manual.'));
    else {
      const ul = h('ul', { class: 'real__list' });
      for (const c of manual) {
        const k = (c.data.implementation?.modules ?? []).length;
        ul.append(h('li', null, link(c.id), h('span', { class: 'real__muted' }, ` — ${k} module${k === 1 ? '' : 's'}`)));
      }
      boundary.append(ul);
    }
    main.append(boundary);

    // discrepancies
    const disc = h('section', { class: 'real__section', 'data-testid': 'realisation-discrepancies' },
      h('h4', { class: 'real__sub' }, 'Model / implementation discrepancies'));
    if (!trace) disc.append(h('p', { class: 'real__muted' }, 'Traceability has not been checked. Run ', h('code', null, 'npm run verify'), '.'));
    else {
      const miss = trace.missingModules ?? [];
      const un = trace.unclaimedFiles ?? [];
      disc.append(h('p', { class: 'real__muted' }, `Checked ${trace.checkedModules ?? 0} declared module${trace.checkedModules === 1 ? '' : 's'}.`));
      if (!miss.length && !un.length) disc.append(h('p', null, 'No discrepancies found in the checked scope.'));
      if (miss.length) {
        const ul = h('ul', { class: 'real__list' });
        for (const m of miss) ul.append(h('li', null, link(m.component), ' declares ', h('code', null, m.module), h('span', { class: 'real__bad' }, ' — missing on disk')));
        disc.append(h('h5', { class: 'real__sub2' }, 'Declared modules missing on disk'), ul);
      }
      if (un.length) {
        const ul = h('ul', { class: 'real__list real__mono' });
        for (const f of un) ul.append(h('li', null, f));
        disc.append(h('h5', { class: 'real__sub2' }, 'Source files no component claims'), ul);
      }
    }
    main.append(disc);
  }

  function renderGen() {
    clear(genBox);
    genBox.append(h('h4', { class: 'real__sub' }, 'Generated artifacts'));
    const btn = h('button', {
      type: 'button', 'data-testid': 'generate-artifacts', disabled: gen.busy || !session.model || session.project?.errorCount > 0,
      title: !session.model ? 'The specification has errors' : 'Derive artifacts from the model (deterministic)',
      onclick: generate,
    }, gen.busy ? 'Generating…' : 'Generate from model');
    genBox.append(btn);
    if (gen.error) genBox.append(h('p', { class: 'real__bad', role: 'alert' }, gen.error));
    if (gen.files) {
      const names = Object.keys(gen.files);
      genBox.append(h('p', { class: 'real__muted', 'data-testid': 'generate-status' },
        gen.written ? `${gen.written.length} file${gen.written.length === 1 ? '' : 's'} written to specs/${session.projectName}/generated/.` : gen.note));
      for (const name of names) {
        const text = gen.files[name];
        const lines = text.split('\n');
        const preview = lines.length > PREVIEW_LINES ? lines.slice(0, PREVIEW_LINES).join('\n') + `\n… ${lines.length - PREVIEW_LINES} more line(s) not shown` : text;
        genBox.append(h('details', { class: 'real__file', 'data-testid': `generated-file-${name}` },
          h('summary', null, h('span', { class: 'real__mono' }, name), h('span', { class: 'real__muted' }, ` · ${new Blob([text]).size} bytes · ${lines.length} lines`)),
          h('pre', { class: 'real__pre' }, preview)));
      }
    }
  }

  async function generate() {
    if (gen.busy || !session.model) return;
    session.traffic?.record('generate-clicked');
    gen = { busy: true, files: null, written: null, note: '', error: '' };
    renderGen();
    try {
      const files = generateAll(session.model, {
        claimResults: session.claimResults,
        diagnostics: session.diagnostics,
        traceability: session.recorded?.traceability,
      });
      gen.files = files;
      if (session.persistent) {
        const requestId = session.traffic.nextRequestId();
        const hash = filesHash(files);
        session.traffic.record('generated-intent', { name: session.projectName, files: hash, requestId });
        const res = await writeGenerated(session.projectName, files, { requestId, filesHash: hash });
        if (res?.ok) session.traffic.record('generated-saved', { written: res.written ?? [], requestId });
        if (res?.ok) gen.written = res.written ?? Object.keys(files);
        else gen.error = `Could not write generated files: ${/** @type {any} */ (res)?.error ?? 'unknown error'}`;
        if (!gen.written) gen.note = 'Not written to disk.';
      } else gen.note = 'Preview only — this build cannot write files.';
    } catch (e) {
      gen.files = null;
      gen.error = `Generation failed: ${/** @type {Error} */ (e).message}`;
    }
    gen.busy = false;
    renderGen();
  }

  function renderAll(/** @type {boolean} */ resetGen) {
    if (resetGen) gen = { busy: false, files: null, written: null, note: '', error: '' };
    const active = document.activeElement;
    const tid = active && el.contains(active) ? active.getAttribute('data-testid') : null;
    const scroll = el.scrollTop;
    renderMain();
    if (resetGen || !genBox.firstChild) renderGen();
    el.scrollTop = scroll;
    if (tid && document.activeElement !== active) /** @type {HTMLElement|null} */ (el.querySelector(`[data-testid="${CSS.escape(tid)}"]`))?.focus({ preventScroll: true });
  }

  const offs = [
    session.on('model', () => renderAll(true)),
    session.on('project', () => renderAll(true)),
    session.on('claims', () => renderAll(false)),
  ];
  renderAll(true);
  return () => { for (const off of offs) off(); };
}
