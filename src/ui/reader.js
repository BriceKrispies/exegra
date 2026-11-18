// Reader surface: shown in place of the scene while the current view uses the reader
// projection. Draws the page src/core/reader.js derives from the model and the view,
// keeps each view's filters, and routes every entity link to the session's selection,
// so the inspector (and its editing) serves the reader as it serves the scene.

import { h, clear } from './dom.js';
import { readerPage, kindPage, sectionBlocks, refIndex, ROW_CAP } from '../core/reader.js';

const INLINE = /(\*\*[^*]+\*\*|`[^`]+`|\[[^\]\n]+\]\((?:https?:\/\/)[^)\s]+\)|\[[^\]\n]{1,200}\]|\b[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)*-\d+[a-z]?\b)/g;

/** @param {number} n @param {string} one @param {string} [many] */
const plural = (n, one, many) => `${n.toLocaleString()} ${n === 1 ? one : many ?? `${one}s`}`;

/**
 * @param {HTMLElement} host
 * @param {any} session
 */
export function mountReader(host, session) {
  /** @type {Map<string, {facets: Set<string>, q: string, showAll: boolean, kind: string|null, section: string|null}>} */
  const states = new Map();
  /** @type {Map<string, string>} */
  let refs = new Map();
  let modelSeen = null;
  let shownKey = '';

  const app = /** @type {HTMLElement} */ (document.getElementById('app'));
  const active = () => session.scene?.projection === 'reader' && !!session.model;

  /** @returns {{facets: Set<string>, q: string, showAll: boolean, kind: string|null, section: string|null}} */
  const stateOf = () => {
    const key = `${session.projectName}/${session.viewId}`;
    let s = states.get(key);
    if (!s) states.set(key, (s = { facets: new Set(), q: '', showAll: false, kind: null, section: null }));
    return s;
  };

  /** @param {string} id @param {any} label @param {string} [cls] */
  const link = (id, label, cls) => h('button', {
    type: 'button', class: ['rd-link', cls], 'data-entity': id,
    'aria-current': session.selection === id ? 'true' : null,
    onclick: () => session.select(id, { source: 'reader' }),
  }, label);

  /** @param {string} text */
  const inline = (text) => {
    /** @type {any[]} */
    const out = [];
    let last = 0;
    const s = String(text ?? '');
    for (const m of s.matchAll(INLINE)) {
      const t = m[0];
      const at = m.index ?? 0;
      if (at > last) out.push(s.slice(last, at));
      last = at + t.length;
      if (t.startsWith('**')) out.push(h('strong', {}, ...inline(t.slice(2, -2))));
      else if (t.startsWith('`')) out.push(h('code', {}, t.slice(1, -1)));
      else if (t.startsWith('[')) {
        const url = t.match(/^\[([^\]]+)\]\((https?:\/\/[^)]+)\)$/);
        if (url) out.push(h('a', { href: url[2], rel: 'noreferrer', target: '_blank' }, url[1]));
        else out.push(h('span', { class: 'rd-cite' }, '[', ...inline(t.slice(1, -1)), ']'));
      } else {
        const id = refs.get(t.toLowerCase());
        out.push(id ? link(id, t, 'rd-link--ref') : t);
      }
    }
    if (last < s.length) out.push(s.slice(last));
    return out;
  };

  /** Paragraphs, lists and headings. @param {string} text */
  const prose = (text) => {
    /** @type {any[]} */
    const blocks = [];
    /** @type {string[]} */
    let para = [];
    /** @type {{ordered: boolean, el: HTMLElement}|null} */
    let list = null;
    const flushPara = () => { if (para.length) blocks.push(h('p', {}, ...inline(para.join(' ')))); para = []; };
    const flushList = () => { if (list) blocks.push(list.el); list = null; };
    for (const raw of String(text ?? '').split('\n')) {
      const line = raw.trimEnd();
      if (!line.trim()) { flushPara(); flushList(); continue; }
      const head = line.match(/^(#{1,6})\s+(.*)$/);
      if (head) { flushPara(); flushList(); blocks.push(h('h4', { class: 'rd-subhead' }, ...inline(head[2]))); continue; }
      const item = line.match(/^\s*([-*]|\d+\.)\s+(.*)$/);
      if (item) {
        flushPara();
        const ordered = /\d/.test(item[1]);
        if (!list || list.ordered !== ordered) { flushList(); list = { ordered, el: h(ordered ? 'ol' : 'ul', {}) }; }
        list.el.append(h('li', {}, ...inline(item[2])));
        continue;
      }
      flushList();
      para.push(line.trim());
    }
    flushPara();
    flushList();
    return h('div', { class: 'rd-prose' }, ...blocks);
  };

  /** @param {any} c */
  const cellContent = (c) => {
    if (c.status != null) return statusMark(c.tone, c.text, c.title);
    if (c.links?.length) return c.links.flatMap((/** @type {any} */ l, /** @type {number} */ i) => [i ? ', ' : '', link(l.id, l.label)]);
    return inline(c.text);
  };

  /** @param {string} tone @param {string} label @param {string} [title] */
  const statusMark = (tone, label, title) => h('span', { class: 'rd-status', 'data-tone': tone || 'none', title: title && title !== label ? title : null },
    h('span', { class: 'rd-status__glyph', 'aria-hidden': 'true' }), label);

  /** @param {{value: string, label: string, tone: string, count: number}[]} values @param {number} total @param {string} label */
  const bar = (values, total, label) => h('div', { class: 'rd-bar', role: 'img', 'aria-label': `${label}: ${values.map((v) => `${v.count} ${v.label}`).join(', ')}` },
    ...values.filter((v) => v.count > 0).map((v) => h('span', { class: 'rd-bar__seg', 'data-tone': v.tone, style: { flexGrow: String(v.count) }, title: `${v.label}: ${v.count} of ${total}` })));

  /** @param {any} b */
  const countsBlock = (b) => h('section', { class: 'rd-block' },
    b.title && h('h2', { class: 'rd-h2' }, b.title),
    bar(b.values, b.total, b.title || 'Counts'),
    h('ul', { class: 'rd-legend', role: 'list' }, ...b.values.map((/** @type {any} */ v) => h('li', {}, statusMark(v.tone, v.label), h('span', { class: 'rd-num' }, String(v.count))))),
    b.groups.length > 0 && h('ul', { class: 'rd-groupbars', role: 'list' }, ...b.groups.map((/** @type {any} */ g) => h('li', { class: 'rd-groupbar' },
      g.entity ? link(g.entity, g.label, 'rd-groupbar__label') : h('span', { class: 'rd-groupbar__label' }, g.label),
      bar(g.values, g.total, g.label),
      h('span', { class: 'rd-num rd-muted' }, String(g.total))))));

  /** Toolbar and grouped rows shared by table and list blocks. @param {any} b @param {number} n */
  const rowsBlock = (b, n) => {
    const st = stateOf();
    const key = `${n}`;
    const results = h('div', { class: 'rd-results' });
    const status = h('p', { class: 'rd-muted rd-count', role: 'status' });
    const facetKey = (/** @type {string} */ v) => `${key}:${v}`;
    const draw = () => {
      const q = st.q.trim().toLowerCase();
      const chosen = (b.facet?.values ?? []).filter((/** @type {any} */ v) => st.facets.has(facetKey(v.value))).map((/** @type {any} */ v) => v.value);
      let shown = 0;
      let rendered = 0;
      const groups = b.groups.map((/** @type {any} */ g) => {
        const rows = g.rows.filter((/** @type {any} */ r) => (st.showAll || !r.optional) && (!chosen.length || chosen.some((/** @type {string} */ v) => r.facets.includes(v))) && (!q || r.search.includes(q)));
        shown += rows.length;
        const room = Math.max(0, ROW_CAP - rendered);
        const visible = rows.slice(0, room);
        rendered += visible.length;
        if (!rows.length) return null;
        return h('div', { class: 'rd-group' },
          g.label && h('h3', { class: 'rd-h3' }, g.entity ? link(g.entity, g.label) : g.label, ' ', h('span', { class: 'rd-muted rd-num' }, String(rows.length))),
          b.type === 'table' ? table(b, visible) : list(visible));
      });
      clear(results);
      results.append(...groups.filter(Boolean));
      if (!shown) results.append(h('p', { class: 'rd-muted' }, 'Nothing matches.'));
      status.textContent = shown > rendered ? `${plural(shown, 'match', 'matches')}; the first ${ROW_CAP} are shown. Filter to see the rest.` : `${shown.toLocaleString()} of ${b.total.toLocaleString()} shown`;
    };
    const tools = h('div', { class: 'rd-tools' },
      b.facet && b.facet.values.length > 1 && h('div', { class: 'rd-facets', role: 'group', 'aria-label': b.facet.label },
        ...b.facet.values.map((/** @type {any} */ v) => {
          const btn = h('button', {
            type: 'button', class: 'rd-chip', 'aria-pressed': String(st.facets.has(facetKey(v.value))),
            onclick: () => {
              const k = facetKey(v.value);
              if (st.facets.has(k)) st.facets.delete(k); else st.facets.add(k);
              btn.setAttribute('aria-pressed', String(st.facets.has(k)));
              draw();
            },
          }, v.tone !== 'none' ? statusMark(v.tone, v.label) : v.label, h('span', { class: 'rd-num rd-muted' }, String(v.count)));
          return btn;
        })),
      b.toggle && h('label', { class: 'rd-check' },
        h('input', { type: 'checkbox', checked: st.showAll, onchange: (/** @type {Event} */ e) => { st.showAll = /** @type {HTMLInputElement} */ (e.target).checked; draw(); } }),
        b.toggle.label),
      b.search && h('input', {
        type: 'search', class: 'rd-search', placeholder: 'Filter', 'aria-label': `Filter ${b.title || b.kindLabel}`, value: st.q,
        oninput: (/** @type {Event} */ e) => { st.q = /** @type {HTMLInputElement} */ (e.target).value; draw(); },
      }),
      status);
    draw();
    return h('section', { class: 'rd-block' }, b.title && h('h2', { class: 'rd-h2' }, b.title), tools, results);
  };

  /** @param {any} b @param {any[]} rows */
  const table = (b, rows) => {
    const withRef = rows.some((r) => r.ref) && !b.columns.some((/** @type {any} */ c) => /^ref$/i.test(c.label));
    return h('div', { class: 'rd-table-wrap', role: 'region', tabindex: '0', 'aria-label': b.title || b.kindLabel },
      h('table', { class: 'rd-table' },
        h('thead', {}, h('tr', {}, withRef ? h('th', { scope: 'col' }, 'Ref') : null, ...b.columns.map((/** @type {any} */ c) => h('th', { scope: 'col' }, c.label)))),
        h('tbody', {}, ...rows.map((r) => h('tr', { 'data-selected': session.selection === r.id ? 'true' : null },
          withRef ? h('td', { class: 'rd-ref' }, link(r.id, r.ref)) : null,
          ...r.cells.map((/** @type {any} */ c, /** @type {number} */ i) => (i === 0 && !withRef
            ? h('th', { scope: 'row' }, link(r.id, c.text || r.id))
            : h('td', { class: c.status != null ? 'rd-nowrap' : null }, ...[cellContent(c)].flat()))))))));
  };

  /** @param {any[]} rows */
  const list = (rows) => h('ul', { class: 'rd-items', role: 'list' }, ...rows.map((r) => h('li', { class: 'rd-item', 'data-optional': r.optional ? 'true' : null, 'data-selected': session.selection === r.id ? 'true' : null },
    h('span', { class: 'rd-ref' }, r.ref),
    h('div', { class: 'rd-item__main' },
      h('p', { class: 'rd-item__title' }, link(r.id, r.title), r.status && r.status.tone !== 'none' ? h('span', { class: 'rd-item__status' }, statusMark(r.status.tone, r.status.label)) : null),
      r.body && prose(r.body),
      r.meta.length > 0 && h('p', { class: 'rd-meta' }, ...r.meta.map((/** @type {any} */ m) => h('span', {}, h('b', {}, `${m.label} `), ...(m.links.length ? m.links.flatMap((/** @type {any} */ l, /** @type {number} */ i) => [i ? ', ' : '', link(l.id, l.label)]) : inline(m.text)))))))));

  /** A section body: prose, inline tables, and entity rows. @param {any[]} blocks */
  const body = (blocks) => h('div', { class: 'rd-body' }, ...blocks.map((b) => {
    if (b.type === 'prose') return prose(b.text);
    if (b.type === 'entity') return h('p', { class: 'rd-entity' }, h('span', { class: 'rd-muted' }, `${b.kind} `), link(b.id, b.label));
    return h('div', { class: 'rd-table-wrap', role: 'region', tabindex: '0', 'aria-label': `Table ${b.id}` },
      h('table', { class: 'rd-table' },
        h('thead', {}, h('tr', {}, ...b.columns.map((/** @type {string} */ c) => h('th', { scope: 'col' }, ...inline(c))))),
        h('tbody', {}, ...b.rows.map((/** @type {any} */ r) => h('tr', { 'data-selected': session.selection === r.id ? 'true' : null },
          ...r.cells.map((/** @type {string} */ c, /** @type {number} */ i) => (i === 0 ? h('th', { scope: 'row' }, link(r.id, c || r.id)) : h('td', {}, ...inline(c)))))))));
  }));

  /** @param {any} b */
  const documentBlock = (b) => {
    const st = stateOf();
    if (!b.sections.length) return h('section', { class: 'rd-block' }, b.title && h('h2', { class: 'rd-h2' }, b.title), h('p', { class: 'rd-muted' }, 'The specification has no document sections.'));
    const current = b.sections.find((/** @type {any} */ s) => s.id === st.section) ?? b.sections[0];
    const article = h('article', { class: 'rd-article', 'aria-labelledby': 'rd-section-title' },
      h('h3', { class: 'rd-h2', id: 'rd-section-title' }, link(current.id, current.title)),
      body(sectionBlocks(session.model, current.id)));
    const nav = h('nav', { class: 'rd-outline', 'aria-label': b.document?.title ?? 'Outline' },
      h('ol', { role: 'list' }, ...b.sections.map((/** @type {any} */ s) => h('li', { style: { '--level': String(Math.max(0, s.level - 1)) } },
        h('button', {
          type: 'button', class: 'rd-outline__item', 'aria-current': s.id === current.id ? 'true' : null,
          onclick: () => { st.section = s.id; render(true); },
        }, s.title)))));
    return h('section', { class: 'rd-block' }, b.title && h('h2', { class: 'rd-h2' }, b.document?.title ?? b.title), h('div', { class: 'rd-doc' }, nav, article));
  };

  /** @param {any} b */
  const indexBlock = (b) => h('section', { class: 'rd-block' },
    b.title && h('h2', { class: 'rd-h2' }, b.title),
    h('ul', { class: 'rd-kinds', role: 'list' }, ...b.kinds.map((/** @type {any} */ k) => h('li', {},
      h('button', { type: 'button', class: 'rd-kind', onclick: () => { stateOf().kind = k.kind; render(true); } },
        h('span', {}, k.label), h('span', { class: 'rd-num rd-muted' }, k.count.toLocaleString()))))));

  /** @param {any} b @param {number} n */
  const block = (b, n) => {
    switch (b.type) {
      case 'text': return h('section', { class: 'rd-block' }, b.title && h('h2', { class: 'rd-h2' }, b.title), prose(b.text));
      case 'counts': return countsBlock(b);
      case 'table': case 'list': return rowsBlock(b, n);
      case 'document': return documentBlock(b);
      case 'sections': return h('div', { class: 'rd-block' }, b.title && h('h2', { class: 'rd-h2' }, b.title),
        ...b.sections.map((/** @type {any} */ s) => h('section', { class: 'rd-subsection' }, h('h3', { class: 'rd-h3' }, link(s.id, s.title)), body(s.blocks))));
      case 'index': return indexBlock(b);
      default: return null;
    }
  };

  /** @param {boolean} [toTop] */
  function render(toTop) {
    const on = active();
    host.hidden = !on;
    if (on) app.dataset.projection = 'reader'; else delete app.dataset.projection;
    if (!on) { shownKey = ''; return; }
    const model = session.model;
    if (model !== modelSeen) { refs = refIndex(model); modelSeen = model; }
    const st = stateOf();
    const viewEntity = model.entities.get(session.viewId);
    const view = viewEntity?.kind === 'view' ? { ...viewEntity.data, id: viewEntity.id } : { id: session.viewId, name: session.views.find((/** @type {any} */ v) => v.id === session.viewId)?.name ?? 'Reader' };
    if (st.kind && !model.byKind[st.kind]?.length) st.kind = null;
    const page = st.kind ? kindPage(model, st.kind) : readerPage(model, view);
    const key = `${session.projectName}/${session.viewId}/${st.kind ?? ''}`;
    const keep = key === shownKey && !toTop ? host.scrollTop : 0;
    shownKey = key;
    clear(host);
    host.append(h('div', { class: 'rd-page' },
      h('header', { class: 'rd-header' },
        st.kind && h('button', { type: 'button', class: 'rd-back', onclick: () => { st.kind = null; render(true); } }, `← ${view.name ?? 'Back'}`),
        h('h1', { class: 'rd-h1' }, page.title),
        page.description && h('p', { class: 'rd-lede' }, ...inline(page.description))),
      ...page.blocks.map((b, i) => block(b, i))));
    host.scrollTop = keep;
  }

  // Selection only moves the highlighted row; it never rebuilds the page.
  const markSelection = () => {
    if (host.hidden) return;
    for (const el of host.querySelectorAll('[aria-current="true"].rd-link')) el.removeAttribute('aria-current');
    for (const el of host.querySelectorAll('[data-selected="true"]')) el.removeAttribute('data-selected');
    if (!session.selection) return;
    for (const el of host.querySelectorAll(`.rd-link[data-entity="${CSS.escape(session.selection)}"]`)) {
      el.setAttribute('aria-current', 'true');
      el.closest('tr, .rd-item')?.setAttribute('data-selected', 'true');
    }
  };

  session.on('scene', () => render());
  session.on('project', () => render(true));
  session.on('selection', markSelection);
  render(true);
  return { render };
}
