// System explorer: filterable tree of components and flat lists of every other
// entity kind. Selection, visibility and isolate marks update without rebuilds.
// Sections come from the model (built-in kinds, then kinds the specification
// declares). Rows are built lazily: a closed section renders nothing until it is
// opened, and a list shows at most LIMIT matching rows.

import { h, clear, icon, shapeGlyph, lineSwatch, colorVar, revealInScroller } from './dom.js';
import { entityLabel, ancestorsOf } from '../core/query.js';
import { refLabel } from '../core/projections.js';
import { CLAIM_STATUSES } from '../core/claim-methods.js';

const SECTIONS = [
  ['component', 'Components'],
  ['relationship', 'Relationships'],
  ['contract', 'Contracts'],
  ['behavior', 'Behaviors'],
  ['scenario', 'Scenarios'],
  ['claim', 'Claims'],
  ['assumption', 'Assumptions'],
  ['evidence', 'Evidence'],
  ['view', 'Views'],
];

/** Neutral glyph shape per non-component kind. */
const KIND_SHAPE = { contract: 'tablet', behavior: 'capsule', scenario: 'sphere', claim: 'diamond', assumption: 'octa', evidence: 'pipe', view: 'container', event: 'capsule', fault: 'octa', environment: 'hex', failureMode: 'octa', faultModel: 'diamond' };

/** Most rows a list renders; more matches are reached by narrowing the filter. */
const LIMIT = 200;
/** Sections and groups with more matching rows than this start closed. */
const START_CLOSED_OVER = 60;
const NO_AREA = '(no area)';

/**
 * @param {HTMLElement} el
 * @param {any} session
 * @returns {() => void} dispose
 */
export function mountExplorer(el, session) {
  const state = {
    filter: '',
    /** @type {Set<string>} */ cats: new Set(),
    /** @type {Set<string>} */ closedSubs: new Set(),
    /** keys of sections / groups the user closed */
    /** @type {Set<string>} */ closedSections: new Set(),
    /** keys of large sections / groups the user opened */
    /** @type {Set<string>} */ openedSections: new Set(),
  };

  const input = h('input', {
    type: 'search', class: 'explorer__filter', placeholder: 'Filter', 'data-testid': 'explorer-filter',
    'aria-label': 'Filter entities by id, reference, name or statement', autocomplete: 'off', spellcheck: 'false',
    oninput: () => { state.filter = input.value; renderBody(); },
    onkeydown: (/** @type {KeyboardEvent} */ e) => {
      if (e.key === 'Escape' && input.value) { input.value = ''; state.filter = ''; renderBody(); e.stopPropagation(); }
      if (e.key === 'ArrowDown') { const r = rows()[0]; if (r) { e.preventDefault(); focusRow(r); } }
    },
  });
  const chips = h('div', { class: 'explorer__chips', role: 'group', 'aria-label': 'Filter components by category' });
  const body = h('div', { class: 'explorer__body' });
  clear(el);
  el.append(h('div', { class: 'explorer' }, h('div', { class: 'explorer__head' }, input, chips), body));

  /**
   * A section or group built on demand.
   * @typedef {Object} Rec
   * @property {string} key @property {HTMLDetailsElement} d @property {boolean} built
   * @property {() => void} open
   * @property {{items: any[], el: HTMLElement, make: (e: any, prev: any) => any, more: HTMLElement|null}|null} host
   */
  /** @type {Map<string, Rec>} rebuilt by every renderBody */
  let recs = new Map();
  let claimsGrouped = false;
  let building = false;

  // ---- helpers ----------------------------------------------------------------
  const rows = () => /** @type {HTMLElement[]} */ ([...body.querySelectorAll('.explorer__row')].filter((r) => /** @type {HTMLElement} */ (r).offsetParent !== null));
  /** @param {string} id */
  const rowFor = (id) => /** @type {HTMLElement|null} */ ([...body.querySelectorAll('.explorer__row')].find((r) => /** @type {HTMLElement} */ (r).dataset.entityId === id) ?? null);
  /** @param {HTMLElement} row */
  const focusRow = (row) => {
    for (const r of body.querySelectorAll('.explorer__row[tabindex="0"]')) r.setAttribute('tabindex', '-1');
    row.setAttribute('tabindex', '0');
    row.focus({ preventScroll: true });
  };
  const ensureRoving = () => {
    const all = rows();
    if (!all.length || all.some((r) => r.getAttribute('tabindex') === '0')) return;
    (all.find((r) => r.getAttribute('aria-selected') === 'true') ?? all[0]).setAttribute('tabindex', '0');
  };
  /** @param {string} id */
  const labelOf = (id) => { const e = session.model?.entities.get(id); return e ? entityLabel(e) : id; };

  // ---- category chips -------------------------------------------------------------
  const renderChips = () => {
    clear(chips);
    const model = session.model;
    if (!model) return;
    /** @type {string[]} */
    const present = [];
    for (const c of model.byKind.component ?? []) if (c.data.category && !present.includes(c.data.category)) present.push(c.data.category);
    for (const k of [...state.cats]) if (!present.includes(k)) state.cats.delete(k);
    for (const cat of present) {
      const meta = model.meta.categories?.[cat];
      const on = state.cats.has(cat);
      chips.append(h('button', {
        type: 'button', class: 'explorer__chip', 'aria-pressed': String(on), 'data-category': cat,
        title: `${on ? 'Stop filtering by' : 'Show only'} ${meta?.label ?? cat}${meta?.description ? ': ' + meta.description : ''}`,
        onclick: () => { if (state.cats.has(cat)) state.cats.delete(cat); else state.cats.add(cat); renderChips(); renderBody(); },
      }, h('span', { class: 'explorer__dot', style: { background: colorVar(meta?.color) }, 'aria-hidden': 'true' }), meta?.label ?? cat));
    }
  };

  // ---- body -----------------------------------------------------------------------
  /**
   * @param {any} e entity @param {number} level
   * @param {{glyph: Node, expandable?: boolean, expanded?: boolean, name?: string, tail?: any[], actions?: any[], title?: string, flags?: any[], extraClass?: string}} o
   */
  const makeRow = (e, level, o) => {
    const selected = session.selection === e.id;
    const name = o.name ?? entityLabel(e);
    return h('div', {
      class: ['explorer__row', selected ? 'explorer__row--selected' : null, o.extraClass],
      role: 'treeitem', tabindex: '-1', 'data-entity-id': e.id, 'data-kind': e.kind,
      'aria-level': String(level), 'aria-selected': String(selected), 'aria-expanded': o.expandable ? String(!!o.expanded) : null,
      title: o.title ?? `${name}  (${e.id})`, style: { '--depth': level - 1 },
    },
    o.expandable
      ? h('span', { class: 'explorer__twist', 'data-action': 'disclose', 'aria-hidden': 'true' }, icon(o.expanded ? 'chevron-down' : 'chevron-right', 12))
      : h('span', { class: 'explorer__twist explorer__twist--none', 'aria-hidden': 'true' }),
    o.glyph,
    h('span', { class: 'explorer__name' }, name),
    ...(o.flags ?? []),
    h('span', { class: 'explorer__id' }, e.id),
    ...(o.tail ?? []),
    o.actions ? h('span', { class: 'explorer__actions' }, ...o.actions) : null);
  };

  /** @param {string} action @param {string} iconA @param {string|null} iconB @param {string} nm */
  const actionBtn = (action, iconA, iconB, nm) => h('button', {
    type: 'button', class: 'explorer__act', 'data-action': action, tabindex: '-1', 'aria-pressed': 'false', 'aria-label': nm, title: nm,
  }, h('span', { class: 'explorer__ico explorer__ico--off' }, icon(iconA, 12)), iconB ? h('span', { class: 'explorer__ico explorer__ico--on' }, icon(iconB, 12)) : null);

  /** The "showing N of M" row at the end of a truncated list. @param {number} n */
  const moreRow = (n) => h('button', {
    type: 'button', class: 'explorer__more', 'data-testid': 'explorer-more',
    title: 'Focus the filter',
    onclick: () => input.focus({ preventScroll: true }),
  }, `Showing ${LIMIT} of ${n} — type in the filter to narrow`);

  /**
   * A collapsible section or group whose rows are built the first time it is open.
   * @param {{key: string, group?: boolean, title: string, count: string, countTitle: string, big: boolean, fill: (body: HTMLElement, rec: Rec) => void}} o
   */
  const makeDetails = (o) => {
    const open = state.closedSections.has(o.key) ? false : (o.big ? state.openedSections.has(o.key) : true);
    const list = h('div', { class: o.group ? 'explorer__sublist' : 'explorer__list', ...(o.group ? {} : { role: 'tree', 'aria-label': o.title }) });
    /** @type {Rec} */
    const rec = { key: o.key, d: /** @type {any} */ (null), built: false, host: null, open: () => {} };
    const ensure = () => {
      if (rec.built) return;
      rec.built = true;
      o.fill(list, rec);
      if (!building) { updateMarks(); ensureRoving(); }
    };
    const d = /** @type {HTMLDetailsElement} */ (h('details', {
      class: o.group ? 'explorer__subgroup' : 'explorer__section', open, [o.group ? 'data-group' : 'data-section']: o.key,
      ontoggle: () => {
        if (d.open) { state.closedSections.delete(o.key); if (o.big) state.openedSections.add(o.key); ensure(); }
        else { state.closedSections.add(o.key); state.openedSections.delete(o.key); }
      },
    },
    h('summary', { class: o.group ? 'explorer__summary explorer__subsummary' : 'explorer__summary' },
      h('span', { class: 'explorer__caret', 'aria-hidden': 'true' }, icon('chevron-right', 12)),
      h('span', { class: 'explorer__section-title' }, o.title),
      h('span', { class: 'explorer__count', title: o.countTitle }, o.count)),
    list));
    rec.d = d;
    rec.open = () => { if (!d.open) d.open = true; state.closedSections.delete(o.key); if (o.big) state.openedSections.add(o.key); ensure(); };
    recs.set(o.key, rec);
    if (open) ensure();
    return d;
  };

  /**
   * Fill a body with at most LIMIT rows of `items` and a "showing" row when more match.
   * @param {HTMLElement} listEl @param {Rec} rec @param {any[]} items @param {(e: any, prev: any) => any} make
   */
  const fillLimited = (listEl, rec, items, make) => {
    /** @type {NonNullable<Rec['host']>} */
    const host = { items, el: listEl, make, more: null };
    rec.host = host;
    /** @type {any} */
    let prev = null;
    for (const e of items.slice(0, LIMIT)) { listEl.append(...[].concat(make(e, prev))); prev = e; }
    if (items.length > LIMIT) { host.more = moreRow(items.length); listEl.append(host.more); }
  };

  const renderBody = () => {
    const model = session.model;
    const scrollTop = body.scrollTop;
    const hadFocus = body.contains(document.activeElement) ? /** @type {HTMLElement} */ (document.activeElement)?.dataset?.entityId ?? null : null;
    clear(body);
    recs = new Map();
    claimsGrouped = false;
    if (!model) {
      body.append(h('p', { class: 'explorer__empty' }, 'No valid model. The source has syntax errors; fix them in the Source tab.'));
      return;
    }
    building = true;
    const q = state.filter.trim().toLowerCase();
    const filtering = !!q || state.cats.size > 0;
    /** @param {any} e @param {...string} extra */
    const textMatch = (e, ...extra) => !q || [e.id, e.data?.ref, e.data?.name, e.data?.statement, ...extra].some((v) => typeof v === 'string' && v.toLowerCase().includes(q));

    const violated = new Set();
    for (const r of session.claimResults ?? []) if (r.status === 'violated') for (const id of r.involved ?? []) violated.add(id);
    const hiddenSet = session.ui?.hidden ?? new Set();
    const stateCounts = new Map();
    for (const s of model.byKind.state ?? []) stateCounts.set(s.owner, (stateCounts.get(s.owner) ?? 0) + 1);

    // Built-in sections first, then one per kind the specification declares.
    const known = new Set(SECTIONS.map(([k]) => k));
    /** @type {[string, string][]} */
    const sections = [...SECTIONS];
    // Every kind with a top-level section of its own (events, faults, fault models, ...) is listed.
    const topLevel = new Set(Object.values(model.meta.sections ?? {}).map((/** @type {any} */ s) => s.entity).filter(Boolean));
    for (const [k, def] of Object.entries(model.meta.entities ?? {})) {
      if (k === 'system' || !(/** @type {any} */ (def).declared || topLevel.has(k)) || known.has(k) || !(model.byKind[k] ?? []).length) continue;
      sections.push([k, `${/** @type {any} */ (def).label ?? k}s`]);
    }

    /** @type {HTMLElement[]} */
    const sectionEls = [];

    for (const [kind, title] of sections) {
      const all = model.byKind[kind] ?? [];
      if (!all.length) continue;
      const declaredMeta = model.meta.entities?.[kind]?.declared ? model.meta.entities[kind] : null;
      let matched = 0;
      /** @type {(listEl: HTMLElement, rec: Rec) => void} */
      let fill;

      if (kind === 'component') {
        const byParent = new Map();
        for (const c of all) { const k = c.data.parent ?? null; if (!byParent.has(k)) byParent.set(k, []); byParent.get(k).push(c); }
        const passes = (/** @type {any} */ c) => textMatch(c) && (!state.cats.size || state.cats.has(c.data.category));
        const visible = new Set();
        const mark = (/** @type {any} */ c, /** @type {Set<string>} */ seen) => {
          if (seen.has(c.id)) return false;
          seen.add(c.id);
          let any = passes(c);
          if (any) matched++;
          for (const k of byParent.get(c.id) ?? []) if (mark(k, seen)) any = true;
          if (any) visible.add(c.id);
          return any;
        };
        const seen = new Set();
        for (const r of byParent.get(null) ?? []) mark(r, seen);
        fill = (listEl) => {
          const walk = (/** @type {any} */ c, /** @type {number} */ level, /** @type {Set<string>} */ path) => {
            if (!visible.has(c.id) || path.has(c.id)) return;
            const kids = (byParent.get(c.id) ?? []).filter((/** @type {any} */ k) => visible.has(k.id));
            const isSub = c.data.kind === 'subsystem' || (byParent.get(c.id) ?? []).length > 0;
            const expanded = isSub && (filtering ? true : !state.closedSubs.has(c.id));
            const cat = model.meta.categories?.[c.data.category];
            const actions = [
              actionBtn('visibility', 'eye', 'eye-off', `Hide ${entityLabel(c)} in the scene`),
            ];
            if (isSub) {
              actions.push(actionBtn('collapse', 'collapse', null, `Collapse ${entityLabel(c)} in the scene`));
              actions.push(actionBtn('isolate', 'isolate', null, `Isolate ${entityLabel(c)}`));
            }
            const flags = [];
            if (c.data.illustrative) flags.push(h('span', { class: 'explorer__tag', title: 'Illustrative: an example, not a statement about a real system' }, 'illustrative'));
            if (violated.has(c.id)) flags.push(h('span', { class: 'explorer__flag', role: 'img', 'aria-label': 'Involved in a violated claim', title: 'Involved in a violated claim' }));
            listEl.append(makeRow(c, level, {
              glyph: shapeGlyph(isSub ? 'container' : cat?.shape, cat?.color), expandable: isSub, expanded,
              flags, actions, extraClass: hiddenSet.has(c.id) ? 'explorer__row--hidden' : null,
              title: `${entityLabel(c)}  (${c.id})${cat ? ' - ' + cat.label : ''}`,
            }));
            if (expanded) {
              const nextPath = new Set(path); nextPath.add(c.id);
              for (const k of kids) walk(k, level + 1, nextPath);
            }
          };
          for (const r of byParent.get(null) ?? []) walk(r, 1, new Set());
        };
      } else if (kind === 'relationship') {
        const items = all.filter((r) => textMatch(r, labelOf(r.data.from), labelOf(r.data.to), r.data.from, r.data.to));
        matched = items.length;
        // Keep relationships of one kind together under a group header.
        /** @type {Map<string, any[]>} */
        const groups = new Map();
        for (const r of items) { if (!groups.has(r.data.kind)) groups.set(r.data.kind, []); /** @type {any[]} */ (groups.get(r.data.kind)).push(r); }
        const ordered = [...groups.values()].flat();
        fill = (listEl, rec) => fillLimited(listEl, rec, ordered, (/** @type {any} */ r, /** @type {any} */ prev) => {
          const meta = model.meta.relationshipKinds?.[r.data.kind];
          const out = [];
          if (!prev || prev.data.kind !== r.data.kind) {
            out.push(h('div', { class: 'explorer__group', role: 'presentation' },
              lineSwatch(meta?.line, meta?.color, { arrow: true }),
              h('span', { class: 'explorer__group-name' }, meta?.label ?? r.data.kind),
              h('span', { class: 'explorer__count' }, String(groups.get(r.data.kind)?.length ?? 0))));
          }
          out.push(makeRow(r, 1, {
            glyph: lineSwatch(meta?.line, meta?.color, { arrow: true, width: 18 }), name: `${labelOf(r.data.from)} → ${labelOf(r.data.to)}`,
            title: `${r.data.from} → ${r.data.to}  (${r.id})`,
          }));
          return out;
        });
      } else {
        const items = all.filter((e) => textMatch(e));
        matched = items.length;
        /** One row of a generic list. @param {any} e */
        const make = (e) => {
          /** @type {any[]} */ const tail = [];
          let glyph = declaredMeta ? shapeGlyph(declaredMeta.shape, declaredMeta.color) : shapeGlyph(/** @type {any} */ (KIND_SHAPE)[kind], 'neutral');
          const nm = refLabel(e);
          let rowTitle;
          if (kind === 'behavior') {
            const n = stateCounts.get(e.id) ?? (Array.isArray(e.data.states) ? e.data.states.length : 0);
            tail.push(h('span', { class: 'explorer__meta' }, `${n} state${n === 1 ? '' : 's'}`));
          } else if (kind === 'claim') {
            const res = session.claimResult?.(e.id);
            const st = res?.status ?? 'not-evaluated';
            const def = /** @type {any} */ (CLAIM_STATUSES)[st] ?? CLAIM_STATUSES['not-evaluated'];
            tail.push(h('span', { class: ['explorer__status', `explorer__status--${def.tone}`], title: def.label },
              h('span', { class: 'explorer__dot', 'aria-hidden': 'true' }), st.replace('-', ' ')));
            glyph = shapeGlyph('diamond', 'neutral');
            rowTitle = `${nm}  (${e.id}) - ${def.label}`;
          } else if (kind === 'view') {
            rowTitle = `${nm}  (${e.id}) - double-click to switch to this view`;
          }
          return makeRow(e, 1, { glyph, tail, name: nm, title: rowTitle });
        };
        /** @param {any} e */
        const areaOf = (e) => (typeof e.data.area === 'string' && e.data.area ? e.data.area : null);
        if (kind === 'claim' && all.some(areaOf)) {
          claimsGrouped = true;
          /** @type {Map<string, any[]>} */
          const byArea = new Map();
          for (const e of items) { const a = areaOf(e) ?? NO_AREA; if (!byArea.has(a)) byArea.set(a, []); /** @type {any[]} */ (byArea.get(a)).push(e); }
          const names = [...byArea.keys()].sort((a, b) => (a === NO_AREA ? 1 : b === NO_AREA ? -1 : a.localeCompare(b)));
          fill = (listEl) => {
            for (const a of names) {
              const list = /** @type {any[]} */ (byArea.get(a));
              listEl.append(makeDetails({
                key: `claim::${a}`, group: true, title: a, count: String(list.length), countTitle: `${list.length} claims`,
                big: list.length > START_CLOSED_OVER,
                fill: (sub, rec) => fillLimited(sub, rec, list, make),
              }));
            }
          };
        } else {
          fill = (listEl, rec) => fillLimited(listEl, rec, items, make);
        }
      }

      if (!matched) continue;
      const total = all.length;
      sectionEls.push(makeDetails({
        key: kind, title, count: filtering ? `${matched}/${total}` : String(total), countTitle: filtering ? `${matched} of ${total} match` : `${total} total`,
        big: matched > START_CLOSED_OVER, fill,
      }));
    }

    if (!sectionEls.length) {
      body.append(h('p', { class: 'explorer__empty' }, filtering ? 'No entity matches the filter.' : 'This specification declares no entities.'));
    } else {
      body.append(...sectionEls);
    }
    building = false;
    body.scrollTop = scrollTop;
    updateMarks();
    ensureRoving();
    if (hadFocus) { const r = rowFor(hadFocus); if (r) focusRow(r); }
  };

  /** Visibility / collapse / isolate marks, without rebuilding. */
  const updateMarks = () => {
    const ui = session.ui ?? {};
    for (const row of /** @type {NodeListOf<HTMLElement>} */ (body.querySelectorAll('.explorer__row[data-kind="component"]'))) {
      const id = /** @type {string} */ (row.dataset.entityId);
      const name = row.querySelector('.explorer__name')?.textContent ?? id;
      const hidden = ui.hidden?.has(id) ?? false;
      row.classList.toggle('explorer__row--hidden', hidden);
      const set = (/** @type {string} */ action, /** @type {boolean} */ pressed, /** @type {string} */ on, /** @type {string} */ off) => {
        const b = row.querySelector(`[data-action="${action}"]`);
        if (!b) return;
        b.setAttribute('aria-pressed', String(pressed));
        b.setAttribute('aria-label', pressed ? on : off);
        b.setAttribute('title', pressed ? on : off);
      };
      set('visibility', hidden, `Show ${name} in the scene`, `Hide ${name} in the scene`);
      set('collapse', ui.collapsed?.has(id) ?? false, `Expand ${name} in the scene`, `Collapse ${name} in the scene`);
      set('isolate', ui.isolate === id, `Stop isolating ${name}`, `Isolate ${name}`);
      row.classList.toggle('explorer__row--isolated', ui.isolate === id);
    }
  };

  /**
   * Make the row of an entity exist: open its section (and group) and, when it is
   * beyond the rendered window of a truncated list, insert it.
   * @param {string} id @returns {HTMLElement|null}
   */
  const reveal = (id) => {
    const model = session.model;
    const e = model?.entities.get(id);
    if (!model || !e) return null;
    let target = rowFor(id);
    if (target) return target;
    if (e.kind === 'component') {
      // selected elsewhere inside a closed subsystem: open the path to it
      let changed = false;
      for (const a of ancestorsOf(model, id)) if (state.closedSubs.delete(a)) changed = true;
      if (changed) renderBody();
    }
    const section = recs.get(e.kind);
    if (!section) return rowFor(id);
    section.open();
    let leaf = section;
    if (claimsGrouped && e.kind === 'claim') {
      const g = recs.get(`claim::${typeof e.data.area === 'string' && e.data.area ? e.data.area : NO_AREA}`);
      if (g) { g.open(); leaf = g; }
    }
    target = rowFor(id);
    const host = leaf.host;
    if (!target && host && host.items.includes(e)) {
      const made = [].concat(host.make(e, e));
      const row = /** @type {HTMLElement} */ (made[made.length - 1]);
      host.el.insertBefore(row, host.more);
      target = row;
    }
    return target;
  };

  const updateSelection = () => {
    const sel = session.selection;
    const target = sel ? reveal(sel) : null;
    for (const r of body.querySelectorAll('.explorer__row')) {
      const on = !!sel && /** @type {HTMLElement} */ (r).dataset.entityId === sel;
      r.setAttribute('aria-selected', String(on));
      r.classList.toggle('explorer__row--selected', on);
    }
    if (target) {
      for (const r of body.querySelectorAll('.explorer__row[tabindex="0"]')) r.setAttribute('tabindex', '-1');
      target.setAttribute('tabindex', '0');
      revealInScroller(target);
    } else ensureRoving();
  };

  // ---- interaction (delegated) ---------------------------------------------------------
  /** @param {HTMLElement} row */
  const toggleOpen = (row, open) => {
    const id = /** @type {string} */ (row.dataset.entityId);
    const isOpen = row.getAttribute('aria-expanded') === 'true';
    if (open === isOpen) return;
    if (open) state.closedSubs.delete(id); else state.closedSubs.add(id);
    renderBody();
    const r = rowFor(id);
    if (r) focusRow(r);
  };
  /** @param {HTMLElement} row @param {string} action */
  const runAction = (row, action) => {
    const id = /** @type {string} */ (row.dataset.entityId);
    if (action === 'disclose') toggleOpen(row, row.getAttribute('aria-expanded') !== 'true');
    else if (action === 'visibility') session.setHidden(id, !(session.ui?.hidden?.has(id)));
    else if (action === 'collapse') session.toggleCollapsed(id);
    else if (action === 'isolate') session.setIsolate(session.ui?.isolate === id ? null : id);
  };
  body.addEventListener('click', (e) => {
    const t = /** @type {HTMLElement} */ (e.target);
    const row = /** @type {HTMLElement|null} */ (t.closest('.explorer__row'));
    if (!row) return;
    const act = /** @type {HTMLElement|null} */ (t.closest('[data-action]'));
    if (act && row.contains(act)) { runAction(row, /** @type {string} */ (act.dataset.action)); return; }
    row.setAttribute('tabindex', '0');
    session.select(row.dataset.entityId, { source: 'explorer' });
  });
  body.addEventListener('dblclick', (e) => {
    const t = /** @type {HTMLElement} */ (e.target);
    const row = /** @type {HTMLElement|null} */ (t.closest('.explorer__row'));
    if (!row || t.closest('[data-action]')) return;
    const id = /** @type {string} */ (row.dataset.entityId);
    if (row.dataset.kind === 'view') session.setView(id);
    else session.requestFit([id]);
  });
  body.addEventListener('focusin', (e) => {
    const row = /** @type {HTMLElement|null} */ (/** @type {HTMLElement} */ (e.target).closest?.('.explorer__row'));
    if (!row) return;
    for (const r of body.querySelectorAll('.explorer__row[tabindex="0"]')) if (r !== row) r.setAttribute('tabindex', '-1');
    row.setAttribute('tabindex', '0');
  });
  body.addEventListener('keydown', (e) => {
    const t = /** @type {HTMLElement} */ (e.target);
    const row = /** @type {HTMLElement|null} */ (t.closest('.explorer__row'));
    if (!row || e.altKey || e.ctrlKey || e.metaKey) return;
    const all = rows();
    const i = all.indexOf(row);
    const expanded = row.getAttribute('aria-expanded');
    const id = /** @type {string} */ (row.dataset.entityId);
    switch (e.key) {
      case 'ArrowDown': e.preventDefault(); if (all[i + 1]) focusRow(all[i + 1]); break;
      case 'ArrowUp': e.preventDefault(); if (i > 0) focusRow(all[i - 1]); else input.focus({ preventScroll: true }); break;
      case 'Home': e.preventDefault(); focusRow(all[0]); break;
      case 'End': e.preventDefault(); focusRow(all[all.length - 1]); break;
      case 'ArrowRight':
        e.preventDefault();
        if (expanded === 'false') toggleOpen(row, true);
        else if (expanded === 'true' && all[i + 1]) focusRow(all[i + 1]);
        break;
      case 'ArrowLeft': {
        e.preventDefault();
        if (expanded === 'true' && !state.filter && !state.cats.size) { toggleOpen(row, false); break; }
        const level = Number(row.getAttribute('aria-level'));
        for (let j = i - 1; j >= 0; j--) if (Number(all[j].getAttribute('aria-level')) < level) { focusRow(all[j]); break; }
        break;
      }
      case 'Enter': case ' ':
        if (t !== row) return; // let focused action buttons handle their own activation
        e.preventDefault();
        session.select(id, { source: 'explorer' });
        break;
      case 'v': case 'V':
        if (row.dataset.kind === 'component') { e.preventDefault(); runAction(row, 'visibility'); }
        break;
      case 'c': case 'C':
        if (row.querySelector('[data-action="collapse"]')) { e.preventDefault(); runAction(row, 'collapse'); }
        break;
      case 'i': case 'I':
        if (row.querySelector('[data-action="isolate"]')) { e.preventDefault(); runAction(row, 'isolate'); }
        break;
      default:
    }
  });

  // ---- wiring ----------------------------------------------------------------------------
  const rebuild = () => { renderChips(); renderBody(); };
  const offs = [
    session.on('project', rebuild),
    session.on('model', rebuild),
    session.on('claims', renderBody),
    session.on('selection', updateSelection),
    session.on('ui', updateMarks),
  ];
  rebuild();
  return () => { for (const off of offs) off(); };
}
