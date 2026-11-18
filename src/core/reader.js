// Reader pages: turn a view of the reader projection into plain page data (blocks of
// text, counts, tables, lists and document sections) for a 2D reading surface. Pure:
// every value comes from the model and the view's `reader.blocks`; nothing here knows
// any particular specification.

import { own } from './own.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */

export const BLOCK_TYPES = ['text', 'counts', 'table', 'list', 'document', 'sections', 'index'];
export const TONES = ['done', 'partial', 'todo', 'open', 'danger', 'none'];

/** Rows a table or list renders before asking for a filter. */
export const ROW_CAP = 300;

const TITLE_KEYS = ['name', 'title', 'term', 'question', 'statement', 'summary', 'label', 'text', 'description'];
const SKIP_COLUMNS = new Set(['id', 'source', 'sourceColumn', 'citations', 'mentions', 'table', 'idColumn', 'path', 'commit', 'body']);
const MARKER = /^\{\{entity:([^}]+)\}\}$/;

/** @param {unknown} v @returns {string} */
export function textOf(v) {
  if (v == null) return '';
  if (Array.isArray(v)) return v.map(textOf).filter(Boolean).join(', ');
  if (typeof v === 'object') return JSON.stringify(v);
  return String(v);
}

/** @param {string} s @param {number} [max] */
function clip(s, max = 160) {
  const t = s.replace(/\s+/g, ' ').trim();
  return t.length > max ? `${t.slice(0, max - 1)}…` : t;
}

/**
 * Short title of any entity: a table row's cells, else the first text-like property, else its id.
 * @param {Model} model @param {Entity|undefined} e
 */
export function titleOf(model, e) {
  if (!e) return '';
  const d = e.data ?? {};
  if (Array.isArray(d.cells)) return clip(d.cells.filter(Boolean).join(' · '));
  for (const k of TITLE_KEYS) if (typeof d[k] === 'string' && d[k].trim()) return clip(d[k]);
  const props = own(model.meta.entities, e.kind)?.properties ?? {};
  for (const [k, p] of Object.entries(props)) {
    if (SKIP_COLUMNS.has(k) || k === 'ref') continue;
    if ((p.type === 'text' || p.type === 'string') && typeof d[k] === 'string' && d[k].trim()) return clip(d[k]);
  }
  return e.id;
}

/** @param {Model} model @param {string} kind */
export function kindLabel(model, kind) {
  return own(model.meta.entities, kind)?.label ?? kind;
}

/**
 * The ids a property of a kind refers to, when its meta-model type is a reference.
 * @param {Model} model @param {string} kind @param {string} prop @param {unknown} value
 * @returns {string[]}
 */
function refIds(model, kind, prop, value) {
  const def = own(model.meta.entities, kind)?.properties?.[prop];
  const isRef = def?.type === 'ref' || (def?.type === 'list' && def.items?.type === 'ref');
  const list = Array.isArray(value) ? value : [value];
  return list.filter((x) => typeof x === 'string' && (isRef || model.entities.has(x)) && model.entities.has(x));
}

/**
 * Follow a dotted path through references and nested objects: "table.section" reads
 * `table`, opens that entity, then reads its `section`; "evaluate.method" reads into an
 * object. Returns the entity the path ends on, or the raw value.
 * @param {Model} model @param {Entity} e @param {string} path
 * @returns {{entity?: Entity, value?: unknown}}
 */
export function resolvePath(model, e, path) {
  /** @type {any} */
  let holder = e.data;
  /** @type {unknown} */
  let value;
  /** @type {Entity|undefined} */
  let cur;
  for (const seg of path.split('.')) {
    if (holder == null || typeof holder !== 'object') return {};
    value = holder[seg];
    cur = typeof value === 'string' ? model.entities.get(value) : undefined;
    holder = cur ? cur.data : value;
  }
  return cur ? { entity: cur } : { value };
}

/**
 * The text of a property, or of a dotted path (an entity at the end reads as its title).
 * @param {Model} model @param {Entity} e @param {string|undefined} prop
 */
function read(model, e, prop) {
  if (!prop) return '';
  if (!prop.includes('.')) return textOf(e.data?.[prop]);
  const r = resolvePath(model, e, prop);
  return r.entity ? titleOf(model, r.entity) : textOf(r.value);
}

/**
 * The first rule whose pattern matches the text, or the text itself as its own value.
 * @param {string} text @param {any[]|undefined} rules
 * @returns {{value: string, label: string, tone: string}}
 */
export function classify(text, rules) {
  if (Array.isArray(rules) && rules.length) {
    for (const r of rules) {
      let re;
      try { re = new RegExp(String(r.pattern), 'i'); } catch { continue; }
      if (re.test(text)) return { value: String(r.value), label: String(r.label ?? r.value), tone: TONES.includes(r.tone) ? r.tone : 'none' };
    }
    return { value: '', label: 'Other', tone: 'none' };
  }
  return { value: text, label: text || 'Not set', tone: 'none' };
}

/**
 * Whether an entity passes a block's `where` conditions (all must hold); a property may be a dotted path.
 * @param {Model} model @param {Entity} e @param {any[]|undefined} where
 */
function passes(model, e, where) {
  for (const w of where ?? []) {
    const raw = String(w.property).includes('.') ? undefined : e.data?.[w.property];
    const text = read(model, e, w.property);
    const set = raw === undefined ? text !== '' : raw != null && raw !== '' && !(Array.isArray(raw) && raw.length === 0);
    if (w.set === true && !set) return false;
    if (w.set === false && set) return false;
    if (w.equals != null && text !== String(w.equals)) return false;
    if (w.matches != null) {
      let re;
      try { re = new RegExp(String(w.matches), 'i'); } catch { return false; }
      if (!re.test(text)) return false;
    }
  }
  return true;
}

/** @param {Model} model @param {any} block @returns {Entity[]} */
function entitiesFor(model, block) {
  return (model.byKind[block.kind] ?? []).filter((e) => passes(model, e, block.where));
}

/**
 * One cell: its text and the entities it refers to.
 * @param {Model} model @param {Entity} e @param {any} col @param {any[]|undefined} rules
 */
function cell(model, e, col, rules) {
  const raw = e.data?.[col.property];
  const text = read(model, e, col.property);
  if (col.status) {
    const c = classify(text, rules);
    return { text: c.label, status: c.value, tone: c.tone, title: text };
  }
  const ids = refIds(model, e.kind, col.property, raw);
  return ids.length ? { text, links: ids.map((id) => ({ id, label: titleOf(model, model.entities.get(id)) })) } : { text };
}

/**
 * Group entities by a dotted path; groups keep the order their first member appears in.
 * @param {Model} model @param {Entity[]} list @param {string|undefined} groupBy
 */
function groupsOf(model, list, groupBy) {
  if (!groupBy) return [{ key: '', label: '', entity: null, items: list }];
  /** @type {Map<string, {key: string, label: string, entity: string|null, items: Entity[]}>} */
  const groups = new Map();
  for (const e of list) {
    const r = resolvePath(model, e, groupBy);
    const key = r.entity ? r.entity.id : textOf(r.value);
    let g = groups.get(key);
    if (!g) groups.set(key, (g = { key, label: r.entity ? titleOf(model, r.entity) : key || 'Not set', entity: r.entity?.id ?? null, items: [] }));
    g.items.push(e);
  }
  // Groups that are entities read in declaration order; plain values keep first appearance.
  const order = new Map([...model.entities.keys()].map((id, i) => [id, i]));
  return [...groups.values()].sort((a, b) => (a.entity && b.entity ? (order.get(a.entity) ?? 0) - (order.get(b.entity) ?? 0) : 0));
}

/** @param {Model} model @param {string} kind */
function autoColumns(model, kind) {
  const props = own(model.meta.entities, kind)?.properties ?? {};
  const cols = [];
  if (props.ref) cols.push({ property: 'ref', label: 'Ref' });
  for (const [k, p] of Object.entries(props)) {
    if (SKIP_COLUMNS.has(k) || k === 'ref') continue;
    if (!['text', 'string', 'enum', 'ref', 'number', 'boolean'].includes(p.type)) continue;
    cols.push({ property: k, label: p.label ?? k });
    if (cols.length >= 5) break;
  }
  return cols;
}

/** @param {Model} model @param {any} block */
function counts(model, block) {
  const list = entitiesFor(model, block);
  /** @param {Entity[]} items */
  const tally = (items) => {
    /** @type {Map<string, {value: string, label: string, tone: string, count: number}>} */
    const m = new Map();
    for (const r of block.classify ?? []) m.set(String(r.value), { value: String(r.value), label: String(r.label ?? r.value), tone: TONES.includes(r.tone) ? r.tone : 'none', count: 0 });
    for (const e of items) {
      const c = classify(read(model, e, block.property), block.classify);
      const slot = m.get(c.value) ?? { ...c, count: 0 };
      slot.count++;
      m.set(c.value, slot);
    }
    return [...m.values()].filter((v) => v.count > 0 || (block.classify ?? []).length);
  };
  return {
    type: 'counts', title: block.title ?? '', total: list.length, values: tally(list),
    groups: block.groupBy ? groupsOf(model, list, block.groupBy).map((g) => ({ label: g.label, entity: g.entity, total: g.items.length, values: tally(g.items) })) : [],
  };
}

/** @param {Model} model @param {any} block @param {'table'|'list'} type */
function rows(model, block, type) {
  const list = entitiesFor(model, block);
  const columns = block.columns?.length ? block.columns : autoColumns(model, block.kind);
  const facetValues = new Map();
  // The status property is classified; a facet on it uses the same rules.
  const statusProp = block.statusProperty ?? columns.find((/** @type {any} */ c) => c.status)?.property;
  const facetRules = block.facet && block.facet === statusProp ? block.classify : undefined;
  const make = (/** @type {Entity} */ e) => {
    // A separator splits one text into several facet values ("Decision, Build").
    const facetTexts = block.facet ? (block.facetSeparator ? read(model, e, block.facet).split(block.facetSeparator).map((s) => s.trim()).filter(Boolean) : [read(model, e, block.facet)]) : [];
    const facets = facetTexts.map((s) => classify(s, facetRules));
    for (const facet of facets) {
      const f = facetValues.get(facet.value) ?? { value: facet.value, label: facet.label, tone: facet.tone, count: 0 };
      f.count++;
      facetValues.set(facet.value, f);
    }
    const hideSet = block.hideWhenSet ? passes(model, e, [{ property: block.hideWhenSet, set: true }]) : false;
    const base = { id: e.id, ref: typeof e.data?.ref === 'string' ? e.data.ref : '', facets: [...new Set(facets.map((f) => f.value))], optional: hideSet };
    if (type === 'table') {
      const cells = columns.map((/** @type {any} */ c) => cell(model, e, c, block.classify));
      return { ...base, cells, search: [base.ref, ...cells.map((c) => c.text)].join(' ').toLowerCase() };
    }
    const title = read(model, e, block.titleProperty) || titleOf(model, e);
    const body = read(model, e, block.bodyProperty);
    const meta = (block.metaProperties ?? []).map((/** @type {string} */ p) => {
      const ids = refIds(model, e.kind, p, e.data?.[p]);
      const label = own(model.meta.entities, e.kind)?.properties?.[p]?.label ?? p;
      return { label, text: read(model, e, p), links: ids.map((id) => ({ id, label: titleOf(model, model.entities.get(id)) })) };
    }).filter((/** @type {any} */ m) => m.text);
    const status = block.statusProperty ? classify(read(model, e, block.statusProperty), block.classify) : null;
    return { ...base, title, body, meta, status, search: [base.ref, title, body, ...meta.map((/** @type {any} */ m) => m.text)].join(' ').toLowerCase() };
  };
  const groups = groupsOf(model, list, block.groupBy).map((g) => ({ key: g.key, label: g.label, entity: g.entity, rows: g.items.map(make) }));
  return {
    type, title: block.title ?? '', kind: block.kind, kindLabel: kindLabel(model, block.kind),
    columns: type === 'table' ? columns.map((/** @type {any} */ c) => ({ label: c.label ?? c.property, status: !!c.status })) : [],
    facet: block.facet ? { label: block.facetLabel ?? own(model.meta.entities, block.kind)?.properties?.[block.facet]?.label ?? block.facet, values: [...facetValues.values()] } : null,
    toggle: block.hideWhenSet ? { label: block.hideLabel ?? 'Show all' } : null,
    search: block.search !== false, total: list.length, groups,
  };
}

/**
 * The blocks of a section body: prose, and the tables its `{{entity:id}}` markers place.
 * @param {Model} model @param {string} sectionId
 */
export function sectionBlocks(model, sectionId) {
  const sec = model.entities.get(sectionId);
  /** @type {any[]} */
  const out = [];
  if (!sec) return out;
  /** @type {string[]} */
  let prose = [];
  /** @type {any} */
  let table = null;
  const flushProse = () => { const t = prose.join('\n').trim(); if (t) out.push({ type: 'prose', text: t }); prose = []; };
  const flushTable = () => { if (table) out.push(table); table = null; };
  const tableOf = (/** @type {Entity} */ t) => ({ type: 'table', id: t.id, columns: Array.isArray(t.data.columns) ? t.data.columns.map(String) : [], rows: /** @type {any[]} */ ([]) });
  for (const line of textOf(sec.data.body).split('\n')) {
    const m = line.trim().match(MARKER);
    if (!m) { flushTable(); prose.push(line); continue; }
    const e = model.entities.get(m[1]);
    if (!e) continue;
    if (e.kind === 'table') { flushProse(); flushTable(); table = tableOf(e); continue; }
    const t = typeof e.data.table === 'string' ? model.entities.get(e.data.table) : undefined;
    if (!t) { flushProse(); flushTable(); out.push({ type: 'entity', id: e.id, label: titleOf(model, e), kind: kindLabel(model, e.kind) }); continue; }
    if (!table || table.id !== t.id) { flushProse(); flushTable(); table = tableOf(t); }
    table.rows.push({ id: e.id, cells: rowCells(t, e) });
  }
  flushTable();
  flushProse();
  return out;
}

/** @param {Entity} t @param {Entity} e @returns {string[]} */
function rowCells(t, e) {
  if (Array.isArray(e.data.cells)) return e.data.cells.map(textOf);
  if (Array.isArray(t.data.columnProperties)) return t.data.columnProperties.map((/** @type {string} */ p) => textOf(e.data[p]));
  return (Array.isArray(t.data.columns) ? t.data.columns : []).map(() => '');
}

/**
 * Sections of a document in reading order, with their level; with no document id, the first document.
 * @param {Model} model @param {string} [documentId]
 */
export function outline(model, documentId) {
  const doc = documentId ? model.entities.get(documentId) : (model.byKind.document ?? [])[0];
  const sections = (model.byKind.section ?? []).filter((s) => !doc || !s.data.document || s.data.document === doc.id);
  const order = (/** @type {Entity} */ s) => (typeof s.data.order === 'number' ? s.data.order : 0);
  return {
    document: doc ? { id: doc.id, title: textOf(doc.data.title) || doc.id } : null,
    sections: [...sections].sort((a, b) => order(a) - order(b)).map((s) => ({ id: s.id, title: textOf(s.data.title) || s.id, level: typeof s.data.level === 'number' ? s.data.level : 1 })),
  };
}

/** Kinds that hold entities, with counts, largest first. @param {Model} model */
export function kindIndex(model) {
  return Object.entries(model.byKind)
    .filter(([, list]) => list.length > 0)
    .map(([kind, list]) => ({ kind, label: kindLabel(model, kind), count: list.length }))
    .sort((a, b) => b.count - a.count || a.label.localeCompare(b.label));
}

/**
 * Resolve one block of a reader view.
 * @param {Model} model @param {any} block
 */
export function resolveBlock(model, block) {
  switch (block?.type) {
    case 'text': return { type: 'text', title: block.title ?? '', text: textOf(block.text) };
    case 'counts': return counts(model, block);
    case 'table': return rows(model, block, 'table');
    case 'list': return rows(model, block, 'list');
    case 'document': return { type: 'document', title: block.title ?? '', ...outline(model, block.document) };
    case 'sections': return {
      type: 'sections', title: block.title ?? '',
      sections: (block.ids ?? []).map((/** @type {string} */ id) => model.entities.get(id)).filter(Boolean).map((/** @type {Entity} */ s) => ({ id: s.id, title: textOf(s.data.title) || titleOf(model, s), blocks: s.kind === 'table' ? [tableBlock(model, s)] : sectionBlocks(model, s.id) })),
    };
    case 'index': return { type: 'index', title: block.title ?? '', kinds: kindIndex(model) };
    default: return { type: 'text', title: '', text: `Unknown block type "${block?.type}".` };
  }
}

/** A table entity with every row that names it. @param {Model} model @param {Entity} t */
export function tableBlock(model, t) {
  const rowsOf = [...model.entities.values()].filter((e) => e.kind !== 'table' && e.data?.table === t.id);
  return { type: 'table', id: t.id, columns: Array.isArray(t.data.columns) ? t.data.columns.map(String) : [], rows: rowsOf.map((e) => ({ id: e.id, cells: rowCells(t, e) })) };
}

/**
 * The page for a view of the reader projection. A view without blocks reads the system,
 * an index of its kinds and, when it has documents, the outline of the first one.
 * @param {Model} model @param {any} view
 */
export function readerPage(model, view) {
  const declared = Array.isArray(view?.reader?.blocks) && view.reader.blocks.length ? view.reader.blocks : null;
  const blocks = declared ?? [
    { type: 'text', text: textOf(model.system?.data?.description) },
    { type: 'index', title: 'What the specification holds' },
    ...((model.byKind.document ?? []).length ? [{ type: 'document', title: 'Documents' }] : []),
  ];
  return {
    title: textOf(view?.name) || textOf(model.system?.data?.name) || 'Reader',
    description: textOf(view?.description),
    blocks: blocks.map((b) => resolveBlock(model, b)).filter((b) => !(b.type === 'text' && !b.text)),
  };
}

/**
 * The page for one kind, reached from an index: every entity of the kind as a table.
 * @param {Model} model @param {string} kind
 */
export function kindPage(model, kind) {
  return { title: kindLabel(model, kind), description: own(model.meta.entities, kind)?.doc ?? '', blocks: [resolveBlock(model, { type: 'table', kind })] };
}

/** Entity ids keyed by their lowercased `ref`, for linking refs written in prose. @param {Model} model */
export function refIndex(model) {
  /** @type {Map<string, string>} */
  const m = new Map();
  for (const e of model.entities.values()) if (typeof e.data?.ref === 'string' && e.data.ref) m.set(e.data.ref.toLowerCase(), e.id);
  return m;
}
