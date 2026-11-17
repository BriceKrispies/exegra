#!/usr/bin/env node
// Converts one Markdown specification file of headings, prose and register tables into
// the specification file of a linked project. Every table row becomes an entity, every
// line is held (verbatim prose, or a marker standing for an entity), and every entity
// names the line it came from. See docs/importing-markdown.md, "A single-file register".
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { parse as parseJsonc, parseTree, getNodeValue } from 'jsonc-parser';
import { Loss, fileLines, slugify, uniquifier, marker, coverage, readGitHead } from './import-markdown.js';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.resolve(HERE, '..');
const SPECS_DIR = path.join(ROOT, 'specs');

const MARKER = /^\{\{entity:([^}]+)\}\}$/;
const SEPARATOR = /^\s*\|?\s*:?-+:?\s*(\|\s*:?-+:?\s*)*\|?\s*$/;
const FENCE = /^\s*(```|~~~)/;
const HEADING = /^(#{1,6})\s+(.*\S)\s*$/;
const CITATION = /\[([^\]\s][^\]]*)\]/g;

/**
 * Split a table row into cells as GitHub renders it: on every `|` not escaped by a
 * backslash. Cells are trimmed and otherwise kept as written, escapes included.
 * @param {string} line
 */
export function rowCells(line) {
  let s = line.trim();
  if (s.startsWith('|')) s = s.slice(1);
  if (s.endsWith('|') && !s.endsWith('\\|')) s = s.slice(0, -1);
  /** @type {string[]} */
  const cells = [];
  let cur = '';
  for (let i = 0; i < s.length; i++) {
    if (s[i] === '\\' && s[i + 1] === '|') { cur += '\\|'; i++; continue; }
    if (s[i] === '|') { cells.push(cur.trim()); cur = ''; continue; }
    cur += s[i];
  }
  cells.push(cur.trim());
  return cells;
}

/**
 * A row as Markdown: canonical spacing, or the row's own `layout` template, in which
 * each `{}` stands for one cell. @param {string[]} cells @param {string} [layout]
 */
export function renderRow(cells, layout) {
  if (!layout) return `|${cells.map((c) => (c === '' ? ' ' : ` ${c} `)).join('|')}|`;
  const parts = layout.split('{}');
  return parts.map((p, k) => p + (k < cells.length ? cells[k] : '')).join('');
}

/**
 * The spacing of a row as a template (pipes and whitespace, `{}` per cell), or undefined
 * when the canonical rendering already gives the line. Holds no cell text. @param {string} line
 */
export function rowLayout(line) {
  const cells = rowCells(line);
  if (renderRow(cells) === line.replace(/\s+$/, '')) return undefined;
  let out = '';
  let pos = 0;
  for (const c of cells) {
    const at = c === '' ? -1 : line.indexOf(c, pos);
    if (c === '') {
      const end = nextBar(line, nextBar(line, pos) + 1);
      out += line.slice(pos, end) + '{}';
      pos = end;
      continue;
    }
    if (at < 0) return undefined;
    out += line.slice(pos, at) + '{}';
    pos = at + c.length;
  }
  const layout = out + line.slice(pos).replace(/\s+$/, '');
  return renderRow(cells, layout) === line.replace(/\s+$/, '') ? layout : undefined;
}

/** Index of the next unescaped pipe at or after `from`, or the line end. @param {string} line @param {number} from */
function nextBar(line, from) {
  for (let i = from; i < line.length; i++) { if (line[i] === '\\' && line[i + 1] === '|') { i++; continue; } if (line[i] === '|') return i; }
  return line.length;
}

/** `Data store` -> `dataStore`; a property name Exegra accepts. @param {string} header */
export function propertyName(header) {
  const words = header.replace(/[`*_]/g, '').split(/[^A-Za-z0-9]+/).filter(Boolean);
  if (header.trim() === '#') return 'number';
  if (!words.length) return 'column';
  const s = words.map((w, i) => (i === 0 ? w.toLowerCase() : w[0].toUpperCase() + w.slice(1).toLowerCase())).join('');
  return /^[A-Za-z]/.test(s) ? s : `c${s}`;
}

/** Properties the importer sets itself; a column of the same name gets a suffix. */
const RESERVED = new Set(['id', 'ref', 'table', 'source', 'mentions', 'citations', 'cells', 'category', 'kind']);
/** @param {string} header */
export function columnProperty(header) {
  const p = propertyName(header);
  return RESERVED.has(p) ? `${p}Column` : p;
}

/** An identifier cell without its formatting; a whole code span keeps its content (`*` is a key). @param {string} cell */
export function cleanKey(cell) {
  const code = /^`([^`]+)`$/.exec(cell.trim());
  return code ? code[1].trim() : cell.replace(/[`*[\]]/g, '').trim();
}

/** [start, end) of each inline code span; a bracket that opens in code is not a citation. @param {string} text */
const codeSpans = (text) => [...text.matchAll(/`[^`\n]*`/g)].map((m) => [/** @type {number} */ (m.index), /** @type {number} */ (m.index) + m[0].length]);

/** @param {string} key */
export function idFromKey(key) { return slugify(key.replace(/\./g, '_')); }

/** Section id from a heading: `4.1 Platform` -> `sec-4-1`, `Appendix A. ...` -> `sec-appendix-a`. @param {string} title */
export function sectionKey(title) {
  const num = /^(\d+(?:\.\d+)*)\.?\s/.exec(title);
  if (num) return `sec-${num[1].replace(/\./g, '-')}`;
  const app = /^Appendix ([A-Z])\b/.exec(title);
  if (app) return `sec-appendix-${app[1].toLowerCase()}`;
  const sub = /^([A-Z](?:\.\d+)+)\.?\s/.exec(title);
  if (sub) return `sec-${sub[1].toLowerCase().replace(/\./g, '-')}`;
  return `sec-${slugify(title).slice(0, 48).replace(/-+$/, '') || 'untitled'}`;
}

/**
 * @typedef {{kind: string, header: string[], under?: string,
 *   id?: {column?: string, prefix?: string, pattern?: string, fallback?: string, fallbackColumn?: string},
 *   columns?: Record<string, string>, refs?: Record<string, string>,
 *   relationship?: {kind: string, from: string, to: string, description?: string, properties?: Record<string, string>}}} Rule
 * @typedef {string | {pattern: string, notUnder?: string}} MentionPattern
 * @typedef {{format: string, project: {id: string, name: string}, source?: string, file: string,
 *   description?: string, kinds?: Record<string, {label: string, section: string, shape: string, color: string, doc?: string}>,
 *   rules?: Rule[], mentions?: MentionPattern[], sourceTextColumns?: string[], categories?: Record<string, string>, aliases?: Record<string, string>,
 *   relationshipKinds?: Record<string, any>, views?: any[], drafts?: string[], authority?: string, authoritySince?: string}} RegisterMap
 * @typedef {{file: string, meta: Record<string, any>, vocabulary: Record<string, any>, lists: Map<string, any[]>}} Draft
 */

/** Lists a draft may add to besides the sections of the kinds it declares. */
const DRAFT_BUILT_IN_LISTS = ['components', 'relationships', 'claims', 'assumptions'];

/**
 * A draft fragment: authored entities, not imported ones. Each gets origin "draft" and the
 * file and line of its declaration as source. @param {string} file @param {string} text @returns {Draft}
 */
export function readDraft(file, text) {
  /** @type {import('jsonc-parser').ParseError[]} */
  const errors = [];
  const tree = parseTree(text, errors, { allowTrailingComma: true });
  if (errors.length || !tree) throw new Error(`${file}: ${errors.length} JSONC error(s), first at offset ${errors[0]?.offset}.`);
  const value = /** @type {Record<string, any>} */ (getNodeValue(tree));
  const lineAt = (/** @type {number} */ off) => text.slice(0, off).split('\n').length;
  /** @type {Map<string, any[]>} */
  const lists = new Map();
  for (const prop of tree.children ?? []) {
    const [k, v] = prop.children ?? [];
    if (!k || !v || k.value === 'draft' || k.value === 'vocabulary') continue;
    if (v.type !== 'array') throw new Error(`${file}: "${k.value}" must be a list of entities.`);
    lists.set(k.value, (v.children ?? []).map((n) => {
      const e = getNodeValue(n);
      return { ...e, origin: 'draft', source: `${file}:${lineAt(n.offset)}` };
    }));
  }
  return { file, meta: value.draft ?? {}, vocabulary: value.vocabulary ?? {}, lists };
}

/**
 * Parse the file into headings and tables, outside code fences.
 * @param {string[]} lines
 */
export function scan(lines) {
  /** @type {{i: number, level: number, title: string}[]} */
  const heads = [];
  /** @type {{start: number, end: number, header: string[], separator: string}[]} 0-based, end exclusive */
  const tables = [];
  /** @type {number[]} lines that start with a pipe but belong to no table */
  const orphans = [];
  let fence = false;
  for (let i = 0; i < lines.length; i++) {
    const l = lines[i];
    if (FENCE.test(l)) { fence = !fence; continue; }
    if (fence) continue;
    const h = HEADING.exec(l);
    if (h) { heads.push({ i, level: h[1].length, title: h[2] }); continue; }
    if (/^\s*\|/.test(l) && i + 1 < lines.length && SEPARATOR.test(lines[i + 1]) && lines[i + 1].includes('-')) {
      let end = i + 2;
      while (end < lines.length && /^\s*\|/.test(lines[end])) end++;
      tables.push({ start: i, end, header: rowCells(l), separator: lines[i + 1] });
      i = end - 1;
    } else if (/^\s*\|/.test(l)) orphans.push(i);
  }
  return { heads, tables, orphans };
}

/**
 * Build the specification text from one Markdown file and its import map.
 * @param {{map: RegisterMap, text: string, file: string, commit: string, drafts?: Draft[]}} opts
 */
export function buildRegisterSpec({ map, text, file, commit, drafts = [] }) {
  const loss = new Loss();
  const lines = fileLines(text);
  const { heads, tables, orphans } = scan(lines);
  for (const i of orphans) loss.add('line that starts with a pipe but is in no table (no header and separator above it), held verbatim as prose', `${file}:${i + 1}`);
  const src = (/** @type {number} */ i) => `${file}:${i + 1}`;
  const uniq = uniquifier();
  const rules = map.rules ?? [];
  const kinds = map.kinds ?? {};
  for (const r of rules) if (r.kind !== 'component' && !kinds[r.kind]) throw new Error(`Rule for [${r.header.join(' | ')}] names kind "${r.kind}", which the map does not declare in "kinds".`);

  // ---- sections ----------------------------------------------------------------
  const docId = `doc-${slugify(path.basename(file, '.md'))}`;
  /** @type {any[]} */
  const sections = [];
  /** @type {{start: number, end: number, id: string, headLine: number}[]} line span of each section's own body */
  const spans = [];
  /** @type {{id: string, level: number, title: string}[]} */
  const stack = [];
  /** @type {Map<number, {id: string, chain: string[]}>} heading line -> section */
  const sectionAtLine = new Map();
  const firstHead = heads.length ? heads[0].i : lines.length;
  if (firstHead > 0) {
    const id = uniq('sec-preamble');
    sections.push({ id, title: '', level: 0, document: docId, order: 1 });
    spans.push({ start: 0, end: firstHead, id, headLine: 0 });
  }
  heads.forEach((h, k) => {
    while (stack.length && stack[stack.length - 1].level >= h.level) stack.pop();
    const id = uniq(sectionKey(h.title));
    const parent = stack.length ? stack[stack.length - 1].id : undefined;
    sections.push({ id, title: h.title, level: h.level, document: docId, ...(parent ? { parent } : {}), order: sections.length + 1 });
    spans.push({ start: h.i + 1, end: k + 1 < heads.length ? heads[k + 1].i : lines.length, id, headLine: h.i });
    stack.push({ id, level: h.level, title: h.title });
    sectionAtLine.set(h.i, { id, chain: stack.map((s) => s.title) });
  });
  /** Section holding line i, and the titles of it and its ancestors. @param {number} i */
  const sectionOfLine = (i) => {
    let best = spans[0];
    for (const s of spans) { if (s.start <= i) best = s; else break; }
    const at = sectionAtLine.get(best.headLine);
    return { id: best.id, chain: at ? at.chain : [] };
  };

  // ---- tables and rows -----------------------------------------------------------
  /** @type {any[]} */ const tableEntities = [];
  /** @type {Map<string, any[]>} */ const rowsByKind = new Map();
  /** @type {any[]} */ const components = [];
  /** @type {{rowId: string, line: number, rel: {kind: string, from: string, to: string, description?: string}, fromText: string, toText: string, label?: string, description?: string, extra: Record<string, string>}[]} */
  const pendingRels = [];
  /** @type {Map<string, string[]>} table id -> titles of its section and ancestors */
  const chainOf = new Map();
  /** @type {Map<string, string>} row id -> its cells without the source-text columns */
  const citeTextById = new Map();
  /** @type {{entity: any, column: string, prop: string, text: string, line: number}[]} */
  const pendingRefs = [];
  /** @type {Map<string, string>} id -> raw source lines */
  const rawById = new Map();
  /** @type {{id: string, start: number, end: number}[]} 1-based inclusive line runs replaced by markers */
  const runs = [];
  /** @type {Map<string, string[]>} kind -> property names in first-seen order */
  const kindProps = new Map();
  /** @type {Map<string, Map<string, string>>} kind -> property -> header label */
  const kindLabels = new Map();
  const genSeq = new Map();
  const nextGen = (/** @type {string} */ prefix) => { const n = (genSeq.get(prefix) ?? 0) + 1; genSeq.set(prefix, n); return `${prefix}-${n}`; };
  /** @type {Map<string, {matched: number, rows: number, example: string}>} */
  const unmatched = new Map();

  tables.forEach((t, ti) => {
    const sec = sectionOfLine(t.start);
    const rule = rules.find((r) => r.header.length === t.header.length && r.header.every((h, k) => h === t.header[k])
      && (!r.under || sec.chain.some((c) => new RegExp(/** @type {string} */ (r.under)).test(c))));
    const kind = rule ? rule.kind : 'tableRow';
    const props = t.header.map((h) => (rule?.columns?.[h]) ?? columnProperty(h));
    if (rule) props.forEach((p, k) => { if (RESERVED.has(p)) throw new Error(`Rule for kind "${kind}" maps column "${t.header[k]}" to the reserved property "${p}".`); });
    if (rule) {
      const seen = new Set();
      props.forEach((p, k) => { if (seen.has(p)) throw new Error(`${src(t.start)}: rule for kind "${kind}" maps two columns to "${p}" (${t.header[k]}).`); seen.add(p); });
      if (!kindProps.has(kind)) { kindProps.set(kind, []); kindLabels.set(kind, new Map()); }
      props.forEach((p, k) => { const kp = /** @type {string[]} */ (kindProps.get(kind)); if (!kp.includes(p)) kp.push(p); kindLabels.get(kind)?.set(p, t.header[k]); });
    } else {
      const key = t.header.join(' | ');
      const u = unmatched.get(key) ?? { matched: 0, rows: 0, example: src(t.start) };
      u.matched++; u.rows += t.end - t.start - 2; unmatched.set(key, u);
    }
    const tableId = uniq(`tbl-${String(ti + 1).padStart(3, '0')}`);
    chainOf.set(tableId, sec.chain);
    const sourceText = t.header.map((h) => (map.sourceTextColumns ?? []).includes(h));
    const table ={ id: tableId, section: sec.id, columns: t.header, ...(rule ? { columnProperties: props } : {}), separator: t.separator.trim(), rowKind: kind, rowCount: 0, source: src(t.start) };
    tableEntities.push(table);
    runs.push({ id: tableId, start: t.start + 1, end: t.start + 2 });
    rawById.set(tableId, `${lines[t.start]}\n${lines[t.start + 1]}`);

    for (let i = t.start + 2; i < t.end; i++) {
      const cells = rowCells(lines[i]);
      if (cells.length !== t.header.length) {
        loss.add('row with a different number of cells than its header, held verbatim', `${src(i)} (${cells.length} of ${t.header.length})`);
        continue;
      }
      /** @type {Record<string, any>} */
      const e = {};
      let ref;
      if (rule?.id?.column) {
        const k = t.header.indexOf(rule.id.column);
        if (k < 0) throw new Error(`Rule for kind "${kind}" names id column "${rule.id.column}", which the table at ${src(t.start)} does not have.`);
        ref = cleanKey(cells[k]);
        const key = kind === 'component' ? slugify(ref) : idFromKey(ref);
        const base = rule.id.prefix && key ? `${rule.id.prefix}-${key}` : key;
        // A cell the rule's pattern does not accept (e.g. "(no Epics)") is not an identifier;
        // the row is then about the identifier in fallbackColumn, if that cell holds one.
        const pattern = rule.id.pattern;
        const fk = rule.id.fallbackColumn ? t.header.indexOf(rule.id.fallbackColumn) : -1;
        const found = pattern && fk >= 0 ? new RegExp(`(?<![A-Za-z0-9-])(?:${pattern})(?![A-Za-z0-9])`).exec(cells[fk]) : null;
        if (pattern && !new RegExp(`^(?:${pattern})$`).test(ref) && found) {
          ref = found[0];
          const fbase = rule.id.prefix ? `${rule.id.prefix}-${idFromKey(ref)}` : idFromKey(ref);
          e.id = uniq(fbase);
          if (e.id !== fbase) loss.add('duplicate identifier, row given a suffixed id', `${src(i)} ${ref} -> ${e.id}`);
        }
        else if (pattern && !new RegExp(`^(?:${pattern})$`).test(ref)) { ref = undefined; e.id = uniq(nextGen(rule.id.fallback ?? kind.toLowerCase())); }
        else if (!base || !/^[a-z]/.test(base)) { loss.add('identifier that gives no valid id, row given a generated id', `${src(i)} "${ref}"`); e.id = uniq(nextGen(rule.id.prefix ?? kind.toLowerCase())); }
        else {
          e.id = uniq(base);
          if (e.id !== base) loss.add('duplicate identifier, row given a suffixed id', `${src(i)} ${ref} -> ${e.id}`);
        }
      } else {
        e.id = uniq(rule ? nextGen(rule.id?.prefix ?? kind.toLowerCase()) : `${tableId}-r${i - t.start - 1}`);
      }
      if (ref !== undefined) e.ref = ref;
      e.table = tableId;
      if (rule) cells.forEach((c, k) => { if (c !== '') e[props[k]] = c; });
      else e.cells = cells;
      const lay = rowLayout(lines[i]);
      if (lay !== undefined) e.layout = lay;
      e.source = src(i);
      table.rowCount++;
      runs.push({ id: e.id, start: i + 1, end: i + 1 });
      rawById.set(e.id, lines[i]);
      if (sourceText.includes(true)) citeTextById.set(e.id, cells.filter((_, k) => !sourceText[k]).join(' | '));
      if (rule?.refs) for (const [col, prop] of Object.entries(rule.refs)) {
        const k = t.header.indexOf(col);
        if (k >= 0 && cells[k]) pendingRefs.push({ entity: e, column: col, prop, text: cells[k], line: i });
      }
      if (rule?.relationship) {
        const fk = t.header.indexOf(rule.relationship.from); const tk = t.header.indexOf(rule.relationship.to);
        /** @type {Record<string, string>} */
        const extra = {};
        for (const [col, prop] of Object.entries(rule.relationship.properties ?? {})) { const v = cells[t.header.indexOf(col)]; if (v) extra[prop] = v; }
        pendingRels.push({ rowId: e.id, line: i, rel: rule.relationship, fromText: cells[fk] ?? '', toText: cells[tk] ?? '', label: ref, description: rule.relationship.description ? cells[t.header.indexOf(rule.relationship.description)] : undefined, extra });
      }
      if (kind === 'component') {
        const cat = map.categories?.[ref ?? ''];
        if (!cat) throw new Error(`Component "${ref}" (${src(i)}) has no category in the import map.`);
        e.category = cat;
        components.push(e);
      } else {
        if (!rowsByKind.has(kind)) rowsByKind.set(kind, []);
        rowsByKind.get(kind)?.push(e);
      }
    }
  });

  // ---- references between entities ------------------------------------------------
  /** @type {Map<string, string>} id -> kind */
  const kindOf = new Map();
  for (const c of components) kindOf.set(c.id, 'component');
  for (const [k, list] of rowsByKind) for (const e of list) kindOf.set(e.id, k);
  for (const t of tableEntities) kindOf.set(t.id, 'table');
  for (const s of sections) kindOf.set(s.id, 'section');

  /** Component named by a phrase: by name, then by alias. @type {[RegExp, string][]} */
  const componentNames = [];
  for (const c of components) componentNames.push([new RegExp(`(^|[^A-Za-z0-9-])${escapeRe(c.ref)}([^A-Za-z0-9-]|$)`), c.id]);
  for (const [alias, target] of Object.entries(map.aliases ?? {})) {
    const id = components.find((c) => c.ref === target)?.id;
    if (!id) throw new Error(`Alias "${alias}" names component "${target}", which is not imported.`);
    componentNames.push([new RegExp(`(^|[^A-Za-z0-9-])${escapeRe(alias)}([^A-Za-z0-9-]|$)`), id]);
  }
  /** @param {string} text */
  const componentsIn = (text) => [...new Set(componentNames
    .map(([re, id]) => ({ id, at: text.search(re) }))
    .filter((x) => x.at >= 0)
    .sort((a, b) => a.at - b.at)
    .map((x) => x.id))];

  for (const p of pendingRefs) {
    const ids = componentsIn(p.text);
    if (ids.length) p.entity[p.prop] = ids;
    else loss.add(`"${p.column}" cell that names no component`, `${src(p.line)} "${p.text.slice(0, 60)}"`);
  }
  /** @type {any[]} */
  const relationships = [];
  const relUniq = uniquifier();
  for (const p of pendingRels) {
    const from = componentsIn(p.fromText); const to = componentsIn(p.toText);
    if (from.length !== 1 || to.length !== 1) { loss.add(`${p.rel.kind} row whose ends are not one component each, no relationship`, `${src(p.line)} "${p.fromText}" -> "${p.toText}"`); continue; }
    if (from[0] === to[0]) { loss.add(`${p.rel.kind} row from a component to itself, no relationship`, `${src(p.line)} ${from[0]}`); continue; }
    relationships.push({ id: relUniq(`${p.rowId}-${p.rel.kind}`), kind: p.rel.kind, from: from[0], to: to[0], ...(p.label ? { label: p.label } : {}), ...(p.description ? { description: p.description } : {}), ...p.extra, row: p.rowId, source: src(p.line) });
  }

  /** @type {Map<string, {line: number, key: string}>} unresolved id -> its first mention */
  const unresolved = new Map();
  // A pattern with notUnder is not read in a section whose heading chain matches it (another numbering there).
  const mentionRes = (map.mentions ?? []).map((m) => {
    const p = typeof m === 'string' ? { pattern: m } : m;
    return { re: new RegExp(`(?<![A-Za-z0-9-])(${p.pattern})(?![A-Za-z0-9])`, 'g'), notUnder: p.notUnder ? new RegExp(p.notUnder) : undefined };
  });
  /** @param {string} ownId @param {string} text @param {number} line 0-based @param {string[]} chain */
  const mentionsIn = (ownId, text, line, chain) => {
    const out = new Set();
    for (const { re, notUnder } of mentionRes) {
      if (notUnder && chain.some((c) => notUnder.test(c))) continue;
      for (const m of text.matchAll(re)) {
        const id = idFromKey(m[1]);
        if (id === ownId) continue;
        if (kindOf.has(id)) out.add(id);
        else if (!unresolved.has(id) || /** @type {any} */ (unresolved.get(id)).line > line) unresolved.set(id, { line, key: m[1] });
      }
    }
    return out.size ? [...out] : undefined;
  };
  /** @param {string} text */
  const citationsIn = (text) => {
    const out = new Set();
    const code = codeSpans(text);
    for (const m of text.matchAll(CITATION)) {
      const at = /** @type {number} */ (m.index);
      if (code.some(([a, b]) => at > a && at < b)) continue;
      if (/[A-Za-z]/.test(m[1]) && !/^(x| )$/.test(m[1])) out.add(m[1]);
    }
    return out.size ? [...out] : undefined;
  };
  const allRows = [...components, ...[...rowsByKind.values()].flat()];
  for (const e of allRows) {
    const raw = /** @type {string} */ (rawById.get(e.id));
    const m = mentionsIn(e.id, raw, Number(e.source.split(':').pop()) - 1, chainOf.get(e.table) ?? []); if (m) e.mentions = m;
    const c = citationsIn(citeTextById.get(e.id) ?? raw); if (c) e.citations = c;
  }

  // ---- section bodies ----------------------------------------------------------------
  const byStart = new Map(runs.map((r) => [r.start, r]));
  let placed = 0;
  spans.forEach((sp, k) => {
    /** @type {string[]} */
    const out = [];
    /** @type {number[]} source line of each prose line */
    const proseLines = [];
    for (let i = sp.start; i < sp.end; i++) {
      const r = byStart.get(i + 1);
      if (r) {
        if (r.end > sp.end) throw new Error(`${src(r.start - 1)}: entity ${r.id} runs past the end of its section.`);
        out.push(marker(r.id)); placed++; i = r.end - 1;
      } else {
        if (MARKER.test(lines[i])) throw new Error(`${src(i)}: a line looks like an entity marker.`);
        out.push(lines[i]); proseLines.push(i);
      }
    }
    const s = sections[k];
    s.body = out.length ? out.join('\n') + '\n' : '';
    // The heading is part of the section's text: "5.5 Work to make the gateway obey rule B-1".
    const prose = [s.title, ...out.filter((l) => !MARKER.test(l))].join('\n');
    const chain = sectionAtLine.get(sp.headLine)?.chain ?? [];
    /** @type {[number, string][]} */
    const texts = [...(s.level > 0 ? [/** @type {[number, string]} */ ([sp.headLine, s.title])] : []), ...proseLines.map((i) => /** @type {[number, string]} */ ([i, lines[i]]))];
    const found = new Set(texts.flatMap(([i, l]) => mentionsIn(s.id, l, i, chain) ?? []));
    if (found.size) s.mentions = [...found];
    const c = citationsIn(prose); if (c) s.citations = c;
    s.source = src(sp.headLine);
  });
  if (placed !== runs.length) throw new Error(`${runs.length - placed} imported entities were not placed in a section body.`);
  for (const { line, key } of [...unresolved.values()].sort((a, b) => a.line - b.line)) loss.add(`identifier mentioned but defined by no row (${key.replace(/[0-9]+$/, 'n')}), first mention`, `${src(line)} ${key}`);

  // ---- vocabulary ------------------------------------------------------------------------
  const anyRef = { type: 'list', items: { type: 'ref', ref: ['*'] }, label: 'Mentions', doc: 'Imported entities whose identifier the text names.' };
  const citations = { type: 'list', items: { type: 'string' }, label: 'Citations', doc: 'The bracketed citations of the text, as written.' };
  const source = { type: 'string', required: true, label: 'Source', doc: 'File and line in the source repository where this was imported from.' };
  const refProp = { type: 'string', label: 'Source id', doc: 'The identifier as written in the Markdown, formatting removed.' };
  const tableRef = { type: 'ref', ref: ['table'], required: true, label: 'Table' };
  const layoutProp = { type: 'string', label: 'Row spacing', doc: 'The pipes and spaces of the source row, {} standing for each cell; present only where the row is not spaced as | a | b |.' };
  /** @type {Record<string, any>} */
  const entityKinds = {
    document: { label: 'Document', section: 'documents', shape: 'box', color: 'slate', doc: 'The Markdown file.', properties: { path: { type: 'string', required: true, label: 'Path' }, title: { type: 'string', label: 'Title' }, commit: { type: 'string', label: 'Git commit' }, source } },
    section: { label: 'Section', section: 'sections', shape: 'chamfer', color: 'neutral', doc: 'One heading and the Markdown under it, up to the next heading, verbatim. Each table header and table row is replaced by one {{entity:<id>}} marker line.',
      properties: { title: { type: 'string', label: 'Title' }, level: { type: 'number', required: true, label: 'Heading level' }, document: { type: 'ref', ref: ['document'], required: true, label: 'Document' }, parent: { type: 'ref', ref: ['section'], label: 'Parent section' }, order: { type: 'number', required: true, label: 'Order' }, body: { type: 'text', label: 'Body' }, mentions: anyRef, citations, source } },
    table: { label: 'Table', section: 'tables', shape: 'tablet', color: 'steel', doc: 'A Markdown table: its header cells and separator line. Its rows are entities of kind rowKind.',
      properties: { section: { type: 'ref', ref: ['section'], required: true, label: 'Section' }, columns: { type: 'list', items: { type: 'string' }, required: true, label: 'Columns' }, columnProperties: { type: 'list', items: { type: 'string' }, label: 'Column properties', doc: 'The property of each column on a typed row.' }, separator: { type: 'string', required: true, label: 'Separator line' }, rowKind: { type: 'string', required: true, label: 'Row kind' }, rowCount: { type: 'number', required: true, label: 'Rows' }, source } },
    tableRow: { label: 'Table row', section: 'tableRows', shape: 'capsule', color: 'neutral', doc: 'A row of a table no rule of the import map types: its cells in column order.',
      properties: { table: tableRef, cells: { type: 'list', items: { type: 'string' }, required: true, label: 'Cells' }, layout: layoutProp, mentions: anyRef, citations, source } },
  };
  for (const [kind, def] of Object.entries(kinds)) {
    /** @type {Record<string, any>} */
    const props = { ref: refProp, table: tableRef };
    for (const p of kindProps.get(kind) ?? []) props[p] = { type: 'text', label: kindLabels.get(kind)?.get(p) ?? p };
    for (const r of rules.filter((x) => x.kind === kind)) for (const [col, p] of Object.entries(r.refs ?? {})) props[p] = refListProp(col, p);
    props.layout = layoutProp; props.mentions = anyRef; props.citations = citations; props.source = source;
    entityKinds[kind] = { ...def, properties: props };
  }
  /** @type {any[]} */
  const extraProps = [];
  const builtIn = new Set(['id', 'name', 'kind', 'category', 'parent', 'purpose', 'responsibilities', 'owner', 'trustZone', 'ports', 'unknowns', 'illustrative', 'tags', 'implementation']);
  const compProps = ['ref', 'table', 'layout', ...(kindProps.get('component') ?? []).filter((p) => !builtIn.has(p)), 'mentions', 'citations', 'source'];
  for (const p of compProps) {
    const def = p === 'ref' ? refProp : p === 'table' ? { ...tableRef, required: false } : p === 'layout' ? layoutProp : p === 'mentions' ? anyRef : p === 'citations' ? citations : p === 'source' ? { ...source, required: false } : { type: 'text', label: kindLabels.get('component')?.get(p) ?? p };
    extraProps.push({ entity: 'component', name: p, ...def });
  }
  for (const r of rules) for (const [col, p] of Object.entries(r.relationship?.properties ?? {})) {
    if (!extraProps.some((x) => x.entity === 'relationship' && x.name === p)) extraProps.push({ entity: 'relationship', name: p, type: 'text', label: col, doc: `The "${col}" cell of the row.` });
  }
  extraProps.push({ entity: 'relationship', name: 'row', type: 'ref', ref: ['*'], label: 'Row', doc: 'The table row this relationship was read from.' });
  extraProps.push({ entity: 'relationship', name: 'source', type: 'string', label: 'Source', doc: 'File and line of that row.' });
  /** @type {Record<string, any>} */
  const vocabulary = { entityKinds, properties: extraProps, ...(map.relationshipKinds ? { relationshipKinds: { ...map.relationshipKinds } } : {}) };
  if (drafts.length) mergeDraftVocabulary(vocabulary, drafts);

  // ---- system ---------------------------------------------------------------------------
  const document = { id: docId, path: file, title: heads.length ? heads[0].title : file, commit, source: `${file}:1` };
  const counts = /** @type {Record<string, number>} */ ({ sections: sections.length, tables: tableEntities.length, components: components.length, relationships: relationships.length });
  for (const [k, list] of rowsByKind) counts[k] = list.length;
  const rowTotal = allRows.length;
  const bytes = Buffer.byteLength(text);
  const mentionScopes = (map.mentions ?? []).flatMap((m) => (typeof m === 'object' && m.notUnder ? [`${m.pattern} (not under /${m.notUnder}/)`] : []));
  const unmatchedLines = [...unmatched].sort((a, b) => b[1].rows - a[1].rows).map(([h, u]) => `${u.rows} rows in ${u.matched} table(s) [${h}], first at ${u.example}`);
  const notes = [
    `PRODUCED BY IMPORT. tools/import-register.js converted ${file} (${lines.length} lines, ${bytes} bytes) at git commit ${commit}. Every line is held: prose verbatim in a section body, and each table header and table row as an entity that a {{entity:<id>}} marker line in the body stands for. The import checked that the file rebuilds line for line with each marker expanded to its source lines, and that every row rendered from its properties gives the cells of its source row.`,
    'Every entity carries "source" (file:line in the source repository). A row whose table has an identifier column carries "ref", the identifier as written; its id is that identifier in lower case. Other rows have generated ids.',
    `Imported: ${sections.length} sections, ${tableEntities.length} tables and ${rowTotal} rows (${Object.entries(counts).filter(([k]) => !['sections', 'tables', 'relationships'].includes(k)).map(([k, n]) => `${n} ${k}`).join(', ')}), and ${relationships.length} relationships read from rows.`,
    `"mentions" lists the imported entities whose identifiers a text (a section's heading and prose, or a row) names, by the patterns of the import map${mentionScopes.length ? `; these patterns are not read under headings where the text uses a different numbering: ${mentionScopes.join('; ')}` : ''}. "citations" lists the bracketed citations of the text as written, outside code spans${map.sourceTextColumns?.length ? ` and outside the columns that hold the text of a source (${map.sourceTextColumns.join(', ')})` : ''}. Component references in typed columns, component categories and component aliases come from the import map: an Exegra-side reading the Markdown does not state.`,
    `Tables that no rule types become rows of kind tableRow with their cells in column order (${unmatched.size} header shapes).`,
    ...unmatchedLines.slice(0, 25).map((l) => `UNTYPED TABLE, ${l}`),
    ...(unmatchedLines.length > 25 ? [`UNTYPED TABLE, and ${unmatchedLines.length - 25} more header shapes.`] : []),
    ...loss.lines().map((l) => `NOT MAPPED, ${l}`),
    ...drafts.map((d) => `DRAFT, NOT FROM THE MARKDOWN. ${d.file}${d.meta.title ? ` (${d.meta.title})` : ''} adds ${[...d.lists].map(([k, l]) => `${l.length} ${k}`).join(', ')}. These entities are authored, carry origin "draft" and "source" in that file, and cite the imported entities they answer in "basis". ${d.meta.status ?? ''}`.trim()),
  ];
  const system = { id: map.project.id, name: map.project.name, version: `git ${commit.slice(0, 12)}`, description: map.description ?? `${map.project.name}, imported from ${file}.`, illustrative: false, notes };
  const views = map.views ?? [
    { id: 'architecture', name: 'Architecture', projection: 'structural', description: 'The components and the relationships read from rows.' },
    { id: 'traceability', name: 'Traceability', projection: 'references', description: 'The selected entity and the entities that mention it or that it mentions.', display: { depth: 1 } },
  ];

  // ---- text -------------------------------------------------------------------------------
  const out = ['{'];
  out.push(`  // ${map.project.name}. Produced by Exegra's tools/import-register.js from ${file} at git commit ${commit}.`);
  out.push('  // Every line of the Markdown is held here; "source" on an entity is the file and line it came from.');
  out.push('  "exegra": "0.1",', '');
  out.push('  "system": ' + JSON.stringify(system, null, 2).replace(/\n/g, '\n  ') + ',', '');
  out.push('  "vocabulary": ' + JSON.stringify(vocabulary, null, 2).replace(/\n/g, '\n  ') + ',');
  /** @param {string} title @param {string} key @param {any[]} items */
  const block = (title, key, items) => {
    out.push('', `  // ---- ${title} ${'-'.repeat(Math.max(3, 70 - title.length))}`, `  "${key}": [`);
    items.forEach((e, i) => out.push('    ' + JSON.stringify(e) + (i < items.length - 1 ? ',' : '')));
    out.push('  ],');
  };
  /** @param {string} key */
  const drafted = (key) => drafts.flatMap((d) => d.lists.get(key) ?? []);
  block('Components', 'components', [...components, ...drafted('components')]);
  block('Relationships read from rows', 'relationships', [...relationships, ...drafted('relationships')]);
  for (const key of ['claims', 'assumptions']) if (drafted(key).length) block(`Draft ${key}`, key, drafted(key));
  for (const d of drafts) for (const [key, list] of d.lists) if (!DRAFT_BUILT_IN_LISTS.includes(key)) block(`Draft: ${key}`, key, list);
  for (const [kind, def] of Object.entries(kinds)) block(def.label, def.section, rowsByKind.get(kind) ?? []);
  block('Table rows no rule types', 'tableRows', rowsByKind.get('tableRow') ?? []);
  block('Tables', 'tables', tableEntities);
  block('Document', 'documents', [document]);
  block('Sections (one per heading)', 'sections', sections);
  out.push('', '  "views": ' + JSON.stringify(views) , '}', '');
  const specText = out.join('\n');

  // ---- checks ---------------------------------------------------------------------------
  const onDisk = new Map([[file, text]]);
  const cov = coverage(new Map([[file, rebuild(sections, (id) => rawById.get(id))]]), onDisk);
  const spec = parseJsonc(specText);
  const unfaithful = renderCheck(spec, rawById);
  const rendered = coverage(new Map([[file, renderMarkdown(spec)]]), onDisk);
  return { text: specText, counts, loss, cov, unfaithful, rendered, unmatched: unmatchedLines, ok: cov.ok && unfaithful.length === 0 };
}

/**
 * A list of the components a cell names. The cell may name one as a candidate or to exclude it,
 * so the list is a reading, not a statement of ownership. @param {string} col @param {string} p
 */
function refListProp(col, p) {
  return { type: 'list', items: { type: 'ref', ref: ['component'] }, label: p, doc: `The components that the "${col}" cell names (by name or import-map alias), in order. The cell text is the statement; a name in it can be a candidate, a former owner or an exclusion.` };
}

/** @param {string} s */
function escapeRe(s) { return s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'); }

/**
 * Adds a draft's kinds, methods and relationship kinds, and the draft properties
 * (origin, basis, source) on the built-in kinds drafts use. @param {Record<string, any>} vocabulary @param {Draft[]} drafts
 */
function mergeDraftVocabulary(vocabulary, drafts) {
  for (const d of drafts) {
    for (const [k, def] of Object.entries(d.vocabulary.entityKinds ?? {})) {
      if (vocabulary.entityKinds[k]) throw new Error(`${d.file}: entity kind "${k}" is already declared.`);
      vocabulary.entityKinds[k] = def;
    }
    vocabulary.relationshipKinds = { ...(vocabulary.relationshipKinds ?? {}), ...(d.vocabulary.relationshipKinds ?? {}) };
    vocabulary.verificationMethods = { ...(vocabulary.verificationMethods ?? {}), ...(d.vocabulary.verificationMethods ?? {}) };
    vocabulary.properties.push(...(d.vocabulary.properties ?? []));
  }
  const used = new Set(drafts.flatMap((d) => [...d.lists.keys()]));
  const props = /** @type {any[]} */ (vocabulary.properties);
  const add = (/** @type {string} */ entity, /** @type {string} */ name, /** @type {Record<string, any>} */ def) => { if (!props.some((p) => p.entity === entity && p.name === name)) props.push({ entity, name, ...def }); };
  for (const [list, entity] of [['components', 'component'], ['relationships', 'relationship'], ['claims', 'claim'], ['assumptions', 'assumption']]) {
    if (!used.has(list)) continue;
    add(entity, 'origin', { type: 'string', label: 'Origin', doc: '"draft" for an authored entity; absent for an imported one.' });
    add(entity, 'basis', { type: 'list', items: { type: 'ref', ref: ['*'] }, label: 'Basis', doc: 'The imported entities (rules, gaps, conflicts, capabilities) this draft entity answers.' });
    add(entity, 'source', { type: 'string', label: 'Source', doc: 'File and line where this was imported from or declared.' });
  }
}

/**
 * The file from its sections, each marker expanded by `expand`.
 * @param {any[]} sections @param {(id: string) => string | undefined} expand
 */
export function rebuild(sections, expand) {
  /** @type {string[]} */
  const out = [];
  for (const s of [...sections].sort((a, b) => a.order - b.order)) {
    if (s.level > 0) out.push(`${'#'.repeat(s.level)} ${s.title}`);
    if (!s.body) continue;
    for (const l of s.body.slice(0, -1).split('\n')) {
      const m = MARKER.exec(l);
      if (!m) { out.push(l); continue; }
      const r = expand(m[1]);
      if (r === undefined) throw new Error(`Section ${s.id} names entity ${m[1]}, which does not render.`);
      out.push(...r.split('\n'));
    }
  }
  return out.length ? out.join('\n') + '\n' : '';
}

/** Index of the entities of a written specification that render to Markdown. @param {any} spec */
function renderIndex(spec) {
  /** @type {Map<string, any>} */
  const tables = new Map((spec.tables ?? []).map((/** @type {any} */ t) => [t.id, t]));
  /** @type {Map<string, any>} */
  const rows = new Map();
  for (const [key, list] of Object.entries(spec)) {
    if (!Array.isArray(list) || key === 'tables' || key === 'sections' || key === 'documents' || key === 'views' || key === 'relationships') continue;
    for (const e of list) if (e && typeof e === 'object' && typeof e.table === 'string') rows.set(e.id, e);
  }
  return { tables, rows };
}

/** One entity of a written specification as Markdown, or undefined. @param {any} spec */
export function entityRenderer(spec) {
  const { tables, rows } = renderIndex(spec);
  return (/** @type {string} */ id) => {
    const t = tables.get(id);
    if (t) return `${renderRow(t.columns)}\n${t.separator}`;
    const r = rows.get(id);
    if (!r) return undefined;
    const table = tables.get(r.table);
    if (!table) return undefined;
    const cells = Array.isArray(r.cells) ? r.cells : (table.columnProperties ?? []).map((/** @type {string} */ p) => (typeof r[p] === 'string' ? r[p] : ''));
    return renderRow(cells, typeof r.layout === 'string' ? r.layout : undefined);
  };
}

/** The Markdown rendered from a written specification alone. @param {any} spec */
export function renderMarkdown(spec) { return rebuild(spec.sections ?? [], entityRenderer(spec)); }

/**
 * Entities whose rendering does not give the cells of their source lines.
 * @param {any} spec @param {Map<string, string>} rawById
 */
export function renderCheck(spec, rawById) {
  const render = entityRenderer(spec);
  /** @type {{id: string, raw: string, rendered: string}[]} */
  const bad = [];
  for (const [id, raw] of rawById) {
    const r = render(id);
    const same = r !== undefined && r.split('\n').length === raw.split('\n').length
      && r.split('\n').every((l, k) => (SEPARATOR.test(l) ? l.trim() === raw.split('\n')[k].trim() : JSON.stringify(rowCells(l)) === JSON.stringify(rowCells(raw.split('\n')[k]))));
    if (!same) bad.push({ id, raw, rendered: r ?? '(does not render)' });
  }
  return bad;
}

// ---------------------------------------------------------------------------
// Command line
// ---------------------------------------------------------------------------

/**
 * Read an import map, refusing any JSONC error: an invalid escape such as "\d" would otherwise
 * be dropped silently and change a pattern. @param {string} file @returns {RegisterMap}
 */
export function readMap(file) {
  /** @type {import('jsonc-parser').ParseError[]} */
  const errors = [];
  const map = parseJsonc(fs.readFileSync(file, 'utf8'), errors, { allowTrailingComma: true });
  if (errors.length) throw new Error(`${file}: ${errors.length} JSONC error(s), first at offset ${errors[0].offset} (code ${errors[0].error}); write a backslash in a pattern as \\\\.`);
  return map;
}

const USAGE = 'node tools/import-register.js --project <name> [--source <dir>] [--out <file>] [--map <file>] [--check] [--export-md <file>]\n       node tools/import-register.js --render <spec.jsonc | project> [--out <file.md>]';

/** @param {string[]} argv */
function parseArgs(argv) {
  /** @type {Record<string, string | boolean>} */
  const o = {};
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--check') o.check = true;
    else if (['--project', '--source', '--out', '--map', '--export-md', '--render'].includes(a)) { if (i + 1 >= argv.length) throw new Error(`${a} needs a value.`); o[a.slice(2)] = argv[++i]; }
    else throw new Error(`Unknown argument ${a}.`);
  }
  return o;
}

/** The specification file a linked project names. @param {string} project */
function projectSpecFile(project) {
  const pj = path.join(SPECS_DIR, project, 'project.jsonc');
  if (!fs.existsSync(pj)) throw new Error(`${pj} does not exist; give --out.`);
  const p = parseJsonc(fs.readFileSync(pj, 'utf8'));
  if (!p || typeof p.spec !== 'string') throw new Error(`${pj} names no "spec".`);
  return path.resolve(path.dirname(pj), p.spec);
}

function main() {
  let args;
  try { args = parseArgs(process.argv.slice(2)); } catch (e) { console.error(`${/** @type {Error} */ (e).message}\n${USAGE}`); process.exit(2); }
  if (typeof args.render === 'string') {
    const specFile = fs.existsSync(args.render) ? path.resolve(args.render) : projectSpecFile(args.render);
    const md = renderMarkdown(parseJsonc(fs.readFileSync(specFile, 'utf8')));
    if (typeof args.out === 'string') { fs.writeFileSync(args.out, md); console.log(`wrote ${args.out}`); } else process.stdout.write(md);
    return;
  }
  const project = typeof args.project === 'string' ? args.project : undefined;
  const mapFile = typeof args.map === 'string' ? path.resolve(args.map) : project ? path.join(SPECS_DIR, project, 'import-map.jsonc') : undefined;
  if (!mapFile) { console.error(USAGE); process.exit(2); }
  /** @type {RegisterMap} */
  let map;
  try { map = readMap(mapFile); } catch (e) { console.error(/** @type {Error} */ (e).message); process.exit(2); }
  if (map.format !== 'register') { console.error(`${mapFile} is not a register import map ("format": "register").`); process.exit(2); }
  // Once the JSONC is the authority, an import would overwrite edits made in it.
  if (map.authority === 'jsonc' && !args.out) { console.error(`${mapFile}: the JSONC is the authority (${map.authoritySince ?? 'date not given'}); importing would overwrite it. Use --out to write elsewhere, or --render to get the Markdown.`); process.exit(1); }
  const sourceDir = path.resolve(typeof args.source === 'string' ? args.source : path.resolve(path.dirname(mapFile), map.source ?? '.'));
  const outFile = typeof args.out === 'string' ? path.resolve(args.out) : project ? projectSpecFile(project) : undefined;
  if (!outFile) { console.error(USAGE); process.exit(2); }
  const text = fs.readFileSync(path.join(sourceDir, map.file), 'utf8');
  const commit = readGitHead(sourceDir);
  const drafts = (map.drafts ?? []).map((f) => readDraft(f, fs.readFileSync(path.join(sourceDir, f), 'utf8')));
  const r = buildRegisterSpec({ map, text, file: map.file, commit, drafts });

  console.log(`source ${map.file} at ${commit}`);
  console.log(`imported ${Object.entries(r.counts).map(([k, n]) => `${n} ${k}`).join(', ')}`);
  console.log(`coverage: ${r.cov.ok ? 'every line held' : `FAILED at line ${r.cov.files[0].first?.line}: expected ${JSON.stringify(r.cov.files[0].first?.expected)}, got ${JSON.stringify(r.cov.files[0].first?.actual)}`}`);
  console.log(`rendering: ${r.unfaithful.length === 0 ? 'every row renders to its cells' : `${r.unfaithful.length} entities do not render to their cells`}; rendered from the file alone, ${r.rendered.files[0].lines - r.rendered.files[0].differing} of ${r.rendered.files[0].lines} lines are byte-identical`);
  for (const u of r.unfaithful.slice(0, 10)) console.error(`  ${u.id}\n    source:   ${u.raw}\n    rendered: ${u.rendered}`);
  if (r.loss.total) { console.error(`Not mapped (${r.loss.total} items in ${r.loss.kinds.size} kinds):`); for (const l of r.loss.lines()) console.error(`  ${l}`); }
  console.log(`untyped table shapes: ${r.unmatched.length}`);
  if (!r.ok) { console.error('Import failed; nothing written.'); process.exit(1); }
  if (typeof args['export-md'] === 'string') fs.writeFileSync(args['export-md'], renderMarkdown(parseJsonc(r.text)));
  if (args.check) {
    const cur = fs.existsSync(outFile) ? fs.readFileSync(outFile, 'utf8') : '';
    if (cur !== r.text) { console.error(`${outFile} is out of date.`); process.exit(1); }
    console.log(`${outFile} is up to date.`);
    return;
  }
  fs.mkdirSync(path.dirname(outFile), { recursive: true });
  fs.writeFileSync(outFile, r.text);
  console.log(`wrote ${outFile} (${Buffer.byteLength(r.text)} bytes)`);
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) main();
