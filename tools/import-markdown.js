#!/usr/bin/env node
// Import a structured Markdown specification into an Exegra specification
// project.
//
//   node tools/import-markdown.js --project <name> [--source <dir>] [--out <file>] [--map <file>] [--check]
//
// The tool reads the Markdown (never writes there), extracts what it states,
// invents nothing, and reports every construct it recognised but could not map.
// Its output can replace the Markdown in the source repository: the JSONC is then
// the specification's authority there, and this tool only runs against a
// checkout that still has the Markdown (an earlier commit).
// Same input, same bytes. Every imported entity is checked to render back to
// the words of the lines it came from, so the output needs no copy of them.
//
// What the Markdown does not state but Exegra requires (a category for each
// component), and what names the project and where its files are, comes from the
// project's import map, specs/<name>/import-map.jsonc:
//   { "project": { "id", "name", "title" }, "source": "<dir, relative to the map>",
//     "layout": { "whitepaper", "roadmap", "verification", "specsDir", "srcDir" },
//     "categories": { "<component ref>": "<category>" } }

import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { parse as parseJsonc } from 'jsonc-parser';
import { createWorkspace } from './workspace.js';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.resolve(HERE, '..');
/** Where a document of the Markdown specification lives, relative to its repository; an import map's "layout" overrides it. */
export const DEFAULT_LAYOUT = {
  whitepaper: 'specifications/00-vision/whitepaper.md',
  roadmap: 'specifications/00-vision/roadmap.md',
  verification: 'docs/agents/verification.md',
  specsDir: 'specifications',
  srcDir: 'src',
};
/** The layout of the conversion in progress (set by buildSpec; the parsing functions default their file names from it). */
let LAYOUT = { ...DEFAULT_LAYOUT };
/** The import map of a project in `specsDir`. @param {string} specsDir @param {string} project */
export function importMapFile(specsDir, project) { return path.join(specsDir, project, 'import-map.jsonc'); }

// ---------------------------------------------------------------------------
// Loss collection
// ---------------------------------------------------------------------------

export class Loss {
  constructor() {
    /** @type {Map<string, {count: number, examples: string[]}>} */
    this.kinds = new Map();
  }
  /** @param {string} kind @param {string} example */
  add(kind, example) {
    let e = this.kinds.get(kind);
    if (!e) { e = { count: 0, examples: [] }; this.kinds.set(kind, e); }
    e.count++;
    if (e.examples.length < 10) e.examples.push(example);
  }
  get total() { let n = 0; for (const e of this.kinds.values()) n += e.count; return n; }
  /** @returns {string[]} one line per loss kind, in first-seen order */
  lines() {
    return [...this.kinds].map(([k, e]) => `${k}: ${e.count} (e.g. ${e.examples.join('; ')})`);
  }
}

// ---------------------------------------------------------------------------
// Pure text helpers
// ---------------------------------------------------------------------------

/** Trim and collapse every run of whitespace (including newlines) to one space. @param {string} s */
export function collapse(s) { return s.replace(/\s+/g, ' ').trim(); }

/**
 * Text that spans several source lines, held with its structure: a first line,
 * then lines indented by `indent` spaces (a list item's body; 0 for a block).
 * Wrapped lines are joined with one space; blank lines, nested list items and
 * table rows stay separate lines, keeping their indentation relative to `indent`.
 * @param {string[]} lines @param {number} [indent]
 */
export function blockText(lines, indent = 0) {
  /** @type {string[]} */
  const out = [];
  lines.forEach((line, i) => {
    let l = line.replace(/\s+$/, '');
    if (i === 0) l = indent > 0 ? l.trim() : l;
    else l = l.slice(Math.min(/^ */.exec(l)?.[0].length ?? 0, indent));
    if (l === '') { out.push(''); return; }
    const prev = out.length ? out[out.length - 1] : '';
    const starts = /^\s*([-*+] |\d+\. |\||#)/.test(l);
    if (out.length && prev !== '' && !starts && !/^\s*\|/.test(prev)) out[out.length - 1] = `${prev} ${l.trim()}`;
    else out.push(l);
  });
  while (out.length && out[out.length - 1] === '') out.pop();
  return out.join('\n');
}

/**
 * Lines of `text` written after `head` (e.g. `- **D-1** `), its later lines
 * indented by `indent` spaces. @param {string} head @param {string} text @param {number} indent
 */
export function underHead(head, text, indent) {
  const [first, ...rest] = text.split('\n');
  return [`${head}${first}`.replace(/\s+$/, ''), ...rest.map((l) => (l === '' ? '' : ' '.repeat(indent) + l))];
}

/** @param {string} text */
export function splitLines(text) { return text.replace(/^\uFEFF/, '').split(/\r?\n/); }

/** Split a Markdown table row into cells, honouring backticks and `\|`. @param {string} line */
export function splitRow(line) {
  let s = line.trim();
  if (s.startsWith('|')) s = s.slice(1);
  if (s.endsWith('|') && !s.endsWith('\\|')) s = s.slice(0, -1);
  /** @type {string[]} */
  const cells = [];
  let cur = '';
  let tick = false;
  for (let i = 0; i < s.length; i++) {
    const ch = s[i];
    if (ch === '`') tick = !tick;
    if (ch === '\\' && s[i + 1] === '|') { cur += '|'; i++; continue; }
    if (ch === '|' && !tick) { cells.push(cur.trim()); cur = ''; continue; }
    cur += ch;
  }
  cells.push(cur.trim());
  return cells;
}

/** `C-2` -> `c-2`. @param {string} ref */
export function idOf(ref) { return ref.toLowerCase(); }

const MENTION = /\b(NG|G|D|K|Q|B|C)-(\d+)\b/g;
const RANGE = /\b(NG|G|D|K|Q|B|C)-(\d+) to \1-(\d+)\b/g;

/**
 * Ids (lower-cased, unique, in order of appearance) of the white paper's
 * reference classes mentioned in `text`, plus the "X-a to X-b" ranges (only the
 * endpoints are mentioned; the ids in between are not expanded).
 * @param {string} text
 */
export function extractMentions(text) {
  /** @type {string[]} */
  const ids = [];
  for (const m of text.matchAll(MENTION)) { const id = idOf(m[0]); if (!ids.includes(id)) ids.push(id); }
  const ranges = [...text.matchAll(RANGE)].map((m) => m[0]);
  return { ids, ranges };
}

/**
 * The index of the heading section starting at `start` (a heading line index):
 * lines up to, not including, the next heading of the same or a higher level.
 * @param {string[]} lines @param {RegExp} headingRe matches the heading line
 * @returns {{from: number, to: number} | null} from is the heading line index
 */
export function sectionRange(lines, headingRe) {
  const from = lines.findIndex((l) => headingRe.test(l));
  if (from < 0) return null;
  const level = /^(#+)/.exec(lines[from])?.[1].length ?? 1;
  let to = lines.length;
  for (let i = from + 1; i < lines.length; i++) {
    const h = /^(#+)\s/.exec(lines[i]);
    if (h && h[1].length <= level) { to = i; break; }
  }
  return { from, to };
}

// ---------------------------------------------------------------------------
// Requirements
// ---------------------------------------------------------------------------

const REQ_START = /^\*\*([A-Z]+-\d+)\*\*\s*(.*)$/;
const KEY_LINE = /^- ([A-Za-z][A-Za-z ]*?):\s*(.*)$/;
const KNOWN_REQ_KEYS = ['Status', 'Verify', 'Cases', 'Boundary', 'Traces', 'Depends', 'Rationale', 'Milestone', 'Seam'];

/**
 * @typedef {object} RawRequirement
 * @property {string} ref @property {string} id @property {string} statement
 * @property {number} line @property {number} endLine @property {string} file @property {string} section
 * @property {Record<string, string>} keys
 */

/**
 * Parse every `**ABC-123** statement` block (followed by `- Key: value` lines)
 * of one Markdown file.
 * @param {string} text @param {string} file path relative to the source root
 * @param {Loss} [loss]
 * @returns {RawRequirement[]}
 */
export function parseRequirements(text, file, loss = new Loss()) {
  const lines = splitLines(text);
  let section = '';
  /** @type {RawRequirement[]} */
  const out = [];
  for (let i = 0; i < lines.length; i++) {
    const h = /^#{1,6}\s+(.*\S)\s*$/.exec(lines[i]);
    if (h) { section = collapse(h[1]); continue; }
    const m = REQ_START.exec(lines[i]);
    if (!m) continue;
    const statement = [m[2]];
    /** @type {Record<string, string>} */
    const keys = {};
    /** @type {string|null} */
    let last = null;
    let j = i + 1;
    for (; j < lines.length && lines[j].trim() !== ''; j++) {
      const km = KEY_LINE.exec(lines[j]);
      if (km) {
        const key = km[1];
        if (Object.hasOwn(keys, key)) {
          loss.add('repeated key in requirement (values joined with a space)', `${m[1]} ${key}`);
          keys[key] += ' ' + km[2];
        } else keys[key] = km[2];
        last = key;
      } else if (last) keys[last] += ' ' + lines[j].trim();
      else statement.push(lines[j].trim());
    }
    for (const k of Object.keys(keys)) keys[k] = collapse(keys[k]);
    out.push({ ref: m[1], id: idOf(m[1]), statement: collapse(statement.join(' ')), line: i + 1, endLine: j, file, section, keys });
    i = j - 1;
  }
  return out;
}

/** @param {string} v */
function splitRefList(v) { return v.split(',').map((s) => s.trim()).filter(Boolean); }

/**
 * Turn a raw requirement into a claim, resolving references against `index`
 * (id -> entity kind). Unresolved or malformed things are recorded in `loss`.
 * @param {RawRequirement} r @param {Map<string, string>} index @param {Loss} loss @param {{caseIds?: Map<string, string>}} [ctx]
 */
export function requirementToClaim(r, index, loss, ctx = {}) {
  const k = r.keys;
  for (const key of Object.keys(k)) if (!KNOWN_REQ_KEYS.includes(key)) loss.add('unmapped requirement key', `${r.ref} "- ${key}:"`);
  if (!k.Verify) throw new Error(`${r.file}:${r.line} ${r.ref} has no "- Verify:" line, so Exegra's required "evaluate" cannot be filled.`);
  /** @type {Record<string, any>} */
  const c = { id: r.id, kind: 'requirement', statement: r.statement };
  if (k.Rationale) c.rationale = k.Rationale;

  // Components named in the statement or the Boundary line.
  const subjects = [];
  for (const id of extractMentions(`${r.statement} ${k.Boundary ?? ''}`).ids) {
    if (!/^c-\d+$/.test(id)) continue;
    if (index.get(id) === 'component') subjects.push(id);
    else loss.add('unresolved reference (subjects)', `${r.ref} -> ${id.toUpperCase()}`);
  }
  if (subjects.length) c.subjects = subjects;
  c.evaluate = { method: k.Verify };

  c.ref = r.ref;
  c.source = `${r.file}:${r.line}`;
  c.area = r.file.split('/')[1] ?? '';
  if (r.section) c.section = r.section;
  c.lifecycle = 'active';
  if (k.Status !== undefined) {
    if (k.Status === 'retired') c.lifecycle = 'retired';
    else loss.add('unmapped Status value', `${r.ref} "${k.Status}"`);
  }
  if (k.Boundary) {
    const m = /^(B-\d+)\b\s*(.*)$/.exec(k.Boundary);
    if (!m) loss.add('Boundary line without a B- id', `${r.ref} "${k.Boundary}"`);
    else {
      if (index.get(idOf(m[1])) === 'boundary') c.boundary = idOf(m[1]);
      else loss.add('unresolved reference (boundary)', `${r.ref} -> ${m[1]}`);
      if (m[2]) c.boundaryDetail = m[2];
    }
  }
  if (k.Traces !== undefined) {
    const traces = [];
    for (const t of splitRefList(k.Traces)) {
      const id = idOf(t);
      const kind = index.get(id);
      if (/^[A-Z]+-\d+$/.test(t) && kind && TRACE_KINDS.includes(kind)) { if (!traces.includes(id)) traces.push(id); }
      else loss.add('unresolved reference (traces)', `${r.ref} -> ${t}`);
    }
    if (traces.length) c.traces = traces;
  }
  if (k.Depends !== undefined) {
    const deps = [];
    for (const t of splitRefList(k.Depends)) {
      const id = idOf(t);
      if (/^[A-Z]+-\d+$/.test(t) && index.get(id) === 'claim') { if (!deps.includes(id)) deps.push(id); }
      else loss.add('unresolved reference (depends)', `${r.ref} -> ${t}`);
    }
    if (deps.length) c.dependsOn = deps;
  }
  for (const [key, prop] of /** @type {const} */ ([['Milestone', 'milestone'], ['Seam', 'seam']])) {
    if (k[key] === undefined) continue;
    if (/^\d+$/.test(k[key])) c[prop] = Number(k[key]);
    else loss.add(`non-numeric ${key}`, `${r.ref} "${k[key]}"`);
  }
  if (k.Cases) {
    /** @type {string[]} */ const ids = [];
    /** @type {string[]} */ const unresolved = [];
    for (const p of splitRefList(k.Cases)) {
      const id = ctx.caseIds?.get(p);
      if (id) { if (!ids.includes(id)) ids.push(id); } else { unresolved.push(p); loss.add('Cases path matching no case-table file', `${r.ref} -> ${p}`); }
    }
    if (ids.length) c.cases = ids;
    if (unresolved.length) c.casesPath = unresolved.join(', ');
  }
  return c;
}

/** Entity kinds a requirement's Traces may resolve to. */
export const TRACE_KINDS = ['goal', 'nonGoal', 'constraint', 'decision', 'openQuestion'];

// ---------------------------------------------------------------------------
// White paper tables and lists
// ---------------------------------------------------------------------------

/**
 * Table rows whose first cell matches `idRe`, within lines[from, to).
 * Rows with the wrong cell count are recorded in `loss` and skipped.
 * @param {string[]} lines @param {number} from @param {number} to
 * @param {RegExp} idRe @param {number} cols @param {string} what @param {Loss} loss
 * @param {number} [idCol]
 */
function tableRows(lines, from, to, idRe, cols, what, loss, idCol = 0) {
  /** @type {{cells: string[], line: number}[]} */
  const rows = [];
  for (let i = from; i < to; i++) {
    if (!lines[i].startsWith('|')) continue;
    const cells = splitRow(lines[i]);
    if (!idRe.test(cells[idCol] ?? '')) continue;
    if (cells.length !== cols) { loss.add(`unparsable ${what} row`, `line ${i + 1}: ${cells.length} cells, expected ${cols}`); continue; }
    rows.push({ cells, line: i + 1 });
  }
  return rows;
}

/**
 * Process-topology rows `| C-n | Component | Owns | Talks to |`.
 * @param {string} text white paper text @param {string} [file] @param {Loss} [loss]
 */
export function parseComponentRows(text, file = LAYOUT.whitepaper, loss = new Loss()) {
  const lines = splitLines(text);
  const r = sectionRange(lines, /^### Process topology\s*$/);
  if (!r) return [];
  return tableRows(lines, r.from, r.to, /^C-\d+$/, 4, 'component', loss).map(({ cells, line }) => ({
    ref: cells[0], id: idOf(cells[0]), name: cells[1],
    owns: cells[2], talksTo: cells[3], line, source: `${file}:${line}`,
  }));
}

/**
 * Boundary rows `| B-n | Boundary | Kind | Who uses it |`.
 * @param {string} text white paper text @param {string} [file] @param {Loss} [loss]
 */
export function parseBoundaryRows(text, file = LAYOUT.whitepaper, loss = new Loss()) {
  const lines = splitLines(text);
  const r = sectionRange(lines, /^## Boundaries\s*$/);
  if (!r) return [];
  return tableRows(lines, r.from, r.to, /^B-\d+$/, 4, 'boundary', loss).map(({ cells, line }) => ({
    ref: cells[0], id: idOf(cells[0]), name: cells[1], interfaceKind: cells[2], usedBy: cells[3], line, source: `${file}:${line}`,
  }));
}

/**
 * Trust boundaries: numbered items `N. **Name** ...`; every component id named
 * in an item gets that item's level and zone name.
 * @param {string} text
 */
export function parseTrustZones(text) {
  const lines = splitLines(text);
  const r = sectionRange(lines, /^### Trust boundaries\s*$/);
  /** @type {{level: number, zone: string, components: string[]}[]} */
  const zones = [];
  if (!r) return zones;
  for (let i = r.from + 1; i < r.to; i++) {
    const m = /^(\d+)\.\s+\*\*(.+?)\*\*(.*)$/.exec(lines[i]);
    if (!m) continue;
    let body = m[3];
    let j = i + 1;
    while (j < r.to && /^\s+\S/.test(lines[j])) body += ' ' + lines[j++].trim();
    const components = [...body.matchAll(/\bC-\d+\b/g)].map((x) => idOf(x[0]));
    zones.push({ level: Number(m[1]), zone: m[2].replace(/:$/, ''), components: [...new Set(components)] });
    i = j - 1;
  }
  return zones;
}

/**
 * Top-level bullets `- **ID** text` within lines[from, to), with the group
 * heading (a plain line followed directly by a bullet) each sits under.
 * @param {string[]} lines @param {number} from @param {number} to @param {RegExp} idRe e.g. /^[A-Z]+-\d+$/
 */
export function parseBullets(lines, from, to, idRe) {
  /** @type {{ref: string, id: string, text: string, line: number, end: number, group: string}[]} */
  const out = [];
  let group = '';
  for (let i = from; i < to; i++) {
    const l = lines[i];
    const prevBlank = i === 0 || lines[i - 1].trim() === '';
    if (l.trim() && prevBlank && !/^[-|#>\s]/.test(l) && !/^\d+\./.test(l) && /^- \*\*/.test(lines[i + 1] ?? '')) { group = collapse(l); continue; }
    const m = /^- \*\*([A-Z]+-\d+)\*\*\s*(.*)$/.exec(l);
    if (!m || !idRe.test(m[1])) continue;
    let j = i + 1;
    while (j < to) {
      if (/^\s+\S/.test(lines[j])) { /* continuation or nested item */ }
      else if (lines[j].trim() === '' && /^\s{2,}\S/.test(lines[j + 1] ?? '')) { /* blank inside an item */ }
      else break;
      j++;
    }
    out.push({ ref: m[1], id: idOf(m[1]), text: blockText([m[2], ...lines.slice(i + 1, j)], 2), line: i + 1, end: j, group });
    i = j - 1;
  }
  return out;
}

/** Ids named in `text` by `re`, lower-cased, unique, in order of appearance. @param {string} text @param {RegExp} re */
function idsIn(text, re) {
  /** @type {string[]} */
  const ids = [];
  for (const m of text.matchAll(re)) { const id = idOf(m[0]); if (!ids.includes(id)) ids.push(id); }
  return ids;
}

/** @param {string} text @param {RegExp} headingRe */
function bulletsIn(text, headingRe, idRe) {
  const lines = splitLines(text);
  const r = sectionRange(lines, headingRe);
  return r ? parseBullets(lines, r.from + 1, r.to, idRe) : [];
}

/** First paragraph under the `# <title>` heading. @param {string} text @param {string} title */
export function firstParagraph(text, title) {
  const lines = splitLines(text);
  const i = lines.findIndex((l) => l.trim() === `# ${title}`);
  if (i < 0) return '';
  let j = i + 1;
  while (j < lines.length && lines[j].trim() === '') j++;
  const parts = [];
  for (; j < lines.length && lines[j].trim() !== ''; j++) parts.push(lines[j]);
  return collapse(parts.join(' '));
}

/**
 * The white paper's release-stage table.
 * @param {string} text @param {Loss} loss
 */
export function parseReleaseStages(text, loss = new Loss()) {
  const lines = splitLines(text);
  const r = sectionRange(lines, /^### Release stages\s*$/);
  if (!r) return [];
  return tableRows(lines, r.from, r.to, /^\*\*.+\*\*$/, 4, 'release stage', loss).map(({ cells, line }) => {
    const bold = cells[0].slice(2, -2);
    const m = /^(R\d+(?:\.\d+)?)\s+(.*)$/.exec(bold);
    const ref = m ? m[1] : bold;
    const id = m ? m[1].toLowerCase().replace(/\./g, '_') : bold.toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-|-$/g, '');
    return { ref, id, name: m ? m[2] : bold, purpose: cells[1], milestones: cells[2], exitEvidence: cells[3], line };
  });
}

/**
 * The white paper's numbered milestone list: number -> text after the title.
 * @param {string} text
 */
export function parseWhitepaperMilestones(text) {
  const lines = splitLines(text);
  const r = sectionRange(lines, /^### Milestones\s*$/);
  /** @type {Map<number, string>} */
  const out = new Map();
  if (!r) return out;
  for (let i = r.from + 1; i < r.to; i++) {
    const m = /^(\d+)\.\s+(.*)$/.exec(lines[i]);
    if (!m) continue;
    const parts = [m[2]];
    let j = i + 1;
    while (j < r.to && /^\s+\S/.test(lines[j])) parts.push(lines[j++].trim());
    out.set(Number(m[1]), collapse(parts.join(' ')));
    i = j - 1;
  }
  return out;
}

/**
 * The roadmap's `### RM-n Title` sections.
 * @param {string} text @param {string} [file]
 */
export function parseRoadmapMilestones(text, file = LAYOUT.roadmap) {
  const lines = splitLines(text);
  const out = [];
  for (let i = 0; i < lines.length; i++) {
    const m = /^### (RM-(\d+)) (.+?)\s*$/.exec(lines[i]);
    if (!m) continue;
    let j = i + 1;
    while (j < lines.length && !/^#{1,3} /.test(lines[j])) j++;
    const body = lines.slice(i + 1, j);
    const flat = collapse(body.join(' '));
    const proves = /^\*\*Proves:\*\*\s*(.*)$/.exec(body.find((l) => l.startsWith('**Proves:**')) ?? '');
    let provesText = '';
    const pi = body.findIndex((l) => l.startsWith('**Proves:**'));
    if (pi >= 0 && proves) {
      const parts = [proves[1]];
      for (let k = pi + 1; k < body.length && body[k].trim() !== ''; k++) parts.push(body[k].trim());
      provesText = collapse(parts.join(' '));
    }
    let stage = '';
    const sm = /(?:^|\s|^- )Stage: ([^\n]*?)\.?\s*$/m.exec(body.join('\n')) ?? /\bStage: ([^.\n]*)\./.exec(flat);
    if (sm) stage = collapse(sm[1]);
    let a = i + 1; let b = j; while (a < b && lines[a].trim() === '') a++;
    while (b > a && lines[b - 1].trim() === '') b--;
    out.push({ ref: m[1], id: idOf(m[1]), number: Number(m[2]), name: m[3], proves: provesText, stage, detail: blockText(lines.slice(a, b), 0), startLine: a + 1, endLine: b, source: `${file}:${i + 1}` });
    i = j - 1;
  }
  return out;
}

// ---------------------------------------------------------------------------
// Documents, sections, case tables, terms
// ---------------------------------------------------------------------------

/** Lines of a file as written (no line terminators; a final terminator does not add an empty line). @param {string} text */
export function fileLines(text) {
  const l = splitLines(text);
  if (l.length && l[l.length - 1] === '') l.pop();
  return l;
}

/** @param {string} s */
export function slugify(s) { return s.toLowerCase().replace(/[^a-z0-9_]+/g, '-').replace(/^-+|-+$/g, ''); }
/** `specifications/04-platform-kernel/kernel.md` -> `04-platform-kernel-kernel`. @param {string} p */
export function pathSlug(p) { return slugify(p.replace(/^specifications\//, '').replace(/\.md$/, '')); }
/** Returns a function making ids unique by appending -2, -3, ... in call order. */
export function uniquifier() {
  const seen = new Set();
  return (/** @type {string} */ id) => { let c = id; let n = 2; while (seen.has(c)) c = `${id}-${n++}`; seen.add(c); return c; };
}

export const DOCUMENT_ROLES = ['whitepaper', 'roadmap', 'requirements', 'cases', 'glossary', 'index'];
/** @param {string} file */
export function roleOf(file) {
  if (file === LAYOUT.whitepaper) return 'whitepaper';
  if (file === LAYOUT.roadmap) return 'roadmap';
  if (file === `${LAYOUT.specsDir}/glossary.md`) return 'glossary';
  if (file === `${LAYOUT.specsDir}/index.md`) return 'index';
  return file.includes('/cases/') ? 'cases' : 'requirements';
}

const MARKER = /^\{\{entity:([^}]+)\}\}$/;
/** @param {string} id */
export function marker(id) { return `{{entity:${id}}}`; }

/**
 * Split one Markdown file into a document, its sections (non-case files) or a
 * case table (case files). `runs` are the line ranges (1-based, inclusive) that
 * were imported as separate entities; each is replaced in the section body by
 * one marker line.
 * @param {string} file @param {string} text
 * @param {{id: string, start: number, end: number}[]} runs
 */
export function buildDocumentEntities(file, text, runs) {
  const lines = fileLines(text);
  const slug = pathSlug(file);
  const docId = `doc-${slug}`;
  const role = roleOf(file);
  /** @type {{i: number, level: number, title: string}[]} */
  const heads = [];
  let fence = false;
  lines.forEach((l, i) => {
    if (/^\s*(```|~~~)/.test(l)) { fence = !fence; return; }
    const h = !fence && /^(#{1,6})\s+(.*\S)\s*$/.exec(l);
    if (h) heads.push({ i, level: h[1].length, title: h[2] });
  });
  const document = { id: docId, path: file, ...(heads.length ? { title: heads[0].title } : {}), role, source: `${file}:1` };
  /** @type {Map<string, string>} entity id -> section id */
  const sectionOf = new Map();
  if (role === 'cases') {
    let columns, rowCount;
    for (let i = 0; i + 1 < lines.length; i++) {
      if (lines[i].startsWith('|') && /^\|?\s*:?-{3,}/.test(lines[i + 1])) {
        columns = splitRow(lines[i]);
        rowCount = 0;
        for (let k = i + 2; k < lines.length && lines[k].startsWith('|'); k++) rowCount++;
        break;
      }
    }
    const caseTable = { id: `cases-${slug}`, path: file, ...(heads.length ? { title: heads[0].title } : {}), document: docId, body: lines.length ? lines.join('\n') + '\n' : '', ...(columns ? { columns, rowCount } : {}), source: `${file}:1` };
    return { document, sections: [], caseTable, sectionOf };
  }
  const byStart = new Map(runs.map((r) => [r.start, r]));
  let placed = 0;
  /** @param {number} from @param {number} to 0-based [from, to) */
  const bodyOf = (from, to) => {
    /** @type {string[]} */
    const out = [];
    for (let i = from; i < to; i++) {
      const r = byStart.get(i + 1);
      if (r) {
        if (r.end > to) throw new Error(`${file}:${r.start}: entity ${r.id} runs past the end of its section.`);
        out.push(marker(r.id)); placed++;
        i = r.end - 1;
      } else {
        if (MARKER.test(lines[i])) throw new Error(`${file}:${i + 1}: a line looks like an entity marker.`);
        out.push(lines[i]);
      }
    }
    return out.length ? out.join('\n') + '\n' : '';
  };
  /** @type {Record<string, any>[]} */
  const sections = [];
  /** @type {{id: string, level: number}[]} */
  const stack = [];
  const addSection = (/** @type {number} */ level, /** @type {string} */ title, /** @type {number} */ headLine, /** @type {number} */ from, /** @type {number} */ to) => {
    const id = `sec-${slug}-${sections.length + 1}`;
    while (stack.length && stack[stack.length - 1].level >= level) stack.pop();
    const body = bodyOf(from, to);
    const sec = { id, title, level, document: docId, ...(stack.length && level > 0 ? { parent: stack[stack.length - 1].id } : {}), order: sections.length + 1, body, source: `${file}:${headLine}` };
    for (const m of body.split('\n')) { const mm = MARKER.exec(m); if (mm) sectionOf.set(mm[1], id); }
    sections.push(sec);
    if (level > 0) stack.push({ id, level });
  };
  if ((heads.length ? heads[0].i : lines.length) > 0) addSection(0, '', 1, 0, heads.length ? heads[0].i : lines.length);
  heads.forEach((h, k) => addSection(h.level, h.title, h.i + 1, h.i + 1, k + 1 < heads.length ? heads[k + 1].i : lines.length));
  if (placed !== runs.length) throw new Error(`${file}: ${runs.length - placed} imported entit${runs.length - placed === 1 ? 'y' : 'ies'} not placed in any section body.`);
  return { document, sections, caseTable: undefined, sectionOf };
}

/**
 * Glossary entries: top-level bullets `- **Term**: definition` in lines[from, to).
 * @param {string[]} lines @param {number} from @param {number} to @param {Loss} [loss] @param {string} [file]
 */
export function parseTerms(lines, from, to, loss = new Loss(), file = '') {
  /** @type {{term: string, definition: string, line: number, end: number}[]} */
  const out = [];
  for (let i = from; i < to; i++) {
    if (!lines[i].startsWith('- ')) continue;
    const m = /^- \*\*(.+?)\*\*:?\s*(.*)$/.exec(lines[i]);
    if (!m) { loss.add('glossary bullet that is not "- **Term**: definition"', `${file}:${i + 1}`); continue; }
    let j = i + 1;
    while (j < to && /^\s+\S/.test(lines[j])) j++;
    out.push({ term: m[1], definition: blockText([m[2], ...lines.slice(i + 1, j)], 2), line: i + 1, end: j });
    i = j - 1;
  }
  return out;
}

// ---------------------------------------------------------------------------
// Reconstruction and the coverage check
// ---------------------------------------------------------------------------

/** The lists whose entities stand in section bodies as markers. */
export const RENDERED_LISTS = ['components', 'goals', 'nonGoals', 'boundaries', 'decisions', 'constraints', 'openQuestions', 'releaseStages', 'milestones', 'claims', 'terms'];

/** A table row; `|` outside code spans is escaped. @param {string[]} cells */
function tableRow(cells) {
  const esc = (/** @type {string} */ c) => c.split(/(`[^`]*`)/).map((part, i) => (i % 2 ? part : part.replace(/\|/g, '\\|'))).join('');
  return `| ${cells.map(esc).join(' | ')} |`;
}

/**
 * The Markdown of one imported entity, rendered from its properties alone.
 * Requirement attributes come in one fixed order.
 * @param {string} list the specification list the entity is in
 * @param {Record<string, any>} e
 * @param {Map<string, Record<string, any>>} byId every entity by id (for references)
 * @returns {string[]} lines
 */
export function renderEntity(list, e, byId) {
  const refOf = (/** @type {string} */ id) => byId.get(id)?.ref ?? id;
  switch (list) {
    case 'claims': {
      const out = [`**${e.ref}** ${e.statement}`];
      if (e.lifecycle === 'retired') out.push('- Status: retired');
      if (e.evaluate?.method) out.push(`- Verify: ${e.evaluate.method}`);
      const cases = [...(e.cases ?? []).map((/** @type {string} */ id) => byId.get(id)?.path ?? id), ...(e.casesPath ? [e.casesPath] : [])];
      if (cases.length) out.push(`- Cases: ${cases.join(', ')}`);
      const boundary = [e.boundary ? refOf(e.boundary) : '', e.boundaryDetail ?? ''].filter(Boolean).join(' ');
      if (boundary) out.push(`- Boundary: ${boundary}`);
      if (e.traces?.length) out.push(`- Traces: ${e.traces.map(refOf).join(', ')}`);
      if (e.dependsOn?.length) out.push(`- Depends: ${e.dependsOn.map(refOf).join(', ')}`);
      if (e.rationale) out.push(`- Rationale: ${e.rationale}`);
      if (e.milestone !== undefined) out.push(`- Milestone: ${e.milestone}`);
      if (e.seam !== undefined) out.push(`- Seam: ${e.seam}`);
      return out;
    }
    case 'components': return [tableRow([e.ref, e.name, e.purpose ?? '', e.talksTo ?? ''])];
    case 'boundaries': return [tableRow([e.ref, e.name, e.interfaceKind ?? '', e.usedBy ?? ''])];
    case 'releaseStages': return [tableRow([`**${e.ref === e.name ? e.name : `${e.ref} ${e.name}`}**`, e.purpose ?? '', e.milestones ?? '', e.exitEvidence ?? ''])];
    case 'goals': return underHead(`- **${e.ref}** `, e.stage === undefined ? e.statement : `${e.statement} *(${e.stage})*`, 2);
    case 'nonGoals': return underHead(`- **${e.ref}** `, e.horizon === undefined ? e.statement : `*${e.horizon}* ${e.statement}`, 2);
    case 'decisions': case 'constraints': case 'openQuestions': return underHead(`- **${e.ref}** `, e.statement, 2);
    case 'terms': return underHead(`- **${e.term}**: `, e.definition, 2);
    case 'milestones': return String(e.detail ?? '').split('\n');
    default: throw new Error(`No Markdown rendering for entities of "${list}".`);
  }
}

/** Every entity of the rendered lists, by id. @param {any} spec */
export function renderIndex(spec) {
  /** @type {Map<string, Record<string, any>>} */
  const byId = new Map();
  /** @type {Map<string, string>} */
  const listOf = new Map();
  for (const list of [...RENDERED_LISTS, 'caseTables']) for (const e of spec[list] ?? []) { byId.set(e.id, e); listOf.set(e.id, list); }
  return { byId, listOf };
}

/** @param {Record<string, string>} keys */
function sortedKeys(keys) { return JSON.stringify(Object.keys(keys).sort().map((k) => [k, keys[k]])); }

/**
 * Whether `e` renders back to the words of `raw`, the lines it was imported
 * from. Line wrapping is not compared. A requirement is compared as parsed:
 * the same statement and the same attribute values, in any order.
 * @param {string} list @param {Record<string, any>} e @param {string} raw @param {Map<string, Record<string, any>>} byId
 * @returns {string|null} null when faithful, else the rendering
 */
export function unfaithfulRendering(list, e, raw, byId) {
  const rendered = renderEntity(list, e, byId).join('\n');
  if (list === 'claims') {
    const [a] = parseRequirements(raw, '');
    const [b] = parseRequirements(rendered, '');
    return a && b && a.ref === b.ref && a.statement === b.statement && sortedKeys(a.keys) === sortedKeys(b.keys) ? null : rendered;
  }
  return collapse(rendered) === collapse(raw) ? null : rendered;
}

/**
 * Rebuild every Markdown file from the model. Markers expand to `expand(id)`,
 * by default the entity rendered from its properties.
 * @param {any} spec plain value of the generated specification
 * @param {(id: string) => string|undefined} [expand]
 * @returns {Map<string, string>} path -> text (lines terminated by \n)
 */
export function reconstructMarkdown(spec, expand) {
  if (!expand) {
    const { byId, listOf } = renderIndex(spec);
    expand = (id) => {
      const list = listOf.get(id);
      const e = byId.get(id);
      return list && e && list !== 'caseTables' ? renderEntity(list, e, byId).join('\n') : undefined;
    };
  }
  /** @type {Map<string, any[]>} */
  const secsByDoc = new Map();
  for (const s of spec.sections ?? []) { if (!secsByDoc.has(s.document)) secsByDoc.set(s.document, []); secsByDoc.get(s.document)?.push(s); }
  const caseByDoc = new Map((spec.caseTables ?? []).map((/** @type {any} */ c) => [c.document, c]));
  /** @type {Map<string, string>} */
  const out = new Map();
  for (const d of spec.documents ?? []) {
    const ct = caseByDoc.get(d.id);
    if (ct) { out.set(d.path, ct.body); continue; }
    const secs = (secsByDoc.get(d.id) ?? []).sort((a, b) => a.order - b.order);
    /** @type {string[]} */
    const lines = [];
    for (const s of secs) {
      if (s.level > 0) lines.push(`${'#'.repeat(s.level)} ${s.title}`);
      if (!s.body) continue;
      for (const l of s.body.slice(0, -1).split('\n')) {
        const m = MARKER.exec(l);
        if (!m) { lines.push(l); continue; }
        const r = expand(m[1]);
        if (r === undefined) throw new Error(`Section ${s.id} names entity ${m[1]}, which is not an imported entity that renders to Markdown.`);
        lines.push(...r.split('\n'));
      }
    }
    out.set(d.path, lines.length ? lines.join('\n') + '\n' : '');
  }
  return out;
}

/** Normalised lines: line endings as \n, trailing whitespace stripped per line, no final terminator. @param {string} t */
function normLines(t) { return fileLines(t).map((l) => l.replace(/\s+$/, '')); }

/**
 * Compare reconstructed files with the files on disk.
 * @param {Map<string, string>} rebuilt @param {Map<string, string>} onDisk
 */
export function coverage(rebuilt, onDisk) {
  /** @type {{path: string, identical: boolean, lines: number, differing: number, first?: {line: number, expected: string, actual: string}}[]} */
  const files = [];
  let lines = 0; let bytes = 0;
  for (const [p, disk] of onDisk) {
    const a = normLines(disk);
    const b = rebuilt.has(p) ? normLines(/** @type {string} */ (rebuilt.get(p))) : [];
    lines += a.length; bytes += Buffer.byteLength(disk);
    let differing = Math.abs(a.length - b.length);
    let first;
    for (let i = 0; i < Math.min(a.length, b.length); i++) if (a[i] !== b[i]) { differing++; first ??= { line: i + 1, expected: a[i], actual: b[i] }; }
    if (!first && a.length !== b.length) { const i = Math.min(a.length, b.length); first = { line: i + 1, expected: a[i] ?? '(end of file)', actual: b[i] ?? '(end of file)' }; }
    files.push({ path: p, identical: differing === 0 && rebuilt.has(p), lines: a.length, differing, first });
  }
  for (const p of rebuilt.keys()) if (!onDisk.has(p)) files.push({ path: p, identical: false, lines: 0, differing: 1, first: { line: 0, expected: '(no such file)', actual: '(reconstructed)' } });
  return { files, lines, bytes, ok: files.every((f) => f.identical) };
}

// ---------------------------------------------------------------------------
// Git commit of the source repository (read from files, no shelling out)
// ---------------------------------------------------------------------------

/** @param {string} dir */
export function readGitHead(dir) {
  try {
    const gitDir = path.join(dir, '.git');
    const head = fs.readFileSync(path.join(gitDir, 'HEAD'), 'utf8').trim();
    const m = /^ref:\s*(.+)$/.exec(head);
    if (!m) return head;
    const refFile = path.join(gitDir, ...m[1].split('/'));
    if (fs.existsSync(refFile)) return fs.readFileSync(refFile, 'utf8').trim();
    const packed = fs.readFileSync(path.join(gitDir, 'packed-refs'), 'utf8');
    for (const l of packed.split(/\r?\n/)) {
      const pm = /^([0-9a-f]{40}) (.+)$/.exec(l);
      if (pm && pm[2] === m[1]) return pm[1];
    }
  } catch { /* fall through */ }
  return 'unknown';
}

// ---------------------------------------------------------------------------
// Files
// ---------------------------------------------------------------------------

/** All files below `dir` ending in `.md`, relative with forward slashes, sorted by path. @param {string} dir @param {string} sub */
function listMarkdown(dir, sub) {
  /** @type {string[]} */
  const out = [];
  const walk = (/** @type {string} */ rel) => {
    for (const e of fs.readdirSync(path.join(dir, rel), { withFileTypes: true })) {
      const r = rel ? `${rel}/${e.name}` : e.name;
      if (e.isDirectory()) walk(r);
      else if (e.name.endsWith('.md')) out.push(r);
    }
  };
  if (fs.existsSync(path.join(dir, sub))) walk(sub);
  return out.sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
}

/** @param {string} dir @param {string} rel */
function readText(dir, rel) { return fs.readFileSync(path.join(dir, rel), 'utf8'); }

/** @param {string} dir */
function countFiles(dir) {
  if (!fs.existsSync(dir)) return 0;
  let n = 0;
  for (const e of fs.readdirSync(dir, { withFileTypes: true })) n += e.isDirectory() ? countFiles(path.join(dir, e.name)) : 1;
  return n;
}

// ---------------------------------------------------------------------------
// Vocabulary
// ---------------------------------------------------------------------------

const MENTION_KINDS = ['goal', 'nonGoal', 'boundary', 'decision', 'constraint', 'openQuestion', 'component'];
const REF_PROPS = {
  ref: { type: 'string', label: 'Source id', doc: 'The identifier as written in the Markdown specification.' },
  source: { type: 'string', label: 'Source', doc: 'File and line in the source repository where this was imported from.' },
  mentions: { type: 'list', items: { type: 'ref', ref: MENTION_KINDS }, label: 'Mentions', doc: 'Goals, non-goals, boundaries, decisions, constraints, open questions and components named in the text.' },
};
/** Every kind a prose mention may resolve to. */
const ALL_MENTION_KINDS = [...MENTION_KINDS, 'releaseStage', 'milestone', 'claim'];

/** @param {Record<string, any>} extra */
function kindProps(extra) { return { ...extra, ref: { ...REF_PROPS.ref, required: true }, source: REF_PROPS.source, mentions: REF_PROPS.mentions }; }

/** @param {Record<string, {label: string, description: string}>} methods */
function buildVocabulary(methods) {
  return {
    entityKinds: {
      document: { label: 'Document', section: 'documents', shape: 'box', color: 'slate', doc: 'One Markdown file of the specification tree.',
        properties: { path: { type: 'string', required: true, label: 'Path', doc: 'Relative to the source repository root.' }, title: { type: 'string', label: 'Title', doc: 'The first heading of the file.' }, role: { type: 'enum', values: DOCUMENT_ROLES, required: true, label: 'Role' }, source: REF_PROPS.source } },
      section: { label: 'Section', section: 'sections', shape: 'chamfer', color: 'neutral', doc: 'One heading of a document and the Markdown under it, up to the next heading. Level 0 is the text before the first heading of a file.',
        properties: { title: { type: 'string', label: 'Title' }, level: { type: 'number', required: true, label: 'Heading level' }, document: { type: 'ref', ref: ['document'], required: true, label: 'Document' }, parent: { type: 'ref', ref: ['section'], label: 'Parent section' }, order: { type: 'number', required: true, label: 'Order', doc: 'Position within the document.' }, body: { type: 'text', label: 'Body', doc: 'The own Markdown of the section, verbatim. Lines imported as separate entities are replaced by one {{entity:<id>}} marker line each, which stands for that entity rendered from its properties.' }, mentions: { type: 'list', items: { type: 'ref', ref: ALL_MENTION_KINDS }, label: 'Mentions', doc: 'Entities named in the body.' }, source: REF_PROPS.source } },
      caseTable: { label: 'Case table', section: 'caseTables', shape: 'cylinder', color: 'teal', doc: 'A file under a cases/ directory of the specification tree: the table a conformance requirement reads.',
        properties: { path: { type: 'string', required: true, label: 'Path' }, title: { type: 'string', label: 'Title' }, document: { type: 'ref', ref: ['document'], required: true, label: 'Document' }, body: { type: 'text', required: true, label: 'Body', doc: 'The whole file, verbatim.' }, columns: { type: 'list', items: { type: 'string' }, label: 'Columns', doc: 'Header cells of the first table of the file.' }, rowCount: { type: 'number', label: 'Rows', doc: 'Data rows of the first table of the file.' }, source: REF_PROPS.source } },
      term: { label: 'Term', section: 'terms', shape: 'capsule', color: 'blue', doc: 'A glossary entry, from a glossary.md of the specification tree or the Glossary section of the white paper.',
        properties: { term: { type: 'string', required: true, label: 'Term' }, definition: { type: 'text', required: true, label: 'Definition' }, mentions: { type: 'list', items: { type: 'ref', ref: ALL_MENTION_KINDS }, label: 'Mentions' }, source: REF_PROPS.source } },
      goal: { label: 'Goal', section: 'goals', shape: 'diamond', color: 'green', doc: 'A goal of the white paper (G-n): one observable outcome with the release stage that first requires it.',
        properties: kindProps({ statement: { type: 'text', required: true, label: 'Statement' }, stage: { type: 'string', label: 'Release stage tag', doc: 'The tag at the end of the goal, as written.' }, group: { type: 'string', label: 'Group', doc: 'The subject heading the goal is listed under.' } }) },
      nonGoal: { label: 'Non-goal', section: 'nonGoals', shape: 'sphere', color: 'red', doc: 'A non-goal of the white paper (NG-n).',
        properties: kindProps({ statement: { type: 'text', required: true, label: 'Statement' }, horizon: { type: 'string', label: 'Horizon', doc: 'The italic lead-in as written, e.g. "Not at launch." or "Never."' } }) },
      boundary: { label: 'Boundary', section: 'boundaries', shape: 'pipe', color: 'teal', doc: 'A public or internal boundary of the white paper (B-n): the surfaces at which requirements may be stated.',
        properties: kindProps({ name: { type: 'string', required: true, label: 'Name' }, interfaceKind: { type: 'string', label: 'Kind', doc: 'The boundary table\'s Kind column.' }, usedBy: { type: 'text', label: 'Used by' } }) },
      decision: { label: 'Decision', section: 'decisions', shape: 'capsule', color: 'violet', doc: 'A decision of the white paper (D-n).',
        properties: kindProps({ title: { type: 'string', required: true, label: 'Title' }, statement: { type: 'text', label: 'Statement', doc: 'The decision as written in the white paper, sub-points included.' }, group: { type: 'string', label: 'Group' }, owner: { type: 'string', label: 'Decided by', doc: 'The first word of "Decided by": founder or draft.' }, decided: { type: 'string', label: 'Decided by (as written)' }, reversibility: { type: 'string', label: 'Reversibility', doc: 'two-way, costly or one-way, as written in the decision index.' } }) },
      constraint: { label: 'Constraint', section: 'constraints', shape: 'octa', color: 'amber', doc: 'A measurable limit of the white paper (K-n).',
        properties: kindProps({ statement: { type: 'text', required: true, label: 'Statement' }, group: { type: 'string', label: 'Group' } }) },
      openQuestion: { label: 'Open question', section: 'openQuestions', shape: 'tablet', color: 'rose', doc: 'An open question of the white paper (Q-n), with its answer once recorded.',
        properties: kindProps({ statement: { type: 'text', required: true, label: 'Statement' } }) },
      releaseStage: { label: 'Release stage', section: 'releaseStages', shape: 'box', color: 'steel', doc: 'A release stage of the white paper\'s dependency order (R0, R0.5, R1, ...).',
        properties: kindProps({ name: { type: 'string', required: true, label: 'Name' }, purpose: { type: 'text', label: 'Purpose' }, milestones: { type: 'string', label: 'Milestones', doc: 'The Milestones column as written.' }, exitEvidence: { type: 'text', label: 'Exit evidence' } }) },
      milestone: { label: 'Milestone', section: 'milestones', shape: 'hex', color: 'blue', doc: 'A roadmap milestone (RM-n). Requirements name the number in their Milestone line.',
        properties: kindProps({ name: { type: 'string', required: true, label: 'Name' }, number: { type: 'number', label: 'Number' }, proves: { type: 'text', label: 'Proves' }, stage: { type: 'string', label: 'Stage (as written)' }, stageRef: { type: 'ref', ref: ['releaseStage'], label: 'Release stage' }, detail: { type: 'text', label: 'Roadmap text', doc: 'The roadmap section as written, wrapped lines joined.' }, whitepaper: { type: 'text', label: 'White paper text', doc: 'The milestone\'s paragraph in the white paper\'s Milestones list.' } }) },
    },
    properties: [
      { entity: 'component', name: 'ref', ...REF_PROPS.ref },
      { entity: 'component', name: 'source', ...REF_PROPS.source },
      { entity: 'component', name: 'trustLevel', type: 'number', label: 'Trust level', doc: 'Position (1 least trusted to 6 most trusted) of the white paper\'s "Trust boundaries" item that names this component.' },
      { entity: 'component', name: 'mentions', ...REF_PROPS.mentions },
      { entity: 'component', name: 'talksTo', type: 'text', label: 'Talks to (as written)', doc: 'The process-topology table\'s Talks to cell; the talks-to relationships are read from it.' },
      { entity: 'claim', name: 'ref', ...REF_PROPS.ref },
      { entity: 'claim', name: 'source', ...REF_PROPS.source },
      { entity: 'claim', name: 'inSection', type: 'ref', ref: ['section'], label: 'In section', doc: 'The section whose body holds the marker of this requirement.' },
      { entity: 'claim', name: 'area', type: 'string', label: 'Specification area', doc: 'The numbered specification directory the requirement is written in.' },
      { entity: 'claim', name: 'section', type: 'string', label: 'Section', doc: 'The nearest heading above the requirement.' },
      { entity: 'claim', name: 'lifecycle', type: 'enum', values: ['active', 'retired'], label: 'Lifecycle', doc: 'retired when the requirement carries "Status: retired".' },
      { entity: 'claim', name: 'boundary', type: 'ref', ref: ['boundary'], label: 'Boundary' },
      { entity: 'claim', name: 'boundaryDetail', type: 'text', label: 'Boundary detail', doc: 'The rest of the Boundary line after the B- id.' },
      { entity: 'claim', name: 'traces', type: 'list', items: { type: 'ref', ref: TRACE_KINDS }, label: 'Traces to' },
      { entity: 'claim', name: 'dependsOn', type: 'list', items: { type: 'ref', ref: ['claim'] }, label: 'Depends on' },
      { entity: 'claim', name: 'milestone', type: 'number', label: 'Milestone', doc: 'The milestone at which the requirement is first verified.' },
      { entity: 'claim', name: 'seam', type: 'number', label: 'Seam', doc: 'The milestone by which the seam the requirement needs exists.' },
      { entity: 'claim', name: 'cases', type: 'list', items: { type: 'ref', ref: ['caseTable'] }, label: 'Case tables', doc: 'The case-table files the Cases line names.' },
      { entity: 'claim', name: 'casesPath', type: 'string', label: 'Unresolved case paths', doc: 'Cases paths that match no file of the specification tree, as written.' },
    ],
    verificationMethods: methods,
    relationshipKinds: {
      'talks-to': { label: 'Talks to', line: 'solid', color: 'blue', dependency: true, description: 'Listed in the white paper\'s process-topology table \'Talks to\' column.' },
    },
  };
}

/** Verification methods named by requirements, defined by docs/agents/verification.md when present. @param {string} dir @param {string[]} used @param {Loss} loss */
function verificationMethods(dir, used, loss) {
  /** @type {Map<string, string>} */
  const defs = new Map();
  try {
    for (const l of splitLines(readText(dir, LAYOUT.verification))) {
      if (!l.startsWith('|')) continue;
      const c = splitRow(l);
      const m = c.length === 3 ? /^`(\w+)`$/.exec(c[0]) : null;
      if (m) defs.set(m[1], `When: ${c[1]} Proof: ${c[2]} (${LAYOUT.verification})`);
    }
  } catch { /* the doc is optional */ }
  /** @type {Record<string, {label: string, description: string}>} */
  const out = {};
  for (const m of used) {
    const d = defs.get(m);
    if (!d) loss.add('verification method without a definition in the source', m);
    out[m] = { label: m[0].toUpperCase() + m.slice(1), description: d ?? 'As named in the Markdown specification.' };
  }
  return out;
}

// ---------------------------------------------------------------------------
// The conversion
// ---------------------------------------------------------------------------

/** @param {string} s */
function oneLine(s) { return JSON.stringify(s); }

/**
 * Convert the Markdown specification in the repository at `sourceDir` into specification text.
 * @param {{sourceDir: string, mapFile: string, project?: string}} opts
 * @returns {{text: string, counts: Record<string, number>, loss: Loss, commit: string, cov: ReturnType<typeof coverage>, unfaithful: {list: string, id: string, raw: string, rendered: string}[], rendered: ReturnType<typeof coverage>, ok: boolean, totals: {files: number, lines: number, bytes: number}}}
 */
export function buildSpec(opts) {
  if (!opts?.sourceDir || !opts?.mapFile) throw new Error('buildSpec needs a sourceDir and a mapFile (an import map).');
  const dir = opts.sourceDir.replace(/\\/g, '/');
  const mapFile = opts.mapFile;
  const loss = new Loss();
  const map = /** @type {{categories?: Record<string, string>, project?: {id?: string, name?: string, title?: string}, layout?: Partial<typeof DEFAULT_LAYOUT>}} */ (parseJsonc(fs.readFileSync(mapFile, 'utf8')) ?? {});
  LAYOUT = { ...DEFAULT_LAYOUT, ...(map.layout ?? {}) };
  const projectId = map.project?.id ?? opts.project ?? 'imported';
  const projectName = map.project?.name ?? projectId;
  const projectTitle = map.project?.title ?? projectName;
  const commit = readGitHead(dir);

  if (!fs.existsSync(path.join(dir, LAYOUT.whitepaper))) {
    throw new Error(`${dir} has no ${LAYOUT.whitepaper}: its specification is no longer Markdown, so there is nothing to import. Point --source at a checkout of a commit that still has the Markdown.`);
  }
  const wp = readText(dir, LAYOUT.whitepaper);
  const wpLines = splitLines(wp);

  // ---- parse -------------------------------------------------------------
  const componentRows = parseComponentRows(wp, LAYOUT.whitepaper, loss);
  const boundaryRows = parseBoundaryRows(wp, LAYOUT.whitepaper, loss);
  const zones = parseTrustZones(wp);
  const goals = bulletsIn(wp, /^## Goals\s*$/, /^G-\d+$/);
  const nonGoals = bulletsIn(wp, /^## Non-goals\s*$/, /^NG-\d+$/);
  const decisionBodies = bulletsIn(wp, /^## Decisions\s*$/, /^D-\d+$/);
  const constraints = bulletsIn(wp, /^## Constraints\s*$/, /^K-\d+$/);
  const questions = bulletsIn(wp, /^## Open questions\s*$/, /^Q-\d+$/);
  const stages = parseReleaseStages(wp, loss);
  const wpMilestones = parseWhitepaperMilestones(wp);
  const milestones = parseRoadmapMilestones(readText(dir, LAYOUT.roadmap));
  /** @type {Map<string, {title: string, group: string, decided: string, reversibility: string, line: number}>} */
  const decisionIndex = new Map();
  {
    const r = sectionRange(wpLines, /^## Decisions\s*$/);
    if (r) for (const { cells, line } of tableRows(wpLines, r.from, r.to, /^D-\d+$/, 5, 'decision index', loss, 1)) {
      decisionIndex.set(idOf(cells[1]), { title: cells[0], group: cells[2], decided: cells[3], reversibility: cells[4], line });
    }
  }

  const specFiles = listMarkdown(dir, LAYOUT.specsDir);
  /** @type {RawRequirement[]} */
  const reqs = [];
  let regexCount = 0;
  /** @type {Map<string, string>} */
  const texts = new Map();
  for (const f of specFiles) {
    const t = readText(dir, f);
    texts.set(f, t);
    regexCount += splitLines(t).filter((l) => /^\*\*[A-Z]+-[0-9]+\*\*/.test(l)).length;
    reqs.push(...parseRequirements(t, f, loss));
  }
  if (reqs.length !== regexCount) throw new Error(`Parsed ${reqs.length} requirements but a plain regex counts ${regexCount} lines starting with an id.`);

  // ---- checks on the component map -----------------------------------------
  const categories = map.categories ?? {};
  const missing = componentRows.filter((c) => !categories[c.ref]).map((c) => c.ref);
  if (missing.length) throw new Error(`import-map.jsonc (${mapFile}) has no category for: ${missing.join(', ')}.`);
  for (const k of Object.keys(categories)) if (!componentRows.some((c) => c.ref === k)) loss.add('import-map category for an unknown component', k);

  // ---- id registry ---------------------------------------------------------
  /** @type {Map<string, string>} */
  const index = new Map();
  const register = (/** @type {string} */ id, /** @type {string} */ kind, /** @type {string} */ where) => {
    if (index.has(id)) throw new Error(`Duplicate id "${id}" (${kind} at ${where}; already a ${index.get(id)}).`);
    if (!/^[a-z][a-z0-9_]*(-[a-z0-9_]+)*$/.test(id)) throw new Error(`Id "${id}" (${where}) does not match Exegra's id pattern.`);
    index.set(id, kind);
  };
  for (const c of componentRows) register(c.id, 'component', c.source);
  for (const b of boundaryRows) register(b.id, 'boundary', b.source);
  for (const g of goals) register(g.id, 'goal', `${LAYOUT.whitepaper}:${g.line}`);
  for (const g of nonGoals) register(g.id, 'nonGoal', `${LAYOUT.whitepaper}:${g.line}`);
  for (const d of decisionBodies) register(d.id, 'decision', `${LAYOUT.whitepaper}:${d.line}`);
  for (const k of constraints) register(k.id, 'constraint', `${LAYOUT.whitepaper}:${k.line}`);
  for (const q of questions) register(q.id, 'openQuestion', `${LAYOUT.whitepaper}:${q.line}`);
  for (const s of stages) register(s.id, 'releaseStage', `${LAYOUT.whitepaper}:${s.line}`);
  for (const m of milestones) register(m.id, 'milestone', m.source);
  for (const r of reqs) register(r.id, 'claim', `${r.file}:${r.line}`);

  // ---- glossary terms, entity runs, documents, sections, case tables --------
  const termId = uniquifier();
  /** @type {{id: string, term: string, definition: string, line: number, end: number, file: string}[]} */
  const terms = [];
  {
    const gl = `${LAYOUT.specsDir}/glossary.md`;
    const wpGlossary = sectionRange(wpLines, /^## Glossary\s*$/);
    if (wpGlossary) for (const t of parseTerms(wpLines, wpGlossary.from + 1, wpGlossary.to, loss, LAYOUT.whitepaper)) terms.push({ ...t, file: LAYOUT.whitepaper, id: termId('term-' + (slugify(t.term) || 'x')) });
    if (texts.has(gl)) { const gLines = splitLines(texts.get(gl) ?? ''); for (const t of parseTerms(gLines, 0, gLines.length, loss, gl)) terms.push({ ...t, file: gl, id: termId('term-' + (slugify(t.term) || 'x')) }); }
  }
  for (const t of terms) register(t.id, 'term', `${t.file}:${t.line}`);

  /** @type {Map<string, {id: string, start: number, end: number}[]>} */
  const runs = new Map();
  /** @param {string} file @param {string} id @param {number} start @param {number} end */
  const addRun = (file, id, start, end) => { if (!runs.has(file)) runs.set(file, []); runs.get(file)?.push({ id, start, end }); };
  for (const c of componentRows) addRun(LAYOUT.whitepaper, c.id, c.line, c.line);
  for (const b of boundaryRows) addRun(LAYOUT.whitepaper, b.id, b.line, b.line);
  for (const g of [...goals, ...nonGoals, ...decisionBodies, ...constraints, ...questions]) addRun(LAYOUT.whitepaper, g.id, g.line, g.end);
  for (const s of stages) addRun(LAYOUT.whitepaper, s.id, s.line, s.line);
  for (const m of milestones) { if (m.startLine <= m.endLine) addRun(LAYOUT.roadmap, m.id, m.startLine, m.endLine); else loss.add('roadmap milestone with no body lines (no raw)', m.ref); }
  for (const r of reqs) addRun(r.file, r.id, r.line, r.endLine);
  for (const t of terms) addRun(t.file, t.id, t.line, t.end);
  /** @type {Map<string, string[]>} */
  const lineCache = new Map();
  /** @param {string} file @param {number} start @param {number} end */
  const rawOf = (file, start, end) => {
    if (!lineCache.has(file)) lineCache.set(file, fileLines(texts.get(file) ?? ''));
    return /** @type {string[]} */ (lineCache.get(file)).slice(start - 1, end).join('\n');
  };

  /** @type {Record<string, any>[]} */ const documents = [];
  /** @type {Record<string, any>[]} */ const sections = [];
  /** @type {Record<string, any>[]} */ const caseTables = [];
  /** @type {Map<string, string>} entity id -> section id */
  const sectionOf = new Map();
  /** @type {Map<string, string>} path -> case table id */
  const caseIds = new Map();
  for (const f of specFiles) {
    const rs = (runs.get(f) ?? []).sort((a, b) => a.start - b.start);
    for (let i = 1; i < rs.length; i++) if (rs[i].start <= rs[i - 1].end) throw new Error(`${f}: entities ${rs[i - 1].id} and ${rs[i].id} overlap.`);
    const d = buildDocumentEntities(f, texts.get(f) ?? '', rs);
    if (!d.document.title) loss.add('file without a heading (document has no title)', f);
    register(d.document.id, 'document', f); documents.push(d.document);
    for (const s of d.sections) { register(s.id, 'section', s.source); sections.push(s); }
    if (d.caseTable) { register(d.caseTable.id, 'caseTable', f); caseTables.push(d.caseTable); caseIds.set(f, d.caseTable.id); }
    for (const [k, v] of d.sectionOf) sectionOf.set(k, v);
  }

  // ---- mentions ------------------------------------------------------------
  /** @param {string} ownerRef @param {string} ownerId @param {string} text @returns {string[]|undefined} */
  const mentionsOf = (ownerRef, ownerId, text) => {
    const { ids, ranges } = extractMentions(text);
    for (const r of ranges) loss.add('range reference (only its endpoints are linked)', `${ownerRef} "${r}"`);
    const out = [];
    for (const id of ids) {
      if (id === ownerId) continue;
      const kind = index.get(id);
      if (kind && MENTION_KINDS.includes(kind)) out.push(id);
      else loss.add('unresolved reference (mentions)', `${ownerRef} -> ${id.toUpperCase()}`);
    }
    return out.length ? out : undefined;
  };
  /** @param {Record<string, any>} e */
  const clean = (e) => { for (const k of Object.keys(e)) if (e[k] === undefined) delete e[k]; return e; };

  // ---- entities ------------------------------------------------------------
  const zoneOf = new Map();
  for (const z of zones) for (const c of z.components) {
    if (zoneOf.has(c) && zoneOf.get(c).level !== z.level) loss.add('component named in two trust boundaries (first kept)', c.toUpperCase());
    else if (!zoneOf.has(c)) zoneOf.set(c, z);
  }
  const components = componentRows.map((c) => {
    const z = zoneOf.get(c.id);
    if (!z) loss.add('component not named in the Trust boundaries list (no trustZone)', c.ref);
    return clean({ id: c.id, name: c.name, category: categories[c.ref], purpose: c.owns, talksTo: c.talksTo, trustZone: z?.zone, ref: c.ref, source: c.source, trustLevel: z?.level, mentions: mentionsOf(c.ref, c.id, c.owns) });
  });

  /** @type {Record<string, any>[]} */
  const relationships = [];
  let rowsWithoutRelationship = 0;
  for (const c of componentRows) {
    const { ids, ranges } = extractMentions(c.talksTo);
    for (const r of ranges) loss.add('range reference (only its endpoints are linked)', `${c.ref} Talks to "${r}"`);
    const targets = ids.filter((id) => /^c-\d+$/.test(id));
    let made = 0;
    for (const t of targets) {
      if (t === c.id) { loss.add('Talks-to reference to the row\'s own component', c.ref); continue; }
      if (index.get(t) !== 'component') { loss.add('unresolved reference (talks-to)', `${c.ref} -> ${t.toUpperCase()}`); continue; }
      relationships.push({ id: `${c.id}-talks-to-${t}`, kind: 'talks-to', from: c.id, to: t, description: c.talksTo });
      made++;
    }
    if (!made) { rowsWithoutRelationship++; loss.add('Talks-to cell naming no component id (no relationship)', `${c.ref} "${c.talksTo.slice(0, 60)}"`); }
  }

  const boundaries = boundaryRows.map((b) => clean({ id: b.id, name: b.name, interfaceKind: b.interfaceKind, usedBy: b.usedBy, ref: b.ref, source: b.source, mentions: mentionsOf(b.ref, b.id, `${b.name} ${b.usedBy}`) }));

  const goalEntities = goals.map((g) => {
    const m = /^(.*?)\s*\*\(([^*]*)\)\*\s*$/s.exec(g.text);
    if (!m) loss.add('goal without a trailing release-stage tag', g.ref);
    const statement = m ? m[1] : g.text;
    return clean({ id: g.id, statement, stage: m ? collapse(m[2]) : undefined, group: g.group || undefined, ref: g.ref, source: `${LAYOUT.whitepaper}:${g.line}`, mentions: mentionsOf(g.ref, g.id, statement) });
  });
  const nonGoalEntities = nonGoals.map((g) => {
    const m = /^\*([^*]+?)\*\s*(.*)$/s.exec(g.text);
    if (!m) loss.add('non-goal without an italic horizon lead-in', g.ref);
    const horizon = m ? m[1] : undefined;
    const statement = m ? m[2] : g.text;
    return clean({ id: g.id, statement, horizon, ref: g.ref, source: `${LAYOUT.whitepaper}:${g.line}`, mentions: mentionsOf(g.ref, g.id, statement) });
  });
  const decisionEntities = decisionBodies.map((d) => {
    const ix = decisionIndex.get(d.id);
    const lead = /^\*\*(.+?)\*\*/.exec(d.text)?.[1].replace(/\.$/, '');
    if (!ix) loss.add('decision body without a row in the decision index', d.ref);
    else if (ix.group !== d.group) loss.add('decision group differs between the index and the body', `${d.ref} "${ix.group}" vs "${d.group}"`);
    return clean({ id: d.id, title: ix?.title ?? lead ?? d.ref, statement: d.text, group: ix?.group ?? (d.group || undefined), owner: ix ? ix.decided.split(',')[0].trim() : undefined, decided: ix?.decided, reversibility: ix?.reversibility, ref: d.ref, source: `${LAYOUT.whitepaper}:${d.line}`, mentions: mentionsOf(d.ref, d.id, d.text) });
  });
  for (const [id, ix] of decisionIndex) if (!decisionBodies.some((d) => d.id === id)) loss.add('decision index row without a body', `${id.toUpperCase()} "${ix.title}"`);
  const constraintEntities = constraints.map((k) => clean({ id: k.id, statement: k.text, group: k.group || undefined, ref: k.ref, source: `${LAYOUT.whitepaper}:${k.line}`, mentions: mentionsOf(k.ref, k.id, k.text) }));
  const questionEntities = questions.map((q) => clean({ id: q.id, statement: q.text, ref: q.ref, source: `${LAYOUT.whitepaper}:${q.line}`, mentions: mentionsOf(q.ref, q.id, q.text) }));
  const stageEntities = stages.map((s) => clean({ id: s.id, name: s.name, purpose: s.purpose, milestones: s.milestones, exitEvidence: s.exitEvidence, ref: s.ref, source: `${LAYOUT.whitepaper}:${s.line}`, mentions: mentionsOf(s.ref, s.id, `${s.purpose} ${s.exitEvidence}`) }));
  const milestoneEntities = milestones.map((m) => {
    if (!m.stage) loss.add('milestone without a Stage line', m.ref);
    const sm = /^(R\d+(?:\.\d+)?)\b/.exec(m.stage);
    const stageRef = sm ? sm[1].toLowerCase().replace(/\./g, '_') : undefined;
    if (m.stage && (!stageRef || index.get(stageRef) !== 'releaseStage')) loss.add('milestone stage naming no release stage', `${m.ref} "${m.stage}"`);
    const wpText = wpMilestones.get(m.number);
    if (wpText === undefined) loss.add('roadmap milestone without a white paper milestone paragraph', m.ref);
    return clean({ id: m.id, name: m.name, number: m.number, proves: m.proves || undefined, stage: m.stage || undefined, stageRef: stageRef && index.get(stageRef) === 'releaseStage' ? stageRef : undefined, detail: m.detail, whitepaper: wpText, ref: m.ref, source: m.source, mentions: mentionsOf(m.ref, m.id, `${m.detail} ${wpText ?? ''}`) });
  });
  for (const n of wpMilestones.keys()) if (!milestones.some((m) => m.number === n)) loss.add('white paper milestone without a roadmap RM- section', String(n));

  const claims = reqs.map((r) => {
    const c = requirementToClaim(r, index, loss, { caseIds });
    const sec = sectionOf.get(r.id);
    if (sec) c.inSection = sec; else loss.add('requirement not placed in any section', r.ref);
    return c;
  });
  // The original lines of every imported entity: used to check that the entity
  // renders back to them, never written out.
  /** @type {Map<string, string>} */
  const rawById = new Map();
  reqs.forEach((r) => rawById.set(r.id, rawOf(r.file, r.line, r.endLine)));
  componentRows.forEach((c) => rawById.set(c.id, rawOf(LAYOUT.whitepaper, c.line, c.line)));
  boundaryRows.forEach((b) => rawById.set(b.id, rawOf(LAYOUT.whitepaper, b.line, b.line)));
  for (const g of [...goals, ...nonGoals, ...decisionBodies, ...constraints, ...questions]) rawById.set(g.id, rawOf(LAYOUT.whitepaper, g.line, g.end));
  stages.forEach((g) => rawById.set(g.id, rawOf(LAYOUT.whitepaper, g.line, g.line)));
  milestones.forEach((m) => { if (m.startLine <= m.endLine) rawById.set(m.id, rawOf(LAYOUT.roadmap, m.startLine, m.endLine)); });

  // Prose mentions (sections and terms): any id-bearing entity, by the id prefixes in use.
  const prefixes = new Set();
  for (const id of index.keys()) { const pm = /^([a-z]+)-\d+$/.exec(id); if (pm) prefixes.add(pm[1].toUpperCase()); }
  const PROSE = new RegExp('\\b(' + [...prefixes].sort((a, b) => b.length - a.length).join('|') + ')-(\\d+)\\b', 'g');
  /** @param {string} owner @param {string} ownerId @param {string} text @returns {string[]|undefined} */
  const proseMentions = (owner, ownerId, text) => {
    const out = [];
    for (const id of idsIn(text, PROSE)) {
      if (id === ownerId) continue;
      const kind = index.get(id);
      if (kind && ALL_MENTION_KINDS.includes(kind)) out.push(id);
      else loss.add('unresolved reference (section and term mentions)', `${owner} -> ${id.toUpperCase()}`);
    }
    return out.length ? out : undefined;
  };
  for (const sec of sections) {
    const m = proseMentions(sec.source, sec.id, sec.body.split('\n').filter((/** @type {string} */ l) => !MARKER.test(l)).join('\n'));
    if (m) { sec.mentions = m; const src = sec.source; delete sec.source; sec.source = src; }
  }
  const termEntities = terms.map((t) => clean({ id: t.id, term: t.term, definition: t.definition, mentions: proseMentions(`${t.file}:${t.line}`, t.id, t.definition), source: `${t.file}:${t.line}` }));
  terms.forEach((t) => rawById.set(t.id, rawOf(t.file, t.line, t.end)));

  // ---- every entity must render back to the words it came from ---------------
  const entityLists = /** @type {[string, Record<string, any>[]][]} */ ([['components', components], ['goals', goalEntities], ['nonGoals', nonGoalEntities], ['boundaries', boundaries], ['decisions', decisionEntities], ['constraints', constraintEntities], ['openQuestions', questionEntities], ['releaseStages', stageEntities], ['milestones', milestoneEntities], ['claims', claims], ['terms', termEntities]]);
  const { byId } = renderIndex({ ...Object.fromEntries(entityLists), caseTables });
  /** @type {{list: string, id: string, raw: string, rendered: string}[]} */
  const unfaithful = [];
  for (const [list, items] of entityLists) for (const e of items) {
    const raw = rawById.get(e.id);
    if (raw === undefined) continue;
    const rendered = unfaithfulRendering(list, e, raw, byId);
    if (rendered !== null) unfaithful.push({ list, id: e.id, raw, rendered });
  }

  // ---- vocabulary and system -------------------------------------------------
  const methodsUsed = [...new Set(claims.map((c) => c.evaluate.method))];
  const vocabulary = buildVocabulary(verificationMethods(dir, methodsUsed, loss));

  const srcFiles = countFiles(path.join(dir, LAYOUT.srcDir));
  const caseFiles = caseTables.length;
  const counts = {
    documents: documents.length, sections: sections.length, caseTables: caseTables.length, terms: termEntities.length,
    components: components.length, relationships: relationships.length, boundaries: boundaries.length, goals: goalEntities.length,
    nonGoals: nonGoalEntities.length, decisions: decisionEntities.length, constraints: constraintEntities.length,
    openQuestions: questionEntities.length, releaseStages: stageEntities.length, milestones: milestoneEntities.length, claims: claims.length,
  };
  const entityTotal = Object.entries(counts).filter(([k]) => k !== 'relationships').reduce((a, [, n]) => a + n, 0);

  /** @type {Map<string, string>} */
  const onDisk = new Map(specFiles.map((f) => [f, texts.get(f) ?? '']));
  const totalLines = [...onDisk.values()].reduce((a, t) => a + fileLines(t).length, 0);
  const totalBytes = [...onDisk.values()].reduce((a, t) => a + Buffer.byteLength(t), 0);

  const notes = [
    `PRODUCED BY IMPORT. This file was produced by tools/import-markdown.js importing the Markdown specification (the ${LAYOUT.specsDir}/ tree of the source repository) at git commit ${commit}. The importer's coverage check covered all ${specFiles.length} Markdown files (${totalLines} lines, ${totalBytes} bytes): every line outside an imported entity is held verbatim in a section body or case table, and every imported entity was checked to render from its properties back to the words of the lines it came from (requirements: the same statement and attribute values). Only line wrapping and the order of requirement attribute lines are not kept. This file then replaced the Markdown in the source repository and is the specification's authority: edit it in Exegra or as text, never by re-importing.`,
    'Exegra renders each document back to Markdown from this file (tools/import-markdown.js renderEntity; --export-md <dir> writes the tree), and Concordance renders the same text to lint the specification and reconcile it with the code.',
    `How the Markdown is held: each file is a "document"; each heading of a non-case file is a "section" whose "body" is the Markdown under it, verbatim, with every line range imported as a separate entity (requirements, white-paper list items and table rows, glossary entries, roadmap milestones) replaced by one {{entity:<id>}} marker line that stands for the entity rendered from its properties; the ${caseFiles} files under specifications/*/cases/ are "caseTable" entities holding the whole file in "body". Multi-line text (decisions with sub-points, roadmap milestones) keeps its paragraphs and list items as separate lines. Reading the sections of a document in "order" and expanding the markers gives the file.`,
    `Imported as parsed entities: ${counts.claims} requirements as claims, ${counts.components} components and ${counts.relationships} talks-to relationships from the white paper's process-topology table, ${counts.boundaries} boundaries, ${counts.goals} goals, ${counts.nonGoals} non-goals, ${counts.decisions} decisions, ${counts.constraints} constraints, ${counts.openQuestions} open questions, ${counts.releaseStages} release stages, ${counts.milestones} roadmap milestones and ${counts.terms} glossary terms; plus ${counts.documents} documents, ${counts.sections} sections and ${counts.caseTables} case tables (${entityTotal} entities in all). Outside specifications/ nothing is imported (contracts/, decisions/, diagrams/, threat-models/, runbooks/, workflows/, reviews/, traceability/ and docs/ stay where they are), except the verification-method definitions read from docs/agents/verification.md.`,
    `Nothing is verified: the source repository has no implementation yet (its ${LAYOUT.srcDir}/ holds ${srcFiles} file${srcFiles === 1 ? '' : 's'}). Every claim names its verification method (evaluate.method) and is carried out outside Exegra; no evidence is recorded here.`,
    'Component categories come from the import map of the project, an importer input that is not part of the source: they are an Exegra-side classification the Markdown does not state.',
    'Milestones: a requirement\'s "milestone" property is the number from its Milestone line; the roadmap\'s RM-n milestone with that number is the entity rm-<number>.',
    ...loss.lines().map((l) => `NOT MAPPED, ${l}`),
  ];

  const system = {
    id: projectId,
    name: projectName,
    version: `git ${commit.slice(0, 12)}`,
    description: `${firstParagraph(wp, projectTitle)} This project was produced by importing the Markdown specification at git commit ${commit}; the importer's coverage check showed that every line of ${LAYOUT.specsDir}/ is represented here, apart from line wrapping. This file replaced the Markdown and is the specification's authority.`,
    illustrative: false,
    notes,
  };

  const views = [
    { id: 'architecture', name: 'Architecture', projection: 'structural', description: 'The white paper\'s components and the talks-to relationships of its process-topology table.' },
    { id: 'trust-levels', name: 'Trust levels', projection: 'structural', description: 'The same components, coloured by the trust boundary the white paper lists them in.', display: { colorBy: 'trustZone' } },
    { id: 'traceability', name: 'Traceability', projection: 'references', description: 'Goals, constraints, decisions, boundaries and requirements and the references between them.', display: { depth: 1 } },
    { id: 'claims', name: 'Requirements', projection: 'claims', description: 'Every requirement, with its verification method.' },
  ];

  // ---- text ----------------------------------------------------------------
  const out = [];
  out.push('{');
  out.push(`  // The ${projectName} specification. This file is its authority: edit it in Exegra (project "${projectId}") or as text.`);
  out.push(`  // It was produced by Exegra's tools/import-markdown.js from the Markdown specification (the ${LAYOUT.specsDir}/ tree) at`);
  out.push('  // git commit ' + commit + ', and then replaced that Markdown.');
  out.push('  // Coverage: every line of every Markdown file under ' + LAYOUT.specsDir + '/ is represented in this file (' + specFiles.length + ' files, ' + totalLines + ' lines,');
  out.push('  // ' + totalBytes + ' bytes). Prose is held verbatim; every imported entity renders from its properties back to the words it came from.');
  out.push('  // Each document is rendered back to Markdown from this file; section bodies hold prose verbatim and stand for');
  out.push('  // every other entity by a {{entity:<id>}} marker. "source" on an entity is where it was imported from (file:line).');
  out.push('  "exegra": "0.1",');
  out.push('');
  out.push('  "system": ' + JSON.stringify(system, null, 2).replace(/\n/g, '\n  ') + ',');
  out.push('');
  out.push('  "vocabulary": ' + JSON.stringify(vocabulary, null, 2).replace(/\n/g, '\n  ') + ',');
  /** @param {string} title @param {string} key @param {any[]} items @param {boolean} [last] */
  const section = (title, key, items, last = false) => {
    out.push('');
    out.push(`  // ---- ${title} ${'-'.repeat(Math.max(3, 70 - title.length))}`);
    out.push(`  "${key}": [`);
    items.forEach((e, i) => out.push('    ' + JSON.stringify(e) + (i < items.length - 1 ? ',' : '')));
    out.push('  ]' + (last ? '' : ','));
  };
  section('Components (white paper, Process topology)', 'components', components);
  section('Relationships (Talks to)', 'relationships', relationships);
  section('Goals', 'goals', goalEntities);
  section('Non-goals', 'nonGoals', nonGoalEntities);
  section('Boundaries', 'boundaries', boundaries);
  section('Decisions', 'decisions', decisionEntities);
  section('Constraints', 'constraints', constraintEntities);
  section('Open questions', 'openQuestions', questionEntities);
  section('Release stages', 'releaseStages', stageEntities);
  section('Milestones (roadmap)', 'milestones', milestoneEntities);
  section('Requirements', 'claims', claims);
  section('Glossary terms', 'terms', termEntities);
  section('Documents (one per Markdown file)', 'documents', documents);
  section('Sections (one per heading)', 'sections', sections);
  section('Case tables', 'caseTables', caseTables);
  section('Views', 'views', views, true);
  out.push('}');
  out.push('');
  const text = out.join('\n');

  // ---- coverage --------------------------------------------------------------
  // 1. Sections, markers and case tables hold every line: with each marker
  //    expanded to its entity's original lines, every file comes back exactly.
  const cov = coverage(reconstructMarkdown({ documents, sections, caseTables }, (id) => rawById.get(id)), onDisk);
  // 2. The written file alone renders every document (each marker names an
  //    entity that renders); how many come back byte-identical is reported.
  const rendered = coverage(reconstructMarkdown(parseJsonc(text)), onDisk);
  return { text, counts, loss, commit, cov, unfaithful, rendered, ok: cov.ok && unfaithful.length === 0, totals: { files: specFiles.length, lines: totalLines, bytes: totalBytes } };
}

// ---------------------------------------------------------------------------
// Command line
// ---------------------------------------------------------------------------

const USAGE = 'node tools/import-markdown.js --project <name> [--source <dir>] [--out <file>] [--map <file>] [--check] [--coverage] [--export-md <dir>]';

/**
 * Paths come from the arguments: with --project <name>, the map is specs/<name>/import-map.jsonc, the output is the
 * project's specification file (as its project.jsonc names it) and the source is the map's "source" (relative to the map).
 * @param {string[]} argv
 */
function parseArgs(argv) {
  const o = { project: '', source: '', out: '', map: '', check: false, coverage: false, exportMd: '' };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--check') o.check = true;
    else if (a === '--coverage') o.coverage = true;
    else if (a === '--export-md') { const v = argv[++i]; if (!v) throw new Error('--export-md needs a directory.'); o.exportMd = v; }
    else if (a === '--project' || a === '--source' || a === '--out' || a === '--map') {
      const v = argv[++i];
      if (!v) throw new Error(`${a} needs a value.`);
      o[a.slice(2)] = v;
    } else throw new Error(`Unknown argument "${a}". Usage: ${USAGE}`);
  }
  const specsDir = path.join(ROOT, 'specs');
  if (o.project) {
    if (!o.map) o.map = importMapFile(specsDir, o.project);
    if (!o.out) o.out = createWorkspace(specsDir).specFile(o.project);
  }
  if (!o.map || !o.out) throw new Error(`Name the project (--project <name>) or give --map and --out. Usage: ${USAGE}`);
  if (!o.source) {
    const mapped = /** @type {{source?: string}} */ (parseJsonc(fs.readFileSync(o.map, 'utf8')) ?? {}).source;
    if (!mapped) throw new Error(`Give --source <dir>, or a "source" in ${o.map}. Usage: ${USAGE}`);
    o.source = path.resolve(path.dirname(o.map), mapped);
  }
  return o;
}

function main() {
  let opts;
  try { opts = parseArgs(process.argv.slice(2)); } catch (e) { console.error(/** @type {Error} */ (e).message); process.exit(2); }
  let result;
  try { result = buildSpec({ sourceDir: opts.source, mapFile: opts.map, project: opts.project || undefined }); } catch (e) { console.error('import failed: ' + /** @type {Error} */ (e).message); process.exit(1); }
  const { text, counts, loss, commit, cov, unfaithful, rendered, ok, totals } = result;
  if (loss.total) {
    console.error(`Not mapped (${loss.total} item${loss.total === 1 ? '' : 's'} in ${loss.kinds.size} kind${loss.kinds.size === 1 ? '' : 's'}):`);
    for (const l of loss.lines()) console.error('  ' + l);
  } else console.error('Nothing was left unmapped.');
  console.log(`Source git commit ${commit}`);
  console.log('Imported: ' + Object.entries(counts).map(([k, n]) => `${k} ${n}`).join(', '));
  console.log(`Not mapped: ${loss.total} item(s) in ${loss.kinds.size} kind(s)` + [...loss.kinds].map(([k, e]) => `\n  ${e.count} x ${k}`).join(''));

  // The coverage check: normalisation is line endings to \n and trailing whitespace stripped per line.
  const bad = cov.files.filter((f) => !f.identical);
  if (opts.coverage) for (const f of cov.files) console.log(f.identical ? `identical  ${f.path} (${f.lines} lines)` : `DIFFERENT  ${f.path}: ${f.differing} differing line(s), first at ${f.first?.line}: expected ${JSON.stringify(f.first?.expected)} got ${JSON.stringify(f.first?.actual)}`);
  else for (const f of bad) console.error(`DIFFERENT  ${f.path}: ${f.differing} differing line(s), first at ${f.first?.line}: expected ${JSON.stringify(f.first?.expected)} got ${JSON.stringify(f.first?.actual)}`);
  console.log(`Coverage: ${cov.files.length - bad.length} of ${cov.files.length} files rebuild exactly from sections, case tables and the lines of each imported entity; ${totals.files} files, ${totals.lines} lines, ${totals.bytes} bytes covered.`);
  for (const u of unfaithful.slice(0, 20)) console.error(`UNFAITHFUL ${u.list} ${u.id}:\n  source:   ${JSON.stringify(u.raw)}\n  rendered: ${JSON.stringify(u.rendered)}`);
  const entityCount = Object.entries(counts).filter(([k]) => !['documents', 'sections', 'caseTables', 'relationships'].includes(k)).reduce((a, [, n]) => a + n, 0);
  console.log(`Rendering: ${entityCount - unfaithful.length} of ${entityCount} imported entities render from their properties back to the words they came from.`);
  console.log(`Rendered from the file alone, ${rendered.files.filter((f) => f.identical).length} of ${rendered.files.length} documents are byte-identical to the Markdown; the rest differ in line wrapping or requirement attribute order.`);
  if (!ok) { console.error(`Coverage check FAILED (${bad.length} file(s), ${unfaithful.length} entit${unfaithful.length === 1 ? 'y' : 'ies'}); nothing was written.`); process.exit(1); }
  if (opts.coverage) return;

  if (opts.exportMd) {
    const files = reconstructMarkdown(parseJsonc(text));
    for (const [p, t] of files) {
      const dest = path.join(opts.exportMd, ...p.split('/'));
      fs.mkdirSync(path.dirname(dest), { recursive: true });
      fs.writeFileSync(dest, t);
    }
    console.log(`Exported ${files.size} Markdown files under ${opts.exportMd}.`);
  }
  if (opts.check) {
    const onDisk = fs.existsSync(opts.out) ? fs.readFileSync(opts.out, 'utf8') : null;
    if (onDisk !== text) { console.error(`${opts.out} is out of date: re-run node tools/import-markdown.js.`); process.exit(1); }
    console.log(`${opts.out} is up to date.`);
    return;
  }
  if (opts.exportMd) return;
  fs.mkdirSync(path.dirname(opts.out), { recursive: true });
  fs.writeFileSync(opts.out, text);
  console.log(`Wrote ${opts.out} (${text.length} characters).`);
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
