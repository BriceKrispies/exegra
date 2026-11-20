// The specification store: a project's JSONC specification held in SQLite (node:sqlite), with an exact
// round trip. Node-only, like tools/workspace.js.
//
// The text is cut into verbatim slices, and every code unit of it belongs to exactly one row:
//   entity  one per item of an entity section (components, claims, a section a vocabulary entityKinds
//           declares, ...), and one per other top-level value, stored whole (system, exegra, vocabulary,
//           a section the meta-model has no entity kind for, an entity section that is not an array);
//   trivia  everything between those values: the text before the root's first member and after the last,
//           member keys and colons, brackets, commas, comments, whitespace and line endings.
// source_text and trivia.text are slices of the original text, so export (the rows in position order,
// concatenated) is the original text, byte for byte. import checks that before it commits.
//
// Positions are UTF-16 code-unit offsets of the slice's start in the text that was imported (the offsets
// jsonc-parser reports, and JavaScript string indices), not byte offsets. They order the rows; nothing
// reads them as offsets into a later text.
//
// The json, hash, kind, id, component and refs columns are derived from the slice when it is written, as
// an index; source_text is the authority. The model is still derived from the text by the Lean kernel
// (src/core/parse.js): loadModelFromStore derives it from the exported text.
//
// A text that does not parse (any jsonc-parser error), is not well-formed Unicode, or is not valid UTF-8
// (importFile) is refused with a StoreError; nothing is stored lossily.

import { createHash } from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { DatabaseSync } from 'node:sqlite';
import { parseTree, getNodeValue, printParseErrorCode } from 'jsonc-parser';
import metamodel from '../src/core/metamodel.json' with { type: 'json' };
import { parseSpec } from '../src/core/parse.js';
import { analyzeSpec } from '../src/core/analyze.js';
import { semanticHash } from '../src/core/hash.js';

/** @typedef {import('jsonc-parser').Node} JsonNode */

export const STORE_FORMAT = 'exegra-spec-store';
export const STORE_FORMAT_VERSION = 1;
/** The unit positions count. */
export const POSITION_UNIT = 'utf16-code-unit';

const SCHEMA = `
CREATE TABLE IF NOT EXISTS meta (
  key TEXT PRIMARY KEY,
  value TEXT NOT NULL
) WITHOUT ROWID;
CREATE TABLE IF NOT EXISTS entity (
  position INTEGER PRIMARY KEY,
  section TEXT,
  id TEXT,
  kind TEXT,
  component TEXT,
  source_text TEXT NOT NULL,
  json TEXT NOT NULL,
  hash TEXT NOT NULL,
  refs TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS entity_section_id ON entity(section, id);
CREATE INDEX IF NOT EXISTS entity_id ON entity(id);
CREATE INDEX IF NOT EXISTS entity_kind ON entity(kind);
CREATE INDEX IF NOT EXISTS entity_component ON entity(component);
CREATE TABLE IF NOT EXISTS trivia (
  position INTEGER PRIMARY KEY,
  section TEXT,
  text TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS ref (
  position INTEGER NOT NULL,
  target TEXT NOT NULL,
  PRIMARY KEY (position, target)
) WITHOUT ROWID;
CREATE INDEX IF NOT EXISTS ref_target ON ref(target);
`;

/** Failure of the store with a stable machine-readable code. */
export class StoreError extends Error {
  /**
   * @param {string} code 'store.syntax' | 'store.encoding' | 'store.format' | 'store.roundtrip' | 'store.stale' | 'store.not-found'
   * @param {string} message
   * @param {{diagnostics?: any[]}} [extra]
   */
  constructor(code, message, extra = {}) {
    super(message);
    this.name = 'StoreError';
    this.code = code;
    this.diagnostics = extra.diagnostics ?? [];
  }
}

/** sha256 hex of the UTF-8 encoding of a text. @param {string} text */
export function sha256Text(text) {
  return createHash('sha256').update(text, 'utf8').digest('hex');
}

/** The default database of a specification file: beside it, `<spec>.sqlite`. @param {string} specFile */
export function defaultDbPath(specFile) {
  return `${specFile}.sqlite`;
}

/**
 * Open (creating when absent) a store database in WAL mode, with the schema in place.
 * @param {string} file a path, or ':memory:'
 * @returns {DatabaseSync}
 */
export function openStore(file) {
  if (file !== ':memory:') fs.mkdirSync(path.dirname(path.resolve(file)), { recursive: true });
  const db = new DatabaseSync(file);
  db.exec('PRAGMA journal_mode = WAL; PRAGMA synchronous = NORMAL; PRAGMA busy_timeout = 5000;');
  db.exec(SCHEMA);
  const format = metaOf(db).format;
  if (format !== undefined && format !== STORE_FORMAT) {
    db.close();
    throw new StoreError('store.format', `${file} is not an Exegra specification store (format ${JSON.stringify(format)}).`);
  }
  return db;
}

/** @param {DatabaseSync} db @returns {Record<string, string>} */
function metaOf(db) {
  /** @type {Record<string, string>} */
  const out = {};
  for (const r of /** @type {any[]} */ (db.prepare('SELECT key, value FROM meta ORDER BY key').all())) out[r.key] = r.value;
  return out;
}

/** The meta rows of a store. @param {DatabaseSync} db */
export function storeMeta(db) {
  return metaOf(db);
}

// ---------------------------------------------------------------------------
// Slicing
// ---------------------------------------------------------------------------

/**
 * @typedef {{position: number, section: string|null, id: string|null, kind: string|null, component: string|null,
 *   source_text: string, json: string, hash: string, refs: string}} EntityRow
 * @typedef {{position: number, section: string|null, text: string}} TriviaRow
 */

/** The entity sections of the base meta-model: section -> {kind, single}. */
const BASE_SECTIONS = new Map(
  Object.entries(/** @type {Record<string, any>} */ (metamodel.sections))
    .filter(([, s]) => typeof s.entity === 'string')
    .map(([name, s]) => [name, { kind: /** @type {string} */ (s.entity), single: s.single === true }]),
);

/** @param {JsonNode|undefined} obj @param {string} key @returns {JsonNode|undefined} the value of the last member named key */
function member(obj, key) {
  if (!obj || obj.type !== 'object') return undefined;
  /** @type {JsonNode|undefined} */
  let found;
  for (const p of obj.children ?? []) if (p.children?.[0]?.value === key) found = p.children[1];
  return found;
}

/**
 * The entity sections of a document: the base meta-model's, extended by the sections its vocabulary's
 * entityKinds declare.
 * @param {JsonNode} root
 */
function sectionsOf(root) {
  const sections = new Map(BASE_SECTIONS);
  const kinds = member(member(root, 'vocabulary'), 'entityKinds');
  if (kinds?.type === 'object') {
    for (const p of kinds.children ?? []) {
      const kind = p.children?.[0]?.value;
      const section = member(p.children?.[1], 'section');
      if (typeof kind === 'string' && section?.type === 'string' && !sections.has(section.value)) {
        sections.set(section.value, { kind, single: false });
      }
    }
  }
  return sections;
}

/** The string value of a member of an object node, or null. @param {JsonNode} node @param {string} key */
function stringMember(node, key) {
  const v = member(node, key);
  return v?.type === 'string' ? v.value : null;
}

/** A lone UTF-16 surrogate: a string holding one has no UTF-8 encoding. */
const LONE_SURROGATE = /[\uD800-\uDBFF](?![\uDC00-\uDFFF])|(?<![\uD800-\uDBFF])[\uDC00-\uDFFF]/;

/** @param {string} text @param {number} offset @returns {{line: number, column: number}} */
function lineColumn(text, offset) {
  let line = 1, start = 0;
  for (let i = 0; i < offset && i < text.length; i++) if (text.charCodeAt(i) === 10) { line++; start = i + 1; }
  return { line, column: offset - start + 1 };
}

/**
 * Parse a specification text the way the store does, or throw StoreError. A leading byte order mark is
 * read as whitespace (it stays in the first trivia row).
 * @param {string} text
 * @returns {JsonNode}
 */
function parseForStore(text) {
  if (LONE_SURROGATE.test(text)) throw new StoreError('store.encoding', 'The specification is not well-formed Unicode (it holds a lone surrogate); it is not stored.');
  const bom = text.charCodeAt(0) === 0xfeff;
  /** @type {import('jsonc-parser').ParseError[]} */
  const errors = [];
  const root = parseTree(bom ? ` ${text.slice(1)}` : text, errors, { allowTrailingComma: true, disallowComments: false });
  if (errors.length || !root) {
    const diagnostics = errors.map((e) => ({ code: `syntax.${printParseErrorCode(e.error)}`, severity: 'error', message: `Syntax error: ${printParseErrorCode(e.error)}.`, entityId: null, ...lineColumn(text, e.offset) }));
    const first = diagnostics[0];
    const where = first ? ` at line ${first.line}, column ${first.column} (${first.code})` : ' (the text is empty)';
    throw new StoreError('store.syntax', `The specification does not parse${where}; it is not stored, since a store holds only what it can give back byte for byte.`, { diagnostics });
  }
  return root;
}

/**
 * Cut a specification text into entity and trivia rows (without refs). Every code unit of the text is in
 * exactly one row; the rows in position order concatenate to the text.
 * @param {string} text
 * @returns {{entities: EntityRow[], trivia: TriviaRow[], root: JsonNode}}
 */
export function sliceSpec(text) {
  const root = parseForStore(text);
  /** @type {EntityRow[]} */
  const entities = [];
  /** @type {TriviaRow[]} */
  const trivia = [];
  let at = 0;
  /** @param {number} end @param {string|null} section */
  const gap = (end, section) => {
    if (end > at) trivia.push({ position: at, section, text: text.slice(at, end) });
    at = end;
  };
  /**
   * @param {JsonNode} node @param {string|null} section @param {string|null} kind
   */
  const value = (node, section, kind) => {
    gap(node.offset, section);
    const source = text.slice(node.offset, node.offset + node.length);
    const json = JSON.stringify(getNodeValue(node)) ?? 'null';
    const id = node.type === 'object' ? stringMember(node, 'id') : null;
    const component = kind === 'component' ? id : node.type === 'object' && kind !== null ? stringMember(node, 'component') : null;
    entities.push({ position: node.offset, section, id: kind === null ? null : id, kind, component, source_text: source, json, hash: sha256Text(json), refs: '[]' });
    at = node.offset + node.length;
  };

  if (root.type !== 'object') {
    value(root, null, null);
  } else {
    const sections = sectionsOf(root);
    for (const p of root.children ?? []) {
      const [k, v] = /** @type {JsonNode[]} */ (p.children);
      const name = /** @type {string} */ (k.value);
      const s = sections.get(name);
      if (!v) continue;
      if (s && !s.single && v.type === 'array') {
        for (const item of v.children ?? []) value(item, name, s.kind);
        gap(v.offset + v.length, name);
      } else {
        value(v, name, s?.single ? s.kind : null);
      }
    }
  }
  gap(text.length, null);
  return { entities, trivia, root };
}

/**
 * The references of each row, from the model's references (by the section and item index they are
 * declared at); a row of a single section is keyed by its section alone.
 * @param {EntityRow[]} entities @param {JsonNode} root @param {import('../src/core/types.js').Model|null} model
 */
function attachRefs(entities, root, model) {
  if (!model || root.type !== 'object') return;
  // The last member of a name is the one the model reads, as in JSON.
  /** @type {Map<string, EntityRow>} */
  const byPath = new Map();
  const byPosition = new Map(entities.map((e) => [e.position, e]));
  for (const p of root.children ?? []) {
    const [k, v] = /** @type {JsonNode[]} */ (p.children);
    if (!v) continue;
    const name = String(k.value);
    if (v.type === 'array') (v.children ?? []).forEach((item, i) => { const r = byPosition.get(item.offset); if (r && r.kind) byPath.set(`${name}\u0000${i}`, r); });
    const whole = byPosition.get(v.offset);
    if (whole) byPath.set(name, whole);
  }
  /** @type {Map<EntityRow, Set<string>>} */
  const targets = new Map();
  for (const r of model.refs) {
    const [section, index] = r.path;
    const row = (typeof index === 'number' ? byPath.get(`${section}\u0000${index}`) : undefined) ?? byPath.get(String(section));
    if (!row) continue;
    if (!targets.has(row)) targets.set(row, new Set());
    /** @type {Set<string>} */ (targets.get(row)).add(r.target);
  }
  for (const [row, set] of targets) row.refs = JSON.stringify([...set]);
}

// ---------------------------------------------------------------------------
// Import and export
// ---------------------------------------------------------------------------

/**
 * Replace the store's contents with a specification text, in one transaction. Refuses (StoreError) a
 * text that does not parse or is not well-formed Unicode, and any text whose export would differ.
 * @param {DatabaseSync} db
 * @param {string} text
 * @param {{project?: string}} [opts]
 * @returns {{entities: number, trivia: number, refs: number, semanticHash: string, length: number}}
 */
export function importText(db, text, opts = {}) {
  const { entities, trivia, root } = sliceSpec(text);
  const { model } = parseSpec(text);
  attachRefs(entities, root, model);
  const hash = semanticHash(model);
  let refCount = 0;
  db.exec('BEGIN IMMEDIATE');
  try {
    db.exec('DELETE FROM entity; DELETE FROM trivia; DELETE FROM ref; DELETE FROM meta;');
    const insEntity = db.prepare('INSERT INTO entity (position, section, id, kind, component, source_text, json, hash, refs) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)');
    const insRef = db.prepare('INSERT OR IGNORE INTO ref (position, target) VALUES (?, ?)');
    for (const e of entities) {
      insEntity.run(e.position, e.section, e.id, e.kind, e.component, e.source_text, e.json, e.hash, e.refs);
      for (const t of JSON.parse(e.refs)) { insRef.run(e.position, t); refCount++; }
    }
    const insTrivia = db.prepare('INSERT INTO trivia (position, section, text) VALUES (?, ?, ?)');
    for (const t of trivia) insTrivia.run(t.position, t.section, t.text);
    const insMeta = db.prepare('INSERT INTO meta (key, value) VALUES (?, ?)');
    const meta = {
      format: STORE_FORMAT,
      format_version: String(STORE_FORMAT_VERSION),
      project: opts.project ?? '',
      semantic_hash: hash,
      position_unit: POSITION_UNIT,
      source_sha256: sha256Text(text),
      source_length: String(text.length),
    };
    for (const [k, v] of Object.entries(meta)) insMeta.run(k, v);
    const back = exportText(db);
    if (back !== text) {
      throw new StoreError('store.roundtrip', `The stored rows do not give the text back (first difference at code unit ${firstDifference(back, text)}); nothing is stored.`);
    }
    db.exec('COMMIT');
  } catch (e) {
    db.exec('ROLLBACK');
    throw e;
  }
  return { entities: entities.length, trivia: trivia.length, refs: refCount, semanticHash: hash, length: text.length };
}

/** @param {string} a @param {string} b */
function firstDifference(a, b) {
  const n = Math.min(a.length, b.length);
  for (let i = 0; i < n; i++) if (a.charCodeAt(i) !== b.charCodeAt(i)) return i;
  return n;
}

/**
 * The specification text the store holds: every row's text in position order.
 * @param {DatabaseSync} db
 * @returns {string}
 */
export function exportText(db) {
  const rows = /** @type {{t: string}[]} */ (db.prepare('SELECT source_text AS t, position FROM entity UNION ALL SELECT text AS t, position FROM trivia ORDER BY position').all());
  let out = '';
  for (const r of rows) out += r.t;
  return out;
}

/**
 * Decode a file's bytes as UTF-8, refusing anything that would not encode back to the same bytes.
 * A byte order mark is kept as U+FEFF.
 * @param {Buffer|Uint8Array} bytes @param {string} [what]
 */
export function decodeUtf8(bytes, what = 'The specification') {
  try {
    return new TextDecoder('utf-8', { fatal: true, ignoreBOM: true }).decode(bytes);
  } catch {
    throw new StoreError('store.encoding', `${what} is not valid UTF-8; it is not stored.`);
  }
}

/**
 * Import a specification file into a store database file.
 * @param {string} specFile @param {string} dbFile @param {{project?: string}} [opts]
 */
export function importFile(specFile, dbFile, opts = {}) {
  let bytes;
  try { bytes = fs.readFileSync(specFile); } catch { throw new StoreError('store.not-found', `${specFile} cannot be read.`); }
  const text = decodeUtf8(bytes, specFile);
  const db = openStore(dbFile);
  try {
    return importText(db, text, opts);
  } finally {
    db.close();
  }
}

/**
 * Export a store database file to a file, atomically. When `guard` is true and the target exists, it is
 * replaced only if it is the text the store last synchronised with, or already the exported text;
 * otherwise StoreError store.stale (the file changed since the import, and writing would lose that).
 * @param {string} dbFile @param {string} outFile @param {{guard?: boolean}} [opts]
 * @returns {{changed: boolean, length: number, bytes: number, sha256: string}}
 */
export function exportFile(dbFile, outFile, opts = {}) {
  if (!fs.existsSync(dbFile)) throw new StoreError('store.not-found', `No store at ${dbFile}; run exegra store import first.`);
  const db = openStore(dbFile);
  try {
    const meta = metaOf(db);
    if (meta.format !== STORE_FORMAT) throw new StoreError('store.format', `${dbFile} holds no imported specification.`);
    const text = exportText(db);
    const sha = sha256Text(text);
    const bytes = Buffer.from(text, 'utf8');
    /** @type {Buffer|null} */
    let current = null;
    try { current = fs.readFileSync(outFile); } catch { current = null; }
    if (current !== null && current.equals(bytes)) return { changed: false, length: text.length, bytes: bytes.length, sha256: sha };
    if (opts.guard && current !== null) {
      const currentSha = createHash('sha256').update(current).digest('hex');
      if (currentSha !== meta.source_sha256) {
        throw new StoreError('store.stale', `${outFile} changed since the store was last synchronised with it; import it again, or export with --out to another file.`);
      }
    }
    const tmp = `${outFile}.${process.pid}.store.tmp`;
    fs.mkdirSync(path.dirname(path.resolve(outFile)), { recursive: true });
    fs.writeFileSync(tmp, bytes);
    fs.renameSync(tmp, outFile);
    db.prepare('UPDATE meta SET value = ? WHERE key = ?').run(sha, 'source_sha256');
    return { changed: true, length: text.length, bytes: bytes.length, sha256: sha };
  } finally {
    db.close();
  }
}

// ---------------------------------------------------------------------------
// Reading
// ---------------------------------------------------------------------------

/**
 * Every row of a store, in position order: for comparing two stores.
 * @param {DatabaseSync} db
 */
export function storeRows(db) {
  return {
    meta: db.prepare('SELECT key, value FROM meta ORDER BY key').all(),
    entity: db.prepare('SELECT position, section, id, kind, component, source_text, json, hash, refs FROM entity ORDER BY position').all(),
    trivia: db.prepare('SELECT position, section, text FROM trivia ORDER BY position').all(),
    ref: db.prepare('SELECT position, target FROM ref ORDER BY position, target').all(),
  };
}

/**
 * The model, diagnostics and semantic hash of the specification a store holds, derived from its exported
 * text by the same analysis as a file (src/core/analyze.js), so validate on the store and on the text
 * report the same. storedHash is the semantic hash recorded at import.
 * @param {DatabaseSync} db
 */
export function loadModelFromStore(db) {
  const text = exportText(db);
  const analysis = analyzeSpec(text);
  return { ...analysis, semanticHash: semanticHash(analysis.model), storedHash: metaOf(db).semantic_hash ?? null, text };
}
