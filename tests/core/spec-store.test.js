// The specification store (tools/spec-store.js): a specification imported into SQLite and exported again
// is the same text byte for byte, re-importing an export gives the same rows, and the model read from the
// store is the model of the text.
import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import zlib from 'node:zlib';
import { fileURLToPath } from 'node:url';
import {
  openStore, importText, exportText, storeRows, loadModelFromStore, sliceSpec, decodeUtf8,
  importFile, exportFile, defaultDbPath, StoreError, POSITION_UNIT,
} from '../../tools/spec-store.js';
import { analyzeSpec } from '../../src/core/analyze.js';
import { semanticHash } from '../../src/core/hash.js';
import { createWorkspace } from '../../tools/workspace.js';
import { runCommand } from '../../cli/commands.js';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const FIXTURES = path.join(ROOT, 'tests/fixtures');

/** Every .jsonc file under a directory. @param {string} dir @returns {string[]} */
function jsoncFiles(dir) {
  /** @type {string[]} */
  const out = [];
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    const p = path.join(dir, entry.name);
    if (entry.isDirectory()) out.push(...jsoncFiles(p));
    else if (entry.name.endsWith('.jsonc')) out.push(p);
  }
  return out.sort();
}

/** The specification of every project under specs/ that has one (linked projects included when present). */
function projectSpecs() {
  const ws = createWorkspace(path.join(ROOT, 'specs'));
  /** @type {string[]} */
  const out = [];
  for (const entry of fs.readdirSync(path.join(ROOT, 'specs'), { withFileTypes: true })) {
    if (!entry.isDirectory()) continue;
    let file;
    try { file = ws.specFile(entry.name); } catch { continue; }
    if (fs.existsSync(file)) out.push(file);
  }
  return out.sort();
}

/** Import a text into a fresh in-memory store. @param {string} text */
function stored(text) {
  const db = openStore(':memory:');
  importText(db, text, { project: 't' });
  return db;
}

/**
 * The rows of a text in position order, checked to be contiguous: every code unit in exactly one row.
 * @param {import('node:sqlite').DatabaseSync} db @param {string} text
 */
function assertPartition(db, text) {
  const { entity, trivia } = storeRows(db);
  const rows = [...entity.map((r) => ({ position: Number(r.position), text: String(r.source_text) })), ...trivia.map((r) => ({ position: Number(r.position), text: String(r.text) }))]
    .sort((a, b) => a.position - b.position);
  let at = 0;
  for (const r of rows) {
    assert.equal(r.position, at, 'rows are contiguous');
    assert.ok(r.text.length > 0, 'no empty row');
    assert.equal(r.text, text.slice(at, at + r.text.length), 'a row is a verbatim slice');
    at += r.text.length;
  }
  assert.equal(at, text.length, 'the rows cover the whole text');
}

/** export(import(S)) is S, byte for byte, and the rows partition S. @param {string} text */
function assertRoundTrip(text) {
  const db = stored(text);
  const back = exportText(db);
  assert.equal(back, text);
  assert.ok(Buffer.from(back, 'utf8').equals(Buffer.from(text, 'utf8')));
  assertPartition(db, text);
  db.close();
}

for (const file of projectSpecs()) {
  test(`round trip: ${path.relative(ROOT, file).split(path.sep).join('/')}`, () => {
    const bytes = fs.readFileSync(file);
    const text = decodeUtf8(bytes);
    const db = stored(text);
    assert.ok(Buffer.from(exportText(db), 'utf8').equals(bytes), 'the export is the file, byte for byte');
    db.close();
  });
}

for (const file of jsoncFiles(FIXTURES)) {
  test(`round trip: ${path.relative(ROOT, file).split(path.sep).join('/')}`, () => {
    const bytes = fs.readFileSync(file);
    const text = decodeUtf8(bytes);
    const db = stored(text);
    assert.ok(Buffer.from(exportText(db), 'utf8').equals(bytes), 'the export is the file, byte for byte');
    assertPartition(db, text);
    db.close();
  });
}

test('round trip of every parse corpus case and refusal of a case that does not parse', () => {
  const cases = JSON.parse(zlib.gunzipSync(fs.readFileSync(path.join(FIXTURES, 'parse-corpus/cases.json.gz'))).toString('utf8'));
  let kept = 0, refused = 0;
  for (const text of cases) {
    assert.equal(typeof text, 'string');
    /** @type {any} */
    let error = null;
    try { sliceSpec(text); } catch (e) { error = e; }
    if (error) {
      assert.ok(error instanceof StoreError, String(error));
      assert.ok(error.code === 'store.syntax' || error.code === 'store.encoding', error.code);
      assert.throws(() => importText(openStore(':memory:'), text), (e) => e instanceof StoreError && e.code === error.code);
      refused++;
    } else {
      assertRoundTrip(text);
      kept++;
    }
  }
  assert.ok(kept > 0 && refused > 0 && kept + refused === cases.length);
});

test('reimporting an export gives the same rows', () => {
  for (const file of [path.join(ROOT, 'specs/exegra/spec.jsonc'), path.join(FIXTURES, 'multiplayer/spec.jsonc'), path.join(FIXTURES, 'register-import/repo/draft.jsonc')]) {
    const d = stored(fs.readFileSync(file, 'utf8'));
    const again = stored(exportText(d));
    assert.deepEqual(storeRows(again), storeRows(d));
    d.close();
    again.close();
  }
});

const EDGE_CASES = {
  crlf: '{\r\n  "exegra": "0.1",\r\n  "system": { "id": "s", "name": "S" },\r\n  "components": [\r\n    { "id": "a", "name": "A", "category": "logical" },\r\n    { "id": "b", "name": "B", "category": "logical" }\r\n  ]\r\n}\r\n',
  bom: '﻿{\n  "exegra": "0.1",\n  "system": { "id": "s", "name": "S" },\n  "components": [ { "id": "a", "name": "A", "category": "logical" } ]\n}\n',
  tabs: '{\n\t"exegra": "0.1",\n\t"system": {\t"id": "s", "name": "S" },\n\t"components": [\n\t\t{ "id": "a",\t"name": "A", "category": "logical" }\n\t]\n}\n',
  trailingCommas: '{\n  "exegra": "0.1",\n  "system": { "id": "s", "name": "S", },\n  "components": [\n    { "id": "a", "name": "A", "category": "logical", },\n    { "id": "b", "name": "B", "category": "logical" },\n  ],\n}\n',
  comments: '// head\n/* block */ {\n  "exegra": "0.1", // version\n  "system": { "id": "s", /* inside */ "name": "S" },\n  // before the section\n  "components": [ // after the bracket\n    // before a\n    { "id": "a", // inside a\n      "name": "A", "category": "logical" } /* after a */ ,\n    /* before b */ { "id": "b", "name": "B", "category": "logical" }\n    // after the last\n  ]\n  // before the end\n}\n// tail\n',
  emptySection: '{\n  "exegra": "0.1",\n  "system": { "id": "s", "name": "S" },\n  "components": [],\n  "claims": [\n  ]\n}\n',
  noTrailingNewline: '{\n  "exegra": "0.1",\n  "system": { "id": "s", "name": "S" },\n  "components": [ { "id": "a", "name": "A", "category": "logical" } ]\n}',
  nonAscii: '{\n  // Größe, naïve, 日本語, 😀\n  "exegra": "0.1",\n  "system": { "id": "s", "name": "Système 😀" },\n  "components": [ { "id": "a", "name": "Ünïcödé 日本", "category": "logical" }, { "id": "b", "name": "\\u00e9 escaped", "category": "logical" } ]\n}\n',
  nonEntitySections: '{\n  "exegra": "0.1",\n  "system": { "id": "s", "name": "S" },\n  "decisions": [ { "id": "d1", "text": "kept whole" } ],\n  "unknownScalar": 42\n}\n',
};

for (const [name, text] of Object.entries(EDGE_CASES)) {
  test(`round trip edge case: ${name}`, () => assertRoundTrip(text));
}

test('positions count UTF-16 code units of the imported text and not bytes', () => {
  assert.equal(POSITION_UNIT, 'utf16-code-unit');
  const text = EDGE_CASES.nonAscii;
  const { entity } = storeRows(stored(text));
  const a = entity.find((r) => r.id === 'a');
  assert.ok(a);
  assert.equal(Number(a.position), text.indexOf('{ "id": "a"'));
  assert.notEqual(Number(a.position), Buffer.byteLength(text.slice(0, text.indexOf('{ "id": "a"')), 'utf8'));
  // The byte order mark is the first code unit, held in the first trivia row.
  const bom = storeRows(stored(EDGE_CASES.bom));
  assert.equal(bom.trivia[0].position, 0);
  assert.ok(String(bom.trivia[0].text).startsWith('﻿{'));
});

test('entity sections are cut per item, other sections are stored whole', () => {
  const rows = storeRows(stored(EDGE_CASES.nonEntitySections));
  assert.deepEqual(rows.entity.map((r) => [r.section, r.kind, r.id]), [['exegra', null, null], ['system', 'system', 's'], ['decisions', null, null], ['unknownScalar', null, null]]);
  assert.equal(rows.entity[2].source_text, '[ { "id": "d1", "text": "kept whole" } ]');
  const comments = storeRows(stored(EDGE_CASES.comments));
  const a = comments.entity.find((r) => r.id === 'a');
  assert.equal(a?.source_text, '{ "id": "a", // inside a\n      "name": "A", "category": "logical" }');
  assert.ok(comments.trivia.some((r) => String(r.text).includes('/* after a */ ,\n    /* before b */ ')));
  // A section a vocabulary declares is an entity section.
  const draft = storeRows(stored(fs.readFileSync(path.join(FIXTURES, 'register-import/repo/draft.jsonc'), 'utf8')));
  assert.ok(draft.entity.some((r) => r.section === 'openDecisions' && r.kind === 'openDecision' && r.id === 'od-1'));
});

test('the index columns: kind, component and references', () => {
  const db = stored(fs.readFileSync(path.join(ROOT, 'specs/exegra/spec.jsonc'), 'utf8'));
  const component = /** @type {any} */ (db.prepare("SELECT * FROM entity WHERE kind = 'component' AND id = 'workspace-service'").get());
  assert.equal(component.component, 'workspace-service');
  const inbound = db.prepare('SELECT e.id FROM ref r JOIN entity e ON e.position = r.position WHERE r.target = ?').all('workspace-service').map((r) => r.id);
  assert.ok(inbound.length > 0);
  for (const r of /** @type {any[]} */ (db.prepare('SELECT * FROM entity').all())) assert.deepEqual(JSON.parse(r.json), JSON.parse(JSON.stringify(analyzeOne(r.source_text))));
  db.close();
});

/** The JSON value of an entity's source text. @param {string} source */
function analyzeOne(source) {
  const { entities } = sliceSpec(`{"x": ${source}}`);
  return JSON.parse(entities[0].json);
}

test('a text that does not parse is refused and the store keeps what it held', () => {
  const db = stored(EDGE_CASES.crlf);
  const broken = '{\n  "exegra": "0.1",\n  "system": { "id": "s" \n}\n';
  assert.throws(() => importText(db, broken), (e) => e instanceof StoreError && e.code === 'store.syntax' && /line \d+, column \d+/.test(e.message) && e.diagnostics.length > 0);
  assert.equal(exportText(db), EDGE_CASES.crlf);
  assert.throws(() => importText(db, ''), (e) => e instanceof StoreError && e.code === 'store.syntax');
  assert.throws(() => importText(db, '{"exegra": "\uD800"}'), (e) => e instanceof StoreError && e.code === 'store.encoding');
  assert.throws(() => decodeUtf8(Buffer.from([0x7b, 0xff, 0x7d])), (e) => e instanceof StoreError && e.code === 'store.encoding');
  assert.equal(exportText(db), EDGE_CASES.crlf);
});

test('the model read from the store is the model of the text: semantic hash and diagnostics', () => {
  const texts = [
    fs.readFileSync(path.join(ROOT, 'specs/exegra/spec.jsonc'), 'utf8'),
    fs.readFileSync(path.join(FIXTURES, 'register-import/repo/draft.jsonc'), 'utf8'),
    EDGE_CASES.bom,
    '{\n  "exegra": "0.1",\n  "system": { "id": "s", "name": "S" },\n  "components": [ { "id": "a", "name": "A", "category": "logical", "parent": "missing" } ]\n}\n',
  ];
  for (const text of texts) {
    const fromText = analyzeSpec(text);
    const fromStore = loadModelFromStore(stored(text));
    assert.equal(fromStore.semanticHash, semanticHash(fromText.model));
    assert.equal(fromStore.storedHash, fromStore.semanticHash);
    assert.deepEqual(fromStore.diagnostics, fromText.diagnostics);
    assert.equal(fromStore.errorCount, fromText.errorCount);
    assert.deepEqual(fromStore.model ? [...fromStore.model.entities.keys()] : null, fromText.model ? [...fromText.model.entities.keys()] : null);
  }
});

test('files: a WAL database beside the specification and an exact export that never overwrites a stale specification', () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-store-'));
  try {
    const spec = path.join(dir, 'spec.jsonc');
    fs.writeFileSync(spec, EDGE_CASES.crlf);
    const db = defaultDbPath(spec);
    assert.equal(db, `${spec}.sqlite`);
    importFile(spec, db, { project: 'p' });
    const open = openStore(db);
    assert.equal(/** @type {any} */ (open.prepare('PRAGMA journal_mode').get()).journal_mode, 'wal');
    open.close();
    const out = path.join(dir, 'out.jsonc');
    assert.equal(exportFile(db, out).changed, true);
    assert.ok(fs.readFileSync(out).equals(fs.readFileSync(spec)));
    assert.equal(exportFile(db, spec, { guard: true }).changed, false);
    fs.writeFileSync(spec, EDGE_CASES.tabs);
    assert.throws(() => exportFile(db, spec, { guard: true }), (e) => e instanceof StoreError && e.code === 'store.stale');
    assert.equal(fs.readFileSync(spec, 'utf8'), EDGE_CASES.tabs);
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
});

test('exegra store import and export through the command line', async () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-store-cli-'));
  try {
    const specs = path.join(dir, 'specs');
    fs.mkdirSync(path.join(specs, 'p'), { recursive: true });
    const spec = path.join(specs, 'p', 'spec.jsonc');
    fs.copyFileSync(path.join(FIXTURES, 'multiplayer/spec.jsonc'), spec);
    const imported = await runCommand('store', ['import', '--project', 'p'], { specs });
    assert.equal(imported.ok, true, JSON.stringify(imported.error));
    assert.equal(imported.result.db, `${spec}.sqlite`);
    assert.equal(imported.semanticHash, semanticHash(analyzeSpec(fs.readFileSync(spec, 'utf8')).model));
    const out = path.join(dir, 'exported.jsonc');
    const exported = await runCommand('store', ['export', '--project', 'p', '--out', out], { specs });
    assert.equal(exported.ok, true, JSON.stringify(exported.error));
    assert.ok(fs.readFileSync(out).equals(fs.readFileSync(spec)));
    fs.writeFileSync(spec, '{ "broken": ');
    const refused = await runCommand('store', ['import', '--project', 'p'], { specs });
    assert.equal(refused.ok, false);
    assert.equal(refused.error?.code, 'store.syntax');
    const stale = await runCommand('store', ['export', '--project', 'p'], { specs });
    assert.equal(stale.error?.code, 'store.stale');
    const bad = await runCommand('store', ['sideways', '--project', 'p'], { specs });
    assert.equal(bad.error?.code, 'usage.invalid-argument');
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
});
