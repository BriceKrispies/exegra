// The register importer: one Markdown file of headings, prose and tables, on the fixture under tests/fixtures/register-import.
import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { parse as parseJsonc } from 'jsonc-parser';
import { analyzeSpec } from '../../src/core/analyze.js';
import { buildRegisterSpec, readDraft, readMap, rowCells, renderCheck, renderMarkdown, propertyName, sectionKey, cleanKey } from '../../tools/import-register.js';
import { fileLines } from '../../tools/import-markdown.js';

const FIXTURE = path.join(path.dirname(fileURLToPath(import.meta.url)), '..', 'fixtures', 'register-import');
const map = readMap(path.join(FIXTURE, 'import-map.jsonc'));
const text = fs.readFileSync(path.join(FIXTURE, 'repo', map.file), 'utf8');
const run = () => buildRegisterSpec({ map, text, file: map.file, commit: 'fixture' });

test('rowCells splits on unescaped pipes only and keeps the escape', () => {
  assert.deepEqual(rowCells('| a | b \\| c | `d` |'), ['a', 'b \\| c', '`d`']);
  assert.equal(propertyName('Data store'), 'dataStore');
  assert.equal(propertyName('#'), 'number');
  assert.equal(sectionKey('4.1 Platform capabilities'), 'sec-4-1');
  assert.equal(sectionKey('Appendix A. Register'), 'sec-appendix-a');
});

// The fixture converts with both checks passing, the output validates without errors and the sections rebuild the file exactly.
// @evidence register-import-holds-every-line
test('the fixture imports and validates and rebuilds line for line', () => {
  const r = run();
  assert.ok(r.ok, 'both checks pass');
  assert.ok(r.cov.ok, 'every line held');
  assert.deepEqual(r.unfaithful, []);
  const { errorCount, diagnostics } = analyzeSpec(r.text);
  assert.equal(errorCount, 0, JSON.stringify(diagnostics.filter((d) => d.severity === 'error')));
  const spec = parseJsonc(r.text);
  assert.deepEqual(fileLines(renderMarkdown(spec)), fileLines(text), 'the file renders back from the written specification alone');
  assert.equal(run().text, r.text, 'deterministic');
  assert.deepEqual(spec.components.map((/** @type {any} */ c) => [c.id, c.category]), [['api', 'computational'], ['store', 'storage']]);
  assert.deepEqual(spec.features.find((/** @type {any} */ c) => c.id === 'cap-02').owners, ['store', 'api']);
  assert.deepEqual(spec.relationships.map((/** @type {any} */ x) => [x.from, x.to, x.label, x.description, x.state]), [['api', 'store', 'I-1', 'SQL over TLS', 'Built']]);
  assert.deepEqual(spec.conflicts[0].mentions, ['cap-02']);
  assert.ok(r.loss.lines().some((l) => l.startsWith('row with a different number of cells')), 'the short row is reported');
  assert.ok(!spec.tables.some((/** @type {any} */ t) => t.columns[0] === 'Not'), 'a table in a code fence is prose');
});

test('ids, mentions and citations follow the map', () => {
  assert.equal(cleanKey('`*`'), '*', 'a whole code span is the key');
  assert.equal(cleanKey('**CAP-01**'), 'CAP-01');
  const spec = parseJsonc(run().text);
  const sec = (/** @type {string} */ id) => spec.sections.find((/** @type {any} */ s) => s.id === id);
  // A row whose id cell fails the pattern takes the identifier in fallbackColumn.
  assert.deepEqual(spec.tickets.map((/** @type {any} */ t) => [t.id, t.ref]), [['erq-2', 'ERQ-2'], ['erq-3', 'ERQ-3']]);
  assert.deepEqual(spec.tickets[0].citations, ['REPO:t.md'], 'no citation from a source-text column');
  assert.deepEqual(sec('sec-4').mentions, ['cap-02'], 'a heading is read for mentions');
  assert.equal(sec('sec-appendix-m').mentions, undefined, 'notUnder skips the pattern');
  assert.deepEqual(sec('sec-appendix-m').citations, ['REPO:b `c.ts`'], 'a bracket opened in code is not a citation');
});

// A row whose rendering differs from its source cells fails the import and is named.
// @evidence register-import-holds-every-line
test('a row that does not render back fails the import', () => {
  const spec = parseJsonc(run().text);
  const cap = spec.features.find((/** @type {any} */ c) => c.id === 'cap-01');
  const raw = new Map([['cap-01', '| CAP-01 | Create widgets | API | [REPO:api/create.ts:1-20] |']]);
  assert.deepEqual(renderCheck(spec, raw), []);
  cap.capability = 'Create';
  const bad = renderCheck(spec, raw);
  assert.equal(bad.length, 1);
  assert.equal(bad[0].id, 'cap-01');
});

// Every document, section, table and row of the fixture output has a source whose line holds the text it came from, and keyed rows carry ref.
// @evidence register-import-entities-cite-source
test('every imported entity names its source line', () => {
  const spec = parseJsonc(run().text);
  const lines = fileLines(text);
  /** @type {any[]} */
  const all = [];
  for (const [key, list] of Object.entries(spec)) if (Array.isArray(list) && key !== 'views') all.push(...list);
  assert.ok(all.length > 10);
  for (const e of all) {
    assert.match(e.source ?? '', /^system\.md:\d+$/, `${e.id} has a source`);
    const line = lines[Number(e.source.split(':')[1]) - 1];
    if (e.ref !== undefined) assert.ok(line.includes(e.ref), `${e.id}: line ${e.source} holds ${e.ref}`);
    if (e.title) assert.ok(line.includes(e.title), `${e.id}: line ${e.source} holds its heading`);
  }
  for (const c of [...spec.components, ...spec.features, ...spec.interfaces, ...spec.conflicts]) assert.equal(typeof c.ref, 'string', `${c.id} carries ref`);
});

// A fixture draft merges with origin and source, its basis references are checked by validation, and the rendered Markdown is unchanged.
// @evidence register-import-drafts-are-marked
test('a draft fragment is merged with origin and source and a checked basis', () => {
  const draftText = fs.readFileSync(path.join(FIXTURE, 'repo', 'draft.jsonc'), 'utf8');
  const drafts = [readDraft('draft.jsonc', draftText)];
  const r = buildRegisterSpec({ map, text, file: map.file, commit: 'fixture', drafts });
  assert.ok(r.ok);
  const { errorCount, diagnostics } = analyzeSpec(r.text);
  assert.equal(errorCount, 0, JSON.stringify(diagnostics.filter((d) => d.severity === 'error')));
  const spec = parseJsonc(r.text);
  const dr = spec.claims.find((/** @type {any} */ c) => c.id === 'dr-1');
  assert.equal(dr.origin, 'draft');
  assert.equal(dr.source, 'draft.jsonc:12');
  assert.deepEqual(spec.openDecisions.map((/** @type {any} */ o) => o.id), ['od-1']);
  assert.ok(spec.components.some((/** @type {any} */ c) => c.id === 'cache' && c.origin === 'draft'));
  assert.ok(spec.system.notes.some((/** @type {string} */ n) => n.startsWith('DRAFT, NOT FROM THE MARKDOWN.')));
  assert.deepEqual(fileLines(renderMarkdown(spec)), fileLines(text), 'drafts do not change the rendered Markdown');
  const bad = buildRegisterSpec({ map, text, file: map.file, commit: 'fixture', drafts: [readDraft('draft.jsonc', draftText.replace('"cap-02"', '"cap-99"'))] });
  assert.ok(analyzeSpec(bad.text).errorCount > 0, 'a basis naming no entity is an error');
});

// An authority map makes the import exit 1 without writing; --render of a written specification gives the source Markdown.
// @evidence register-import-respects-authority
test('a map whose JSONC is the authority refuses to import and render needs only the JSONC', async () => {
  const { spawnSync } = await import('node:child_process');
  const os = await import('node:os');
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'register-authority-'));
  const mapFile = path.join(dir, 'import-map.jsonc');
  fs.writeFileSync(mapFile, JSON.stringify({ ...map, source: path.join(FIXTURE, 'repo'), authority: 'jsonc', authoritySince: 'test' }));
  const tool = path.join(FIXTURE, '..', '..', '..', 'tools', 'import-register.js');
  const refused = spawnSync(process.execPath, [tool, '--map', mapFile], { encoding: 'utf8' });
  assert.equal(refused.status, 1);
  assert.match(refused.stderr, /the JSONC is the authority/);
  const specFile = path.join(dir, 'spec.jsonc');
  fs.writeFileSync(specFile, run().text);
  const rendered = spawnSync(process.execPath, [tool, '--render', specFile], { encoding: 'utf8' });
  assert.equal(rendered.status, 0);
  assert.deepEqual(fileLines(rendered.stdout), fileLines(text));
  fs.rmSync(dir, { recursive: true, force: true });
});
