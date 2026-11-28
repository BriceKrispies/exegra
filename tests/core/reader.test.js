// Tests for reader pages (src/core/reader.js): the page data a reader view derives from the model.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { analyzeSpec } from '../../src/core/analyze.js';
import { listViews, project } from '../../src/core/projections.js';
import { readerPage, kindPage, sectionBlocks, outline, classify, resolvePath, refIndex, ROW_CAP } from '../../src/core/reader.js';

// A small library catalogue: declared kinds for documents, sections, tables, shelves and books.
const SPEC = `{
  "exegra": "0.1",
  "system": { "id": "library", "name": "Library", "description": "A small library catalogue." },
  "vocabulary": {
    "entityKinds": {
      "document": { "label": "Document", "section": "documents", "properties": { "title": { "type": "string" } } },
      "section": { "label": "Section", "section": "sections", "properties": { "title": { "type": "string" }, "level": { "type": "number" }, "order": { "type": "number" }, "document": { "type": "ref", "ref": ["document"] }, "body": { "type": "text" } } },
      "table": { "label": "Table", "section": "tables", "properties": { "section": { "type": "ref", "ref": ["section"] }, "columns": { "type": "list", "items": { "type": "string" } }, "columnProperties": { "type": "list", "items": { "type": "string" } } } },
      "shelf": { "label": "Shelf", "section": "shelves", "properties": { "name": { "type": "string" } } },
      "book": { "label": "Book", "section": "books", "properties": { "ref": { "type": "string" }, "title": { "type": "text", "label": "Title" }, "state": { "type": "text", "label": "State" }, "shelf": { "type": "ref", "ref": ["shelf"], "label": "Shelf" }, "table": { "type": "ref", "ref": ["table"] }, "returnedBy": { "type": "string" } } }
    }
  },
  "documents": [ { "id": "doc-guide", "title": "Guide" } ],
  "sections": [
    { "id": "sec-intro", "title": "Introduction", "level": 1, "order": 1, "document": "doc-guide", "body": "Books are lent for **two weeks**. See BK-2.\\n{{entity:tbl-books}}\\n{{entity:bk-1}}\\n{{entity:bk-2}}\\nAfter the table." },
    { "id": "sec-rules", "title": "Rules", "level": 2, "order": 2, "document": "doc-guide", "body": "- Return on time" }
  ],
  "tables": [ { "id": "tbl-books", "section": "sec-intro", "columns": ["Ref", "Title"], "columnProperties": ["ref", "title"] } ],
  "shelves": [ { "id": "shelf-a", "name": "Shelf A" }, { "id": "shelf-b", "name": "Shelf B" } ],
  "books": [
    { "id": "bk-1", "ref": "BK-1", "title": "Graphs", "state": "On loan.", "shelf": "shelf-a", "table": "tbl-books" },
    { "id": "bk-2", "ref": "BK-2", "title": "Proofs", "state": "Available", "shelf": "shelf-b", "table": "tbl-books", "returnedBy": "a reader" },
    { "id": "bk-3", "ref": "BK-3", "title": "Queues", "state": "Partly damaged", "shelf": "shelf-a" }
  ],
  "views": [
    { "id": "books", "name": "Books", "projection": "reader", "description": "Every book.", "reader": { "blocks": [
      { "type": "counts", "title": "By state", "kind": "book", "property": "state", "groupBy": "shelf",
        "classify": [ { "pattern": "^available", "value": "in", "label": "In", "tone": "done" }, { "pattern": "^partly", "value": "part", "label": "Partly", "tone": "partial" }, { "pattern": "loan", "value": "out", "label": "Out", "tone": "todo" } ] },
      { "type": "table", "title": "Catalogue", "kind": "book", "groupBy": "shelf", "facet": "state",
        "columns": [ { "property": "title", "label": "Title" }, { "property": "state", "label": "State", "status": true }, { "property": "shelf", "label": "Shelf" } ],
        "classify": [ { "pattern": "^available", "value": "in", "label": "In", "tone": "done" }, { "pattern": ".", "value": "other", "label": "Other" } ] },
      { "type": "list", "kind": "book", "where": [ { "property": "title", "matches": "^(graphs|proofs)$" } ], "hideWhenSet": "returnedBy", "metaProperties": ["shelf"] },
      { "type": "sections", "ids": ["sec-intro"] },
      { "type": "document" }
    ] } }
  ]
}`;

const { model, diagnostics } = analyzeSpec(SPEC);

test('a reader view validates and is listed with its projection', () => {
  const errors = diagnostics.filter((d) => d.severity === 'error');
  assert.deepEqual(errors, []);
  const v = listViews(model).find((x) => x.id === 'books');
  assert.equal(v?.projection, 'reader');
  const scene = project(model, 'books');
  assert.equal(scene.projection, 'reader');
  assert.equal(scene.nodes.length, 0);
});

// An unknown block field is an error.
// @evidence reader-blocks-validated
test('unknown fields in a reader block are refused', () => {
  const bad = SPEC.replace('"type": "document" }', '"type": "document", "colour": "red" }');
  const r = analyzeSpec(bad);
  assert.ok(r.diagnostics.some((d) => d.severity === 'error' && /colour/.test(d.message)));
});

// Counts classify a text property and group by a referenced entity.
// @evidence reader-pages-come-from-model
test('counts classify text and group by a reference', () => {
  const page = readerPage(model, model.entities.get('books')?.data);
  const counts = page.blocks[0];
  assert.equal(counts.type, 'counts');
  assert.equal(counts.total, 3);
  assert.deepEqual(counts.values.map((/** @type {any} */ v) => [v.value, v.count]), [['in', 1], ['part', 1], ['out', 1]]);
  assert.deepEqual(counts.groups.map((/** @type {any} */ g) => [g.label, g.total]), [['Shelf A', 2], ['Shelf B', 1]]);
});

// A table groups, classifies, links references and offers facets.
// @evidence reader-pages-come-from-model
test('a table groups and classifies rows with links and facets', () => {
  const t = readerPage(model, model.entities.get('books')?.data).blocks[1];
  assert.equal(t.type, 'table');
  assert.deepEqual(t.groups.map((/** @type {any} */ g) => g.label), ['Shelf A', 'Shelf B']);
  const row = t.groups[0].rows[0];
  assert.equal(row.ref, 'BK-1');
  assert.equal(row.cells[1].status, 'other');
  assert.deepEqual(row.cells[2].links, [{ id: 'shelf-a', label: 'Shelf A' }]);
  assert.deepEqual(t.facet.values.map((/** @type {any} */ v) => v.value).sort(), ['in', 'other']);
});

// A list keeps only rows that meet its conditions and marks the hidden ones.
// @evidence reader-pages-come-from-model
test('a list honours where and marks rows hidden until asked', () => {
  const l = readerPage(model, model.entities.get('books')?.data).blocks[2];
  const ids = l.groups[0].rows.map((/** @type {any} */ r) => [r.id, r.optional]);
  assert.deepEqual(ids, [['bk-1', false], ['bk-2', true]]);
  assert.equal(l.toggle.label, 'Show all');
});

// Section bodies split into prose and tables; the outline follows reading order.
// @evidence reader-pages-come-from-model
test('section bodies split into prose and the tables their markers place', () => {
  const blocks = sectionBlocks(model, 'sec-intro');
  assert.deepEqual(blocks.map((b) => b.type), ['prose', 'table', 'prose']);
  assert.deepEqual(blocks[1].rows.map((/** @type {any} */ r) => r.cells), [['BK-1', 'Graphs'], ['BK-2', 'Proofs']]);
  assert.deepEqual(outline(model).sections.map((s) => [s.id, s.level]), [['sec-intro', 1], ['sec-rules', 2]]);
});

// A view without blocks gives the default page and a page per kind.
// @evidence reader-pages-come-from-model
test('a view without blocks reads the system and its kinds and its document', () => {
  const page = readerPage(model, { name: 'Reader' });
  assert.deepEqual(page.blocks.map((b) => b.type), ['text', 'index', 'document']);
  const kinds = page.blocks[1].kinds.map((/** @type {any} */ k) => k.kind);
  assert.ok(kinds.includes('book') && kinds.includes('section'));
  const books = kindPage(model, 'book');
  assert.equal(books.blocks[0].total, 3);
});

test('helpers: classification, paths and the ref index', () => {
  assert.equal(classify('Partly built', [{ pattern: '^partly', value: 'p' }]).value, 'p');
  assert.equal(classify('x', [{ pattern: '^y', value: 'y' }]).label, 'Other');
  const bk = model.entities.get('bk-1');
  assert.ok(bk);
  assert.equal(resolvePath(model, bk, 'table.section').entity?.id, 'sec-intro');
  assert.equal(refIndex(model).get('bk-2'), 'bk-2');
  assert.ok(ROW_CAP >= 100);
});
