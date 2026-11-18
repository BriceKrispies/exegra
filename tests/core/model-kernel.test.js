// The verified kernel's model derivation and semantic hash (formal/Exegra/Model.lean and
// Hash.lean, called through src/core/parse.js and src/core/hash.js) against the JavaScript they
// replaced (tests/oracle/parse-reference.js): identical diagnostics, model and hash on
// - every specification the tests read: specs/exegra, specs/benchmark and tests/fixtures/**;
// - every specification text the core tests parse (tests/fixtures/parse-corpus/cases.json.gz:
//   the distinct texts parseSpec received while tests/core/{model,vocabulary,roundtrip,references,
//   data-model,contract-trace,fault-model,metric-spec,projections,flows,generate,claims,sim,replay,
//   import-markdown,cli,workspace}.test.js ran, the invalid-spec cases among them; 81 of the 206
//   have diagnostics);
// - the edge cases below (repeated keys, array-index keys, non-ASCII keys, unusual numbers).

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import zlib from 'node:zlib';
import { fileURLToPath } from 'node:url';
import * as reference from '../oracle/parse-reference.js';
import { parseSpec } from '../../src/core/parse.js';
import { semanticHash, normalize } from '../../src/core/hash.js';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');

/** @param {string} dir @returns {string[]} */
function jsoncFiles(dir) {
  return fs.readdirSync(dir, { withFileTypes: true }).flatMap((e) => {
    const p = path.join(dir, e.name);
    return e.isDirectory() ? jsoncFiles(p) : e.name.endsWith('.jsonc') ? [p] : [];
  });
}

/** Everything a model holds, as plain data (entities in declaration order, byKind as ids). @param {any} m */
function plainModel(m) {
  if (!m) return null;
  return {
    schemaVersion: m.schemaVersion,
    system: m.system?.id ?? null,
    entities: [...m.entities.values()],
    byKind: Object.fromEntries(Object.entries(m.byKind).map(([k, v]) => [k, /** @type {any[]} */ (v).map((e) => e.id)])),
    refs: m.refs,
    exprs: m.exprs,
    meta: JSON.parse(JSON.stringify(m.meta)),
    vocabulary: m.vocabulary,
  };
}

/** @param {string} text @param {string} name */
function same(text, name) {
  const want = reference.parseSpec(text);
  const got = parseSpec(text);
  assert.deepEqual(got.diagnostics, want.diagnostics, `${name}: diagnostics`);
  assert.deepEqual(plainModel(got.model), plainModel(want.model), `${name}: model`);
  assert.equal(semanticHash(got.model), reference.semanticHash(want.model), `${name}: semantic hash`);
  if (want.model) {
    // Compared as the text that is hashed: JSON carries -0 as 0 and an infinite number as null.
    assert.equal(JSON.stringify(normalize(/** @type {any} */ (got.model))), JSON.stringify(reference.normalize(want.model)), `${name}: normal form`);
    // A model without the hash parseSpec attached is hashed by Lean from its declarations.
    assert.equal(semanticHash({ .../** @type {any} */ (got.model), semanticHash: undefined }), reference.semanticHash(want.model), `${name}: hash of declarations`);
  }
  return want.diagnostics.length;
}

test('the specifications and fixtures the tests read derive identically', () => {
  const files = ['specs/exegra/spec.jsonc', 'specs/benchmark/spec.jsonc', ...jsoncFiles(path.join(ROOT, 'tests/fixtures')).map((f) => path.relative(ROOT, f))];
  assert.ok(files.length >= 6);
  for (const f of files) same(fs.readFileSync(path.join(ROOT, f), 'utf8'), f);
});

test('every specification text the core tests parse derives identically', () => {
  /** @type {string[]} */
  const cases = JSON.parse(zlib.gunzipSync(fs.readFileSync(path.join(ROOT, 'tests/fixtures/parse-corpus/cases.json.gz'))).toString('utf8'));
  let invalid = 0;
  cases.forEach((text, i) => { if (same(text, `case ${i}`)) invalid++; });
  assert.equal(cases.length, 206);
  assert.ok(invalid >= 80, `only ${invalid} cases have diagnostics`);
});

const BASE = (extra) => `{ "exegra": "0.1", "system": { "id": "s", "name": "S" }, ${extra} }`;

test('edge cases derive identically', () => {
  const cases = [
    '[]', '"x"', '{}', '{ "exegra": "0.2" }', '{ "exegra": { "v": 1 } }', '{ "exegra": 0.1 }',
    BASE('"components": [ { "id": "a", "name": "A", "category": "logical", "name": "B" } ]'),
    `{ "exegra": "0.1", "exegra": "0.1", "system": { "id": "s", "name": "S" }, "vocabulary": { "categories": { "x": 1 } } }`,
    BASE('"components": [ { "id": "a", "name": "A", "category": "logical", "tags": ["b", "a"], "10": 1, "9": 2, "z": 3, "ä": 4, "😀": 5, "": 6 } ]'),
    BASE('"components": [ { "id": "a", "name": "A", "category": "logical", "implementation": { "status": "manual", "notes": "-0 1e400", "x": -0, "y": 1e400, "z": 1.5e-7, "w": 123456789012345678901234 } } ]'),
    BASE('"components": [ { "id": "Bad--id", "name": "A" }, { "id": "a-", "name": "A" }, { "id": "a", "name": 1 }, { "id": "a", "name": "A" }, { "name": "no id" }, 7 ]'),
    BASE('"relationships": [ { "id": "r", "kind": "calls", "from": "s", "to": "nowhere" } ], "claims": [ { "id": "c", "kind": "structural", "statement": "x", "evaluate": { "method": "no-relationship", "from": ["s", "q"], "to": { "ids": "s", "within": "z" } } } ]'),
    BASE('"vocabulary": { "categories": { "k": { "label": 5, "shape": "nope", "extra": true }, "j": [1, null, "x"] }, "relationshipKinds": { "r": { "label": "R", "line": "dashed", "color": "blue", "dependency": "yes" } }, "entityKinds": { "goal": { "label": "Goal", "section": "goals", "properties": { "parent": { "type": "ref", "ref": "goal" }, "toString": { "type": "list", "items": { "type": "list" } }, "id": { "type": "string" } } }, "Bad": {}, "component": { "label": "x", "section": "y" } }, "properties": [ { "entity": "component", "name": "constructor", "type": "string" }, { "entity": "nope", "name": "x", "type": "string" }, { "entity": "component", "name": "risk", "type": "enum", "values": [] }, 3 ], "verificationMethods": { "reachable": { "label": "x" }, "audit": { "label": "Audit", "description": 1, "z": 0 } }, "extra": 1 }, "goals": [ { "id": "g", "parent": "s" } ]'),
    BASE('"vocabulary": [], "unknownSection": 1, "components": {}'),
    BASE('"vocabulary": { "categories": { "a": { "label": "A", "shape": "box", "color": "slate" }, "a": { "label": "B" } } }'),
  ];
  for (const [i, text] of cases.entries()) same(text, `edge ${i}`);
});
