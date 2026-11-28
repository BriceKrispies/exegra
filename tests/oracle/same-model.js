// Shared by tests/core/model-kernel.test.js and tests/proofs/model-kernel.test.js: the verified kernel's
// derivation compared with the JavaScript reference (tests/oracle/parse-reference.js).
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import * as reference from './parse-reference.js';
import { parseSpec } from '../../src/core/parse.js';
import { semanticHash, normalize } from '../../src/core/hash.js';

/** @param {string} dir @returns {string[]} */
export function jsoncFiles(dir) {
  return fs.readdirSync(dir, { withFileTypes: true }).flatMap((e) => {
    const p = path.join(dir, e.name);
    return e.isDirectory() ? jsoncFiles(p) : e.name.endsWith('.jsonc') ? [p] : [];
  });
}

/** Everything a model holds, as plain data (entities in declaration order, byKind as ids). @param {any} m */
export function plainModel(m) {
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
export function same(text, name) {
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
