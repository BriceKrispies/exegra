import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { analyzeSpec } from '../../src/core/analyze.js';
import { readinessGaps } from '../../src/core/readiness.js';
import { wordsOf, routeShape } from '../../src/core/derivation.js';
import { spec, FIXTURES, READINESS_FIXTURES } from '../fixtures/derivations/fixtures.js';

// Derived and facade contracts (WG-4935, NC-4 and NC-5 of WG-4895). The passing fixture is the specification of
// specc's golden fixture for derived contracts (crates/spec-compiler/tests/fixtures/derived/spec.jsonc in Strata):
// a pure, a read and two command derivations over a load and a commit contract, and a facade; and a read with a need
// loop (WG-4939).

const errors = (/** @type {any} */ r) => r.diagnostics.filter((/** @type {any} */ d) => d.severity === 'error');
const codes = (/** @type {any} */ ds) => ds.map((/** @type {any} */ d) => d.code);
const CODES = ['derivation.kind', 'derivation.signature', 'derivation.load', 'derivation.commit', 'derivation.bounds', 'contract.facade-route'];

test('pure and read and command derivations over a load and a commit contract and a facade validate with nothing missing for generation', () => {
  for (const generation of [false, true]) {
    const r = analyzeSpec(spec(undefined, { generation }));
    assert.deepEqual(errors(r).map((/** @type {any} */ d) => `${d.code} ${d.message}`), []);
    assert.deepEqual(readinessGaps(/** @type {any} */ (r.model)), []);
  }
});

for (const [title, code, mutate] of FIXTURES) {
  for (const generation of [false, true]) {
    test(`${title} is reported once as ${code}${generation ? ' (generation set)' : ''}`, () => {
      const r = analyzeSpec(spec(mutate, { generation }));
      assert.deepEqual(codes(errors(r)), [code], r.diagnostics.map((/** @type {any} */ d) => `${d.code} ${d.message}`).join('\n'));
      assert.ok(errors(r)[0].loc && errors(r)[0].loc.line > 1);
    });
  }
}

for (const [title, code, mutate] of READINESS_FIXTURES) {
  test(`${title} is reported once as ${code} only when generation is set`, () => {
    const off = analyzeSpec(spec(mutate, { generation: false }));
    assert.deepEqual(codes(errors(off)), [], off.diagnostics.map((/** @type {any} */ d) => `${d.code} ${d.message}`).join('\n'));
    assert.deepEqual(codes(readinessGaps(/** @type {any} */ (off.model))), [code]);
    const on = analyzeSpec(spec(mutate, { generation: true }));
    assert.deepEqual(codes(errors(on)), [code], on.diagnostics.map((/** @type {any} */ d) => `${d.code} ${d.message}`).join('\n'));
  });
}

test('every derivation code has a negative fixture', () => {
  const have = new Set(FIXTURES.map(([, code]) => code));
  assert.deepEqual(CODES.filter((c) => !have.has(c)), []);
  assert.ok(READINESS_FIXTURES.some(([, code]) => code === 'ready.derived-function-missing'));
});

test('error variants and contract errors are matched by their words and a route by its method and path and shape', () => {
  assert.equal(wordsOf('VersionConflict'), 'version-conflict');
  assert.equal(wordsOf('version-conflict'), 'version-conflict');
  assert.equal(wordsOf('HTTPError'), 'http-error');
  assert.deepEqual(routeShape('POST /api/records records update post'), { method: 'POST', path: '/api/records', shape: 'records' });
  assert.deepEqual(routeShape('GET /api/view view'), { method: 'GET', path: '/api/view', shape: 'view' });
  assert.equal(routeShape('POST /api/login'), undefined);
  assert.equal(routeShape('FETCH /api/view view'), undefined);
});

test('the format documentation states every derivation code and kind', () => {
  const doc = fs.readFileSync(new URL('../../docs/model-and-format.md', import.meta.url), 'utf8');
  for (const code of [...CODES, 'ready.derived-function-missing']) assert.ok(doc.includes(`\`${code}\``), `code ${code} is documented`);
  for (const kind of ['pure', 'read', 'command']) assert.ok(doc.includes(`"kind": "${kind}"`), `kind ${kind} is documented`);
});
