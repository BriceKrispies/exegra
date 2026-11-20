import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { analyzeSpec } from '../../src/core/analyze.js';
import { readinessGaps } from '../../src/core/readiness.js';
import { typeStructure } from '../../src/core/codegen-model.js';
import { analyzeFunctions } from '../../src/core/function.js';
import { compareOrdered, isOrderable, UnionValue } from '../../src/core/function-value.js';
import { suppliedInputs } from '../../src/core/supplied-inputs.js';
import { toWire, fromWire, fieldWireName } from '../../src/core/wire.js';
import { spec, FIXTURES } from '../fixtures/format-gaps/fixtures.js';

// The format gaps of the read and view functions (WG-4968, from WG-4939): an untagged union wire encoding, inputs a
// request supplies from its route or session, the JSON null in function bodies, reference lookup in eval, and
// lexicographic order of lists in sortBy. The passing fixture also carries every example of the new functions, which
// validation evaluates; and contract realisation target and the derivation header are in derivations.test.js.

const errors = (/** @type {any} */ r) => r.diagnostics.filter((/** @type {any} */ d) => d.severity === 'error');
const codes = (/** @type {any} */ ds) => ds.map((/** @type {any} */ d) => d.code);
const model = () => /** @type {any} */ (analyzeSpec(spec()).model);

test('the fixture validates with every example holding and nothing missing for generation', () => {
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

test('every new code has a negative fixture', () => {
  const have = new Set(FIXTURES.map(([, code]) => code));
  for (const code of ['type.encoding', 'contract.supplied-by', 'form.supplied-input', 'action.supplied-input']) assert.ok(have.has(code), code);
});

test('an untagged union is written as the raw JSON of its variant and read back in declaration order', () => {
  const t = /** @type {any} */ (typeStructure(model(), 'plain-json'));
  const raw = { a: [1, 'x', null, true], b: {}, c: 'text' };
  const value = fromWire(t, raw);
  assert.equal(value.variant, 'Members');
  assert.deepEqual(toWire(t, value), raw);
  for (const j of [null, true, 1.5, 'x', [], [null, [false]], {}]) assert.deepEqual(toWire(t, fromWire(t, j)), j);
  assert.equal(fromWire(t, null).variant, 'Null');
  assert.equal(fromWire(t, [1]).variant, 'Items');
  assert.equal(fromWire(t, 'x').variant, 'Text');
});

test('the other tags round-trip too external internal adjacent and tuple variants', () => {
  const m = model();
  const mutation = /** @type {any} */ (typeStructure(m, 'mutation'));
  const body = { op: 'update', object: 'note', id: 3, fields: { title: 'x' }, expected_version: 2 };
  const v = fromWire(mutation, body, { wireCase: 'snake_case' });
  assert.equal(v.variant, 'Update');
  assert.deepEqual(v.fields['expected-version'], 2);
  assert.deepEqual(toWire(mutation, v, { wireCase: 'snake_case' }), body);
  assert.deepEqual(toWire(mutation, fromWire(mutation, { op: 'delete', object: 'note', id: 3 })), { op: 'delete', object: 'note', id: 3 });
  assert.throws(() => fromWire(mutation, { op: 'delete', object: 'note', id: 3, extra: 1 }), /no member/);
  const shape = /** @type {any} */ (typeStructure(m, 'shape'));
  for (const j of ['Empty', { Radius: 4 }, { Corners: [2, 3] }, { Label: { text: 'a', bold: true } }, { Label: { text: 'a' } }]) assert.deepEqual(toWire(shape, fromWire(shape, j)), j);
  const adjacent = /** @type {any} */ (typeStructure(m, 'shape-adjacent'));
  for (const j of [{ t: 'empty-shape' }, { t: 'radius', c: 4 }, { t: 'corners', c: [2, 3] }, { t: 'label', c: { text: 'a' } }]) assert.deepEqual(toWire(adjacent, fromWire(adjacent, j)), j);
  assert.throws(() => fromWire(adjacent, { t: 'radius' }), /needs a "c" member/);
  assert.equal(fieldWireName('expected-version', 'camelCase'), 'expectedVersion');
  assert.equal(fieldWireName('expected-version', 'snake_case'), 'expected_version');
  assert.equal(fieldWireName('expected-version', undefined), 'expected-version');
});

test('inputs the route or session supplies are read from the contract binding and nothing else', () => {
  const c = model().entities.get('save-note');
  assert.deepEqual([...suppliedInputs(c)], [['tenant', 'route'], ['context', 'session']]);
  assert.deepEqual([...suppliedInputs(model().entities.get('view-home'))], []);
});

test('lists and unions are ordered as the kernel orders a Value by variant then item by item', () => {
  const m = model();
  const list = /** @type {any} */ ({ k: 'list', of: { k: 'prim', name: 'u64' } });
  assert.equal(compareOrdered(list, [1], [1, 2]), -1);
  assert.equal(compareOrdered(list, [], [0]), -1);
  assert.equal(compareOrdered(list, [2], [1, 9]), 1);
  assert.equal(compareOrdered(list, [1, 2], [1, 2]), 0);
  const value = /** @type {any} */ (typeStructure(m, 'value'));
  const u = (/** @type {string} */ variant, /** @type {any} */ fields = {}) => new UnionValue('value', variant, fields);
  assert.equal(compareOrdered(value, u('Bool', { value: true }), u('Int', { value: -5 })), -1);
  assert.equal(compareOrdered(value, u('List', { value: [u('Int', { value: 1 })] }), u('List', { value: [] })), 1);
  assert.equal(isOrderable(value), true);
  assert.equal(isOrderable(/** @type {any} */ ({ k: 'prim', name: 'json' })), false);
  assert.equal(isOrderable(/** @type {any} */ ({ k: 'map', key: { k: 'prim', name: 'string' }, value: { k: 'prim', name: 'u8' } })), false);
});

test('the new functions are well typed and their examples are the only evidence they need', () => {
  const { sigs } = analyzeFunctions(model());
  for (const id of ['blank-view', 'empty-block', 'text-or-null', 'is-null-text', 'author-name', 'author-name-unfollowed', 'sort-values', 'sort-lists']) assert.ok(sigs.get(id)?.ok, id);
});

test('the format documentation states every new code and construct', () => {
  const doc = fs.readFileSync(new URL('../../docs/model-and-format.md', import.meta.url), 'utf8');
  for (const needle of ['`contract.supplied-by`', '`form.supplied-input`', '`action.supplied-input`', '"untagged"', '"target"', '"suppliedBy"', '"header": true']) assert.ok(doc.includes(needle), `${needle} is documented`);
});
