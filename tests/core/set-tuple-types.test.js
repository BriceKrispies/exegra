import { test } from 'node:test';
import assert from 'node:assert/strict';
import { analyzeSpec } from '../../src/core/analyze.js';
import { readinessGaps } from '../../src/core/readiness.js';
import { typeClass, typeResolves, parseTypeName, unsharedText } from '../../src/core/codegen-model.js';
import { valueProblem } from '../../src/core/scenario-input.js';
import { typeSensitivity } from '../../src/core/telemetry.js';
import { splitTop } from '../../src/core/type-expr.js';
import { spec, FIXTURES } from '../fixtures/union-types/fixtures.js';

// Sets, tuple variants and nested generic type texts (WG-4956). The negative fixtures are in FIXTURES and run in
// union-types.test.js; these tests cover what the fixtures do not: parsing, classes and scenario values.

const errors = (/** @type {any} */ r) => r.diagnostics.filter((/** @type {any} */ d) => d.severity === 'error');
const codes = (/** @type {any} */ ds) => ds.map((/** @type {any} */ d) => d.code);
const model = () => /** @type {any} */ (analyzeSpec(spec()).model);

test('a specification with sets and tuple variants and maps of maps validates and has no readiness gap', () => {
  for (const generation of [false, true]) {
    const r = analyzeSpec(spec(undefined, { generation }));
    assert.deepEqual(errors(r).map((/** @type {any} */ d) => `${d.code} ${d.message}`), []);
    assert.deepEqual(readinessGaps(/** @type {any} */ (r.model)), []);
  }
});

test('set types resolve when their item resolves and have the class list', () => {
  const m = model();
  assert.deepEqual(parseTypeName('set<field-id>'), { k: 'set', of: 'field-id' });
  assert.ok(typeResolves(m, 'set<field-id>') && typeResolves(m, 'option<set<string>>') && typeResolves(m, 'map<string, set<u8>>'));
  assert.ok(!typeResolves(m, 'set<tag>') && !typeResolves(m, 'set<>'));
  assert.equal(typeClass(m, 'set<string>'), 'list');
  assert.equal(typeClass(m, 'option<set<string>>'), 'list');
});

test('a set of an unresolved type is refused', () => {
  const fixture = FIXTURES.find(([title]) => title === 'a set of an unresolved type');
  assert.ok(fixture);
  const r = analyzeSpec(spec(fixture[2]));
  assert.deepEqual(codes(errors(r)), ['type.field-unresolved']);
  assert.match(errors(r)[0].message, /set<tag>/);
});

test('a scenario value of a set type is an array of distinct items of the item type', () => {
  const m = model();
  assert.equal(valueProblem(m, 'set<field-id>', ['a', 'b']), null);
  assert.equal(valueProblem(m, 'set<field-id>', []), null);
  assert.match(valueProblem(m, 'set<field-id>', ['a', 'a']) ?? '', /repeats item 1/);
  assert.match(valueProblem(m, 'set<u8>', [1, 300]) ?? '', /item 1/);
  assert.match(valueProblem(m, 'set<string>', 'a') ?? '', /not a list/);
});

test('sensitivity is carried through a set', () => {
  const m = /** @type {any} */ (analyzeSpec(spec((d) => {
    d.types.find((/** @type {any} */ t) => t.id === 'field-id').sensitive = 'personal';
  })).model);
  assert.equal(typeSensitivity(m, 'set<field-id>'), 'personal');
  assert.equal(typeSensitivity(m, 'map<string, set<field-id>>'), 'personal');
});

test('nested generic type texts split at the top-level comma', () => {
  assert.deepEqual(splitTop('K, map<K2, V>', ','), ['K', 'map<K2, V>']);
  assert.deepEqual(splitTop('list<map<K, V>>, string', ','), ['list<map<K, V>>', 'string']);
  assert.deepEqual(splitTop('(a) => b | string', '|'), ['(a) => b', 'string']);
  assert.deepEqual(parseTypeName('map<object-type-id, map<record-id, record>>'), { k: 'map', key: 'object-type-id', value: 'map<record-id, record>' });
  assert.deepEqual(parseTypeName('list<map<string, u8>>'), { k: 'list', of: 'map<string, u8>' });
  assert.deepEqual(parseTypeName('map<string, list<map<u8, bool>>>'), { k: 'map', key: 'string', value: 'list<map<u8, bool>>' });
  const m = model();
  assert.ok(typeResolves(m, 'map<field-id, map<version, cond>>') && typeResolves(m, 'list<map<string, set<u8>>>'));
  assert.ok(!typeResolves(m, 'map<field-id, map<version, cell>>'));
});

test('tuple variants are accepted under the external and adjacent tags', () => {
  const r = analyzeSpec(spec());
  assert.deepEqual(codes(errors(r)), []);
  const cond = /** @type {any} */ (r.model).entities.get('cond');
  assert.deepEqual(cond.data.variants.filter((/** @type {any} */ v) => v.tuple === true).map((/** @type {any} */ v) => v.name), ['Var', 'Cmp']);
  assert.equal(typeClass(/** @type {any} */ (r.model), 'cond'), 'json');
});

// Sharing hints (WG-4960): shared<T> is read as T everywhere, and a refusal names the type it wraps.
test('a shared hint parses and resolves, and classes and holds values as its type does', () => {
  const m = model();
  assert.deepEqual(parseTypeName('shared<field-id>'), { k: 'shared', of: 'field-id' });
  assert.deepEqual(parseTypeName('shared<shared<version>>'), { k: 'shared', of: 'shared<version>' });
  assert.equal(unsharedText(' shared<shared<version>> '), 'version');
  assert.ok(typeResolves(m, 'shared<field-id>') && typeResolves(m, 'shared<set<field-id>>') && typeResolves(m, 'list<shared<string>>'));
  assert.ok(!typeResolves(m, 'shared<tag>'));
  assert.equal(typeClass(m, 'shared<string>'), 'string');
  assert.equal(typeClass(m, 'shared<set<string>>'), 'list');
  assert.equal(valueProblem(m, 'shared<set<field-id>>', ['a', 'b']), null);
  assert.match(valueProblem(m, 'shared<set<field-id>>', ['a', 'a']) ?? '', /repeats item 1/);
  assert.match(valueProblem(m, 'shared<u8>', 300) ?? '', /outside the range of u8/);
});

test('a shared field is checked as its type in a specification, as a map key and as a struct', () => {
  const r = analyzeSpec(spec((d) => {
    const counts = d.types.find((/** @type {any} */ t) => t.id === 'counts');
    counts.fields.push({ name: 'by-name', type: 'map<shared<field-id>, u32>' }, { name: 'shared-tags', type: 'shared<set<field-id>>' });
  }));
  assert.deepEqual(codes(errors(r)), []);
  assert.deepEqual(readinessGaps(/** @type {any} */ (r.model)), []);
});

test('sensitivity is carried through a shared hint', () => {
  const m = /** @type {any} */ (analyzeSpec(spec((d) => {
    d.types.find((/** @type {any} */ t) => t.id === 'field-id').sensitive = 'personal';
  })).model);
  assert.equal(typeSensitivity(m, 'shared<field-id>'), 'personal');
  assert.equal(typeSensitivity(m, 'shared<set<field-id>>'), 'personal');
});
