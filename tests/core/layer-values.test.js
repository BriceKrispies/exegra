// The generic check of a typed section's value against a platform type (src/core/layer-values.js,
// WG-5046): structs, unions, enums, ids, maps and the member that names an item. The platform here is
// a small set of types; tests/core/layers.test.js runs the sections over the real fixtures.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { checkTypedItem, namespaceOf, REFERENCE_TYPES } from '../../src/core/layer-values.js';

/** @type {Record<string, any>} */
const TYPES = {
  step: { kind: 'union', encoding: { tag: 'external', variantCase: 'PascalCase' }, variants: [{ name: 'wait-for', fields: [{ name: 'duration', type: 'duration' }] }, { name: 'end' }, { name: 'int', newtype: true, fields: [{ name: 'value', type: 'i64' }] }] },
  'step-def': { kind: 'struct', fields: [{ name: 'id', type: 'step-id' }, { name: 'action', type: 'step' }, { name: 'next', type: 'option<step-id>', optional: true }, { name: 'tags', type: 'map<string, expression>', optional: true }, { name: 'object', type: 'object-type-id', optional: true }] },
  'step-id': { kind: 'id', repr: 'string', constraints: { pattern: '^[a-z][a-z0-9_]*$', maxLength: 8 } },
  'object-type-id': { kind: 'id', repr: 'string', constraints: { pattern: '^[a-z][a-z0-9_]*$', maxLength: 64 } },
  expression: { kind: 'scalar', repr: 'string' },
  'unit-decl': { kind: 'struct', fields: [{ name: 'unit', type: 'unit-name' }, { name: 'description', type: 'string' }] },
  'unit-name': { kind: 'id', repr: 'string' },
  'object-def': { kind: 'struct', fields: [{ name: 'id', type: 'object-type-id' }] },
  level: { kind: 'enum', values: ['tenant', 'team'] },
  'level-def': { kind: 'struct', fields: [{ name: 'level', type: 'level' }] },
};
const types = (/** @type {string} */ name) => TYPES[name];
const STEPS = { section: 'steps', type: 'step-def', idField: 'id', purpose: 'steps' };
const UNITS = { section: 'units', type: 'unit-decl', idField: 'unit', purpose: 'units' };
const run = (/** @type {any} */ section, /** @type {string} */ id, /** @type {any} */ item) => checkTypedItem(types, 'p.jsonc', section, id, item);

test('a conforming value is accepted', () => {
  assert.deepEqual(run(STEPS, 'one', { id: 'one', action: { WaitFor: { duration: 5 } }, next: 'two' }).problems, []);
  assert.deepEqual(run(STEPS, 'one', { id: 'one', action: 'End', tags: { a: 'x' } }).problems, []);
  assert.deepEqual(run(STEPS, 'one', { id: 'one', action: { Int: 5 } }).problems, [], 'a newtype variant carries its value directly');
});

test('a missing field and a stray field and a wrong scalar and an id outside its pattern are refused', () => {
  const messages = (/** @type {any} */ item) => run(STEPS, 'one', item).problems.map((p) => `${p.code} ${p.message}`);
  assert.match(messages({ id: 'one' }).join('\n'), /layer\.value-invalid .*lacks the required field "action"/);
  assert.match(messages({ id: 'one', action: 'End', extra: 1 }).join('\n'), /"extra" is not a field of its type/);
  assert.match(messages({ id: 'one', action: { WaitFor: { duration: 'soon' } } }).join('\n'), /must be a whole number/);
  assert.match(messages({ id: 'Bad-Id', action: 'End' }).join('\n'), /does not match the pattern/);
  assert.match(messages({ id: 'one', action: 'End', next: 'far_too_long' }).join('\n'), /longer than 8 characters/);
  assert.match(messages({ id: 'one', action: { Int: 'five' } }).join('\n'), /must be a whole number/);
});

test('a variant the union lacks is outside the catalogue and a variant with fields needs them', () => {
  const out = run(STEPS, 'one', { id: 'one', action: { Run: { source: 'x' } } }).problems;
  assert.equal(out.length, 1);
  assert.equal(out[0].code, 'layer.outside-catalogue');
  assert.match(out[0].message, /"Run" at action.*variants WaitFor, End, Int/);
  assert.deepEqual(out[0].path, ['action']);
  assert.match(run(STEPS, 'one', { id: 'one', action: 'WaitFor' }).problems[0].message, /without its fields duration/);
  assert.match(run(STEPS, 'one', { id: 'one', action: { End: { x: 1 } } }).problems[0].message, /takes no fields/);
});

test('an enum takes its values only', () => {
  const level = { section: 'levels', type: 'level-def', idField: null, purpose: 'levels' };
  assert.deepEqual(run(level, 'p__a', { id: 'p__a', level: 'team' }).problems, [], 'the id of an item with no naming member has only a product name');
  assert.deepEqual(run(level, 'p__a', { level: 'team' }).problems, []);
  assert.match(run(level, 'p__a', { level: 'platform' }).problems[0].message, /must be one of tenant, team \(level\)/);
});

test('the member that names the item is the id, and a different value is refused', () => {
  assert.deepEqual(run(UNITS, 'p__points', { id: 'p__points', description: 'd' }).problems, []);
  assert.match(run(UNITS, 'p__points', { id: 'p__points', unit: 'other', description: 'd' }).problems[0].message, /must be the id "p__points"/);
});

test('names of the product are collected as references, but the member that declares the item is not one', () => {
  const found = run(STEPS, 'p__one', { id: 'p__one', action: 'End', object: 'p__thing' });
  assert.deepEqual(found.problems, []);
  assert.deepEqual(found.refs.map((r) => [r.name, r.path.join('.'), r.sections.join(',')]), [['p__thing', 'object', 'objects']]);
  assert.equal(Object.hasOwn(REFERENCE_TYPES, 'step-id'), false, 'the declared member is of an id type that is not a reference type here');
  const declared = run({ section: 'objects', type: 'object-def', idField: 'id', purpose: 'x' }, 'p__one', { id: 'p__one' });
  assert.deepEqual(declared.refs, [], 'an object type that declares itself does not refer to itself');
});

test('the namespace of a product is its id with underscores and two underscores', () => {
  assert.equal(namespaceOf('badge-milestones'), 'badge_milestones__');
  assert.equal(namespaceOf('badges'), 'badges__');
});
