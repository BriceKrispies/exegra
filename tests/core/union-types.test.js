import { test } from 'node:test';
import assert from 'node:assert/strict';
import { analyzeSpec } from '../../src/core/analyze.js';
import { readinessGaps } from '../../src/core/readiness.js';
import { exprClass, typeClass, typeResolves, parseTypeName } from '../../src/core/codegen-model.js';
import { typeSensitivity } from '../../src/core/telemetry.js';
import { variantWireName } from '../../src/core/type-shapes.js';
import { parseExpr } from '../../src/core/expr.js';
import { spec, FIXTURES } from '../fixtures/union-types/fixtures.js';

// Union and map types, wire encoding, id and scalar constraints, map keys and recursion (WG-4925).

const errors = (/** @type {any} */ r) => r.diagnostics.filter((/** @type {any} */ d) => d.severity === 'error');
const codes = (/** @type {any} */ ds) => ds.map((/** @type {any} */ d) => d.code);

// A variant field of an undeclared type: exactly one type.union-field error.
// @evidence union-map-types-rules # a variant field whose type does not resolve is reported once as type.union-field
// A tagField on an external tag: exactly one type.encoding error; the other encoding fixtures (contentField, missing tagField or contentField, newtype under an internal tag) each give one.
// @evidence union-map-types-rules # a tagField on an external tag is reported once as type.encoding
// A map keyed by f64: exactly one type.map-key error; further fixtures key by a union, a list, json and an id over a uuid.
// @evidence union-map-types-rules # a map keyed by f64 is reported once as type.map-key
// A struct holding itself, and two structs holding each other: one type.recursion each; a cycle through list, option, map and union variant is allowed.
// @evidence union-map-types-rules # a struct holding itself is reported once as type.recursion
// A bad pattern: exactly one type.constraints error; further fixtures put constraints on an enum, a pattern or length on a number, and a minLength above the maxLength.
// @evidence union-map-types-rules # a pattern that is not a regular expression is reported once as type.constraints
// A specification using the serde forms of the kernel types (external, internal and adjacent tags, newtype and unit variants, maps, constraints) has no error and no readiness gap.
// @evidence union-map-types-rules # a specification using unions and maps and constraints in the kernel forms validates
// A variant field of type set<column>, column undeclared: exactly one type.union-field error.
// @evidence set-tuple-nested-types-rules # a set of an unresolved type in a variant field is reported once as type.union-field
// A map keyed by set<string>: exactly one type.map-key error; further fixtures put an f64 key inside a set and inside a map of maps.
// @evidence set-tuple-nested-types-rules # a map keyed by a set is reported once as type.map-key
// A tuple variant with one field: exactly one type.union-variants error; further fixtures mark a tuple variant newtype and make a tuple field optional.
// @evidence set-tuple-nested-types-rules # a tuple variant with one field is reported once as type.union-variants
// A tuple variant in an internally tagged union: exactly one type.encoding error.
// @evidence set-tuple-nested-types-rules # an internal tag over a tuple variant is reported once as type.encoding
// A map of maps whose inner value is undeclared: exactly one type.union-field error.
// @evidence set-tuple-nested-types-rules # a map of maps whose inner value does not resolve is reported once as type.union-field
// A struct field of type shared<tag>, tag undeclared: exactly one type.field-unresolved error.
// @evidence set-tuple-nested-types-rules # a shared of an unresolved type is reported once as type.field-unresolved
// A struct that holds itself through a shared<T> field: exactly one type.recursion error.
// @evidence set-tuple-nested-types-rules # a struct that holds itself through a shared field is reported once as type.recursion
test('a specification using unions and maps and constraints in the kernel forms validates and has no readiness gap', () => {
  for (const generation of [false, true]) {
    const r = analyzeSpec(spec(undefined, { generation }));
    assert.deepEqual(errors(r).map((/** @type {any} */ d) => `${d.code} ${d.message}`), []);
    assert.deepEqual(readinessGaps(/** @type {any} */ (r.model)), []);
  }
});

const generationChecked = new Set();
for (const [title, code, mutate] of FIXTURES) {
  // The generation switch is checked once per family of reported codes (the part before the dot); the other cases run without it.
  const modes = generationChecked.has(code.split(".")[0]) ? [false] : [false, true];
  generationChecked.add(code.split(".")[0]);
  for (const generation of modes) {
    test(`${title} is reported once as ${code}${generation ? ' (generation set)' : ''}`, () => {
      const r = analyzeSpec(spec(mutate, { generation }));
      assert.deepEqual(codes(errors(r)), [code], r.diagnostics.map((/** @type {any} */ d) => d.message).join('\n'));
      assert.ok(errors(r)[0].loc && errors(r)[0].loc.line > 1);
    });
  }
}

test('every new code has a negative fixture', () => {
  const want = ['type.union-variants', 'type.union-field', 'type.encoding', 'type.map-key', 'type.recursion', 'type.constraints'];
  const have = new Set(FIXTURES.map(([, code]) => code));
  assert.deepEqual(want.filter((c) => !have.has(c)), []);
});

test('a cycle through a list or option or map or union variant is allowed and a cycle through struct fields alone is not', () => {
  const ok = analyzeSpec(spec());
  assert.deepEqual(codes(errors(ok)), []);
  const bad = analyzeSpec(spec((d) => { d.types.find((/** @type {any} */ t) => t.id === 'tree').fields.push({ name: 'self', type: 'tree' }); }));
  assert.deepEqual(codes(errors(bad)), ['type.recursion']);
  assert.match(errors(bad)[0].message, /tree/);
});

// map<K, V> resolves when K and V do; readiness reports an unresolved map in a record field and an event payload only when system.generation is set.
// @evidence union-map-types-rules # map types resolve when key and value resolve
test('map types resolve when key and value resolve and readiness reports the ones that do not', () => {
  const m = /** @type {any} */ (analyzeSpec(spec()).model);
  assert.ok(typeResolves(m, 'map<string, u32>') && typeResolves(m, 'map<field-id, list<value>>') && typeResolves(m, 'option<map<u8, intent>>'));
  assert.ok(!typeResolves(m, 'map<string>') && !typeResolves(m, 'map<string, nope>') && !typeResolves(m, 'map<a, b, c>') && !typeResolves(m, 'map<nope, string>'));
  assert.deepEqual(parseTypeName('map<string, list<map<u8, bool>>>'), { k: 'map', key: 'string', value: 'list<map<u8, bool>>' });
  const bad = (/** @type {any} */ d) => { d.records[0].fields[1].type = 'map<field-id, cell>'; };
  assert.deepEqual(codes(errors(analyzeSpec(spec(bad, { generation: false })))), []);
  assert.deepEqual(codes(errors(analyzeSpec(spec(bad, { generation: true })))), ['ready.field-type-undeclared']);
  const badEvent = (/** @type {any} */ d) => { d.events[0].payload[1].type = 'map<string>'; };
  assert.deepEqual(codes(errors(analyzeSpec(spec(badEvent, { generation: true })))), ['ready.event-payload-type-undeclared']);
});

// A union without variants: exactly one type.union-variants error, with and without system.generation.
// @evidence union-map-types-rules # a union without variants is reported once as type.union-variants
// A union and a map have the class json in guard expressions: == and != only.
// @evidence union-map-types-rules # a union or map value has the opaque class of json
test('a union or map value has the opaque class of json in guard expressions', () => {
  const m = /** @type {any} */ (analyzeSpec(spec()).model);
  assert.equal(typeClass(m, 'value'), 'json');
  assert.equal(typeClass(m, 'map<string, u32>'), 'json');
  assert.equal(typeClass(m, 'option<intent>'), 'json');
  assert.equal(typeClass(m, 'list<value>'), 'list');
  const cls = (/** @type {string} */ src, /** @type {string} */ type) => {
    const p = parseExpr(src);
    assert.ok(p.ok, src);
    return exprClass(/** @type {any} */ (p).ast, () => typeClass(m, type));
  };
  assert.equal(cls('x == null', 'value').error, undefined);
  assert.equal(cls('x == y', 'map<string, u32>').error, undefined);
  assert.match(cls('x + 1', 'value').error ?? '', /json/);
  assert.match(cls('x < y', 'map<string, u32>').error ?? '', /json/);
  assert.match(cls('x == 1', 'value').error ?? '', /compares a json with a number/);
});

test('sensitivity is carried by union variant fields and map values', () => {
  const m = /** @type {any} */ (analyzeSpec(spec((d) => {
    d.types.find((/** @type {any} */ t) => t.id === 'intent').variants[0].fields[1].sensitive = 'token';
  })).model);
  assert.equal(typeSensitivity(m, 'intent'), 'token');
  assert.equal(typeSensitivity(m, 'map<string, intent>'), 'token');
  assert.equal(typeSensitivity(m, 'list<option<intent>>'), 'token');
  assert.equal(typeSensitivity(m, 'value'), undefined);
  assert.equal(typeSensitivity(m, 'map<string, value>'), undefined);
});

test('variant names are written on the wire in the encoding case, or as written', () => {
  assert.equal(variantWireName('CreateRecord', undefined), 'CreateRecord');
  assert.equal(variantWireName('CreateRecord', 'snake_case'), 'create_record');
  assert.equal(variantWireName('CreateRecord', 'kebab-case'), 'create-record');
  assert.equal(variantWireName('create_record', 'PascalCase'), 'CreateRecord');
  assert.equal(variantWireName('create-record', 'PascalCase'), 'CreateRecord');
  assert.equal(variantWireName('Null', 'snake_case'), 'null');
  assert.equal(variantWireName('HTTPError', 'snake_case'), 'http_error');
});
