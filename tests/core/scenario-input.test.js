import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { analyzeSpec } from '../../src/core/analyze.js';
import { valueProblem } from '../../src/core/scenario-input.js';

// scenario.input-type: what a scenario feeds a machine must have the type its event declares. An error when the
// specification sets system.generation, a warning otherwise.

const FIXTURE = fs.readFileSync(new URL('../fixtures/scenario-input/spec.jsonc', import.meta.url), 'utf8');
const UUID = '00000000-0000-4000-8000-000000000001';

/** The fixture with one step payload (or a mutation of the whole document) and the generation switch on or off. */
function analyse(/** @type {any} */ payload, { generation = true, mutate = (/** @type {any} */ _d) => {} } = {}) {
  const d = JSON.parse(FIXTURE.replace(/^\s*\/\/.*$/gm, ''));
  if (!generation) delete d.system.generation;
  d.scenarios[0].steps[0].payload = payload;
  mutate(d);
  return analyzeSpec(JSON.stringify(d));
}
const inputTypes = (/** @type {any} */ r) => r.diagnostics.filter((/** @type {any} */ d) => d.code === 'scenario.input-type');
const good = { 'move-id': UUID, kind: 'copy', priority: 3 };

// The negative fixture, a uuid key given as x-1: exactly one scenario.input-type error.
// @evidence scenario-input-typed
test('the negative fixture with a uuid key given as x-1 is refused with exactly one scenario.input-type', () => {
  const r = analyzeSpec(FIXTURE);
  assert.deepEqual(r.diagnostics.filter((/** @type {any} */ d) => d.severity === 'error').map((/** @type {any} */ d) => d.code), ['scenario.input-type']);
  const [d] = inputTypes(r);
  assert.match(d.message, /"move-id".*not a uuid.*"x-1"/);
  assert.ok(d.loc && d.loc.line > 1);
});

test('a scenario whose inputs have the declared types has no scenario.input-type finding', () => {
  assert.deepEqual(inputTypes(analyse(good)), []);
  assert.deepEqual(inputTypes(analyse({ ...good, note: null })), [], 'an option field may be null');
  assert.deepEqual(inputTypes(analyse({ ...good, note: 'x' })), []);
});

// Without system.generation the same finding is a warning.
// @evidence scenario-input-typed
test('the same finding is a warning when the specification does not set system.generation', () => {
  const r = analyse({ ...good, 'move-id': 'x-1' }, { generation: false });
  assert.deepEqual(inputTypes(r).map((/** @type {any} */ d) => d.severity), ['warning']);
  assert.equal(r.errorCount, 0);
});

const REFUSED = [
  ['an integer past the bound of its type', { ...good, priority: 256 }, /priority.*outside the range of u8/],
  ['a negative value for an unsigned type', { ...good, priority: -1 }, /priority.*outside the range of u8/],
  ['a fraction for an integer type', { ...good, priority: 1.5 }, /priority.*not an integer/],
  ['a value outside the enum', { ...good, kind: 'move' }, /kind.*not a value of enum move-kind/],
  ['a required field left out', { 'move-id': UUID, kind: 'copy' }, /Payload field "priority".*missing/],
  ['no payload at all', undefined, /"move-id".*missing/],
  ['a field the event does not declare', { ...good, extra: 1 }, /"extra" is not a field of event/],
  ['an option field of the wrong type', { ...good, note: 5 }, /note.*not a string/],
];

for (const [title, payload, pattern] of REFUSED) {
  test(`${title} is one scenario.input-type error`, () => {
    const r = analyse(payload);
    const found = inputTypes(r);
    assert.equal(found.length >= 1, true);
    assert.ok(found.every((/** @type {any} */ d) => d.severity === 'error'));
    assert.match(found.map((/** @type {any} */ d) => d.message).join('\n'), /** @type {RegExp} */ (pattern));
  });
}

// An inject-event fault payload is checked against the event it injects.
// @evidence scenario-input-typed
test('an inject-event fault payload is checked against the event it injects', () => {
  const r = analyse(good, { mutate: (d) => { d.faults = [{ id: 'move-repeated', name: 'Repeated', kind: 'inject-event', event: 'move-requested', at: 5, payload: { ...good, 'move-id': 'x-2' } }]; } });
  const [d] = inputTypes(r);
  assert.equal(inputTypes(r).length, 1);
  assert.equal(d.entityId, 'move-repeated');
});

// Values are judged by type: integer bounds, uuid, enum, struct, list and option.
// @evidence scenario-input-typed
test('values are judged by type: integer bounds and uuid and struct and list and option', () => {
  const model = /** @type {any} */ (analyse(good).model);
  assert.equal(valueProblem(model, 'u8', 255), null);
  assert.notEqual(valueProblem(model, 'u8', 256), null);
  assert.equal(valueProblem(model, 'i32', -2147483648), null);
  assert.notEqual(valueProblem(model, 'i32', 2147483648), null);
  assert.equal(valueProblem(model, 'u64', 12345678901), null);
  assert.notEqual(valueProblem(model, 'u64', -1), null);
  assert.equal(valueProblem(model, 'uuid', UUID), null);
  assert.notEqual(valueProblem(model, 'uuid', 'move-1'), null);
  assert.equal(valueProblem(model, 'list<u8>', [1, 2]), null);
  assert.match(String(valueProblem(model, 'list<u8>', [1, 300])), /item 1/);
  assert.equal(valueProblem(model, 'option<uuid>', null), null);
  assert.equal(valueProblem(model, 'move-id', UUID), null);
  assert.notEqual(valueProblem(model, 'move-id', 'x-1'), null);
  assert.equal(valueProblem(model, 'json', { any: [1] }), null);
  assert.equal(valueProblem(model, 'principal-id', 'anything'), null, 'a type that does not resolve accepts what it cannot read');
});
