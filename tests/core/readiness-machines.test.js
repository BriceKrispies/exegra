import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, existsSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { analyzeSpec } from '../../src/core/analyze.js';
import { initEngine } from '../../src/core/engine.js';
import { createWorkspace } from '../../tools/workspace.js';
import { engineInput } from '../../src/core/engine.js';
import { BUILTIN_TYPES, isBuiltinType } from '../../src/core/builtin-types.js';
import { machineReadiness, typeResolves } from '../../src/core/readiness-machines.js';

initEngine();

const FIXED = readFileSync(fileURLToPath(new URL('../fixtures/readiness-machines/spec.jsonc', import.meta.url)), 'utf8');

/** The fixed specification with one textual change, which must apply exactly once. */
function broken(from, to) {
  assert.equal(FIXED.split(from).length - 1, 1, `fixture text occurs once: ${from}`);
  return FIXED.replace(from, to);
}
const readyCodes = (text) => analyzeSpec(text).diagnostics.filter((d) => d.code.startsWith('ready.')).map((d) => d.code);

// The fixed fixture machine has no error and no readiness diagnostic.
// @evidence implementation-machine-readiness-rules
test('the fixed implementation-level machine has no readiness diagnostic and no error', () => {
  const a = analyzeSpec(FIXED);
  assert.deepEqual(a.diagnostics.filter((d) => d.severity === 'error'), []);
  assert.deepEqual(machineReadiness(a.model), []);
});

const RULES = [
  ['ready.repr-missing', 'a variable without repr', ', "repr": "u32" }', ' }'],
  ['ready.repr-unresolved', 'a variable whose repr is not a type', '"repr": "u32"', '"repr": "u33"'],
  ['ready.instances-storage', 'an instance key that is not a key field of the record', '"key": "id", "storedIn"', '"key": "other", "storedIn"'],
  ['ready.event-field-undeclared', 'a guard reading an undeclared event field', '"guard": "event.n > 0"', '"guard": "event.m > 0"'],
  ['ready.emit-receiver-missing', 'an emit without a receiver', '"emit": "ev-note", "to": "mailer", ', '"emit": "ev-note", '],
  ['ready.delivery-missing', 'an emitted event without delivery', '"delivery": "at-least-once", ', ''],
  ['ready.transaction-missing', 'no transaction', '"transaction": { "scope": "transition", "isolation": "serializable" },', ''],
  ['ready.fault-only', 'a faultOnly transition', '"transitions": [', '"transitions": [ { "id": "t-fault", "from": "closed", "to": "closed", "on": "ev-tick", "faultOnly": true },'],
  ['ready.elapsed-no-timer', 'an elapsed event no timer emits', '{ "timer": "t1", "after": 5, "emit": "ev-tick" },', ''],
  ['ready.order-ambiguous', 'a last transition with neither guard nor otherwise', '"on": "ev-start", "otherwise": true },\n        { "id": "t-waiting-start"', '"on": "ev-start" },\n        { "id": "t-waiting-start"'],
  ['ready.otherwise-misplaced', 'otherwise on a transition that is not last', '"guard": "event.n > 0",', '"guard": "event.n > 0", "otherwise": true,'],
  ['ready.outcome-missing', 'a state with no outcome for an event', '"ignores": ["ev-tick"]', '"ignores": []'],
  ['ready.storage-missing', 'a machine that names no record holding it', '"instances": { "key": "id", "storedIn": "session" }, "storage": { "record": "session", "key": "id" },', ''],
  ['ready.storage-key', 'a storage key that is not a key field of its record', '"instances": { "key": "id", "storedIn": "session" }, "storage": { "record": "session", "key": "id" },', '"storage": { "record": "session", "key": "other" },'],
  ['ready.storage-mismatch', 'storage and instances naming different records', '"storage": { "record": "session", "key": "id" }', '"storage": { "record": "archive", "key": "id" }'],
  ['ready.storage-field-unknown', 'storage.fields mapping a variable to a field the record lacks', '"fields": { "total": "sum" }', '"fields": { "total": "summ" }'],
  ['ready.storage-variable-unmapped', 'a variable with no field of its name and no mapping', '"fields": { "total": "sum" }, ', ''],
  ['ready.storage-field-type', 'a variable held in a field of another type', '{ "name": "sum", "type": "u16" }', '{ "name": "sum", "type": "string" }'],
  ['ready.storage-state-field', 'an enum state field whose values do not cover a state', '"stateValues": { "t-open": "open", "t-shut": "shut" }', '"stateValues": { "t-open": "open" }'],
  ['ready.storage-creates-unfilled', 'a creating machine that leaves a required field unfilled', '"state": "phase",', '"state": "phase", "creates": true,'],
  ['ready.payload-type-unresolved', 'a payload field of an unresolved type', '{ "name": "n", "type": "u32" } ] },\n    { "id": "ev-tick"', '{ "name": "n", "type": "u32" }, { "name": "x", "type": "int" } ] },\n    { "id": "ev-tick"'],
];

for (const [code, what, from, to] of RULES) {
  // Twenty-one tests, one per ready.* code: the fixture machines with one deliberate break give exactly that one error.
  // @evidence implementation-machine-readiness-rules # readiness rule ready
  test(`readiness rule ${code}: ${what} gives exactly that one error`, () => {
    const a = analyzeSpec(broken(from, to));
    const ready = a.diagnostics.filter((d) => d.code.startsWith('ready.'));
    assert.deepEqual(ready.map((d) => d.code), [code]);
    assert.equal(ready[0].severity, 'error');
    assert.ok(ready[0].entityId);
  });
}

// A machine that does not create records reports nothing for a required record field it does not hold; creating, it reports nothing once that field is optional.
// @evidence implementation-machine-readiness-rules
test('a non-creating machine leaves the required fields it does not hold to whoever creates the record', () => {
  // "label" of tally-rec is required and not held by the tally machine, which does not create records.
  assert.deepEqual(readyCodes(FIXED), []);
  assert.deepEqual(readyCodes(broken('"state": "phase",', '"state": "phase", "creates": false,')), []);
  assert.deepEqual(readyCodes(broken('"state": "phase",', '"state": "phase", "creates": true,').replace('{ "name": "label", "type": "string" }', '{ "name": "label", "type": "string", "optional": true }')), []);
});

// Without storage.fields a variable is held in the field of its name, the state in field "state"; an enum whose values are the state ids needs no stateValues.
// @evidence implementation-machine-readiness-rules # storage fields default to the field of the variable name
test('storage fields default to the field of the variable name and the state to field "state"', () => {
  // The session machine declares no mapping: count is held in "count", the state in "state".
  assert.deepEqual(readyCodes(broken('{ "name": "count", "type": "u32" }, ', '')), ['ready.storage-variable-unmapped']);
  assert.deepEqual(readyCodes(broken(', { "name": "state", "type": "string" }', '')), ['ready.storage-state-field']);
  // An enum state field whose values are the state ids needs no stateValues.
  assert.deepEqual(readyCodes(broken('"values": ["open", "shut"]', '"values": ["t-open", "t-shut"]').replace(', "stateValues": { "t-open": "open", "t-shut": "shut" }', '')), []);
});

// A variable fits an optional field of its repr and a declared id type over its repr; mapping a variable to the key field is refused.
// @evidence implementation-machine-readiness-rules # a variable fits a field of its repr
test('a variable fits a field of its repr, of a declared type over its repr, or an optional one', () => {
  assert.deepEqual(readyCodes(broken('{ "name": "sum", "type": "u16" }', '{ "name": "sum", "type": "u16", "optional": true }')), []);
  assert.deepEqual(readyCodes(broken('"fields": { "total": "sum" }', '"fields": { "total": "tid" }')), ['ready.storage-field-unknown']);
  assert.deepEqual(readyCodes(broken('"name": "total", "type": "number", "initial": 0, "repr": "u16"', '"name": "total", "type": "number", "initial": 0, "repr": "string"').replace('{ "name": "sum", "type": "u16" }', '{ "name": "sum", "type": "tally-id" }')), []);
});

test('type names resolve as built-ins, declared types, list<T> and option<T>', () => {
  const m = analyzeSpec(FIXED).model;
  assert.ok(BUILTIN_TYPES.every(isBuiltinType) && !isBuiltinType('int'));
  assert.ok(typeResolves(m, 'u32') && typeResolves(m, 'list<u8>') && typeResolves(m, 'option<list<string>>'));
  assert.ok(!typeResolves(m, 'int') && !typeResolves(m, 'list<int>') && !typeResolves(m, undefined));
});

// An unkeyed implementation machine with storage and no instances has no readiness error.
// @evidence implementation-machine-readiness-rules # storage alone
test('storage alone, without instances, says where an unkeyed implementation machine is held', () => {
  assert.deepEqual(readyCodes(broken('"instances": { "key": "id", "storedIn": "session" }, ', '')), []);
});

// A keyed implementation machine with instances.storedIn and no storage has no readiness error.
// @evidence implementation-machine-readiness-rules
test('instances.storedIn alone still says where a keyed implementation machine is held', () => {
  assert.deepEqual(readyCodes(broken(' "storage": { "record": "session", "key": "id" },', '')), []);
});

// A machine with one state and no variables needs no storage; with a second state it does.
// @evidence implementation-machine-readiness-rules
test('a stateless implementation machine with one state and no variables needs no storage and one with two states does', () => {
  const spec = (states) => JSON.stringify({
    exegra: '0.1',
    system: { id: 'sys', name: 'Sys' },
    components: [{ id: 'renderer', name: 'Renderer', category: 'computational' }],
    events: [{ id: 'ev-render', name: 'Render' }],
    behaviors: [{
      id: 'render-impl', name: 'Render', subject: 'renderer', level: 'implementation', initial: 's-ready',
      transaction: { scope: 'transition', isolation: 'serializable' },
      states: states.map((id) => ({ id, name: id })),
      transitions: [{ id: 't-render', from: 's-ready', to: 's-ready', on: 'ev-render', otherwise: true }],
    }],
  });
  const storageCodes = (text) => readyCodes(text).filter((c) => c.startsWith('ready.storage'));
  assert.deepEqual(storageCodes(spec(['s-ready'])), []);
  assert.deepEqual(storageCodes(spec(['s-ready', 's-done'])), ['ready.storage-missing']);
});

// The same machine at level model reports no readiness diagnostic.
// @evidence implementation-machine-readiness-rules
test('a model-level behavior is not held to the machine rules', () => {
  assert.deepEqual(readyCodes(broken('"level": "implementation",', '"level": "model",').replace(', "repr": "u32" }', ' }')), []);
});

// The engine input derived from the fixture machine contains none of the implementation-level properties and keeps its instance key.
// @evidence implementation-properties-declarative
test('the implementation-level properties do not reach the simulation input', () => {
  const input = JSON.stringify(engineInput(analyzeSpec(FIXED).model, 'run'));
  for (const key of ['storedIn', '"storage"', 'otherwise', 'ignores', 'transaction', 'level', 'repr', 'delivery', 'elapsed', 'mailer']) assert.ok(!input.includes(key), key);
  assert.ok(input.includes('"instances":{"key":"id"}'));
});

test('an emit effect "to" must name a component or a contract', () => {
  const codes = analyzeSpec(broken('"to": "mailer"', '"to": "ev-note"')).diagnostics.map((d) => d.code);
  assert.ok(codes.includes('effect.to'));
});

// The strata project is a local link (specs/strata/project.jsonc, untracked) to a large external specification; without
// it the project is absent and this test is skipped, which `exegra verify` records as skipped, never as a pass.
// Only the machine-readiness diagnostics are asserted: other readiness gaps of that specification
// are not about implementation-level machines.
const MACHINE_READY_CODES = new Set([
  'ready.delivery-missing', 'ready.elapsed-no-timer', 'ready.emit-receiver-missing', 'ready.event-field-undeclared', 'ready.fault-only',
  'ready.instances-storage', 'ready.order-ambiguous', 'ready.otherwise-misplaced', 'ready.outcome-missing', 'ready.payload-type-unresolved',
  'ready.repr-missing', 'ready.repr-unresolved', 'ready.storage-creates-unfilled', 'ready.storage-field-type', 'ready.storage-field-unknown',
  'ready.storage-key', 'ready.storage-mismatch', 'ready.storage-missing', 'ready.storage-state-field', 'ready.storage-variable-unmapped',
  'ready.transaction-missing',
]);
const specsDir = fileURLToPath(new URL('../../specs', import.meta.url));
const strataLinked = existsSync(fileURLToPath(new URL('../../specs/strata/project.jsonc', import.meta.url)));

// The exegra and strata projects report no ready.* diagnostic.
// @evidence implementation-machine-readiness-rules
test('the exegra and strata projects have no implementation-level machine and so no readiness diagnostic', { skip: strataLinked ? false : 'the strata project is not linked (specs/strata/project.jsonc is a local link)' }, async () => {
  for (const name of ['exegra', 'strata']) {
    const data = await createWorkspace(specsDir).read(name);
    const p = analyzeSpec(data.spec.text);
    assert.ok(p.model.byKind.behavior.length > 0, name);
    assert.deepEqual(p.diagnostics.filter((d) => MACHINE_READY_CODES.has(d.code)), [], name);
  }
});

// storage.key-whole (WG-4907): a machine is keyed by the whole key of its record, every key field in order. Negative
// fixture: the fixed specification with the session record keyed by two fields and the machine keyed by one of them.
const COMPOSITE_RECORD = ['{ "id": "session", "name": "Session", "owner": "svc", "key": ["id"],', '{ "id": "session", "name": "Session", "owner": "svc", "key": ["other", "id"],'];
const wholeCodes = (text) => analyzeSpec(text).diagnostics.filter((d) => d.code === 'storage.key-whole');

// Negative fixture (WG-4907): a machine keyed by one field of a two-field record key gets storage.key-whole for storage.key and for instances.key, and nothing else.
// @evidence implementation-machine-readiness-rules # rule storage.key-whole
test('rule storage.key-whole: a key naming part of the record key is refused, once for storage.key and once for instances.key', () => {
  assert.deepEqual(wholeCodes(FIXED), []);
  const found = wholeCodes(broken(...COMPOSITE_RECORD));
  assert.deepEqual(found.map((d) => d.path.slice(-2)), [['instances', 'key'], ['storage', 'key']]);
  for (const d of found) {
    assert.equal(d.severity, 'error');
    assert.equal(d.entityId, 'machine');
    assert.match(d.message, /whole key|every key field/);
  }
  // Nothing else is wrong with the fixture: the record key is the only change.
  assert.deepEqual(analyzeSpec(broken(...COMPOSITE_RECORD)).diagnostics.filter((d) => d.severity === 'error' && d.code !== 'storage.key-whole'), []);
});

// The list of every key field in the record's order is accepted; another order, a short list or a single field of a composite key is refused.
// @evidence implementation-machine-readiness-rules # storage.key-whole accepts the list
test('storage.key-whole accepts the list of every key field in the record order, and refuses another order or a short list', () => {
  const held = (key) => broken(...COMPOSITE_RECORD).replace('"instances": { "key": "id", "storedIn": "session" }, "storage": { "record": "session", "key": "id" },', `"storage": { "record": "session", "key": ${key} },`);
  assert.deepEqual(wholeCodes(held('["other", "id"]')), []);
  assert.deepEqual(analyzeSpec(held('["other", "id"]')).diagnostics.filter((d) => d.severity === 'error'), []);
  assert.deepEqual(wholeCodes(held('["id", "other"]')).map((d) => d.code), ['storage.key-whole']);
  assert.deepEqual(wholeCodes(held('["id"]')).map((d) => d.code), ['storage.key-whole']);
  assert.deepEqual(wholeCodes(held('"other"')).map((d) => d.code), ['storage.key-whole']);
});
