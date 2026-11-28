// The time and integer readiness rules of implementation-level machines (src/core/readiness-time.js,
// WG-4902, docs/semantics.md, "Time" and "Numbers"). The fixture is a machine that trusts a checked copy
// for 5000 ms and has no diagnostic; each negative case changes one thing and must give exactly the named
// error, as the rule for validation rules asks (WG-4948).

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { analyzeSpec } from '../../src/core/analyze.js';
import { initEngine } from '../../src/core/engine.js';
import { simulationInput, machineTimeUnit } from '../../src/core/sim-input.js';

initEngine();

const FIXED = readFileSync(fileURLToPath(new URL('../fixtures/readiness-time/spec.jsonc', import.meta.url)), 'utf8');

/** The fixed specification with one textual change, which must apply exactly once. */
function broken(from, to) {
  assert.equal(FIXED.split(from).length - 1, 1, `fixture text occurs once: ${from}`);
  return FIXED.replace(from, to);
}
const errors = (text) => analyzeSpec(text).diagnostics.filter((d) => d.severity === 'error');

const GUARD = '"guard": "checked && checkedAt <= time && time - checkedAt < 5000"';

test('the fixed machine has no error', () => {
  assert.deepEqual(errors(FIXED), []);
});

const NEGATIVE = [
  ['ready.time-epoch', 'time compared with a variable that can still hold its literal initial value', GUARD, '"guard": "checkedAt <= time && time - checkedAt < 5000"'],
  ['ready.time-difference', 'time - x read without first establishing x <= time', GUARD, '"guard": "checked && time - checkedAt < 5000"'],
  ['ready.delay-unit', 'a timer delay that is not a whole number of milliseconds', '"after": 2000', '"after": "2500 us"'],
  ['ready.delay-unit', 'a machine reading time in scenarios that count microseconds', '"timeUnit": "ms"', '"timeUnit": "us"'],
  ['ready.number-bound', 'a number literal beyond 2^53 - 1', 'time - checkedAt < 5000', 'time - checkedAt < 9007199254740992'],
  ['ready.number-bound', 'an integer variable whose initial value is outside its type', '{ "name": "hits", "type": "number", "initial": 0', '{ "name": "hits", "type": "number", "initial": -1'],
  ['ready.number-bound', 'a scenario payload value outside its integer type', '"payload": { "n": 1 }', '"payload": { "n": 4294967296 }'],
  // WG-5681: a simulated behaviour computes on integers; 0.5 in an effect is reported at validate.
  ['ready.number-bound', 'a number that is not an integer in an effect of a simulated behaviour', '"effects": [ { "set": "hits", "to": "hits + 1" }', '"effects": [ { "set": "hits", "to": "hits + 0.5" }'],
];

for (const [code, what, from, to] of NEGATIVE) {
  test(`readiness rule ${code}: ${what} gives exactly that one error`, () => {
    const got = errors(broken(from, to));
    assert.deepEqual(got.map((d) => d.code), [code]);
    assert.ok(got[0].entityId);
  });
}

test('a boolean that starts false and is set only together with the time witnesses it', () => {
  // Setting the flag in a transition that does not set checkedAt from time breaks the witness.
  const t = broken('"effects": [ { "set": "hits", "to": "hits + 1" }, { "emit": "ev-served", "to": "client" } ]',
    '"effects": [ { "set": "hits", "to": "hits + 1" }, { "set": "checked", "to": true }, { "emit": "ev-served", "to": "client" } ]');
  assert.deepEqual(errors(t).map((d) => d.code), ['ready.time-epoch']);
});

test('time - x is guarded by x <= time or time >= x in an earlier conjunct, also inside a negation', () => {
  assert.deepEqual(errors(broken(GUARD, '"guard": "checked && time >= checkedAt && time - checkedAt < 5000"')), []);
  assert.deepEqual(errors(broken(GUARD, '"guard": "!(!checked || !(checkedAt <= time && time - checkedAt < 5000))"')).map((d) => d.code), ['ready.time-epoch']);
  assert.deepEqual(errors(broken(GUARD, '"guard": "checked && !(checkedAt <= time && time - checkedAt >= 5000)"')), []);
});

test('scenarios that disagree on the time unit are refused for a machine with delays', () => {
  const t = broken('"scenarios": [', '"scenarios": [\n    { "id": "run-us", "name": "Run in us", "behaviors": ["copy"], "timeUnit": "us", "steps": [] },');
  assert.ok(errors(t).map((d) => d.code).includes('ready.delay-unit'));
});

test('the machine time unit is the unit of the scenarios that run it, ms when none constrains it', () => {
  const m = analyzeSpec(FIXED).model;
  assert.deepEqual(machineTimeUnit(m, 'copy'), { unit: 'ms', units: ['ms'], scenarios: ['run'] });
  const noScenario = analyzeSpec(broken('"behaviors": ["copy"], "timeUnit": "ms",', '"behaviors": [], "timeUnit": "ms",')).model;
  assert.equal(machineTimeUnit(noScenario, 'copy').unit, 'ms');
});

test('the engine input gives an implementation machine its declared types lowered', () => {
  const input = simulationInput(analyzeSpec(FIXED).model, 'run');
  assert.deepEqual(input.behaviors[0].types, { time: 'i64', checkedAt: 'i64', checked: 'bool', hits: 'u32', 'event.n': 'u32' });
});
