// The faults the generated runtime can produce and the initial state it can reproduce (WG-4903,
// docs/semantics.md, "Faults the runtime can produce"): rules fault.unrealisable
// (src/core/fault-model.js) and machine.initial-unreachable (src/core/readiness-machines.js), the
// lowering of the fault kinds duplicate-event, lose-event and retry-event into the engine input
// (src/core/sim-input.js), and what the engine does with them. The fixture is a machine whose scenario
// injects only faults the runtime can produce and has no error; each negative case changes one thing
// and must give exactly the named error, as the rule for validation rules asks (WG-4948).

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { analyzeSpec } from '../../src/core/analyze.js';
import { initEngine, runScenario } from '../../src/core/engine.js';
import { simulationInput } from '../../src/core/sim-input.js';
import { retryDelay, isRetryDelay } from '../../src/core/fault-model.js';

initEngine();

const FIXED = readFileSync(fileURLToPath(new URL('../fixtures/runtime-faults/spec.jsonc', import.meta.url)), 'utf8');

/** The fixed specification with textual changes, each of which must apply exactly once. */
function broken(...pairs) {
  let t = FIXED;
  for (let i = 0; i < pairs.length; i += 2) {
    assert.equal(t.split(pairs[i]).length - 1, 1, `fixture text occurs once: ${pairs[i]}`);
    t = t.replace(pairs[i], pairs[i + 1]);
  }
  return t;
}
const errors = (text) => analyzeSpec(text).diagnostics.filter((d) => d.severity === 'error');

test('the fixed specification has no error', () => {
  assert.deepEqual(errors(FIXED), []);
});

const NEGATIVE = [
  ['fault.unrealisable', 'dropping an at-least-once event, which its outbox retries until delivered',
    '"kind": "drop-event", "event": "ev-hint"', '"kind": "drop-event", "event": "ev-notice"'],
  ['fault.unrealisable', 'losing an event that is not at-most-once',
    '"kind": "lose-event", "event": "ev-hint"', '"kind": "lose-event", "event": "ev-notice"'],
  ['fault.unrealisable', 'retrying an at-most-once event',
    '"kind": "retry-event", "event": "ev-notice"', '"kind": "retry-event", "event": "ev-hint"'],
  ['fault.unrealisable', 'duplicating an at-most-once event, which is claimed before its dispatch',
    '"kind": "duplicate-event", "event": "ev-notice"', '"kind": "duplicate-event", "event": "ev-hint"'],
  ['fault.unrealisable', 'delaying an at-most-once event, which is never deferred',
    '"kind": "delay-event", "event": "ev-poke"', '"kind": "delay-event", "event": "ev-hint"'],
  ['fault.unrealisable', 'delaying an at-least-once event by what no backoff gives',
    '"by": "1 s", "occurrence": 5', '"by": "2 s", "occurrence": 5'],
  ['fault.unrealisable', 'dropping a timer firing',
    '"kind": "drop-event", "event": "ev-hint"', '"kind": "drop-event", "event": "ev-tick"'],
  ['fault.unrealisable', 'delaying a timer firing',
    '"kind": "delay-event", "event": "ev-poke"', '"kind": "delay-event", "event": "ev-tick"'],
  ['fault.unrealisable', 'turning off a transition of an implementation-level machine',
    '{ "id": "f-poke-extra", "name": "Poke sent again", "kind": "inject-event", "event": "ev-poke", "at": "100 ms" }',
    '{ "id": "f-poke-extra", "name": "Hint ignored", "kind": "disable-transition", "transition": "r-hint" }'],
  ['machine.initial-unreachable', 'a shipped machine that neither creates its records nor names the contract that writes them',
    '"key": "id", "creates": true', '"key": "id"'],
];

for (const [code, what, from, to] of NEGATIVE) {
  test(`rule ${code}: ${what} gives exactly that one error`, () => {
    const got = errors(broken(from, to));
    assert.deepEqual(got.map((d) => d.code), [code], JSON.stringify(got.map((d) => d.message)));
    assert.ok(got[0].entityId);
  });
}

test('a machine whose records a named contract writes or of a component not built yet reaches its initial state', () => {
  assert.deepEqual(errors(broken('"key": "id", "creates": true', '"key": "id", "createdBy": "open-relay"')), []);
  assert.deepEqual(errors(broken('"key": "id", "creates": true', '"key": "id"', '"status": "manual"', '"status": "not-implemented"')), []);
  // createdBy must name a contract.
  assert.ok(errors(broken('"key": "id", "creates": true', '"key": "id", "createdBy": "relay-svc"')).some((d) => d.code === 'machine.initial-unreachable' || d.code.startsWith('ref.')));
});

test('a stated retry policy decides which delays of an at-least-once event are realisable', () => {
  const policy = '"system": { "id": "relays", "name": "Relays", "generation": { "target": "rust", "retry": { "first": "500 ms", "factor": 2, "max": "1 s" } } }';
  const text = broken('"system": { "id": "relays", "name": "Relays" }', policy);
  const m = analyzeSpec(text).model;
  // 500 ms, then 500 + 1000, then capped at 1 s each.
  assert.deepEqual([1, 2, 3, 4].map((n) => retryDelay(m, n, 'ms')), [500, 1500, 2500, 3500]);
  assert.equal(isRetryDelay(m, 1500, 'ms'), true);
  assert.equal(isRetryDelay(m, 1000, 'ms'), false);
  assert.deepEqual(errors(text).filter((d) => d.code === 'fault.unrealisable').length, 1, 'the 1 s delay is no longer a backoff');
});

test('the runtime default backoff is 1 s, 2 s, 4 s, ... capped at 300 s', () => {
  const m = analyzeSpec(FIXED).model;
  assert.deepEqual([1, 2, 3, 9, 10].map((n) => retryDelay(m, n, 'ms')), [1000, 3000, 7000, 511000, 811000]);
});

test('the new fault kinds lower into a format-2 engine input: retry by the backoff, duplicate by its delay', () => {
  const m = analyzeSpec(FIXED).model;
  const input = simulationInput(m, 'run');
  assert.equal(input.version, 2);
  const byId = Object.fromEntries(input.faults.map((f) => [f.id, f]));
  assert.equal(byId['f-notice-twice'].kind, 'duplicate-event');
  assert.equal(byId['f-notice-twice'].by, 500);
  assert.equal(byId['f-notice-retried'].by, 3000);
  assert.equal(byId['f-hint-lost'].kind, 'lose-event');
  // A duplicate with no delay comes at once.
  const noBy = analyzeSpec(broken('"event": "ev-notice", "by": "500 ms", "occurrence": 1', '"event": "ev-notice", "occurrence": 1')).model;
  assert.equal(simulationInput(noBy, 'run').faults.find((f) => f.id === 'f-notice-twice').by, 0);
});

test('the engine delivers a duplicate twice and drops a lost event and delays a retried one by its backoff', () => {
  const m = analyzeSpec(FIXED).model;
  const tr = runScenario(m, 'run');
  const effects = tr.steps.flatMap((s) => s.faults.map((f) => `${f.fault}:${f.effect}:${s.kind}`));
  assert.ok(effects.includes('f-notice-twice:duplicated:deliver'), effects.join(' '));
  assert.ok(effects.includes('f-hint-lost:lost:drop'), effects.join(' '));
  assert.ok(effects.includes('f-hint-dropped:dropped:drop'), effects.join(' '));
  const notices = tr.steps.filter((s) => s.event.id === 'ev-notice').map((s) => s.time);
  // The first delivery at 0, its duplicate 500 ms later (where the retry delays it).
  assert.deepEqual(notices.slice(0, 2), [0, 500]);
  // The duplicate is the notice's second occurrence, which is retried after two failed dispatches.
  const retried = tr.steps.find((s) => s.faults.some((f) => f.fault === 'f-notice-retried'));
  assert.equal(retried?.kind, 'delay');
  assert.ok(tr.steps.some((s) => s.event.id === 'ev-notice' && s.kind === 'deliver' && s.time === 500 + 3000));
});
