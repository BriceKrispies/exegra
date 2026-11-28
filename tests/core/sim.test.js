// Simulation semantics, run through the engine facade (src/core/engine.js) on the Rust engine
// compiled to WebAssembly. Models are built from inline specs through analyzeSpec; a fixture with
// errors fails loudly before any run. The stepwise tests exercise the trace cursor the
// Simulation tab steps through.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { analyzeSpec } from '../../src/core/analyze.js';
import { initEngine, createSimulation, runScenario } from '../../src/core/engine.js';

initEngine();

/** A fresh spec document: a client sends one request, the server acknowledges it two ticks later. */
function doc() {
  return {
    exegra: '0.1',
    system: { id: 'demo-system', name: 'Demo system' },
    components: [
      { id: 'client', name: 'Client', category: 'logical' },
      { id: 'server', name: 'Server', category: 'logical' },
    ],
    events: [
      { id: 'start', name: 'Start' },
      { id: 'request', name: 'Request', payload: [{ name: 'n', type: 'number' }] },
      { id: 'ack', name: 'Acknowledge' },
    ],
    behaviors: [
      {
        id: 'client-machine',
        name: 'Client machine',
        subject: 'client',
        initial: 'idle',
        variables: [{ name: 'sent', type: 'number', initial: 0 }],
        states: [
          { id: 'idle', name: 'Idle' },
          { id: 'waiting', name: 'Waiting' },
          { id: 'done', name: 'Done' },
        ],
        transitions: [
          {
            id: 'send',
            from: 'idle',
            to: 'waiting',
            on: 'start',
            effects: [
              { set: 'sent', to: 'sent + 1' },
              { emit: 'request', after: 1, payload: { n: 'sent' } },
            ],
          },
          { id: 'receive-ack', from: 'waiting', to: 'done', on: 'ack' },
        ],
      },
      {
        id: 'server-machine',
        name: 'Server machine',
        subject: 'server',
        initial: 'listening',
        states: [
          { id: 'listening', name: 'Listening' },
          { id: 'served', name: 'Served' },
          { id: 'refused', name: 'Refused' },
        ],
        transitions: [
          { id: 'serve', from: 'listening', to: 'served', on: 'request', effects: [{ emit: 'ack', after: 2 }] },
        ],
      },
    ],
    scenarios: [
      {
        id: 'basic-exchange',
        name: 'Basic exchange',
        behaviors: ['client-machine', 'server-machine'],
        steps: [{ at: 0, event: 'start' }],
      },
    ],
    faults: [],
  };
}

/** @param {object} d */
function loadModel(d) {
  const { model, errorCount, diagnostics } = analyzeSpec(JSON.stringify(d));
  assert.equal(
    errorCount,
    0,
    `fixture has errors:\n${diagnostics.filter((x) => x.severity === 'error').map((x) => x.message).join('\n')}`,
  );
  assert.ok(model);
  return model;
}

test('request/ack exchange between two machines with emitted events and after delays', () => {
  const model = loadModel(doc());
  const trace = runScenario(model, 'basic-exchange');

  assert.equal(trace.outcome, 'quiescent');
  assert.deepEqual(
    trace.steps.map((s) => [s.time, s.event.id, s.kind]),
    [
      [0, 'start', 'deliver'],
      [1, 'request', 'deliver'],
      [3, 'ack', 'deliver'],
    ],
  );
  assert.deepEqual(trace.steps[0].fired, [
    {
      behavior: 'client-machine',
      transition: 'send',
      from: 'idle',
      to: 'waiting',
      guard: null,
      sets: [{ variable: 'sent', before: 0, after: 1 }],
      emitted: [{ event: 'request', time: 1, seq: 1, payload: { n: 1 } }],
      instance: 0,
    },
  ]);
  assert.deepEqual(trace.steps[0].ignored, [{ behavior: 'server-machine', reason: 'no-transition', considered: [], instance: 0 }]);
  assert.deepEqual(trace.steps[1].responsible, ['request', 'serve', 'server-machine', 'server']);
  assert.deepEqual(trace.steps[2].responsible, ['ack', 'receive-ack', 'client-machine', 'client']);
  assert.equal(trace.final.machines['client-machine'].state, 'done');
  assert.equal(trace.final.machines['server-machine'].state, 'served');
  assert.equal(trace.final.machines['client-machine'].vars.sent, 1);
  assert.equal(trace.final.time, 3);
  assert.deepEqual(trace.final.pending, []);
});

test('guard reads event payload and another machine variable', () => {
  const d = doc();
  d.behaviors[1].transitions = [
    {
      id: 'serve',
      from: 'listening',
      to: 'served',
      on: 'request',
      guard: 'event.n == 1 && client-machine.sent == 1',
      effects: [{ emit: 'ack', after: 2 }],
    },
    { id: 'refuse', from: 'listening', to: 'refused', on: 'request' },
  ];
  const model = loadModel(d);

  const accepted = runScenario(model, 'basic-exchange');
  assert.deepEqual(accepted.steps[1].fired.map((f) => f.transition), ['serve']);
  assert.equal(accepted.steps[1].fired[0].guard, 'event.n == 1 && client-machine.sent == 1');
  assert.equal(accepted.final.machines['server-machine'].state, 'served');

  const refusedDoc = doc();
  refusedDoc.behaviors[1].transitions = d.behaviors[1].transitions.map((t) =>
    t.id === 'serve' ? { ...t, guard: 'event.n == 2 || client-machine.sent == 0' } : t,
  );
  const refused = runScenario(loadModel(refusedDoc), 'basic-exchange');
  assert.deepEqual(refused.steps[1].fired.map((f) => f.transition), ['refuse']);
  assert.equal(refused.final.machines['server-machine'].state, 'refused');
  assert.equal(refused.final.machines['client-machine'].state, 'waiting');
  assert.equal(refused.outcome, 'quiescent');
});

test('identical inputs give deep-equal traces', () => {
  const first = runScenario(loadModel(doc()), 'basic-exchange');
  const second = runScenario(loadModel(doc()), 'basic-exchange');
  assert.deepEqual(second, first);
});

test('drop-event discards the delivery and fires nothing', () => {
  const d = doc();
  d.faults = [{ id: 'drop-request', name: 'Drop request', kind: 'drop-event', event: 'request' }];
  d.scenarios[0].faults = ['drop-request'];
  const trace = runScenario(loadModel(d), 'basic-exchange');

  assert.equal(trace.outcome, 'quiescent');
  assert.deepEqual(
    trace.steps.map((s) => [s.time, s.event.id, s.kind]),
    [
      [0, 'start', 'deliver'],
      [1, 'request', 'drop'],
    ],
  );
  assert.deepEqual(trace.steps[1].faults, [{ fault: 'drop-request', effect: 'dropped' }]);
  assert.deepEqual(trace.steps[1].fired, []);
  assert.deepEqual(trace.steps[1].responsible, ['request', 'drop-request']);
  assert.equal(trace.final.machines['client-machine'].state, 'waiting');
  assert.equal(trace.final.machines['server-machine'].state, 'listening');
});

test('delay-event re-queues the event once and delivers it later', () => {
  const d = doc();
  d.faults = [{ id: 'delay-request', name: 'Delay request', kind: 'delay-event', event: 'request', by: 5 }];
  d.scenarios[0].faults = ['delay-request'];
  const trace = runScenario(loadModel(d), 'basic-exchange');

  assert.equal(trace.outcome, 'quiescent');
  assert.deepEqual(
    trace.steps.map((s) => [s.time, s.event.id, s.kind]),
    [
      [0, 'start', 'deliver'],
      [1, 'request', 'delay'],
      [6, 'request', 'deliver'],
      [8, 'ack', 'deliver'],
    ],
  );
  assert.deepEqual(trace.steps[1].faults, [{ fault: 'delay-request', effect: 'delayed' }]);
  assert.equal(trace.steps[2].event.seq, 2);
  assert.equal(trace.final.time, 8);
  assert.equal(trace.final.machines['client-machine'].state, 'done');
});

test('enable-transition activates a faultOnly transition and records the fault', () => {
  const d = doc();
  d.behaviors[1].transitions = [
    { id: 'serve', from: 'listening', to: 'served', on: 'request', guard: 'event.n == 2' },
    {
      id: 'backup',
      from: 'listening',
      to: 'served',
      on: 'request',
      faultOnly: true,
      effects: [{ emit: 'ack', after: 2 }],
    },
  ];
  d.faults = [{ id: 'enable-backup', name: 'Enable backup', kind: 'enable-transition', transition: 'backup' }];
  const model = loadModel(d);

  const without = runScenario(model, 'basic-exchange');
  assert.equal(without.outcome, 'quiescent');
  assert.deepEqual(without.steps[1].fired, []);
  assert.deepEqual(without.steps[1].ignored.filter((i) => i.behavior === "server-machine"), [
    { behavior: 'server-machine', reason: 'guard-false', considered: ['serve'], instance: 0 },
  ]);
  assert.equal(without.final.machines['client-machine'].state, 'waiting');

  const withFault = runScenario(model, 'basic-exchange', { faults: ['enable-backup'] });
  assert.deepEqual(withFault.steps[1].fired.map((f) => f.transition), ['backup']);
  assert.deepEqual(withFault.steps[1].faults, [{ fault: 'enable-backup', effect: 'enabled' }]);
  assert.ok(withFault.steps[1].responsible.includes('enable-backup'));
  assert.ok(withFault.steps[1].responsible.includes('backup'));
  assert.equal(withFault.final.machines['client-machine'].state, 'done');
});

test('disable-transition stops a transition that would otherwise fire', () => {
  const d = doc();
  d.faults = [{ id: 'disable-serve', name: 'Disable serve', kind: 'disable-transition', transition: 'serve' }];
  d.scenarios[0].faults = ['disable-serve'];
  const trace = runScenario(loadModel(d), 'basic-exchange');

  assert.equal(trace.outcome, 'quiescent');
  assert.deepEqual(trace.steps[1].fired, []);
  assert.deepEqual(trace.steps[1].ignored.filter((i) => i.behavior === "server-machine"), [
    { behavior: 'server-machine', reason: 'disabled', considered: ['serve'], instance: 0 },
  ]);
  assert.deepEqual(trace.steps[1].faults, [{ fault: 'disable-serve', effect: 'disabled' }]);
  assert.equal(trace.final.machines['server-machine'].state, 'listening');
  assert.equal(trace.final.machines['client-machine'].state, 'waiting');
});

test('inject-event delivers a fault-sourced event and records it as injected', () => {
  const d = doc();
  d.faults = [{ id: 'inject-ack', name: 'Inject ack', kind: 'inject-event', event: 'ack', at: 1 }];
  d.scenarios[0].faults = ['inject-ack'];
  const trace = runScenario(loadModel(d), 'basic-exchange');

  assert.equal(trace.outcome, 'quiescent');
  assert.deepEqual(
    trace.steps.map((s) => [s.time, s.event.id]),
    [
      [0, 'start'],
      [1, 'ack'],
      [1, 'request'],
      [3, 'ack'],
    ],
  );
  assert.deepEqual(trace.steps[1].event.source, { kind: 'fault', fault: 'inject-ack' });
  assert.deepEqual(trace.steps[1].faults, [{ fault: 'inject-ack', effect: 'injected' }]);
  assert.ok(trace.steps[1].responsible.includes('inject-ack'));
  assert.equal(trace.steps[1].fired[0].transition, 'receive-ack');
  assert.equal(trace.final.machines['client-machine'].state, 'done');
});

test('reaching maxSteps with events still queued ends the run as step-limit', () => {
  const d = doc();
  d.scenarios[0].maxSteps = 2;
  const trace = runScenario(loadModel(d), 'basic-exchange');

  assert.equal(trace.outcome, 'step-limit');
  assert.equal(trace.steps.length, 2);
  assert.equal(trace.final.pending.length, 1);
  assert.equal(trace.final.pending[0].event, 'ack');
});

test('a failing expression records an error on its step and stops the run', () => {
  const d = doc();
  d.behaviors[1].transitions[0].guard = 'event.n / 0 > 1';
  const trace = runScenario(loadModel(d), 'basic-exchange');

  assert.equal(trace.outcome, 'error');
  const last = trace.steps[trace.steps.length - 1];
  assert.equal(trace.steps.length, 2);
  assert.match(last.error.message, /Division by zero/);
  assert.equal(trace.final.machines['server-machine'].state, 'listening');
});

test('reset returns to the initial configuration and a re-run equals the first run', () => {
  const model = loadModel(doc());
  const sim = createSimulation(model, 'basic-exchange');
  const first = sim.run();
  assert.equal(sim.outcome, 'quiescent');

  sim.reset();
  assert.deepEqual(sim.steps, []);
  assert.equal(sim.outcome, 'running');
  assert.deepEqual(sim.config, sim.initial);

  const second = sim.run();
  assert.deepEqual(second, first);
});

test('stepping one event at a time gives the same trace as run()', () => {
  const model = loadModel(doc());
  const sim = createSimulation(model, 'basic-exchange');
  let count = 0;
  while (sim.step() !== null) count++;
  assert.equal(count, 3);
  assert.equal(sim.step(), null);
  assert.deepEqual(sim.trace(), runScenario(model, 'basic-exchange'));
});

test('recorded trace steps are not changed by later steps', () => {
  const sim = createSimulation(loadModel(doc()), 'basic-exchange');
  sim.step();
  const snapshot = JSON.stringify(sim.steps[0].config);
  sim.run();
  assert.equal(JSON.stringify(sim.steps[0].config), snapshot);
});

test('unknown scenario identifiers are rejected with a plain error', () => {
  const model = loadModel(doc());
  assert.throws(() => createSimulation(model, 'no-such-scenario'), /not a scenario/);
});
