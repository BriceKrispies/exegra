// Refinement of a model machine by an implementation machine (docs/claims-and-evidence.md, "Refinement"):
// the claim method `refines` checks every step of the implementation's traces against the model through the
// refinement mapping, and validation refuses malformed mappings.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { analyzeSpec } from '../../src/core/analyze.js';
import { evaluateClaim } from '../../src/core/claims.js';
import { initEngine } from '../../src/core/engine.js';
import { exploreRefinement } from '../../src/core/refinement-explore.js';

initEngine();

/**
 * A lease: the model has free and held; the implementation adds an internal renewing state, mapped by stutter.
 * The implementation is a complete implementation-level machine (src/core/readiness-machines.js): every variable
 * has a repr, the machine declares its storage and transaction, the emitted event its delivery and receiver, every payload
 * field a resolving type, every transition group ends in a guard or otherwise, and every state has an outcome or
 * an ignore for every event the machine reacts to. Each violated variant below breaks only the refinement.
 */
function leaseSpec() {
  return {
    exegra: '0.1',
    system: { id: 'lease-system', name: 'Lease' },
    components: [{ id: 'lease-service', name: 'Lease service', category: 'computational' }],
    records: [{ id: 'lease', name: 'Lease', owner: 'lease-service', key: ['lease-id'], fields: [{ name: 'lease-id', type: 'string' }, { name: 'state', type: 'string' }, { name: 'owner', type: 'string' }, { name: 'gen', type: 'u64' }, { name: 'renewals', type: 'u32' }] }],
    events: [
      { id: 'acquire', name: 'Acquire', payload: [{ name: 'client', type: 'string' }] },
      { id: 'release', name: 'Release', payload: [{ name: 'client', type: 'string' }] },
      { id: 'renew', name: 'Renew' },
      { id: 'renewed', name: 'Renewed' },
      { id: 'granted', name: 'Granted', payload: [{ name: 'client', type: 'string' }, { name: 'gen', type: 'u64' }], delivery: 'at-least-once' },
    ],
    behaviors: [
      {
        id: 'lease-model', name: 'Lease (model)', subject: 'lease-service', initial: 'lm-free',
        variables: [{ name: 'holder', type: 'string', initial: '' }, { name: 'epoch', type: 'number', initial: 0 }],
        states: [{ id: 'lm-free', name: 'Free' }, { id: 'lm-held', name: 'Held' }],
        transitions: [
          { id: 'lm-acquire', from: 'lm-free', to: 'lm-held', on: 'acquire', guard: "holder == ''",
            effects: [{ set: 'holder', to: 'event.client' }, { set: 'epoch', to: 'epoch + 1' }, { emit: 'granted', payload: { client: 'event.client' } }] },
          { id: 'lm-release', from: 'lm-held', to: 'lm-free', on: 'release', guard: 'event.client == holder',
            effects: [{ set: 'holder', to: "''" }] },
        ],
      },
      {
        id: 'lease-impl', name: 'Lease (implementation)', subject: 'lease-service', initial: 'li-free', level: 'implementation',
        variables: [{ name: 'owner', type: 'string', initial: '', repr: 'string' }, { name: 'gen', type: 'number', initial: 0, repr: 'u64' }, { name: 'renewals', type: 'number', initial: 0, repr: 'u32' }],
        transaction: { scope: 'transition', isolation: 'serializable' },
        storage: { record: 'lease', key: 'lease-id' },
        states: [
          { id: 'li-free', name: 'Free', ignores: ['renew', 'renewed', 'release'] },
          { id: 'li-held', name: 'Held', ignores: ['acquire', 'renewed'] },
          { id: 'li-renewing', name: 'Renewing', ignores: ['acquire', 'renew', 'release'] },
        ],
        transitions: [
          { id: 'li-acquire', from: 'li-free', to: 'li-held', on: 'acquire', otherwise: true,
            effects: [{ set: 'owner', to: 'event.client' }, { set: 'gen', to: 'gen + 1' }, { emit: 'granted', to: 'lease-service', payload: { client: 'event.client', gen: 'gen' } }] },
          { id: 'li-renew', from: 'li-held', to: 'li-renewing', on: 'renew', otherwise: true, effects: [{ set: 'renewals', to: 'renewals + 1' }] },
          { id: 'li-renewed', from: 'li-renewing', to: 'li-held', on: 'renewed', otherwise: true },
          { id: 'li-release', from: 'li-held', to: 'li-free', on: 'release', otherwise: true, effects: [{ set: 'owner', to: "''" }] },
        ],
        refines: 'lease-model',
        refinement: {
          states: { 'li-free': 'lm-free', 'li-held': 'lm-held', 'li-renewing': 'lm-held' },
          variables: { holder: 'owner', epoch: 'gen' },
          transitions: { 'li-acquire': 'lm-acquire', 'li-renew': null, 'li-renewed': null, 'li-release': 'lm-release' },
        },
      },
    ],
    scenarios: [
      { id: 'lease-cycle', name: 'Acquire, renew, release', behaviors: ['lease-impl'],
        steps: [{ at: 0, event: 'acquire', payload: { client: 'a' } }, { at: 1, event: 'renew' }, { at: 2, event: 'renewed' }, { at: 3, event: 'release', payload: { client: 'a' } }] },
    ],
    claims: [
      { id: 'impl-refines-model', kind: 'temporal', statement: 'The implementation of the lease refines its model.',
        evaluate: { method: 'refines', behavior: 'lease-impl' } },
    ],
  };
}

/** @param {any} spec */
function load(spec) {
  const { model, errorCount, diagnostics } = analyzeSpec(JSON.stringify(spec));
  assert.equal(errorCount, 0, JSON.stringify(diagnostics.filter((d) => d.severity === 'error'), null, 1));
  assert.ok(model);
  return model;
}

/** @param {any} spec */
const result = (spec) => evaluateClaim(load(spec), 'impl-refines-model');
/** @param {any} spec @param {string} id */
const implTransition = (spec, id) => spec.behaviors[1].transitions.find((/** @type {any} */ t) => t.id === id);

/**
 * A violated result whose counterexample ends at the failing step.
 * @param {any} r @param {string} reason @param {number} stepIndex @param {string|null} transition
 */
function assertFailsAt(r, reason, stepIndex, transition) {
  assert.equal(r.status, 'violated', r.explanation);
  const cx = r.counterexample;
  assert.equal(cx.reason, reason, cx.summary);
  assert.equal(cx.scenario, 'lease-cycle');
  assert.equal(cx.stepIndex, stepIndex);
  const last = cx.trace[cx.trace.length - 1];
  assert.equal(last.ok, false);
  assert.equal(last.stepIndex, stepIndex);
  assert.equal(last.transition, transition);
  assert.ok(cx.trace.slice(0, -1).every((/** @type {any} */ s) => s.ok));
}

test('a refinement with an internal state mapped by stutter is verified on the trace', () => {
  const r = result(leaseSpec());
  assert.equal(r.status, 'verified', r.explanation);
  assert.equal(r.evaluator, 'exegra.refinement/0.1');
  assert.match(r.explanation, /4 steps \(2 matched to a model transition, 2 stutters\)/);
  assert.match(r.scope, /over every execution of their inputs that delivers simultaneous entries in another order/);
  assert.ok(r.involved.includes('lease-model') && r.involved.includes('lease-cycle'));
});

test('a refinement that holds on the scenario trace but fails under another delivery order is violated at that step', () => {
  // acquire and release arrive at the same time. The engine delivers acquire first, and that trace refines the
  // model; delivered first, release reaches li-early-release, which writes the mapped holder in a stutter.
  const spec = leaseSpec();
  spec.scenarios[0].steps = [{ at: 0, event: 'acquire', payload: { client: 'a' } }, { at: 0, event: 'release', payload: { client: 'a' } }];
  spec.behaviors[1].states[0].ignores = ['renew', 'renewed'];
  spec.behaviors[1].transitions.push({ id: 'li-early-release', from: 'li-free', to: 'li-free', on: 'release', otherwise: true, effects: [{ set: 'owner', to: 'event.client' }] });
  /** @type {any} */ (spec.behaviors[1].refinement.transitions)['li-early-release'] = null;
  const r = result(spec);
  assert.equal(r.status, 'violated', r.explanation);
  assert.equal(r.counterexample.reason, 'stutter-variables');
  assert.equal(r.counterexample.explored, true);
  assert.deepEqual(r.counterexample.order, ['release']);
  assert.equal(r.counterexample.trace.at(-1).transition, 'li-early-release');
  assert.match(r.explanation, /the engine's order does not reach it/);
});

test('an exploration that reaches its configuration cap is incomplete', () => {
  const model = load(leaseSpec());
  const x = exploreRefinement(model, /** @type {any} */ (model.entities.get('lease-impl')), 'lease-cycle', { stateCap: 2 });
  assert.equal(x.status, 'incomplete');
  assert.match(/** @type {any} */ (x).reason, /cap of 2 configurations/);
});

test('an exploration that reaches the step limit is inconclusive and never verified', () => {
  const spec = leaseSpec();
  /** @type {any} */ (spec.scenarios[0]).maxSteps = 2;
  const r = result(spec);
  assert.equal(r.status, 'inconclusive', r.explanation);
  assert.match(r.explanation, /step limit/);
});

test('an implementation that ignores release is refused', () => {
  // docs/assessment/2026-11-26/demos/refines-ignore.mjs: li-renewing ignores release, which the model's lm-held
  // accepts from the holder, so the implementation holds the lease forever and never grants b.
  const spec = leaseSpec();
  spec.scenarios[0].steps = [
    { at: 0, event: 'acquire', payload: { client: 'a' } }, { at: 1, event: 'renew' }, { at: 2, event: 'release', payload: { client: 'a' } },
    { at: 3, event: 'renewed' }, { at: 4, event: 'acquire', payload: { client: 'b' } },
  ];
  const r = result(spec);
  assertFailsAt(r, 'ignored-input', 3, null);
  assert.equal(r.verdict.strength, 'refuted');
  const last = r.counterexample.trace[r.counterexample.trace.length - 1];
  assert.equal(last.event, 'release');
  assert.equal(last.implFrom, 'li-renewing');
  assert.equal(last.model, 'lm-release');
  assert.deepEqual(r.counterexample.trace.map((/** @type {any} */ s) => s.transition), ['li-acquire', 'li-renew', null]);
});

test('refines is violated by a step to the wrong model state', () => {
  const spec = leaseSpec();
  spec.behaviors[1].states.push({ id: 'li-limbo', name: 'Limbo', ignores: ['acquire', 'renew', 'renewed', 'release'] });
  /** @type {any} */ (spec.behaviors[1].refinement.states)['li-limbo'] = 'lm-free';
  implTransition(spec, 'li-acquire').to = 'li-limbo';
  assertFailsAt(result(spec), 'model-to', 0, 'li-acquire');
});

test('refines is violated by a step whose model guard is false', () => {
  const spec = leaseSpec();
  spec.scenarios[0].steps[3].payload = { client: 'b' };
  const r = result(spec);
  assertFailsAt(r, 'model-guard-false', 4, 'li-release');
  assert.equal(r.counterexample.trace.length, 4);
});

test('refines is violated by a wrong mapped post-variable', () => {
  const spec = leaseSpec();
  implTransition(spec, 'li-acquire').effects[1].to = 'gen + 2';
  const r = result(spec);
  assertFailsAt(r, 'post-variables', 0, 'li-acquire');
  assert.match(r.counterexample.summary, /"epoch" maps to 2, but model transition "lm-acquire" makes it 1/);
});

test('refines is violated by a non-stutter step mapped to null', () => {
  const spec = leaseSpec();
  /** @type {any} */ (spec.behaviors[1].refinement.transitions)['li-release'] = null;
  assertFailsAt(result(spec), 'stutter-state', 4, 'li-release');
});

test('refines is violated by a wrong initial state', () => {
  const spec = leaseSpec();
  spec.behaviors[1].initial = 'li-held';
  spec.scenarios[0].steps = [{ at: 0, event: 'release', payload: { client: '' } }];
  assertFailsAt(result(spec), 'initial-state', -1, null);
});

test('refines is violated when emitted events differ from the model', () => {
  const spec = leaseSpec();
  implTransition(spec, 'li-acquire').effects.pop();
  assertFailsAt(result(spec), 'emits', 0, 'li-acquire');
});

test('refines and the ordering rule agree: the model transition is the one declaration order chooses, otherwise last', () => {
  // The model gets an earlier guarded acquire for client "a"; lm-acquire becomes the fall-through (otherwise).
  const ordered = () => {
    const spec = leaseSpec();
    const model = /** @type {any} */ (spec.behaviors[0]);
    const acquire = model.transitions[0];
    delete acquire.guard;
    acquire.otherwise = true;
    model.transitions.unshift({ id: 'lm-acquire-a', from: 'lm-free', to: 'lm-held', on: 'acquire', guard: "event.client == 'a'", effects: acquire.effects });
    return spec;
  };
  // Client "a": the model would fire lm-acquire-a, declared first, so mapping li-acquire to lm-acquire is refused.
  assertFailsAt(result(ordered()), 'model-not-chosen', 0, 'li-acquire');
  // Client "b": the guard of lm-acquire-a is false, so the otherwise transition lm-acquire is the model's step.
  const other = ordered();
  other.scenarios[0].steps[0].payload = { client: 'b' };
  other.scenarios[0].steps[3].payload = { client: 'b' };
  assert.equal(result(other).status, 'verified');
});

/** @param {any} spec */
const errorCodes = (spec) => analyzeSpec(JSON.stringify(spec)).diagnostics.filter((d) => d.severity === 'error').map((d) => d.code);

test('validation refuses a refines that names a non-behavior, a model-level refiner and a chain', () => {
  const notBehavior = leaseSpec();
  notBehavior.behaviors[1].refines = 'lm-free';
  assert.ok(errorCodes(notBehavior).includes('ref.kind'));

  const modelLevel = leaseSpec();
  delete (/** @type {any} */ (modelLevel.behaviors[1])).level;
  assert.ok(errorCodes(modelLevel).includes('behavior.refines-model-level'));

  const chain = leaseSpec();
  const inner = /** @type {any} */ (chain.behaviors[0]);
  inner.level = 'implementation';
  inner.refines = 'lease-impl';
  inner.refinement = { states: { 'lm-free': 'li-free', 'lm-held': 'li-held' }, variables: { owner: 'holder', gen: 'epoch', renewals: 'epoch' }, transitions: { 'lm-acquire': 'li-acquire', 'lm-release': 'li-release' } };
  assert.ok(errorCodes(chain).includes('behavior.refines-chain'));
});

test('validation refuses mappings with unknown or missing states, transitions and variables', () => {
  const unknown = leaseSpec();
  const m = /** @type {any} */ (unknown.behaviors[1].refinement);
  m.states['li-ghost'] = 'lm-free';
  m.states['li-held'] = 'lm-ghost';
  m.transitions['li-ghost'] = null;
  m.transitions['li-renew'] = 'lm-ghost';
  m.variables.ghost = 'owner';
  m.variables.epoch = 'gen + ghost';
  const codes = errorCodes(unknown);
  assert.equal(codes.filter((c) => c === 'refinement.unknown-state').length, 2);
  assert.equal(codes.filter((c) => c === 'refinement.unknown-transition').length, 2);
  assert.equal(codes.filter((c) => c === 'refinement.unknown-variable').length, 2);

  const missing = leaseSpec();
  const n = /** @type {any} */ (missing.behaviors[1].refinement);
  delete n.states['li-renewing'];
  delete n.transitions['li-renewed'];
  delete n.variables.epoch;
  const mcodes = errorCodes(missing);
  for (const c of ['refinement.unmapped-state', 'refinement.unmapped-transition', 'refinement.unmapped-variable']) assert.ok(mcodes.includes(c), c);
});

/**
 * A lease whose implementation sets a timer on acquire and expires when it fires. With `modelTimer` the model
 * sets a timer for the same event (compared); without, the implementation's timer is internal to it.
 * `implTimerEvent` changes the event the implementation's timer emits.
 */
function timerSpec({ modelTimer = true, implTimerEvent = 'lease-timeout' } = {}) {
  const timer = (/** @type {string} */ name, /** @type {string} */ event) => ({ timer: name, after: 10, emit: event });
  return {
    exegra: '0.1',
    system: { id: 'lease-timer-system', name: 'Lease with expiry' },
    components: [{ id: 'lease-service', name: 'Lease service', category: 'computational' }],
    records: [{ id: 'lease', name: 'Lease', owner: 'lease-service', key: ['lease-id'], fields: [{ name: 'lease-id', type: 'string' }, { name: 'state', type: 'string' }] }],
    events: [
      { id: 'acquire', name: 'Acquire' },
      { id: 'lease-timeout', name: 'Lease timeout', elapsed: true },
      { id: 'lease-other', name: 'Other timeout', elapsed: true },
      { id: 'granted', name: 'Granted', delivery: 'at-least-once' },
    ],
    behaviors: [
      {
        id: 'lease-model', name: 'Lease (model)', subject: 'lease-service', initial: 'lm-free',
        states: [{ id: 'lm-free', name: 'Free' }, { id: 'lm-held', name: 'Held' }],
        transitions: [
          { id: 'lm-acquire', from: 'lm-free', to: 'lm-held', on: 'acquire', effects: [...(modelTimer ? [timer('ttl', 'lease-timeout')] : []), { emit: 'granted' }] },
          { id: 'lm-expire', from: 'lm-held', to: 'lm-free', on: 'lease-timeout' },
        ],
      },
      {
        id: 'lease-impl', name: 'Lease (implementation)', subject: 'lease-service', initial: 'li-free', level: 'implementation',
        transaction: { scope: 'transition', isolation: 'serializable' },
        storage: { record: 'lease', key: 'lease-id' },
        states: [
          { id: 'li-free', name: 'Free', ignores: ['lease-timeout'] },
          { id: 'li-held', name: 'Held', ignores: ['acquire'] },
        ],
        transitions: [
          { id: 'li-acquire', from: 'li-free', to: 'li-held', on: 'acquire', otherwise: true, effects: [timer('lease-ttl', implTimerEvent), { emit: 'granted', to: 'lease-service' }] },
          { id: 'li-expire', from: 'li-held', to: 'li-free', on: 'lease-timeout', otherwise: true },
        ],
        refines: 'lease-model',
        refinement: { states: { 'li-free': 'lm-free', 'li-held': 'lm-held' }, variables: {}, transitions: { 'li-acquire': 'lm-acquire', 'li-expire': 'lm-expire' } },
      },
    ],
    // Milliseconds: an implementation machine's delays are whole milliseconds (ready.delay-unit).
    scenarios: [{ id: 'lease-expires', name: 'Acquire and expire', behaviors: ['lease-impl'], timeUnit: 'ms', steps: [{ at: 0, event: 'acquire' }] }],
    claims: [{ id: 'impl-refines-model', kind: 'temporal', statement: 'The implementation of the lease refines its model.', evaluate: { method: 'refines', behavior: 'lease-impl' } }],
  };
}

/**
 * A session gate whose model guards read another behavior's variable (`rev-model.revoked`). The scenario runs
 * the implementation of the revocation flow, which refines rev-model, so the read goes through its mapping; with
 * `direct` it runs rev-model itself and the read is direct. `checksRevocation: false` makes the implementation
 * accept without looking.
 */
function crossSpec({ direct = false, checksRevocation = true } = {}) {
  const implGuard = checksRevocation ? (direct ? '!rev-model.revoked' : '!rev-impl.gone') : 'true';
  return {
    exegra: '0.1',
    system: { id: 'gate-system', name: 'Session gate' },
    components: [{ id: 'gate', name: 'Gate', category: 'computational' }],
    records: [{ id: 'session', name: 'Session', owner: 'gate', key: ['session-id'], fields: [{ name: 'session-id', type: 'string' }, { name: 'gone', type: 'bool' }] }],
    events: [
      { id: 'revoke', name: 'Revoke' },
      { id: 'request', name: 'Request' },
      { id: 'accepted', name: 'Accepted', delivery: 'at-least-once' },
      { id: 'refused', name: 'Refused', delivery: 'at-least-once' },
    ],
    behaviors: [
      { id: 'rev-model', name: 'Revocation (model)', subject: 'gate', initial: 'rv-live',
        variables: [{ name: 'revoked', type: 'boolean', initial: false }],
        states: [{ id: 'rv-live', name: 'Live' }],
        transitions: [{ id: 'rv-revoke', from: 'rv-live', to: 'rv-live', on: 'revoke', effects: [{ set: 'revoked', to: true }] }] },
      { id: 'rev-impl', name: 'Revocation (implementation)', subject: 'gate', initial: 'rv-live-i', level: 'implementation',
        transaction: { scope: 'transition', isolation: 'serializable' }, storage: { record: 'session', key: 'session-id' },
        variables: [{ name: 'gone', type: 'boolean', initial: false, repr: 'bool' }],
        states: [{ id: 'rv-live-i', name: 'Live' }],
        transitions: [{ id: 'rv-revoke-i', from: 'rv-live-i', to: 'rv-live-i', on: 'revoke', otherwise: true, effects: [{ set: 'gone', to: true }] }],
        refines: 'rev-model',
        refinement: { states: { 'rv-live-i': 'rv-live' }, variables: { revoked: 'gone' }, transitions: { 'rv-revoke-i': 'rv-revoke' } } },
      { id: 'gate-model', name: 'Gate (model)', subject: 'gate', initial: 'gm-ready',
        states: [{ id: 'gm-ready', name: 'Ready' }],
        transitions: [
          { id: 'gm-accept', from: 'gm-ready', to: 'gm-ready', on: 'request', guard: '!rev-model.revoked', effects: [{ emit: 'accepted' }] },
          { id: 'gm-refuse', from: 'gm-ready', to: 'gm-ready', on: 'request', guard: 'rev-model.revoked', effects: [{ emit: 'refused' }] },
        ] },
      { id: 'gate-impl', name: 'Gate (implementation)', subject: 'gate', initial: 'gm-ready-i', level: 'implementation',
        transaction: { scope: 'transition', isolation: 'serializable' }, storage: { record: 'session', key: 'session-id' },
        states: [{ id: 'gm-ready-i', name: 'Ready' }],
        transitions: [
          { id: 'gm-accept-i', from: 'gm-ready-i', to: 'gm-ready-i', on: 'request', guard: implGuard, effects: [{ emit: 'accepted', to: 'gate' }] },
          { id: 'gm-refuse-i', from: 'gm-ready-i', to: 'gm-ready-i', on: 'request', otherwise: true, effects: [{ emit: 'refused', to: 'gate' }] },
        ],
        refines: 'gate-model',
        refinement: { states: { 'gm-ready-i': 'gm-ready' }, variables: {}, transitions: { 'gm-accept-i': 'gm-accept', 'gm-refuse-i': 'gm-refuse' } } },
    ],
    scenarios: [{ id: 'revoked-midway', name: 'Request, revoke, request', behaviors: [direct ? 'rev-model' : 'rev-impl', 'gate-impl'],
      steps: [{ at: 0, event: 'request' }, { at: 1, event: 'revoke' }, { at: 2, event: 'request' }] }],
    claims: [{ id: 'impl-refines-model', kind: 'temporal', statement: 'The implementation of the gate refines its model.', evaluate: { method: 'refines', behavior: 'gate-impl' } }],
  };
}

test('a timer the implementation sets and receives refines the same timer of the model', () => {
  const r = result(timerSpec());
  assert.equal(r.status, 'verified', r.explanation);
  assert.match(r.explanation, /2 steps \(2 matched/);
});

test('a timer the model does not set is internal to the implementation', () => {
  const r = result(timerSpec({ modelTimer: false }));
  assert.equal(r.status, 'verified', r.explanation);
});

test('refines is violated when the implementation timer emits another event than the model timer', () => {
  const r = result(timerSpec({ implTimerEvent: 'lease-other' }));
  assert.equal(r.status, 'violated', r.explanation);
  assert.equal(r.counterexample.reason, 'timers');
  assert.equal(r.counterexample.stepIndex, 0);
  assert.equal(r.counterexample.trace.at(-1).transition, 'li-acquire');
});

test('a model guard reading another behavior is evaluated through the machine that refines it', () => {
  const r = result(crossSpec());
  assert.equal(r.status, 'verified', r.explanation);
  assert.match(r.explanation, /2 steps \(2 matched/);
});

test('a model guard reading another behavior is evaluated on that behavior when it runs itself', () => {
  const r = result(crossSpec({ direct: true }));
  assert.equal(r.status, 'verified', r.explanation);
});

test('refines is violated when a model guard reading another behavior is false', () => {
  const r = result(crossSpec({ checksRevocation: false }));
  assert.equal(r.status, 'violated', r.explanation);
  assert.equal(r.counterexample.reason, 'model-guard-false');
  assert.equal(r.counterexample.scenario, 'revoked-midway');
  assert.equal(r.counterexample.stepIndex, 3);
  assert.equal(r.counterexample.trace.at(-1).transition, 'gm-accept-i');
});

/**
 * A sign-in link whose model counts in ticks of one minute (accepted while `time - issuedAt <= 15`, expired by a
 * timer 15 ticks after issue) and whose implementation counts in milliseconds (`timeScale` 60000). The
 * implementation keeps the expiry instant; the mapping converts it back to the model's issue tick.
 * `lifetimeMs` is the implementation's lifetime, `presentAt` the millisecond of the presentation.
 */
function scaledSpec({ lifetimeMs = 900000, presentAt = 840000, timeScale = /** @type {number|null} */ (60000) } = {}) {
  return {
    exegra: '0.1',
    system: { id: 'link-system', name: 'Sign-in link' },
    components: [{ id: 'identity', name: 'Identity service', category: 'computational' }],
    records: [{ id: 'challenge', name: 'Challenge', owner: 'identity', key: ['challenge-id'], fields: [{ name: 'challenge-id', type: 'string' }, { name: 'state', type: 'string' }, { name: 'expiresAt', type: 'timestamp' }, { name: 'uses', type: 'u32' }] }],
    events: [
      { id: 'link-requested', name: 'Link requested' },
      { id: 'link-presented', name: 'Link presented' },
      { id: 'link-expired', name: 'Link expired', elapsed: true },
    ],
    behaviors: [
      {
        id: 'link-model', name: 'Link (model)', subject: 'identity', initial: 'lk-idle',
        variables: [{ name: 'issuedAt', type: 'number', initial: 0 }, { name: 'uses', type: 'number', initial: 0 }],
        states: [{ id: 'lk-idle', name: 'Idle' }, { id: 'lk-pending', name: 'Pending' }, { id: 'lk-expired', name: 'Expired' }],
        transitions: [
          { id: 'lk-issue', from: 'lk-idle', to: 'lk-pending', on: 'link-requested', effects: [{ set: 'issuedAt', to: 'time' }, { timer: 'ttl', after: 60, emit: 'link-expired' }] },
          { id: 'lk-accept', from: 'lk-pending', to: 'lk-pending', on: 'link-presented', guard: 'time - issuedAt <= 15', effects: [{ set: 'uses', to: 'uses + 1' }] },
          { id: 'lk-refuse', from: 'lk-pending', to: 'lk-pending', on: 'link-presented', guard: 'time - issuedAt > 15' },
          { id: 'lk-expire', from: 'lk-pending', to: 'lk-expired', on: 'link-expired' },
        ],
      },
      {
        id: 'link-impl', name: 'Link (implementation)', subject: 'identity', initial: 'lk-idle-i', level: 'implementation',
        transaction: { scope: 'transition', isolation: 'serializable' },
        storage: { record: 'challenge', key: 'challenge-id' },
        variables: [{ name: 'expiresAt', type: 'number', initial: lifetimeMs, repr: 'timestamp' }, { name: 'uses', type: 'number', initial: 0, repr: 'u32' }],
        states: [
          { id: 'lk-idle-i', name: 'Idle', ignores: ['link-presented', 'link-expired'] },
          { id: 'lk-pending-i', name: 'Pending' },
          { id: 'lk-expired-i', name: 'Expired', ignores: ['link-requested', 'link-presented', 'link-expired'] },
        ],
        transitions: [
          { id: 'lk-issue-i', from: 'lk-idle-i', to: 'lk-pending-i', on: 'link-requested', otherwise: true,
            effects: [{ set: 'expiresAt', to: `time + ${lifetimeMs}` }, { timer: 'link-ttl', after: 3600000, emit: 'link-expired' }] },
          { id: 'lk-accept-i', from: 'lk-pending-i', to: 'lk-pending-i', on: 'link-presented', guard: 'time <= expiresAt', effects: [{ set: 'uses', to: 'uses + 1' }] },
          { id: 'lk-refuse-i', from: 'lk-pending-i', to: 'lk-pending-i', on: 'link-presented', otherwise: true },
          { id: 'lk-again-i', from: 'lk-pending-i', to: 'lk-pending-i', on: 'link-requested', otherwise: true },
          { id: 'lk-expire-i', from: 'lk-pending-i', to: 'lk-expired-i', on: 'link-expired', otherwise: true },
        ],
        refines: 'link-model',
        refinement: {
          states: { 'lk-idle-i': 'lk-idle', 'lk-pending-i': 'lk-pending', 'lk-expired-i': 'lk-expired' },
          variables: { issuedAt: `(expiresAt - ${lifetimeMs}) / 60000`, uses: 'uses' },
          transitions: { 'lk-issue-i': 'lk-issue', 'lk-accept-i': 'lk-accept', 'lk-refuse-i': 'lk-refuse', 'lk-again-i': null, 'lk-expire-i': 'lk-expire' },
          ...(timeScale === null ? {} : { timeScale }),
        },
      },
    ],
    // Milliseconds: an implementation machine that reads time runs on a millisecond clock (ready.delay-unit).
    scenarios: [{ id: 'link-presented-in-time', name: 'Request, present, expire', behaviors: ['link-impl'], timeUnit: 'ms',
      steps: [{ at: 0, event: 'link-requested' }, { at: presentAt, event: 'link-presented' }] }],
    claims: [{ id: 'impl-refines-model', kind: 'temporal', statement: 'The implementation of the link refines its model.', evaluate: { method: 'refines', behavior: 'link-impl' } }],
  };
}

test('a tick-based model and a millisecond implementation at real timings agree through the time scale', () => {
  const r = result(scaledSpec());
  assert.equal(r.status, 'verified', r.explanation);
  assert.match(r.explanation, /3 steps \(3 matched/);
  // A presentation after the lifetime is refused by both.
  assert.equal(result(scaledSpec({ presentAt: 960000 })).status, 'verified');
});

test('an implementation timer whose delay is read at run time is simulated with its simulate delay and still refines the model', () => {
  const spec = scaledSpec();
  const impl = /** @type {any} */ (spec.behaviors[1]);
  impl.variables.push({ name: 'ttlMs', type: 'number', initial: 3600000, repr: 'u32' });
  /** @type {any} */ (spec.records[0]).fields.push({ name: 'ttlMs', type: 'u32' });
  implTransition(spec, 'lk-issue-i').effects[1].after = { expr: 'ttlMs', simulate: 3600000 };
  const r = result(spec);
  assert.equal(r.status, 'verified', r.explanation);
  // The model's delay is compared with the simulated one, so a simulated delay that disagrees is caught.
  implTransition(spec, 'lk-issue-i').effects[1].after = { expr: 'ttlMs', simulate: 60000 };
  assert.equal(result(spec).status, 'violated');
});

test('refines is violated when the implementation accepts past the scaled lifetime', () => {
  const r = result(scaledSpec({ lifetimeMs: 1200000, presentAt: 960000 }));
  assert.equal(r.status, 'violated', r.explanation);
  assert.equal(r.counterexample.reason, 'model-guard-false');
  assert.equal(r.counterexample.stepIndex, 1);
  assert.equal(r.counterexample.trace.at(-1).transition, 'lk-accept-i');
});

test('without the time scale the model reads milliseconds as ticks and the same run is violated', () => {
  const r = result(scaledSpec({ timeScale: null }));
  assert.equal(r.status, 'violated', r.explanation);
  assert.equal(r.counterexample.stepIndex, 0);
  assert.equal(r.counterexample.reason, 'timers');
});

test('validation refuses a time scale that is not a positive number', () => {
  for (const bad of [0, -1000]) {
    assert.ok(errorCodes(scaledSpec({ timeScale: /** @type {any} */ (bad) })).includes('refinement.time-scale'), String(bad));
  }
});

/**
 * A reminder the model sends 5 ticks after the start as a delayed emit, and the implementation (milliseconds,
 * timeScale 1000) realises as a delayed emit 5000 ms after. `impl` picks how the implementation realises it:
 * `delayed` (a delayed emit with `after` and `event`), `timer` (a timer with `after` and `event`, which delivers
 * to its own machine, not to the receivers, and so never realises an emit), or `emit` for an emit at once.
 */
function delaySpec({ impl = 'delayed', after = 5000, event = 'reminder' } = {}) {
  const realised = impl === 'timer'
    ? { timer: 'remind', after, emit: event, payload: { n: '1' } }
    : impl === 'delayed'
      ? { emit: event, to: 'svc', after, payload: { n: '1' } }
      : { emit: event, to: 'svc', payload: { n: '1' } };
  return {
    exegra: '0.1',
    system: { id: 'reminder-system', name: 'Reminder' },
    components: [{ id: 'svc', name: 'Service', category: 'computational' }],
    records: [{ id: 'task', name: 'Task', owner: 'svc', key: ['task-id'], fields: [{ name: 'task-id', type: 'string' }, { name: 'state', type: 'string' }] }],
    events: [
      { id: 'start', name: 'Start' },
      // An event is marked elapsed only when the implementation's timer produces it (ready.elapsed-no-timer).
      { id: 'reminder', name: 'Reminder', elapsed: impl === 'timer' && event === 'reminder', delivery: 'at-least-once', payload: [{ name: 'n', type: 'u32' }] },
      { id: 'other', name: 'Other', elapsed: impl === 'timer' && event === 'other', delivery: 'at-least-once', payload: [{ name: 'n', type: 'u32' }] },
    ],
    behaviors: [
      { id: 'task-model', name: 'Task (model)', subject: 'svc', initial: 'tk-idle',
        states: [{ id: 'tk-idle', name: 'Idle' }, { id: 'tk-waiting', name: 'Waiting' }, { id: 'tk-done', name: 'Done' }],
        transitions: [
          { id: 'tk-start', from: 'tk-idle', to: 'tk-waiting', on: 'start', effects: [{ emit: 'reminder', after: 5, payload: { n: '1' } }] },
          { id: 'tk-remind', from: 'tk-waiting', to: 'tk-done', on: 'reminder' },
        ] },
      { id: 'task-impl', name: 'Task (implementation)', subject: 'svc', initial: 'tk-idle-i', level: 'implementation',
        transaction: { scope: 'transition', isolation: 'serializable' }, storage: { record: 'task', key: 'task-id' },
        states: [
          { id: 'tk-idle-i', name: 'Idle', ignores: ['reminder'] },
          { id: 'tk-waiting-i', name: 'Waiting', ignores: ['start'] },
          { id: 'tk-done-i', name: 'Done', terminal: true },
        ],
        transitions: [
          { id: 'tk-start-i', from: 'tk-idle-i', to: 'tk-waiting-i', on: 'start', otherwise: true, effects: [realised] },
          { id: 'tk-remind-i', from: 'tk-waiting-i', to: 'tk-done-i', on: 'reminder', otherwise: true },
        ],
        refines: 'task-model',
        refinement: { states: { 'tk-idle-i': 'tk-idle', 'tk-waiting-i': 'tk-waiting', 'tk-done-i': 'tk-done' }, variables: {}, transitions: { 'tk-start-i': 'tk-start', 'tk-remind-i': 'tk-remind' }, timeScale: 1000 } },
    ],
    scenarios: [{ id: 'task-reminded', name: 'Start and be reminded', behaviors: ['task-impl'], steps: [{ at: 0, event: 'start' }] }],
    claims: [{ id: 'impl-refines-model', kind: 'temporal', statement: 'The implementation of the task refines its model.', evaluate: { method: 'refines', behavior: 'task-impl' } }],
  };
}

/** @param {any} r @param {string} reason */
function assertDelayFails(r, reason) {
  assert.equal(r.status, 'violated', r.explanation);
  assert.equal(r.counterexample.reason, reason, r.counterexample.summary);
  assert.equal(r.counterexample.scenario, 'task-reminded');
  assert.equal(r.counterexample.stepIndex, 0);
  assert.equal(r.counterexample.trace.at(-1).transition, 'tk-start-i');
}

test('a delayed emit of the model is realised by a delayed emit at the scaled delay', () => {
  const r = result(delaySpec());
  assert.equal(r.status, 'verified', r.explanation);
  assert.match(r.explanation, /2 steps \(2 matched/);
});

test('refines is violated when the delayed emit realising a delayed emit has another delay', () => {
  assertDelayFails(result(delaySpec({ after: 4000 })), 'emits');
});

test('refines is violated when the delayed emit realising a delayed emit emits another event', () => {
  assertDelayFails(result(delaySpec({ event: 'other' })), 'emits');
});

test('refines is violated when a timer stands in for a delayed emit of the model', () => {
  // The timer has the model's event and delay, but fires it at its own machine; the receivers never get it.
  assertDelayFails(result(delaySpec({ impl: 'timer' })), 'emits');
});

test('refines is violated when a delayed emit of the model is emitted at once', () => {
  assertDelayFails(result(delaySpec({ impl: 'emit' })), 'emits');
});
