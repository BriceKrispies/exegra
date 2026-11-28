// Claim strength (src/core/claim-strength.js): the check behind a claim's status and what it reads,
// on small fixtures that reproduce the Harbourline fold's claims (judge report F1, F2, F7, F8), and the
// admit reasons for a new claim (cli/admit.js). Decision: dec-claim-check-and-grounding.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { analyzeSpec } from '../../src/core/analyze.js';
import { evaluateClaim } from '../../src/core/claims.js';
import { initEngine } from '../../src/core/engine.js';
import { claimStrength, strengthCounts } from '../../src/core/claim-strength.js';
import { runCommand } from '../../cli/commands.js';

initEngine();

/** @param {string} text */
function load(text) {
  const { model, errorCount, diagnostics } = analyzeSpec(text);
  assert.equal(errorCount, 0, JSON.stringify(diagnostics.filter((d) => d.severity === 'error'), null, 1));
  assert.ok(model);
  return model;
}

const SPEC = {
  exegra: '0.1',
  system: { id: 'harbour', name: 'Harbour' },
  components: [
    { id: 'control-plane', name: 'Control plane', category: 'computational', purpose: 'Runs tenant operations.' },
    { id: 'agent-gateway', name: 'Agent gateway', category: 'computational', purpose: 'Admits agent acts.' },
  ],
  capabilities: [
    { id: 'content-read', name: 'Read content', core: true },
    { id: 'plan-change', name: 'Change a plan', core: true },
  ],
  roles: [
    { id: 'owner', level: 'tenant', holders: ['person'], capabilities: ['content-read', 'plan-change'] },
    { id: 'assistant', level: 'tenant', holders: ['agent'], capabilities: ['content-read'] },
  ],
  contracts: [
    { id: 'change-plan', name: 'Change plan', inputs: [{ name: 'plan', type: 'string' }], auth: { scheme: 'session', requires: ['plan-change'] } },
  ],
  events: [
    { id: 'rx-renewal', name: 'Renewal', payload: [{ name: 'daysBeforeExpiry', type: 'number' }] },
    { id: 'rx-renewed', name: 'Renewed' },
    { id: 'gf-create', name: 'Create feature data' },
    { id: 'gf-plan-change', name: 'Plan change', payload: [{ name: 'toGrandfathered', type: 'boolean' }] },
    { id: 'gf-created', name: 'Created' },
    { id: 'ag-attempt', name: 'Agent attempt', payload: [{ name: 'changesPower', type: 'boolean' }] },
    { id: 'ag-act-done', name: 'Act done' },
    { id: 'ag-act-refused', name: 'Act refused' },
    { id: 'pc-requested', name: 'Plan change requested', contract: 'change-plan', role: 'request', payload: [{ name: 'plan', type: 'string' }] },
    { id: 'pc-applied', name: 'Plan change applied' },
  ],
  behaviors: [
    {
      id: 'rx-flow', name: 'Residency exception', subject: 'control-plane', initial: 'rx-open',
      variables: [{ name: 'clockRestarts', type: 'number', initial: 0 }],
      states: [{ id: 'rx-open', name: 'Open' }],
      transitions: [
        { id: 'rx-renew-restarts-clock', from: 'rx-open', to: 'rx-open', on: 'rx-renewal', faultOnly: true, guard: 'event.daysBeforeExpiry <= 14',
          effects: [{ set: 'clockRestarts', to: 'clockRestarts + 1' }, { emit: 'rx-renewed' }] },
        { id: 'rx-renew', from: 'rx-open', to: 'rx-open', on: 'rx-renewal', guard: 'event.daysBeforeExpiry <= 14', effects: [{ emit: 'rx-renewed' }] },
      ],
    },
    {
      id: 'gf-flow', name: 'Grandfathered plan', subject: 'control-plane', initial: 'gf-grandfathered',
      variables: [{ name: 'featureRecords', type: 'number', initial: 0 }],
      states: [{ id: 'gf-grandfathered', name: 'Grandfathered' }, { id: 'gf-standard', name: 'Standard' }],
      transitions: [
        { id: 'gf-create-ok', from: 'gf-grandfathered', to: 'gf-grandfathered', on: 'gf-create', effects: [{ set: 'featureRecords', to: 'featureRecords + 1' }, { emit: 'gf-created' }] },
        { id: 'gf-keep', from: 'gf-grandfathered', to: 'gf-grandfathered', on: 'gf-plan-change', guard: 'event.toGrandfathered' },
        { id: 'gf-lose', from: 'gf-grandfathered', to: 'gf-standard', on: 'gf-plan-change' },
        { id: 'gf-create-after-loss', from: 'gf-standard', to: 'gf-standard', on: 'gf-create', faultOnly: true, effects: [{ set: 'featureRecords', to: 'featureRecords + 1' }, { emit: 'gf-created' }] },
        { id: 'gf-refuse-create', from: 'gf-standard', to: 'gf-standard', on: 'gf-create' },
      ],
    },
    {
      id: 'ag-flow', name: 'Agent acts', subject: 'agent-gateway', initial: 'ag-open',
      states: [{ id: 'ag-open', name: 'Open' }],
      transitions: [
        { id: 'ag-do-anything', from: 'ag-open', to: 'ag-open', on: 'ag-attempt', faultOnly: true, effects: [{ emit: 'ag-act-done' }] },
        { id: 'ag-do', from: 'ag-open', to: 'ag-open', on: 'ag-attempt', guard: '!event.changesPower', effects: [{ emit: 'ag-act-done' }] },
        { id: 'ag-refuse', from: 'ag-open', to: 'ag-open', on: 'ag-attempt', effects: [{ emit: 'ag-act-refused' }] },
      ],
    },
    {
      id: 'pc-flow', name: 'Plan change', subject: 'control-plane', initial: 'pc-idle',
      variables: [{ name: 'applied', type: 'number', initial: 0 }],
      states: [{ id: 'pc-idle', name: 'Idle' }],
      transitions: [
        { id: 'pc-apply', from: 'pc-idle', to: 'pc-idle', on: 'pc-requested', guard: "event.plan != ''", effects: [{ set: 'applied', to: 'applied + 1' }, { emit: 'pc-applied' }] },
      ],
    },
  ],
  faults: [
    { id: 'rx-defect-clock-restart', name: 'Clock restarts', kind: 'enable-transition', transition: 'rx-renew-restarts-clock' },
    { id: 'gf-defect-creates', name: 'Creates after loss', kind: 'enable-transition', transition: 'gf-create-after-loss' },
    { id: 'ag-defect-anything', name: 'Does anything', kind: 'enable-transition', transition: 'ag-do-anything' },
    { id: 'pc-apply-disabled', name: 'Never applies', kind: 'disable-transition', transition: 'pc-apply' },
  ],
  scenarios: [
    { id: 'rx-renew-in-window', name: 'Renewal in the window', behaviors: ['rx-flow'], steps: [{ at: 0, event: 'rx-renewal', payload: { daysBeforeExpiry: 10 } }] },
    { id: 'gf-lost-then-create', name: 'Lost, then create', behaviors: ['gf-flow'],
      steps: [{ at: 0, event: 'gf-create' }, { at: 1, event: 'gf-plan-change', payload: { toGrandfathered: false } }, { at: 2, event: 'gf-create' }] },
    { id: 'ag-forbidden', name: 'A forbidden attempt', behaviors: ['ag-flow'], steps: [{ at: 0, event: 'ag-attempt', payload: { changesPower: true } }] },
    { id: 'pc-one-request', name: 'One plan change', behaviors: ['pc-flow'], steps: [{ at: 0, event: 'pc-requested', payload: { plan: 'business' } }] },
  ],
  claims: [
    { id: 'chk-continuous-renewal', kind: 'invariant', statement: 'A renewal in the window does not restart the expiry clock.',
      evaluate: { method: 'state-invariant', scenarios: ['rx-renew-in-window'], expr: 'rx-flow.clockRestarts == 0',
        negatives: [{ scenario: 'rx-renew-in-window', faults: ['rx-defect-clock-restart'] }] } },
    { id: 'chk-no-creation-after-loss', kind: 'invariant', statement: 'A tenant that lost its grandfathered status creates no more feature data.',
      evaluate: { method: 'state-invariant', scenarios: ['gf-lost-then-create'], expr: 'gf-flow.featureRecords <= 1',
        negatives: [{ scenario: 'gf-lost-then-create', faults: ['gf-defect-creates'] }] } },
    { id: 'chk-forbidden-refused', kind: 'temporal', statement: 'An agent act that changes a power is refused.',
      evaluate: { method: 'never', scenarios: ['ag-forbidden'], occurs: { event: 'ag-act-done' },
        negatives: [{ scenario: 'ag-forbidden', faults: ['ag-defect-anything'] }] } },
    { id: 'chk-plan-applied', kind: 'temporal', statement: 'A plan change request is applied.',
      evaluate: { method: 'eventually', scenarios: ['pc-one-request'], occurs: { event: 'pc-applied' },
        negatives: [{ scenario: 'pc-one-request', faults: ['pc-apply-disabled'] }] } },
  ],
  integrityRules: [
    { id: 'agent-roles-hold-no-plan-change', severity: 'error', statement: 'No role an agent may hold confers plan-change.',
      rule: 'forall r : role where "agent" in r.holders, forall c in r.capabilities, c not in ["plan-change"]' },
  ],
};

const model = load(JSON.stringify(SPEC, null, 2));
const strength = claimStrength(model);

// clockRestarts == 0 with only a fault incrementing it is holds-by-construction, naming the variable and the fault transition; the status stays verified.
// @evidence claim-strength-names-weak-checks
test('a state invariant whose variable only a fault transition changes holds by construction and names the variable and the transition', () => {
  assert.equal(evaluateClaim(model, 'chk-continuous-renewal').status, 'verified', 'the status itself is unchanged');
  const s = strength.get('chk-continuous-renewal');
  assert.equal(s?.check, 'holds-by-construction');
  assert.deepEqual(s?.details.variables?.map((v) => [v.variable, v.faultTransitions]), [['rx-flow.clockRestarts', ['rx-renew-restarts-clock']]]);
  assert.match(s?.details.check ?? '', /rx-flow\.clockRestarts.*assigned by no nominal transition/);
  assert.deepEqual(s?.details.transitions, ['rx-renew-restarts-clock']);
});

// featureRecords <= 1 over a scenario that creates one record is restated-scenario.
// @evidence claim-strength-names-weak-checks
test('a counter bound equal to what its one scenario produces is a restated scenario', () => {
  assert.equal(evaluateClaim(model, 'chk-no-creation-after-loss').status, 'verified');
  const s = strength.get('chk-no-creation-after-loss');
  assert.equal(s?.check, 'restated-scenario');
  assert.match(s?.details.check ?? '', /gf-flow\.featureRecords.*gf-lost-then-create.*largest value is 1/);
});

// A never claim decided by a guard on event.changesPower is single-trace.
// The payload-driven behavior is self-contained and its free input is named.
// @evidence claim-strength-names-weak-checks claim-strength-grounding
test('a claim decided on one scenario by a literal payload guard is single-trace and self-contained and names the free input', () => {
  assert.equal(evaluateClaim(model, 'chk-forbidden-refused').status, 'verified');
  const s = strength.get('chk-forbidden-refused');
  assert.equal(s?.check, 'single-trace');
  assert.deepEqual(s?.details.scenarios, ['ag-forbidden']);
  assert.equal(s?.grounding, 'self-contained');
  assert.deepEqual(s?.details.free, ['event "ag-attempt" field "changesPower"']);
});

// A behavior that reacts to a contract event is bound, naming the contract and the capability it requires.
// @evidence claim-strength-grounding
test('a behavior that reacts to a contract event is bound and names the capabilities the contract requires', () => {
  const s = strength.get('chk-plan-applied');
  assert.equal(s?.check, 'single-trace');
  assert.equal(s?.grounding, 'bound');
  assert.ok(s?.details.reads?.some((r) => /contract "change-plan", which requires "plan-change"/.test(r)), JSON.stringify(s?.details.reads));
});

// An integrity rule quantifying over every role is bound.
// @evidence claim-strength-grounding
test('an integrity rule over the real roles is bound', () => {
  const s = strength.get('agent-roles-hold-no-plan-change');
  assert.equal(s?.entity, 'integrityRule');
  assert.equal(s?.check, 'integrity');
  assert.equal(s?.grounding, 'bound');
  assert.match(s?.details.grounding ?? '', /every role/);
  assert.equal(strengthCounts(strength).integrityRules.grounding.bound, 1);
});

// A supplied exploration makes a single-trace claim explored and leaves a vacuous claim holds-by-construction.
// @evidence claim-strength-names-weak-checks
test('a trace claim an exhaustive exploration found holding is explored', () => {
  const explored = claimStrength(model, { explored: new Set(['chk-forbidden-refused']) });
  assert.equal(explored.get('chk-forbidden-refused')?.check, 'explored');
  assert.equal(explored.get('chk-continuous-renewal')?.check, 'holds-by-construction', 'exploration does not make a vacuous claim strong');
});

// With the contract outside the baseline the same claim is self-contained.
// @evidence claim-strength-grounding
test('under a baseline a contract the change adds anchors nothing', () => {
  const existing = new Set([...model.entities.keys()].filter((id) => id !== 'change-plan'));
  const s = claimStrength(model, { existing }).get('chk-plan-applied');
  assert.equal(s?.grounding, 'self-contained');
});

// A new never claim over a fault transition gets admit.claim-vacuous and admit.claim-self-contained, both acknowledgeable; the counts include the existing vacuous claim, which is no reason.
// @evidence admit-flags-weak-new-claims
test('admit gives a new vacuous self-contained claim acknowledgeable reasons and only reports existing ones', async () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-strength-'));
  try {
    const specs = path.join(dir, 'specs');
    fs.mkdirSync(path.join(specs, 'harbour'), { recursive: true });
    fs.writeFileSync(path.join(specs, 'harbour', 'spec.jsonc'), JSON.stringify(SPEC, null, 2));
    const claim = { id: 'chk-never-renewed-twice', kind: 'temporal', statement: 'A renewal never restarts the clock (stated over the defect transition).',
      evaluate: { method: 'never', scenarios: ['rx-renew-in-window'], occurs: { transition: 'rx-renew-restarts-clock' },
        negatives: [{ scenario: 'rx-renew-in-window', faults: ['rx-defect-clock-restart'] }] } };
    const r = await runCommand('admit', ['--project', 'harbour', '--ops', JSON.stringify([{ type: 'AddClaim', data: claim }])], { specs });
    assert.equal(r.ok, false);
    assert.equal(r.result.verdict, 'rejected');
    assert.deepEqual(r.result.reasons.map((/** @type {any} */ x) => [x.code, x.id, x.acknowledgeable]), [
      ['admit.claim-self-contained', 'chk-never-renewed-twice', true],
      ['admit.claim-vacuous', 'chk-never-renewed-twice', true],
    ]);
    assert.equal(r.result.reasons.find((/** @type {any} */ x) => x.code === 'admit.claim-vacuous').check, 'holds-by-construction');
    assert.deepEqual(r.result.strength.added.map((/** @type {any} */ a) => [a.id, a.check, a.grounding]), [['chk-never-renewed-twice', 'holds-by-construction', 'self-contained']]);
    assert.equal(r.result.strength.before.claims.check['holds-by-construction'], 1, 'the existing vacuous claim is counted');
    assert.equal(r.result.strength.after.claims.check['holds-by-construction'], 2);
    assert.ok(!r.result.reasons.some((/** @type {any} */ x) => x.id === 'chk-continuous-renewal'), 'an existing claim is never a reason');
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
});
