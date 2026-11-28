import { test } from 'node:test';
import assert from 'node:assert/strict';
import { analyzeSpec } from '../../src/core/analyze.js';
import { evaluateClaims, evaluateClaim } from '../../src/core/claims.js';
import { initEngine } from '../../src/core/engine.js';

initEngine();

// What a verified trace claim says about how it was decided (WG-4830): which transition the declaration order
// chose, what only a script establishes, and what only a fault-only transition can produce.

const SPEC = `{
  "exegra": "0.1",
  "system": { "id": "diag", "name": "Diagnostics" },
  "vocabulary": {
    "properties": [
      { "entity": "claim", "name": "models", "type": "ref", "ref": ["claim"], "label": "Checks requirement" }
    ],
    "verificationMethods": { "scenario": { "label": "Scenario", "description": "Checked by an end-to-end test outside Exegra." } }
  },
  "components": [
    { "id": "a", "name": "A", "category": "computational" },
    { "id": "b", "name": "B", "category": "computational" }
  ],
  "relationships": [ { "id": "r-call", "kind": "calls", "from": "a", "to": "b" } ],
  "events": [
    { "id": "go", "name": "Go" }, { "id": "ack", "name": "Ack" },
    { "id": "a1", "name": "A1" }, { "id": "b1", "name": "B1" },
    { "id": "start", "name": "Start" }, { "id": "mid", "name": "Mid" },
    { "id": "tick", "name": "Tick" }, { "id": "leak", "name": "Leak" }
  ],
  "behaviors": [
    { "id": "m", "name": "M", "subject": "a", "initial": "idle",
      "states": [ { "id": "idle", "name": "Idle" }, { "id": "done", "name": "Done" } ],
      "transitions": [
        { "id": "m-first", "from": "idle", "to": "done", "on": "go", "effects": [ { "emit": "ack" } ] },
        { "id": "m-second", "from": "idle", "to": "done", "on": "go" }
      ] },
    { "id": "q", "name": "Q", "subject": "b", "initial": "q-idle",
      "states": [ { "id": "q-idle", "name": "Idle" }, { "id": "q-sent", "name": "Sent" } ],
      "transitions": [ { "id": "q-start", "from": "q-idle", "to": "q-sent", "on": "start", "effects": [ { "emit": "mid", "after": 1 } ] } ] },
    { "id": "r", "name": "R", "subject": "b", "initial": "ok",
      "states": [ { "id": "ok", "name": "Ok" }, { "id": "bad", "name": "Bad" } ],
      "transitions": [
        { "id": "r-defect", "faultOnly": true, "from": "ok", "to": "bad", "on": "tick", "effects": [ { "emit": "leak" } ] },
        { "id": "r-normal", "from": "ok", "to": "ok", "on": "tick" }
      ] }
  ],
  "faults": [
    { "id": "f-disable-first", "name": "First disabled", "kind": "disable-transition", "transition": "m-first" },
    { "id": "f-drop-a1", "name": "Drop a1", "kind": "drop-event", "event": "a1" },
    { "id": "f-disable-start", "name": "Start disabled", "kind": "disable-transition", "transition": "q-start" },
    { "id": "f-inject-mid", "name": "Mid from nowhere", "kind": "inject-event", "event": "mid", "at": 0 },
    { "id": "f-enable-defect", "name": "Defect on", "kind": "enable-transition", "transition": "r-defect" }
  ],
  "scenarios": [
    { "id": "s-order", "name": "Order", "behaviors": ["m"], "steps": [ { "at": 0, "event": "go" } ] },
    { "id": "s-script", "name": "Script", "behaviors": ["m"], "steps": [ { "at": 0, "event": "a1" }, { "at": 1, "event": "b1" } ] },
    { "id": "s-system", "name": "System", "behaviors": ["q"], "steps": [ { "at": 0, "event": "start" } ] },
    { "id": "s-fault", "name": "Fault", "behaviors": ["r"], "steps": [ { "at": 0, "event": "tick" } ] }
  ],
  "claims": [
    { "id": "req-1", "kind": "requirement", "statement": "The first transition acts.", "evaluate": { "method": "scenario" } },
    { "id": "req-2", "kind": "requirement", "statement": "Nothing leaks.", "evaluate": { "method": "scenario" } },
    { "id": "ord", "kind": "temporal", "statement": "m-first fires.", "models": "req-1",
      "evaluate": { "method": "eventually", "scenarios": ["s-order"], "occurs": { "transition": "m-first" },
        "negatives": [ { "scenario": "s-order", "faults": ["f-disable-first"] } ] } },
    { "id": "pr-script", "kind": "temporal", "statement": "b1 only after a1.",
      "evaluate": { "method": "precedes", "scenarios": ["s-script"], "first": { "event": "a1" }, "then": { "event": "b1" },
        "negatives": [ { "scenario": "s-script", "faults": ["f-drop-a1"] } ] } },
    { "id": "pr-system", "kind": "temporal", "statement": "mid only after q-start.",
      "evaluate": { "method": "precedes", "scenarios": ["s-system"], "first": { "transition": "q-start" }, "then": { "event": "mid" },
        "negatives": [ { "scenario": "s-system", "faults": ["f-disable-start", "f-inject-mid"] } ] } },
    { "id": "nv-leak", "kind": "temporal", "statement": "leak never happens.", "models": "req-2",
      "evaluate": { "method": "never", "scenarios": ["s-fault"], "occurs": { "event": "leak" },
        "negatives": [ { "scenario": "s-fault", "faults": ["f-enable-defect"] } ] } },
    { "id": "inv-const", "kind": "invariant", "statement": "While ok, true.",
      "evaluate": { "method": "state-invariant", "scenarios": ["s-fault"], "expr": "r.state == 'ok' => true" } }
  ]
}`;

/** @param {string} text */
function load(text) {
  const { model, errorCount, diagnostics } = analyzeSpec(text);
  assert.equal(errorCount, 0, JSON.stringify(diagnostics.filter((d) => d.severity === 'error'), null, 1));
  assert.ok(model);
  return model;
}

const model = load(SPEC);
const results = Object.fromEntries(evaluateClaims(model).map((r) => [r.claimId, r]));
const warningCodes = (text) => analyzeSpec(text).diagnostics.filter((d) => d.severity === 'warning').map((d) => d.code);

// Two unguarded transitions on one event warn, and the claim scope names the transition the declaration order chose; a guard removes both.
// @evidence trace-claims-state-how-decided
test('two unguarded transitions on one event are warned about and the result says the order decided', () => {
  assert.ok(warningCodes(SPEC).includes('transition.order-decides'));
  const r = results.ord;
  assert.equal(r.status, 'verified', r.explanation);
  assert.match(r.scope, /Declaration order decided which transition fired: "m-first" fired where "m-second"/);
  // A guard on the later transition leaves it to decide, not the order: neither the warning nor the sentence.
  const guarded = SPEC.replace('{ "id": "m-second", "from": "idle", "to": "done", "on": "go" }', '{ "id": "m-second", "from": "idle", "to": "done", "on": "go", "guard": "time >= 0" }');
  assert.notEqual(guarded, SPEC);
  assert.ok(!warningCodes(guarded).includes('transition.order-decides'));
  assert.doesNotMatch(evaluateClaim(load(guarded), 'ord').scope, /Declaration order decided/);
});

// An ordering between two scripted deliveries is inconclusive; one a transition produces is verified.
// @evidence trace-claims-state-how-decided
test('precedes between two scripted deliveries is not verified and one the system produces is', () => {
  const script = results['pr-script'];
  assert.equal(script.status, 'inconclusive');
  assert.match(script.explanation, /never witnessed by the system/);
  const system = results['pr-system'];
  assert.equal(system.status, 'verified', system.explanation);
  assert.match(system.scope, /produced by the system/);
});

// A never over an occurrence only a faultOnly transition emits says so in its scope; it does not when the scenario enables the fault.
// @evidence trace-claims-state-how-decided
test('a never over an occurrence only a faultOnly transition produces says it holds for fault-free runs', () => {
  const r = results['nv-leak'];
  assert.equal(r.status, 'verified', r.explanation);
  assert.match(r.scope, /can only be produced through faultOnly transition "r-defect"/);
  assert.match(r.scope, /no listed scenario enables it/);
  // A claim whose own scenario enables the defect says nothing of the kind.
  const enabled = SPEC.replace('{ "id": "s-fault", "name": "Fault", "behaviors": ["r"],', '{ "id": "s-fault", "name": "Fault", "behaviors": ["r"], "faults": ["f-enable-defect"],')
    .replace('"negatives": [ { "scenario": "s-fault", "faults": ["f-enable-defect"] } ] } },', '"negatives": [] } },');
  assert.notEqual(enabled, SPEC);
  assert.doesNotMatch(evaluateClaim(load(enabled), 'nv-leak').scope, /faultOnly/);
});

// An implication whose consequent names no state or variable is inconclusive.
// @evidence trace-claims-state-how-decided
test('an implication with a constant consequent is not exercised', () => {
  const r = results['inv-const'];
  assert.equal(r.status, 'inconclusive');
  assert.match(r.explanation, /consequent names no state or variable/);
});

// A requirement result lists the claims whose models property names it with their statuses, and its own status is unchanged.
// @evidence models-property-evaluated
test('a requirement shows the model claims that name it and their statuses', () => {
  assert.deepEqual(results['req-1'].modelledBy, [{ claimId: 'ord', status: 'verified' }]);
  assert.deepEqual(results['req-2'].modelledBy, [{ claimId: 'nv-leak', status: 'verified' }]);
  assert.equal(results.ord.modelledBy, undefined);
  // The same through evaluating the requirement alone.
  assert.deepEqual(evaluateClaim(model, 'req-2').modelledBy, [{ claimId: 'nv-leak', status: 'verified' }]);
  // It is information: the requirement's own status is unchanged.
  assert.equal(results['req-1'].status, 'not-evaluated');
});

// A models value that is not a requirement is the error claim.models-not-requirement.
// @evidence models-property-evaluated
test('a models value that names a claim which is not a requirement is a validation error', () => {
  const bad = SPEC.replace('"models": "req-1"', '"models": "pr-script"');
  const d = analyzeSpec(bad).diagnostics.find((x) => x.code === 'claim.models-not-requirement');
  assert.ok(d, 'reported');
  assert.equal(d.severity, 'error');
  assert.equal(d.entityId, 'ord');
});

// A negative that enables a transition of a behavior its scenario does not run is warned about.
// @evidence claim-parameters-always-validated
test('a negative whose fault targets a transition the scenario does not run is a warning', () => {
  const inert = SPEC.replace('"negatives": [ { "scenario": "s-order", "faults": ["f-disable-first"] } ]', '"negatives": [ { "scenario": "s-order", "faults": ["f-disable-first", "f-enable-defect"] } ]');
  assert.notEqual(inert, SPEC);
  const d = analyzeSpec(inert).diagnostics.find((x) => x.code === 'claim.negative.fault-inert');
  assert.ok(d, 'reported');
  assert.equal(d.severity, 'warning');
  assert.match(d.message, /f-enable-defect/);
  assert.ok(!warningCodes(SPEC).includes('claim.negative.fault-inert'));
});

// A claim parameter error is reported together with an unresolved reference elsewhere.
// @evidence claim-parameters-always-validated
test('claim-parameter errors are reported although another reference is unresolved', () => {
  const broken = SPEC
    .replace('"from": "a", "to": "b" }', '"from": "a", "to": "nowhere" }')
    .replace('"scenarios": ["s-fault"], "expr": "r.state == \'ok\' => true"', '"scenarios": [], "expr": "r.state == \'ok\' => true"');
  assert.notEqual(broken, SPEC);
  const codes = analyzeSpec(broken).diagnostics.filter((d) => d.severity === 'error').map((d) => d.code);
  assert.ok(codes.includes('ref.unresolved'), `the unresolved reference: ${codes}`);
  assert.ok(codes.includes('claim.param.value'), `the claim parameter error: ${codes}`);
});

// The scope of a no-principal-in-shared result states that only declared personal markers are read.
// @evidence data-model-rules-computed
test('no-principal-in-shared says it reads only declared personal markers', () => {
  const text = JSON.stringify({
    exegra: '0.1',
    system: { id: 's', name: 'S' },
    components: [
      { id: 'owner', name: 'Owner', category: 'computational' },
      { id: 'cache', name: 'Cache', category: 'storage' },
    ],
    relationships: [{ id: 'cache-reads-owner', kind: 'reads', from: 'cache', to: 'owner' }],
    // "email" holds personal data but declares no personal marker: the rule cannot see it.
    records: [{ id: 'profile', name: 'Profile', owner: 'owner', key: ['id'], fields: [{ name: 'id', type: 'number' }, { name: 'email', type: 'text' }] }],
    copies: [{ id: 'shared-profile', name: 'Shared profile', of: ['profile'], fields: ['email'], heldBy: 'cache', scope: 'shared', freshness: { bound: 5, unit: 'second' } }],
    claims: [{ id: 'none-shared', kind: 'structural', statement: 'No shared copy names a principal.', evaluate: { method: 'data-model', rules: ['no-principal-in-shared'] } }],
  });
  const r = evaluateClaim(load(text), 'none-shared');
  assert.equal(r.status, 'verified', r.explanation);
  assert.match(r.scope, /read only the personal markers the model declares/);
  assert.match(r.scope, /not that it holds no personal data/);
});
