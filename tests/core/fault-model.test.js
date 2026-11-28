import { test } from 'node:test';
import assert from 'node:assert/strict';
import { analyzeSpec } from '../../src/core/analyze.js';
import { evaluateClaim } from '../../src/core/claims.js';
import { initEngine } from '../../src/core/engine.js';
import { Project } from '../../src/core/project.js';
import { engineInput } from '../../src/core/engine.js';

initEngine();

const SPEC = `{
  "exegra": "0.1",
  "system": { "id": "sys", "name": "Sys" },
  "vocabulary": {
    "entityKinds": {
      "constraint": { "label": "Constraint", "section": "constraints", "properties": { "statement": { "type": "text", "required": true } } }
    }
  },
  "components": [
    { "id": "svc", "name": "Service", "category": "computational", "purpose": "Serves." }
  ],
  "constraints": [ { "id": "k-1", "statement": "Runs in two zones." } ],
  "assumptions": [ { "id": "a-rate", "statement": "Hosts crash about twice a year." } ],
  "environments": [
    { "id": "env", "name": "Cloud", "guarantees": [
      { "aspect": "zone-count", "value": 2, "source": "k-1" },
      { "aspect": "clock-skew", "value": 200, "unit": "ms", "source": "a-rate" } ] }
  ],
  "failureModes": [
    { "id": "fm-crash", "name": "Host crash", "kind": "crash", "target": "svc", "scope": "host",
      "rate": { "value": 2, "per": "year", "source": "a-rate" }, "duration": { "typical": 30, "max": 120, "unit": "second", "source": "a-rate" } },
    { "id": "fm-lag", "name": "Message lag", "kind": "delay", "target": "env", "scope": "zone",
      "rate": { "value": 1, "per": "month", "source": "k-1" } }
  ],
  "faultModels": [
    { "id": "fmod", "name": "Cloud faults", "environment": "env", "modes": ["fm-crash"],
      "bounds": [ { "scope": "host", "maxConcurrent": 1, "source": "k-1" } ] }
  ],
  "events": [ { "id": "ping", "name": "Ping" } ],
  "behaviors": [
    { "id": "b", "name": "B", "subject": "svc", "initial": "up", "variables": [ { "name": "n", "type": "number", "initial": 0 } ],
      "states": [ { "id": "up", "name": "Up" } ],
      "transitions": [ { "id": "t", "from": "up", "to": "up", "on": "ping", "effects": [ { "set": "n", "to": 1 } ] } ] }
  ],
  "faults": [
    { "id": "f-drop", "name": "Drop ping", "kind": "drop-event", "event": "ping", "realises": "fm-crash" },
    { "id": "f-late", "name": "Late ping", "kind": "delay-event", "event": "ping", "by": 2, "realises": "fm-lag" }
  ],
  "scenarios": [
    { "id": "sc", "name": "Sc", "behaviors": ["b"], "faultModel": "fmod", "faults": ["f-drop"], "steps": [ { "at": 0, "event": "ping" } ] }
  ],
  "claims": [
    { "id": "c-inv", "kind": "invariant", "statement": "n stays small.", "faultModel": "fmod",
      "evaluate": { "method": "state-invariant", "scenarios": ["sc"], "expr": "b.n <= 1" } },
    { "id": "c-bare", "kind": "invariant", "statement": "n stays small, unscoped.",
      "evaluate": { "method": "state-invariant", "scenarios": ["sc"], "expr": "b.n <= 1" } },
    { "id": "c-ext", "kind": "measured", "statement": "Measured elsewhere.", "faultModel": "fmod", "evaluate": { "method": "external-evidence" } }
  ]
}`;

const load = (text) => analyzeSpec(text);
const codes = (a, sev) => a.diagnostics.filter((d) => d.severity === sev).map((d) => d.code);
const variant = (from, to) => { assert.ok(SPEC.includes(from), from); return SPEC.replace(from, to); };

// Missing sources and wrong enums are errors; renames and deletes follow references through the new properties, including the any-kind source; gap.no-fault-model and the realises-outside-model warning are reported; a claim result's scope begins with the fault model; realises never reaches the engine input.
// @evidence fault-model-scoped-claims #
test('a complete fault model parses and validates without errors', () => {
  const a = load(SPEC);
  assert.deepEqual(a.diagnostics.filter((d) => d.severity === 'error'), []);
  assert.equal(a.model.byKind.faultModel.length, 1);
  assert.equal(a.model.byKind.failureMode.length, 2);
});

test('a missing source is an error on rate, duration, guarantee and bound', () => {
  assert.ok(codes(load(variant('"rate": { "value": 2, "per": "year", "source": "a-rate" }', '"rate": { "value": 2, "per": "year" }')), 'error').includes('failure-mode.no-rate-source'));
  assert.ok(codes(load(variant('"max": 120, "unit": "second", "source": "a-rate"', '"max": 120, "unit": "second"')), 'error').includes('failure-mode.no-duration-source'));
  assert.ok(codes(load(variant('"value": 2, "source": "k-1"', '"value": 2')), 'error').includes('environment.guarantee-no-source'));
  assert.ok(codes(load(variant('"maxConcurrent": 1, "source": "k-1"', '"maxConcurrent": 1')), 'error').includes('fault-model.bound-no-source'));
  const noRate = load(variant('"rate": { "value": 2, "per": "year", "source": "a-rate" }, ', ''));
  assert.ok(codes(noRate, 'error').includes('failure-mode.no-rate-source'));
});

test('wrong enums and wrong or unresolved refs are errors', () => {
  assert.ok(codes(load(variant('"kind": "crash"', '"kind": "explode"')), 'error').includes('property.enum'));
  assert.ok(codes(load(variant('"aspect": "zone-count"', '"aspect": "weather"')), 'error').includes('property.enum'));
  assert.ok(codes(load(variant('"scope": "host", "maxConcurrent"', '"scope": "planet", "maxConcurrent"')), 'error').includes('property.enum'));
  assert.ok(codes(load(variant('"value": 2, "source": "k-1"', '"value": 2, "source": "nowhere"')), 'error').includes('ref.unresolved'));
  assert.ok(codes(load(variant('"target": "svc"', '"target": "ping"')), 'error').includes('ref.kind'));
  assert.ok(codes(load(variant('"faultModel": "fmod", "evaluate": { "method": "external-evidence" }', '"faultModel": "env", "evaluate": { "method": "external-evidence" }')), 'error').includes('ref.kind'));
});

test('a source may be an entity of any kind, including a declared kind', () => {
  const a = load(SPEC);
  const via = a.model.refs.filter((r) => r.allowed.includes('*')).map((r) => r.target);
  assert.ok(via.includes('k-1') && via.includes('a-rate'));
  assert.deepEqual(a.diagnostics.filter((d) => d.severity === 'error'), []);
});

test('renaming a source rewrites every reference through the new properties', () => {
  const p = new Project({ specText: SPEC });
  const r = p.apply({ type: 'RenameEntity', id: 'k-1', newId: 'k-one' });
  assert.equal(r.ok, true, r.message);
  assert.equal(p.errorCount, 0);
  assert.ok(!p.specText.includes('"k-1"'));
  assert.ok(p.specText.includes('"source": "k-one"'));
  const r2 = p.apply({ type: 'RenameEntity', id: 'fm-crash', newId: 'fm-host-crash' });
  assert.equal(r2.ok, true, r2.message);
  assert.equal(p.errorCount, 0);
  assert.ok(p.specText.includes('"realises": "fm-host-crash"'));
});

test('deleting a referenced source or failure mode is refused; cascading a source away is rejected, a failure mode cascades', () => {
  const p = new Project({ specText: SPEC });
  assert.equal(p.apply({ type: 'DeleteEntity', id: 'k-1' }).ok, false);
  assert.equal(p.apply({ type: 'DeleteEntity', id: 'fm-crash' }).ok, false);
  assert.equal(p.apply({ type: 'DeleteEntity', id: 'fmod' }).ok, false);
  // Cascading away the only source of a rate would leave the value unsourced: the transaction is
  // rejected atomically, with the diagnostic that says why, and nothing changes.
  const before = p.specText;
  const refused = p.apply({ type: 'DeleteEntity', id: 'k-1', cascade: true });
  assert.equal(refused.ok, false);
  assert.ok(refused.diagnostics.some((d) => d.code === 'failure-mode.no-rate-source'), JSON.stringify(refused.diagnostics));
  assert.equal(p.specText, before);
  // A failure mode can be cascaded out of the fault models and faults that name it.
  const c = p.apply({ type: 'DeleteEntity', id: 'fm-crash', cascade: true });
  assert.equal(c.ok, true, c.message);
  assert.equal(p.errorCount, 0);
  assert.equal(p.model?.entities.has('fm-crash'), false);
});

test('gap.no-fault-model is info on claims without one, and only when a fault model exists', () => {
  const a = load(SPEC);
  const gaps = a.diagnostics.filter((d) => d.code === 'gap.no-fault-model');
  assert.deepEqual(gaps.map((d) => d.entityId), ['c-bare']);
  assert.equal(gaps[0].severity, 'info');
  const bare = load(`{ "exegra": "0.1", "system": { "id": "s", "name": "S" },
    "claims": [ { "id": "c", "kind": "invariant", "statement": "x", "evaluate": { "method": "external-evidence" } } ] }`);
  assert.equal(bare.diagnostics.filter((d) => d.code === 'gap.no-fault-model').length, 0);
});

test('a fault realising a mode outside its scenario fault model is a warning', () => {
  const a = load(variant('"faults": ["f-drop"]', '"faults": ["f-drop", "f-late"]'));
  const w = a.diagnostics.filter((d) => d.code === 'scenario.fault-outside-model');
  assert.equal(w.length, 1);
  assert.equal(w[0].severity, 'warning');
  assert.equal(w[0].entityId, 'sc');
  assert.equal(load(SPEC).diagnostics.filter((d) => d.code === 'scenario.fault-outside-model').length, 0);
});

test('a claim result states the fault model in its scope, for every method', () => {
  const { model } = load(SPEC);
  const inv = evaluateClaim(model, 'c-inv');
  assert.ok(inv.scope.startsWith('Under fault model Cloud faults (1 failure mode; bounds: at most 1 host-scoped failures at once).'), inv.scope);
  assert.match(inv.explanation, /inject 1 of its 1/);
  const ext = evaluateClaim(model, 'c-ext');
  assert.ok(ext.scope.startsWith('Under fault model Cloud faults'), ext.scope);
  const bare = evaluateClaim(model, 'c-bare');
  assert.ok(!bare.scope.includes('fault model'), bare.scope);
});

test('a fault realises does not reach the engine input', () => {
  const { model } = load(SPEC);
  const input = engineInput(model, 'sc');
  assert.ok(!JSON.stringify(input).includes('realises'));
  assert.ok(!JSON.stringify(input).includes('fmod'));
});
