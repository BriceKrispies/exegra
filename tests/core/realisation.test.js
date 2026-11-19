import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { analyzeSpec } from '../../src/core/analyze.js';
import { initEngine } from '../../src/core/engine.js';
import { machineReadiness } from '../../src/core/readiness-machines.js';
import { effectiveRealisation, effectiveDurability } from '../../src/core/realisation.js';

initEngine();

const FIXED = readFileSync(fileURLToPath(new URL('../fixtures/realisation/spec.jsonc', import.meta.url)), 'utf8');

/** The fixed specification with one textual change, which must apply exactly once. */
function broken(from, to) {
  assert.equal(FIXED.split(from).length - 1, 1, `fixture text occurs once: ${from}`);
  return FIXED.replace(from, to);
}
const errors = (text) => analyzeSpec(text).diagnostics.filter((d) => d.severity === 'error').map((d) => d.code);

test('the fixed fixture has no error and no readiness diagnostic', () => {
  const a = analyzeSpec(FIXED);
  assert.deepEqual(a.diagnostics.filter((d) => d.severity === 'error'), []);
  assert.deepEqual(machineReadiness(a.model), []);
});

test('realisation defaults from the implementation status of the subject and an explicit value wins', () => {
  const m = analyzeSpec(FIXED).model;
  const get = (id) => m.entities.get(id);
  assert.equal(effectiveRealisation(m, get('live')), 'shipped');
  assert.equal(effectiveRealisation(m, get('future')), 'target');
  assert.equal(effectiveRealisation(m, get('ct-built')), 'shipped');
  assert.equal(effectiveRealisation(m, get('ct-planned')), 'target');
  assert.equal(effectiveRealisation(m, get('ct-default')), 'target');
  const d = analyzeSpec(broken('"subject": "planned", "initial": "f-idle", "realisation": "target",', '"subject": "planned", "initial": "f-idle",')).model;
  assert.equal(effectiveRealisation(d, d.entities.get('future')), 'target');
  const w = analyzeSpec(broken('"subject": "built", "initial": "idle", "level"', '"subject": "built", "initial": "idle", "realisation": "target", "level"')).model;
  assert.equal(effectiveRealisation(w, w.entities.get('live')), 'target');
});

const RULES = [
  ['behavior.realisation-subject', 'a machine declared shipped on a not-implemented component', '"initial": "f-idle", "realisation": "target"', '"initial": "f-idle", "realisation": "shipped"'],
  ['contract.deployment-subject', 'a contract declared shipped on a not-implemented component', '"implementedBy": "planned", "deployment": "target"', '"implementedBy": "planned", "deployment": "shipped"'],
  ['storage.durability', 'a memory machine that names a record', '"storage": { "durability": "memory" }', '"storage": { "durability": "memory", "record": "r" }'],
  ['storage.durability', 'a memory machine that creates records', '"storage": { "durability": "memory" }', '"storage": { "durability": "memory", "creates": true }'],
  ['storage.durability', 'a memory machine with a transaction', '"storage": { "durability": "memory" },', '"storage": { "durability": "memory" }, "transaction": { "scope": "transition", "isolation": "serializable" },'],
  ['storage.durability', 'a memory machine with instances stored in a record', '"storage": { "durability": "memory" },', '"storage": { "durability": "memory" }, "instances": { "key": "id", "storedIn": "r" },'],
  ['storage.durability', 'a record machine whose storage names no record', '"storage": { "durability": "memory" }', '"storage": { "key": "id" }, "transaction": { "scope": "transition", "isolation": "serializable" }'],
];

const WITH_RECORD = (text) => text.replace('"events": [', '"records": [ { "id": "r", "name": "R", "owner": "built", "key": ["id"], "fields": [ { "name": "id", "type": "string" } ] } ],\n  "events": [');

for (const [code, what, from, to] of RULES) {
  test(`rule ${code}: ${what} gives exactly that one error`, () => {
    const text = WITH_RECORD(broken(from, to));
    assert.deepEqual(errors(text), [code]);
  });
}

test('a memory machine is held to no storage or transaction readiness rule and a record machine still is', () => {
  const a = analyzeSpec(FIXED).model;
  assert.equal(effectiveDurability(a.entities.get('live')), 'memory');
  // The same machine in a record, with variables and no storage, needs one.
  const text = broken('"storage": { "durability": "memory" },', '"variables": [ { "name": "n", "type": "number", "initial": 0, "repr": "u32" } ],');
  assert.deepEqual(analyzeSpec(text).diagnostics.filter((d) => d.code.startsWith('ready.')).map((d) => d.code).sort(), ['ready.storage-missing', 'ready.transaction-missing']);
});
