// Transition and guard coverage of shipped machines (WG-4965, src/core/machine-coverage.js, docs/coverage.md). The
// fixture's door has one scenario; the search generates the scenarios for the rest, and t-unjam, whose source state
// nothing enters, is the unreachable transition.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { parse } from 'jsonc-parser';
import { analyzeSpec } from '../../src/core/analyze.js';
import { initEngine } from '../../src/core/engine.js';
import { shippedMachines, machineItems, exercisedItems, machineCoverage, coverageOperations, COVERAGE_TAG } from '../../src/core/machine-coverage.js';
import { runCommand } from '../../cli/commands.js';

initEngine();

const FIXTURE = fs.readFileSync(new URL('../fixtures/machine-coverage/spec.jsonc', import.meta.url), 'utf8');
const model = (/** @type {string} */ text) => /** @type {any} */ (analyzeSpec(text).model);
/** The fixture as a plain document. */
const doc = () => parse(FIXTURE);
/** @param {any} d */
const text = (d) => JSON.stringify(d, null, 2);

/** The coverage of the fixture, searched once for the tests that read it. @type {any} */
let baseCoverage;
const base = () => (baseCoverage ??= machineCoverage(model(FIXTURE)));

test('the fixture validates and its one machine is shipped', () => {
  const a = analyzeSpec(FIXTURE);
  assert.deepEqual(a.diagnostics.filter((d) => d.severity === 'error'), []);
  assert.deepEqual(shippedMachines(/** @type {any} */ (a.model)).map((b) => b.id), ['door']);
});

test('the items are the transitions and both outcomes of each guard', () => {
  const m = model(FIXTURE);
  const { items } = machineItems(m, m.entities.get('door'));
  assert.deepEqual(items, ['t:t-open', 'g:t-open:true', 'g:t-open:false', 't:t-open-else', 't:t-close', 't:t-lock', 't:t-unjam']);
});

test('a guard is false when a later transition of the same state and event fires', () => {
  const m = model(FIXTURE);
  const { transitions } = machineItems(m, m.entities.get('door'));
  const trace = { steps: [{ kind: 'deliver', event: { id: 'ev-code' }, fired: [{ behavior: 'door', transition: 't-open-else', from: 'closed' }], ignored: [] }] };
  assert.deepEqual([...exercisedItems(transitions, 'door', trace)].sort(), ['g:t-open:false', 't:t-open-else']);
  const ignored = { steps: [{ kind: 'deliver', event: { id: 'ev-code' }, fired: [], ignored: [{ behavior: 'door', reason: 'guard-false', considered: ['t-open'] }] }] };
  assert.deepEqual([...exercisedItems(transitions, 'door', ignored)], ['g:t-open:false']);
});

test('the scenario covers what it delivers and the search covers the rest and reports the unreachable transition', () => {
  const { machines, findings } = base();
  assert.equal(machines.length, 1);
  const door = machines[0];
  assert.deepEqual(door.transitions, { covered: 4, total: 5, byScenarios: 1 });
  assert.deepEqual(door.guards, { covered: 2, total: 2, byScenarios: 1 });
  const by = Object.fromEntries(door.items.map((i) => [i.item, i.by]));
  assert.equal(by['t:t-open-else'], 'short-code');
  assert.equal(by['g:t-open:false'], 'short-code');
  assert.equal(by['t:t-unjam'], null);
  for (const it of ['t:t-open', 'g:t-open:true', 't:t-close', 't:t-lock']) assert.match(String(by[it]), /^cover-door-\d+$/, it);
  assert.deepEqual(door.generated.flatMap((g) => g.covers).sort(), ['g:t-open:true', 't:t-close', 't:t-lock', 't:t-open']);
  // The lock needs a wait for its timer: the timer fires after 30 ms.
  assert.ok(door.generated.some((g) => g.covers.includes('t:t-lock')));
  assert.deepEqual(findings.map((f) => [f.code, f.severity, f.entityId]), [['machine.transition-unreachable', 'warning', 't-unjam']]);
  assert.match(findings[0].message, /source state "jammed" is entered by no transition/);
});

test('a bound too small to reach a transition is reported as unreachable within that bound', () => {
  const { findings } = machineCoverage(model(FIXTURE), { bound: 1 });
  const close = findings.find((f) => f.entityId === 't-close');
  assert.ok(close, 'with one action the door cannot be opened and closed');
  assert.match(close.message, /within that bound/);
});

test('the generated scenarios added through their operations cover everything the search found', () => {
  const m = model(FIXTURE);
  const { machines } = base();
  const ops = coverageOperations(m, machines);
  assert.ok(ops.length >= 2);
  for (const op of ops) {
    assert.equal(op.type, 'CreateEntity');
    assert.equal(op.kind, 'scenario');
    assert.match(op.data.id, /^cover-door-\d+$/);
    assert.deepEqual(op.data.tags, [COVERAGE_TAG]);
    assert.deepEqual(op.data.behaviors, ['door']);
  }
  const d = doc();
  d.scenarios.push(...ops.map((o) => o.data));
  const after = analyzeSpec(text(d));
  assert.deepEqual(after.diagnostics.filter((x) => x.severity === 'error'), []);
  const again = machineCoverage(/** @type {any} */ (after.model)).machines[0];
  assert.deepEqual(again.transitions, { covered: 4, total: 5, byScenarios: 4 });
  assert.deepEqual(again.guards, { covered: 2, total: 2, byScenarios: 2 });
  assert.deepEqual(again.generated, []);
});

test('a door without the jammed state is fully covered and has no finding', () => {
  const d = doc();
  const door = d.behaviors[0];
  door.states = door.states.filter((/** @type {any} */ s) => s.id !== 'jammed');
  door.transitions = door.transitions.filter((/** @type {any} */ t) => t.id !== 't-unjam');
  for (const s of door.states) s.ignores = s.ignores.filter((/** @type {string} */ e) => e !== 'ev-reset');
  d.events = d.events.filter((/** @type {any} */ e) => e.id !== 'ev-reset');
  const { machines, findings } = machineCoverage(model(text(d)));
  assert.deepEqual(findings, []);
  assert.deepEqual(machines[0].transitions, { covered: 4, total: 4, byScenarios: 1 });
  assert.deepEqual(machines[0].guards, { covered: 2, total: 2, byScenarios: 1 });
});

test('cover-machines reports the table and the finding and writes ops.json that apply accepts', async () => {
  const specs = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-cover-'));
  try {
    fs.mkdirSync(path.join(specs, 'doors'));
    fs.writeFileSync(path.join(specs, 'doors', 'spec.jsonc'), FIXTURE, 'utf8');
    const out = path.join(specs, 'out');
    const r = await runCommand('cover-machines', ['--write', out], { specs, project: 'doors' });
    assert.equal(r.ok, true, JSON.stringify(r.error));
    assert.deepEqual(r.result.table.map((/** @type {any} */ t) => [t.machine, t.transitions, t.guards]), [['door', '4/5', '2/2']]);
    assert.deepEqual(r.result.findings.map((/** @type {any} */ f) => f.code), ['machine.transition-unreachable']);
    const file = path.join(out, 'ops.json');
    assert.equal(r.result.written.file, file);
    const applied = await runCommand('apply', ['--file', file], { specs, project: 'doors' });
    assert.equal(applied.ok, true, JSON.stringify(applied.error));
  } finally {
    fs.rmSync(specs, { recursive: true, force: true });
  }
});
