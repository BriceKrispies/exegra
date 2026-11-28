// Behavioural composition along the hierarchy (docs/composition.md, WG-5729, part of WG-5697): event interfaces,
// composite behaviour with internal events hidden, declared abstractions checked against their members (member
// sets, several levels, hiding, stuttering, time scale; certificate or boundary counterexample; strength),
// behavioural cuts and environment assumptions, independence from presentation state, order independence, claim
// transfer, and same-subject alternative machines. Each diagnostic has a negative fixture; the self-specification's
// persistence abstractions are checked, before (as a counterexample) and after their correction.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { analyzeSpec } from '../../src/core/analyze.js';
import { initEngine, runEngine, runScenario, engineInput } from '../../src/core/engine.js';
import { call } from '../../src/core/lean.js';
import { evaluateClaim } from '../../src/core/claims.js';
import { project } from '../../src/core/projections.js';
import {
  inferredInterface, interfaceReport, crossReads, eventInterfaces, compositeBehavior, checkAbstraction, behaviorsAtLevels,
  inputWith, environmentReport, scenarioCut, orderIndependence, canonicalTrace, transferClaim, alternativeMachines,
  membersOf, regionOf, describeCounterexample,
} from '../../src/core/composition.js';
import { orderCheck, traceVerdicts } from '../../cli/composition-commands.js';
import { runCommand } from '../../cli/commands.js';
import { readSpecFile } from '../../tools/spec-manifest.js';

initEngine();

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const FIXTURE = path.join(ROOT, 'tests/fixtures/composition/spec.jsonc');
const FIXTURE_TEXT = fs.readFileSync(FIXTURE, 'utf8');
/** @type {any} */
let selfModel = null;
const self = () => (selfModel ??= analyzeSpec(readSpecFile(path.join(ROOT, 'specs/exegra/spec.jsonc'))).model);

/** The fixture as a plain document a test can change (the fixture's comments are whole lines). */
const fixtureDoc = () => JSON.parse(FIXTURE_TEXT.split(/\r?\n/).filter((l) => !l.trim().startsWith('//')).join('\n'));

/** @param {any} doc */
const analyze = (doc) => analyzeSpec(JSON.stringify(doc, null, 2));
/** @param {any} doc */
const modelOf = (doc) => {
  const r = analyze(doc);
  assert.equal(r.errorCount, 0, JSON.stringify(r.diagnostics.filter((d) => d.severity === 'error').map((d) => `${d.code} ${d.message}`)));
  return /** @type {any} */ (r.model);
};
/** @param {any} doc @param {string} code */
const diagnosticsOf = (doc, code) => analyze(doc).diagnostics.filter((d) => d.code === code);
/** @param {any} doc @param {string} id */
const behavior = (doc, id) => doc.behaviors.find((/** @type {any} */ b) => b.id === id);
/** @param {any} doc @param {string} id */
const component = (doc, id) => doc.components.find((/** @type {any} */ c) => c.id === id);

// ---------------------------------------------------------------------------
// Criterion 1: interfaces
// ---------------------------------------------------------------------------

test('the fixture validates, and a composite\'s interface is inferred from its members with the internal events apart', () => {
  const doc = fixtureDoc();
  const r = analyze(doc);
  assert.deepEqual(r.diagnostics.filter((d) => d.severity !== 'info').map((d) => d.code), []);
  const m = modelOf(doc);
  const i = inferredInterface(m, 'store');
  assert.deepEqual(i.inputs, ['put']);
  assert.deepEqual(i.outputs, ['conflicted', 'saved']);
  assert.deepEqual(i.internal, ['put-conflict', 'put-ok', 'put-req']);
  assert.deepEqual(i.behaviors, ['front-flow', 'disk-flow'], 'declared abstractions are not counted as members twice');
  assert.equal(interfaceReport(m, 'store')[0].status, 'inferred');
});

test('a read of another element\'s state that its declared interface does not export is behavior.reads-unexported', () => {
  const doc = fixtureDoc();
  // The writer reads the disk's hash in a guard: a cross-element read through the store's boundary.
  behavior(doc, 'writer-flow').transitions[0].guard = "disk-flow.hash == 't1'";
  // Without a declared interface the read is inferred and reported, not an error.
  assert.deepEqual(diagnosticsOf(doc, 'behavior.reads-unexported'), []);
  const m0 = modelOf(doc);
  const read = crossReads(m0).find((x) => x.reader === 'writer-flow');
  assert.ok(read && read.observable === 'disk-flow.hash' && read.crosses.length === 0);
  assert.deepEqual(inferredInterface(m0, 'store').observables, ['disk-flow.hash']);
  // Declared without the observable: an error naming the read.
  component(doc, 'store').interface = { inputs: ['put'], outputs: ['conflicted', 'saved'], observables: [] };
  const hits = diagnosticsOf(doc, 'behavior.reads-unexported');
  assert.equal(hits.length, 1);
  assert.match(hits[0].message, /"disk-flow\.hash"/);
  assert.match(hits[0].message, /"store"/);
  // Exported: no error.
  component(doc, 'store').interface.observables = ['disk-flow.hash'];
  assert.deepEqual(diagnosticsOf(doc, 'behavior.reads-unexported'), []);
});

test('a declared interface that misses a boundary event, or exports what is not state of its members, is an error', () => {
  const doc = fixtureDoc();
  component(doc, 'store').interface = { inputs: [], outputs: ['saved'], observables: ['disk-flow.nothing', 'writer-flow.done'] };
  assert.equal(diagnosticsOf(doc, 'interface.undeclared-input').length, 1);
  assert.match(diagnosticsOf(doc, 'interface.undeclared-output')[0].message, /"conflicted"/);
  assert.equal(diagnosticsOf(doc, 'interface.observable-unknown').length, 1);
  assert.equal(diagnosticsOf(doc, 'interface.observable-foreign').length, 1);
});

test('once interfaces are declared, an event that belongs to none is event.no-interface', () => {
  const doc = fixtureDoc();
  doc.events.push({ id: 'orphan', name: 'Orphan' });
  assert.deepEqual(diagnosticsOf(doc, 'event.no-interface'), [], 'silent while no interface is declared');
  component(doc, 'store').interface = { inputs: ['put'], outputs: ['conflicted', 'saved'] };
  const hits = diagnosticsOf(doc, 'event.no-interface');
  assert.equal(hits.length, 1);
  assert.match(hits[0].message, /"orphan"/);
  component(doc, 'writer').interface = { outputs: ['orphan'] };
  assert.deepEqual(diagnosticsOf(doc, 'event.no-interface'), []);
});

// ---------------------------------------------------------------------------
// Criterion 3: composite behaviour with hiding, on the engine
// ---------------------------------------------------------------------------

test('a composite\'s derived behaviour is its members run on the engine with the internal events hidden (exact)', () => {
  const m = modelOf(fixtureDoc());
  const r = compositeBehavior(m, 'store', 'writer-at-members');
  assert.equal(r.strength, 'exact');
  assert.deepEqual(r.members, ['front-flow', 'disk-flow']);
  assert.deepEqual(r.hidden, ['put-conflict', 'put-ok', 'put-req']);
  assert.deepEqual(r.boundary.map((/** @type {any} */ s) => s.event), ['go', 'put', 'saved']);
  // The projection is the kernel's trace with the hidden steps removed, in order (I1).
  const trace = runScenario(m, 'writer-at-members');
  assert.deepEqual(r.boundary.map((/** @type {any} */ s) => s.index), trace.steps.filter((/** @type {any} */ s) => !r.hidden.includes(s.event.id)).map((/** @type {any} */ s) => s.index));
  assert.equal(r.hiddenSteps, 2);
});

test('engine.boundary hides events and refuses a call without a trace; hiding twice is hiding the union', () => {
  const m = modelOf(fixtureDoc());
  const trace = runScenario(m, 'writer-at-members');
  const once = call('engine.boundary', { trace, hidden: ['put-req', 'put-ok'] });
  assert.ok(once.ok);
  const evs = (/** @type {any} */ r) => r.value.steps.map((/** @type {any} */ s) => s.event);
  assert.deepEqual(evs(once), ['go', 'put', 'saved']);
  assert.deepEqual(evs(call('engine.boundary', { trace, hidden: [] })), trace.steps.map((/** @type {any} */ s) => s.event.id));
  const bad = call('engine.boundary', { hidden: [] });
  assert.equal(bad.ok, false);
});

test('the self-specification\'s visual edit gives the same boundary trace with persistence at its abstract and at its member cut', () => {
  const m = self();
  const abs = runScenario(m, 'visual-edit-flow');
  const lv = behaviorsAtLevels(m, 'visual-edit-flow', { 'workspace-flow': 'finest' });
  assert.ok(lv.behaviors.includes('persistence-client-flow') && lv.behaviors.includes('dev-server-flow') && lv.behaviors.includes('workspace-disk-flow'));
  assert.ok(!lv.behaviors.includes('workspace-flow'));
  const con = runEngine(inputWith(m, 'visual-edit-flow', lv.behaviors, lv.faults));
  const r = checkAbstraction(m, 'workspace-flow', { scenarios: ['visual-edit-flow'], finest: true });
  assert.equal(r.verdict, 'certificate');
  const hidden = r.runs[0].hidden;
  assert.ok(hidden.includes('write-file-request') && hidden.includes('ws-write') && hidden.includes('ws-write-done'));
  const project1 = (/** @type {any} */ t) => call('engine.boundary', { trace: t, hidden }).ok ? /** @type {any} */ (call('engine.boundary', { trace: t, hidden })).value.steps.map((/** @type {any} */ s) => [s.event, s.time, JSON.stringify(s.payload)]) : null;
  assert.deepEqual(project1(con), project1(abs));
  assert.ok(con.steps.length > abs.steps.length, 'the member cut takes hidden steps the abstract cut does not');
});

// ---------------------------------------------------------------------------
// Criterion 4: refinement along the hierarchy
// ---------------------------------------------------------------------------

test('a declared abstraction refined by its members gives a step correspondence with the hidden steps as stutters: conservative', () => {
  const m = modelOf(fixtureDoc());
  const r = checkAbstraction(m, 'store-flow');
  assert.equal(r.verdict, 'certificate');
  assert.equal(r.strength, 'conservative');
  assert.deepEqual(r.region, ['disk', 'front']);
  const run = r.runs.find((/** @type {any} */ x) => x.scenario === 'writer-at-store');
  assert.deepEqual(run.correspondence.map((/** @type {any} */ c) => c.event), ['go', 'put', 'saved']);
  assert.equal(run.stutters.length, 2, 'put-req and put-ok are stutters of the members');
});

test('an abstraction that disagrees with its members gives the first boundary counterexample and no strength', () => {
  const doc = fixtureDoc();
  behavior(doc, 'store-flow').variables[0].initial = 't9';
  const r = checkAbstraction(modelOf(doc), 'store-flow', { scenarios: ['writer-at-store'] });
  assert.equal(r.verdict, 'counterexample');
  assert.equal(r.strength, null);
  const cx = r.counterexample;
  assert.equal(cx.reason, 'event');
  assert.equal(cx.abstractStep.event, 'conflicted');
  assert.deepEqual(cx.abstractStep.payload, { current: 't9' });
  assert.equal(cx.concreteStep.event, 'saved');
  assert.deepEqual(cx.agreedPrefix.map((/** @type {any} */ s) => s.event), ['go', 'put']);
  assert.match(describeCounterexample(cx), /boundary step 2 differs/);
});

test('abstractions at several levels: checked level by level and against the finest members', () => {
  const m = modelOf(fixtureDoc());
  assert.deepEqual(membersOf(m, 'store-top-flow'), ['store-flow']);
  assert.deepEqual(membersOf(m, 'store-top-flow', { finest: true }), ['front-flow', 'disk-flow']);
  assert.deepEqual(regionOf(m, 'store-top-flow'), ['disk', 'front']);
  const one = checkAbstraction(m, 'store-top-flow');
  const finest = checkAbstraction(m, 'store-top-flow', { finest: true });
  assert.equal(one.verdict, 'certificate');
  assert.equal(finest.verdict, 'certificate');
  assert.equal(finest.strength, 'conservative');
  assert.deepEqual(finest.members, ['front-flow', 'disk-flow']);
});

test('a time scale relates the times of the members to those of the abstraction and a wrong one is a time counterexample', () => {
  const doc = fixtureDoc();
  behavior(doc, 'disk-flow').transitions[0].effects[1].after = 2;
  behavior(doc, 'store-flow').transitions[1].effects[1].after = 1;
  behavior(doc, 'store-flow').abstracts.timeScale = 2;
  const ok = checkAbstraction(modelOf(doc), 'store-flow', { scenarios: ['writer-at-store'] });
  assert.equal(ok.verdict, 'certificate');
  assert.equal(ok.timeScale, 2);
  delete behavior(doc, 'store-flow').abstracts.timeScale;
  const bad = checkAbstraction(modelOf(doc), 'store-flow', { scenarios: ['writer-at-store'] });
  assert.equal(bad.verdict, 'counterexample');
  assert.equal(bad.counterexample.reason, 'time');
});

test('a fault that acts at one level only is left out and makes the strength incomplete; applied per level it breaks the refinement', () => {
  const m = modelOf(fixtureDoc());
  const dropped = checkAbstraction(m, 'store-flow', { scenarios: ['writer-stale-at-store'], faults: ['store-ignores-base'] });
  assert.equal(dropped.verdict, 'certificate');
  assert.equal(dropped.strength, 'incomplete');
  assert.deepEqual(dropped.runs[0].droppedFaults, ['store-ignores-base']);
  const neg = checkAbstraction(m, 'store-flow', { scenarios: ['writer-stale-at-store'], faults: ['store-ignores-base'], perLevelFaults: true });
  assert.equal(neg.verdict, 'counterexample');
});

test('an element of the composite of an abstraction that no running machine covers is opaque: incomplete', () => {
  const doc = fixtureDoc();
  doc.components.push({ id: 'cache', name: 'Cache', category: 'logical', parent: 'store', purpose: 'Holds nothing yet.' });
  const r = checkAbstraction(modelOf(doc), 'store-flow', { scenarios: ['writer-at-store'] });
  assert.equal(r.verdict, 'certificate');
  assert.equal(r.strength, 'incomplete');
  assert.deepEqual(r.runs[0].opaque, ['cache']);
});

test('a member set that leaves out the partner of a member is refuted', () => {
  const doc = fixtureDoc();
  behavior(doc, 'store-flow').abstracts.members = ['front-flow'];
  const m = modelOf(doc);
  const r = checkAbstraction(m, 'store-flow', { scenarios: ['writer-at-store'] });
  assert.equal(r.verdict, 'counterexample', 'the front end alone sends put-req to nobody and never answers');
  assert.equal(r.counterexample.reason, 'abstract-longer');
  assert.deepEqual(regionOf(m, 'store-flow'), ['front']);
});

test('malformed abstractions are refused: members, cycles, subject, hidden events', () => {
  const doc = fixtureDoc();
  behavior(doc, 'store-flow').abstracts = { members: ['store-flow', 'front-flow', 'front-flow'] };
  assert.equal(diagnosticsOf(doc, 'behavior.abstraction-members').length, 2, 'itself, and a member listed twice');
  const cyc = fixtureDoc();
  behavior(cyc, 'store-flow').abstracts.members = ['front-flow', 'store-top-flow'];
  assert.equal(diagnosticsOf(cyc, 'behavior.abstraction-cycle').length >= 1, true);
  const sub = fixtureDoc();
  behavior(sub, 'store-flow').subject = 'writer';
  assert.equal(diagnosticsOf(sub, 'behavior.abstraction-subject').length, 1);
  const hid = fixtureDoc();
  behavior(hid, 'store-flow').abstracts.hide = ['saved', 'start'];
  assert.equal(diagnosticsOf(hid, 'behavior.abstraction-hides-boundary').length, 1);
  assert.equal(diagnosticsOf(hid, 'behavior.abstraction-hides-unknown').length, 1);
});

test('the self-specification\'s persistence abstractions are refined: workspace-flow at both levels, write-endpoint-flow', () => {
  const m = self();
  const one = checkAbstraction(m, 'workspace-flow', { scenarios: ['visual-edit-flow', 'source-edit-flow', 'rejected-edit'] });
  assert.equal(one.verdict, 'certificate');
  assert.equal(one.strength, 'conservative');
  assert.deepEqual(one.members, ['persistence-client-flow', 'write-endpoint-flow']);
  const finest = checkAbstraction(m, 'workspace-flow', { scenarios: ['visual-edit-flow'], finest: true });
  assert.equal(finest.verdict, 'certificate');
  assert.deepEqual(finest.region, ['dev-server-plugin', 'persistence-client', 'workspace-service']);
  const ep = checkAbstraction(m, 'write-endpoint-flow');
  assert.equal(ep.verdict, 'certificate');
  assert.deepEqual(ep.runs.map((/** @type {any} */ r) => r.scenario), ['write-with-stale-base-hash']);
  const neg = checkAbstraction(m, 'write-endpoint-flow', { faults: ['endpoint-ignores-base-hash'], perLevelFaults: true });
  assert.equal(neg.verdict, 'counterexample');
});

test('the persistence check exposes the initial disk-hash mismatch the specification had (h2 against h1) as a counterexample', () => {
  const m = self();
  const ep = /** @type {any} */ (m.entities.get('write-endpoint-flow'));
  const original = ep.data.variables;
  try {
    ep.data.variables = original.map((/** @type {any} */ v) => (v.name === 'diskHash' ? { ...v, initial: 'h2' } : v));
    const r = checkAbstraction(m, 'write-endpoint-flow');
    assert.equal(r.verdict, 'counterexample');
    const cx = r.counterexample;
    assert.equal(cx.abstractStep.event, 'write-file-conflict');
    assert.equal(cx.abstractStep.payload.current, 'h2');
    assert.equal(cx.concreteStep.event, 'write-file-conflict');
    assert.equal(cx.concreteStep.payload.current, 'h1');
    assert.equal(cx.reason, 'payload');
  } finally {
    ep.data.variables = original;
  }
});

// ---------------------------------------------------------------------------
// Criterion 5: behavioural cuts, environment assumptions, presentation state
// ---------------------------------------------------------------------------

test('a scenario\'s cut is declared or inferred, and running a region at another level replaces it by its members', () => {
  const m = modelOf(fixtureDoc());
  assert.deepEqual(scenarioCut(m, 'writer-at-store').regions.map((r) => [r.abstraction, r.level, r.declared]), [['store-flow', 'abstract', true], ['store-top-flow', 'members', false]], 'store-top-flow runs at its members, since its one member runs');
  assert.deepEqual(scenarioCut(m, 'writer-at-members').regions.find((r) => r.abstraction === 'store-flow')?.level, 'members');
  assert.deepEqual(behaviorsAtLevels(m, 'writer-at-store', { 'store-flow': 'members' }).behaviors, ['writer-flow', 'front-flow', 'disk-flow']);
  assert.deepEqual(behaviorsAtLevels(m, 'writer-at-members', { 'store-flow': 'abstract' }).behaviors, ['writer-flow', 'store-flow']);
  assert.deepEqual(behaviorsAtLevels(m, 'writer-at-top', { 'store-top-flow': 'finest' }).behaviors, ['writer-flow', 'front-flow', 'disk-flow']);
});

test('a cut whose regions disagree with the listed behaviours, a region run at two levels, and an environment for a running element are refused', () => {
  const doc = fixtureDoc();
  doc.scenarios.find((/** @type {any} */ s) => s.id === 'writer-at-store').cut.regions[0].level = 'members';
  assert.equal(diagnosticsOf(doc, 'scenario.cut-region').length, 1);
  const both = fixtureDoc();
  both.scenarios.find((/** @type {any} */ s) => s.id === 'writer-at-store').behaviors.push('disk-flow');
  assert.equal(diagnosticsOf(both, 'scenario.levels-overlap').length, 1);
  const env = fixtureDoc();
  env.scenarios.find((/** @type {any} */ s) => s.id === 'writer-front-assumed').cut.environment.push({ element: 'front', events: ['put'] });
  assert.equal(diagnosticsOf(env, 'scenario.environment-element').length, 1);
});

test('an omitted element that receives an event needs an environment assumption', () => {
  const m = modelOf(fixtureDoc());
  const bare = environmentReport(m, 'writer-front-only', runScenario(m, 'writer-front-only'));
  assert.deepEqual(bare.unassumed.map((u) => [u.event, u.receivers]), [['put-req', ['disk']]]);
  const assumed = environmentReport(m, 'writer-front-assumed', runScenario(m, 'writer-front-assumed'));
  assert.deepEqual(assumed.unassumed, []);
  assert.deepEqual(assumed.assumed.map((u) => u.event), ['put-req']);
});

test('no presentation state changes a trace or a refinement verdict or a claim verdict', () => {
  const m = self();
  const before = { trace: runScenario(m, 'visual-edit-flow'), refine: checkAbstraction(m, 'workspace-flow', { scenarios: ['visual-edit-flow'] }).verdict, claim: evaluateClaim(m, 'file-matches-model-after-save').status };
  // Project the architecture view with every subsystem collapsed and with none: views read the model, never set its cut.
  const subsystems = (m.byKind.component ?? []).filter((/** @type {any} */ c) => c.data.kind === 'subsystem').map((/** @type {any} */ c) => c.id);
  for (const collapsed of [new Set(), new Set(subsystems)]) {
    project(m, 'architecture', { collapsed });
    assert.deepEqual(runScenario(m, 'visual-edit-flow'), before.trace);
    assert.equal(checkAbstraction(m, 'workspace-flow', { scenarios: ['visual-edit-flow'] }).verdict, before.refine);
    assert.equal(evaluateClaim(m, 'file-matches-model-after-save').status, before.claim);
  }
  // The engine input is a function of the scenario and its faults alone.
  assert.equal(engineInput.length, 3);
  assert.deepEqual(engineInput(m, 'visual-edit-flow'), engineInput(m, 'visual-edit-flow'));
});

test('simulate runs a region at another level from the command line and refuses an unknown abstraction', async () => {
  const out = await runCommand('simulate', ['writer-at-store', '--spec', FIXTURE, '--level', 'store-flow=members']);
  assert.ok(out.ok, JSON.stringify(out.error));
  assert.deepEqual(out.result.atLevels.behaviors, ['writer-flow', 'front-flow', 'disk-flow']);
  assert.equal(out.result.final.machines['writer-flow'].state, 'w-done');
  const bad = await runCommand('simulate', ['writer-at-store', '--spec', FIXTURE, '--level', 'writer-flow=members']);
  assert.equal(bad.ok, false);
  const refine = await runCommand('refine', ['store-flow', '--spec', FIXTURE]);
  assert.ok(refine.ok);
  assert.equal(refine.result.verdict, 'certificate');
  const iface = await runCommand('interfaces', ['store', '--spec', FIXTURE]);
  assert.deepEqual(iface.result.elements[0].inferred.inputs, ['put']);
});

// ---------------------------------------------------------------------------
// Criterion 7: order independence
// ---------------------------------------------------------------------------

test('the foundations F4 example gives the same trace and verdicts in both listings', () => {
  const m = /** @type {any} */ (analyzeSpec(fs.readFileSync(path.join(ROOT, 'tests/fixtures/behaviour-order/spec.jsonc'), 'utf8')).model);
  const r = orderIndependence(m, 'order-ab', (t) => traceVerdicts(m, t));
  assert.equal(r.orders, 1);
  assert.equal(r.traceDifferences, 0);
  assert.deepEqual(canonicalTrace(runScenario(m, 'order-ab')), canonicalTrace(runScenario(m, 'order-ba')));
});

test('a verdict that depends on the order of behaviours is reported (negative)', () => {
  const m = modelOf(fixtureDoc());
  const r = orderIndependence(m, 'race-ab', (t) => traceVerdicts(m, t));
  assert.equal(r.verdictsIndependent, false);
  assert.deepEqual(r.differences[0].claims, [{ claim: 'first-before-second', original: 'holds', reordered: 'violated' }]);
});

// ---------------------------------------------------------------------------
// Criterion 8: claim transfer
// ---------------------------------------------------------------------------

test('safety over the boundary transfers down a certified refinement and not down a failing one', () => {
  const m = modelOf(fixtureDoc());
  const ok = transferClaim(m, 'save-follows-go', 'store-flow');
  assert.equal(ok.transferred, true);
  assert.equal(ok.rule, 'safety-down-refinement');
  const doc = fixtureDoc();
  behavior(doc, 'store-flow').variables[0].initial = 't9';
  const broken = transferClaim(modelOf(doc), 'save-follows-go', 'store-flow');
  assert.equal(broken.transferred, false);
  assert.match(broken.reason, /fails/);
});

test('liveness never transfers without fairness, and a claim on the abstraction\'s own state is not expressible below it', () => {
  const m = modelOf(fixtureDoc());
  const live = transferClaim(m, 'writer-eventually-done', 'store-flow');
  assert.equal(live.transferred, false);
  assert.match(live.reason, /liveness never transfers/);
  const own = transferClaim(m, 'store-hash-stays-known', 'store-flow');
  assert.equal(own.transferred, false);
  assert.match(own.reason, /not expressible/);
});

// ---------------------------------------------------------------------------
// Criterion 9: one behaviour per element per level
// ---------------------------------------------------------------------------

test('two behaviours of one element that share an event and never run together are alternative machines until related', () => {
  const doc = fixtureDoc();
  doc.behaviors.push({ ...JSON.parse(JSON.stringify(behavior(doc, 'front-flow'))), id: 'front-retry-flow', name: 'Front end, retrying',
    states: [{ id: 'fr-ready', name: 'Ready' }], initial: 'fr-ready',
    transitions: [{ id: 'fr-put', from: 'fr-ready', to: 'fr-ready', on: 'put', effects: [{ emit: 'put-req', payload: { text: 'event.text', base: 'event.base' } }] }] });
  const m = modelOf(doc);
  assert.deepEqual(alternativeMachines(m).map((p) => [p.a, p.b, p.shared]), [['front-flow', 'front-retry-flow', ['put']]]);
  assert.equal(diagnosticsOf(doc, 'gap.alternative-machines').length, 1);
  // Declared as an abstraction of the other, the pair is one behaviour per level.
  behavior(doc, 'front-retry-flow').abstracts = { members: ['front-flow'] };
  assert.deepEqual(alternativeMachines(modelOf(doc)), []);
});

test('the self-specification\'s persistence elements have one behaviour per level, related by checked refinement', () => {
  const m = self();
  const persistence = ['persistence-client', 'dev-server-plugin', 'workspace-service'];
  assert.deepEqual(alternativeMachines(m).filter((p) => persistence.includes(p.subject)), []);
  assert.equal(m.entities.get('write-client-flow'), undefined, 'the retrying client, an abstraction of the session\'s overwrite, is gone');
  for (const id of ['persistence-abstraction-refined', 'persistence-abstraction-refined-finest', 'write-endpoint-abstraction-refined', 'persistence-alternatives-reconciled']) {
    assert.equal(evaluateClaim(m, id).status, 'verified', id);
  }
});

// ---------------------------------------------------------------------------
// The self-specification's claims of WG-5729
// ---------------------------------------------------------------------------
