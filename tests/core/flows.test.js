// Message flows of a simulation step (src/core/flows.js): the sender and
// receivers come from the trace, and the path through a scene follows an edge
// only when one connects the two drawn nodes.
import test from 'node:test';
import assert from 'node:assert/strict';
import { analyzeSpec } from '../../src/core/analyze.js';
import { initEngine, runScenario } from '../../src/core/engine.js';
import { project, listViews } from '../../src/core/projections.js';
import { stepFlow, flowPaths, describeFlow } from '../../src/core/flows.js';

initEngine();

/**
 * A client calls a server (declared); the server answers (against the edge's
 * direction); the client then tells an auditor nothing connects it to (undeclared);
 * the auditor notes it to an archive in the same subsystem.
 */
function spec() {
  const machine = (id, subject, initial, transitions) => ({
    id, name: id, subject, initial,
    states: [...new Set(transitions.flatMap((t) => [t.from, t.to]))].map((s) => ({ id: `${id}-${s}`, name: s })),
    transitions: transitions.map((t) => ({ ...t, id: `${id}-${t.id}`, from: `${id}-${t.from}`, to: `${id}-${t.to}` })),
  });
  return {
    exegra: '0.1',
    system: { id: 'flows', name: 'Flows' },
    components: [
      { id: 'client', name: 'Client', category: 'logical' },
      { id: 'server', name: 'Server', category: 'logical' },
      { id: 'records', name: 'Records', category: 'logical', kind: 'subsystem' },
      { id: 'auditor', name: 'Auditor', category: 'logical', parent: 'records' },
      { id: 'archive', name: 'Archive', category: 'storage', parent: 'records' },
    ],
    relationships: [{ id: 'client-calls-server', kind: 'calls', from: 'client', to: 'server' }],
    events: ['start', 'ping', 'pong', 'tell', 'note'].map((id) => ({ id, name: id[0].toUpperCase() + id.slice(1) })),
    behaviors: [
      machine('client-m', 'client', 'client-m-idle', [
        { id: 'send', from: 'idle', to: 'waiting', on: 'start', effects: [{ emit: 'ping', after: 1 }] },
        { id: 'got', from: 'waiting', to: 'done', on: 'pong', effects: [{ emit: 'tell', after: 1 }] },
      ]),
      machine('server-m', 'server', 'server-m-up', [{ id: 'answer', from: 'up', to: 'served', on: 'ping', effects: [{ emit: 'pong', after: 1 }] }]),
      machine('auditor-m', 'auditor', 'auditor-m-idle', [{ id: 'hear', from: 'idle', to: 'heard', on: 'tell', effects: [{ emit: 'note', after: 1 }] }]),
      machine('archive-m', 'archive', 'archive-m-empty', [{ id: 'keep', from: 'empty', to: 'kept', on: 'note' }]),
    ],
    faults: [{ id: 'lose-ping', name: 'Lose ping', kind: 'drop-event', event: 'ping' }],
    scenarios: [
      { id: 'round-trip', name: 'Round trip', behaviors: ['client-m', 'server-m', 'auditor-m', 'archive-m'], steps: [{ at: 0, event: 'start' }] },
      { id: 'lost-ping', name: 'Lost ping', behaviors: ['client-m', 'server-m', 'auditor-m', 'archive-m'], steps: [{ at: 0, event: 'start' }], faults: ['lose-ping'] },
    ],
  };
}

function setup(scenarioId = 'round-trip', viewOptions = {}) {
  const { model, diagnostics, errorCount } = analyzeSpec(JSON.stringify(spec()));
  assert.equal(errorCount, 0, JSON.stringify(diagnostics.filter((d) => d.severity === 'error')));
  assert.ok(model);
  const trace = runScenario(model, scenarioId);
  const view = listViews(model).find((v) => v.projection === 'structural');
  assert.ok(view);
  const scene = project(model, view.id, viewOptions);
  return { model, trace, scene };
}

test('each step names its sender from the trace and its receivers from the behaviors that fired', () => {
  const { model, trace } = setup();
  const flows = trace.steps.map((s) => stepFlow(model, s));
  assert.deepEqual(flows.map((f) => [f.event, f.from, f.to.map((r) => r.component)]), [
    ['start', null, ['client']],
    ['ping', 'client', ['server']],
    ['pong', 'server', ['client']],
    ['tell', 'client', ['auditor']],
    ['note', 'auditor', ['archive']],
  ]);
  assert.deepEqual(flows[0].origin, { kind: 'scenario', step: 0 });
  assert.deepEqual(flows[1].origin, { kind: 'behavior', behavior: 'client-m' });
  assert.equal(flows[1].to[0].transition, 'server-m-answer');
});

test('a path follows the scene edge between the two drawn nodes, in either direction, and never an unrelated one', () => {
  const { model, trace, scene } = setup();
  const paths = trace.steps.map((s) => flowPaths(model, scene, stepFlow(model, s)));
  assert.deepEqual(paths[0], [{ kind: 'enter', to: 'client' }], 'a scenario stimulus enters from outside');
  assert.deepEqual(paths[1], [{ kind: 'edge', from: 'client', to: 'server', edgeId: 'client-calls-server', reverse: false }]);
  assert.deepEqual(paths[2], [{ kind: 'edge', from: 'server', to: 'client', edgeId: 'client-calls-server', reverse: true }], 'an answer runs back along the call');
  assert.deepEqual(paths[3], [{ kind: 'undeclared', from: 'client', to: 'auditor' }], 'no relationship connects them, so no edge is borrowed');
  assert.deepEqual(paths[4], [{ kind: 'undeclared', from: 'auditor', to: 'archive' }]);
  assert.match(describeFlow(model, stepFlow(model, trace.steps[3]), paths[3]), /^tell: Client → Auditor \(1 without a declared relationship\)$/);
  assert.match(describeFlow(model, stepFlow(model, trace.steps[0]), paths[0]), /^start: outside \(scenario\) → Client$/);
});

test('a collapsed subsystem stands for its members, and a dropped event is lost after leaving its sender', () => {
  const collapsed = setup('round-trip', { collapsed: new Set(['records']) });
  const tell = flowPaths(collapsed.model, collapsed.scene, stepFlow(collapsed.model, collapsed.trace.steps[3]));
  assert.deepEqual(tell, [{ kind: 'undeclared', from: 'client', to: 'records' }], 'the auditor is drawn as its collapsed subsystem');
  const note = flowPaths(collapsed.model, collapsed.scene, stepFlow(collapsed.model, collapsed.trace.steps[4]));
  assert.deepEqual(note, [{ kind: 'local', node: 'records' }], 'both ends inside one collapsed node');

  const lost = setup('lost-ping');
  const drop = lost.trace.steps[1];
  assert.equal(drop.kind, 'drop');
  const flow = stepFlow(lost.model, drop);
  assert.deepEqual(flow.to, []);
  assert.deepEqual(flowPaths(lost.model, lost.scene, flow), [{ kind: 'lost', from: 'client' }]);
  assert.match(describeFlow(lost.model, flow, []), /dropped by a fault before delivery/);
});

test('a declared relationship the view does not draw is reported as such, not as undeclared', () => {
  const { model, trace, scene } = setup();
  const noEdges = { ...scene, edges: [] };
  const ping = stepFlow(model, trace.steps[1]);
  const paths = flowPaths(model, noEdges, ping);
  assert.deepEqual(paths, [{ kind: 'unshown', from: 'client', to: 'server', relationship: 'client-calls-server' }]);
  assert.match(describeFlow(model, ping, paths), /1 along a relationship this view does not draw/);
});

test('components the scene does not draw give no path', () => {
  const { model, trace, scene } = setup();
  const without = { ...scene, nodes: scene.nodes.filter((n) => n.id !== 'server') };
  assert.deepEqual(flowPaths(model, without, stepFlow(model, trace.steps[1])), []);
});

test('a hop is classified against the derived model, so collapsing never lends it an edge another relationship witnesses', () => {
  const doc = spec();
  doc.relationships.push({ id: 'client-calls-archive', kind: 'calls', from: 'client', to: 'archive' });
  const { model, errorCount } = analyzeSpec(JSON.stringify(doc));
  assert.equal(errorCount, 0);
  const trace = runScenario(/** @type {any} */ (model), 'round-trip');
  const view = listViews(/** @type {any} */ (model)).find((v) => v.projection === 'structural');
  const tell = stepFlow(/** @type {any} */ (model), trace.steps[3]);
  const expanded = project(/** @type {any} */ (model), /** @type {any} */ (view).id, {});
  const collapsed = project(/** @type {any} */ (model), /** @type {any} */ (view).id, { collapsed: new Set(['records']) });
  assert.ok(collapsed.edges.some((e) => e.from === 'client' && e.to === 'records'), 'the collapsed scene draws client -> records, witnessed by client-calls-archive');
  assert.deepEqual(flowPaths(/** @type {any} */ (model), expanded, tell), [{ kind: 'undeclared', from: 'client', to: 'auditor' }]);
  assert.deepEqual(flowPaths(/** @type {any} */ (model), collapsed, tell), [{ kind: 'undeclared', from: 'client', to: 'records' }], 'no relationship joins the client and the auditor, collapsed or not');
});
