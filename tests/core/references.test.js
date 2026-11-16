// The references projection: follows references between any entities, including
// kinds a specification declares itself, without knowing anything about them.
import test from 'node:test';
import assert from 'node:assert/strict';
import { analyzeSpec } from '../../src/core/analyze.js';
import { listViews, project } from '../../src/core/projections.js';

const SPEC = `{
  "exegra": "0.1",
  "system": { "id": "sys", "name": "Sys" },
  "vocabulary": {
    "entityKinds": {
      "goal": { "label": "Goal", "section": "goals", "shape": "diamond", "color": "green",
        "properties": { "statement": { "type": "text", "required": true }, "stage": { "type": "enum", "values": ["r1", "r2"] } } },
      "boundary": { "label": "Boundary", "section": "boundaries", "shape": "hex", "color": "teal",
        "properties": { "name": { "type": "string", "required": true }, "providedBy": { "type": "list", "items": { "type": "ref", "ref": ["component"] } } } }
    },
    "properties": [
      { "entity": "claim", "name": "traces", "type": "list", "items": { "type": "ref", "ref": ["goal"] }, "label": "Traces to" },
      { "entity": "claim", "name": "boundary", "type": "ref", "ref": "boundary", "label": "Stated at" },
      { "entity": "claim", "name": "dependsOn", "type": "list", "items": { "type": "ref", "ref": ["claim"] } }
    ],
    "verificationMethods": { "property": { "label": "Property test", "description": "Checked by a property-based test outside Exegra." } }
  },
  "components": [
    { "id": "kernel", "name": "Kernel", "category": "logical", "purpose": "Decides." },
    { "id": "store", "name": "Store", "category": "storage", "purpose": "Keeps." }
  ],
  "relationships": [ { "id": "r1", "kind": "calls", "from": "kernel", "to": "store" } ],
  "goals": [
    { "id": "g-1", "statement": "Decisions are deterministic.", "stage": "r1" },
    { "id": "g-2", "statement": "State survives restarts.", "stage": "r2" }
  ],
  "boundaries": [ { "id": "b-17", "name": "Kernel API", "providedBy": ["kernel"] } ],
  "claims": [
    { "id": "krn-002", "kind": "requirement", "statement": "Same input, same output.", "subjects": ["kernel"],
      "traces": ["g-1"], "boundary": "b-17", "evaluate": { "method": "property" } },
    { "id": "krn-003", "kind": "requirement", "statement": "Stored state is read back unchanged.", "subjects": ["store"],
      "traces": ["g-2"], "dependsOn": ["krn-002"], "evaluate": { "method": "property" } }
  ]
}`;

const VIEWS = `"views": [
    { "id": "deep", "name": "Deep", "projection": "references", "display": { "depth": 2 } },
    { "id": "goals-only", "name": "Goals only", "projection": "references", "display": { "depth": 2 }, "filter": { "entityKinds": ["goal"] } }
  ],
  "components"`;

function build(text = SPEC) {
  const { model, errorCount, diagnostics } = analyzeSpec(text);
  assert.equal(errorCount, 0, JSON.stringify(diagnostics.filter((d) => d.severity === 'error')));
  assert.ok(model);
  return model;
}

const ids = (list) => list.map((x) => x.id).sort();

test('focus on a requirement at depth 1 draws its goal, boundary and subject, and what refers to it', () => {
  const model = build();
  const scene = project(model, 'references', { focusEntity: 'krn-002' });
  assert.equal(scene.projection, 'references');
  // krn-003 refers to krn-002, so it is one hop away; store, g-2 and r1 are not.
  assert.deepEqual(ids(scene.nodes), ['b-17', 'g-1', 'kernel', 'krn-002', 'krn-003']);
  const edges = new Map(scene.edges.map((e) => [e.id, e]));
  assert.equal(edges.get('krn-002~traces~g-1')?.label, 'Traces to');
  assert.equal(edges.get('krn-002~boundary~b-17')?.label, 'Stated at');
  assert.equal(typeof edges.get('krn-002~subjects~kernel')?.label, 'string');
  assert.equal(edges.get('krn-003~dependsOn~krn-002')?.entityId, 'krn-003');
  assert.equal(edges.get('b-17~providedBy~kernel')?.entityKind, 'boundary');
  assert.ok(scene.edges.every((e) => e.line === 'solid' && e.color === 'neutral' || e.entityKind === 'relationship'));
  assert.ok(scene.nodes.every((n) => n.parent === null && n.container === false));
  const focus = scene.nodes.find((n) => n.id === 'krn-002');
  assert.deepEqual(focus.badges, ['focus']);
  assert.ok(scene.notes.some((s) => /presentation only/.test(s)));
});

test('depth 2 reaches further, and a relationship between two drawn components becomes an edge', () => {
  const model = build(SPEC.replace('"components"', VIEWS));
  const scene = project(model, 'deep', { focusEntity: 'krn-002' });
  const nodeIds = ids(scene.nodes);
  for (const id of ['g-2', 'store', 'krn-003', 'g-1', 'b-17', 'kernel']) assert.ok(nodeIds.includes(id), id);
  assert.ok(!nodeIds.includes('r1'), 'the relationship is drawn as an edge, not a node');
  const r1 = scene.edges.find((e) => e.id === 'r1');
  assert.ok(r1);
  assert.equal(r1.entityKind, 'relationship');
  assert.deepEqual([r1.from, r1.to], ['kernel', 'store']);
  assert.equal(r1.label, model.meta.relationshipKinds.calls.label);
});

test('every node and edge is backed by a model entity', () => {
  const model = build(SPEC.replace('"components"', VIEWS));
  for (const focusEntity of ['krn-002', 'kernel', 'g-1', 'r1', 'b-17']) {
    for (const view of ['references', 'deep']) {
      const scene = project(model, view, { focusEntity });
      assert.ok(scene.nodes.length > 0, `${view} ${focusEntity}`);
      for (const n of scene.nodes) assert.ok(model.entities.has(n.entityId), `node ${n.id}`);
      for (const e of scene.edges) assert.ok(model.entities.has(e.entityId), `edge ${e.id}`);
    }
  }
});

test('kinds declared by the specification take their shape and color from the meta-model', () => {
  const model = build();
  const scene = project(model, 'references', { focusEntity: 'krn-002' });
  const node = (id) => scene.nodes.find((n) => n.id === id);
  assert.equal(node('g-1').shape, model.meta.entities.goal.shape);
  assert.equal(node('g-1').color, model.meta.entities.goal.color);
  assert.equal(node('g-1').sublabel, 'Goal');
  assert.equal(node('b-17').shape, 'hex');
  assert.equal(node('b-17').color, 'teal');
  assert.equal(node('krn-002').shape, 'diamond');
  assert.equal(node('krn-002').status, 'not-evaluated');
  assert.ok(scene.legend.some((l) => l.kind === 'node' && l.label === 'Goal'));
  assert.ok(scene.legend.some((l) => l.kind === 'edge' && l.label === 'Traces to'));
});

test('a violated claim result colors its node and marks it violated', () => {
  const model = build();
  const results = [{ claimId: 'krn-002', status: 'violated', involved: ['kernel'] }];
  const scene = project(model, 'references', { focusEntity: 'krn-002', claimResults: results });
  assert.equal(scene.nodes.find((n) => n.id === 'krn-002').status, 'violated');
  assert.equal(scene.nodes.find((n) => n.id === 'kernel').status, 'violated');
});

test('filter.entityKinds restricts the drawn kinds, and the focus is always drawn', () => {
  const model = build(SPEC.replace('"components"', VIEWS));
  const scene = project(model, 'goals-only', { focusEntity: 'krn-002' });
  assert.deepEqual(ids(scene.nodes), ['g-1', 'g-2', 'krn-002']);
  const noFocus = project(model, 'goals-only', {});
  assert.deepEqual(ids(noFocus.nodes), ['g-1', 'g-2']);
  assert.equal(noFocus.edges.length, 0);
});

test('no focus and no filter draws nothing and says how to start', () => {
  const model = build();
  const scene = project(model, 'references', {});
  assert.deepEqual(scene.nodes, []);
  assert.deepEqual(scene.edges, []);
  assert.ok(scene.notes.some((s) => s === 'Select an entity to see what it refers to and what refers to it.'));
  assert.ok(scene.notes.some((s) => /Goal 2/.test(s)), 'the notes count entities per kind');
});

test('an implicit References view exists when the specification declares none', () => {
  const views = listViews(build());
  const v = views.find((x) => x.id === 'references');
  assert.ok(v);
  assert.equal(v.name, 'References');
  assert.equal(v.declared, false);
});

test('more than 150 entities in reach are capped with a note', () => {
  const goals = Array.from({ length: 200 }, (_, i) => ({ id: `g${i}`, statement: `Goal ${i}.` }));
  const spec = JSON.parse(SPEC);
  spec.goals = goals;
  spec.claims = [{ id: 'big', kind: 'requirement', statement: 'Traces to every goal.', subjects: ['kernel'], traces: goals.map((g) => g.id), evaluate: { method: 'property' } }];
  const model = build(JSON.stringify(spec));
  const scene = project(model, 'references', { focusEntity: 'big' });
  assert.equal(scene.nodes.length, 150);
  assert.equal(scene.nodes[0].id, 'big');
  assert.ok(scene.notes.some((s) => /left out/.test(s) && /Goal/.test(s)), scene.notes.join(' | '));
  const drawn = new Set(scene.nodes.map((n) => n.id));
  for (const e of scene.edges) assert.ok(drawn.has(e.from) && drawn.has(e.to));
});

test('the same call twice gives identical scenes', () => {
  const model = build(SPEC.replace('"components"', VIEWS));
  for (const view of ['references', 'deep', 'goals-only']) {
    assert.deepEqual(project(model, view, { focusEntity: 'krn-002' }), project(model, view, { focusEntity: 'krn-002' }));
  }
});
