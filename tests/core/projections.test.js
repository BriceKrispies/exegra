import test from 'node:test';
import assert from 'node:assert/strict';
import { analyzeSpec } from '../../src/core/analyze.js';
import { listViews, project, registerProjection } from '../../src/core/projections.js';
import { layoutScene } from '../../src/core/layout.js';

const SPEC = `{
  "exegra": "0.1",
  "system": { "id": "sys", "name": "Sys" },
  "components": [
    { "id": "web", "name": "Web", "category": "client" },
    { "id": "api", "name": "Api", "category": "logical", "kind": "subsystem" },
    { "id": "svc1", "name": "Service one", "category": "computational", "parent": "api" },
    { "id": "svc2", "name": "Service two", "category": "computational", "parent": "api" },
    { "id": "db", "name": "Database", "category": "storage" },
    { "id": "lone", "name": "Lone", "category": "logical" }
  ],
  "relationships": [
    { "id": "r1", "kind": "calls", "from": "web", "to": "svc1" },
    { "id": "r2", "kind": "data-flow", "from": "svc1", "to": "svc2" },
    { "id": "r3", "kind": "data-flow", "from": "svc2", "to": "db" },
    { "id": "r4", "kind": "calls", "from": "svc1", "to": "db" }
  ]
}`;

function build(text = SPEC) {
  const { model, errorCount, diagnostics } = analyzeSpec(text);
  assert.equal(errorCount, 0, JSON.stringify(diagnostics));
  return model;
}

const byId = (list) => new Map(list.map((x) => [x.id, x]));

test('implicit views exist when none are declared', () => {
  const views = listViews(build());
  assert.deepEqual(views.map((v) => v.id), ['structural', 'claims', 'behavior', 'references', 'reader']);
  assert.ok(views.every((v) => v.declared === false));
});

test('unknown view id falls back to the first view', () => {
  const scene = project(build(), 'no-such-view', {});
  assert.equal(scene.viewId, 'structural');
});

test('every scene node and edge is backed by a model entity', () => {
  const model = build();
  for (const v of listViews(model)) {
    const scene = project(model, v.id, {});
    for (const n of scene.nodes) assert.ok(model.entities.has(n.entityId), `${v.id} node ${n.id}`);
    for (const e of scene.edges) assert.ok(model.entities.has(e.entityId), `${v.id} edge ${e.id}`);
  }
});

test('structural: containers come before children and carry the container shape', () => {
  const scene = project(build(), 'structural', {});
  const ids = scene.nodes.map((n) => n.id);
  assert.ok(ids.indexOf('api') < ids.indexOf('svc1'));
  const api = byId(scene.nodes).get('api');
  assert.equal(api.shape, 'container');
  assert.equal(api.container, true);
  assert.equal(byId(scene.nodes).get('svc1').parent, 'api');
  assert.equal(scene.edges.length, 4);
});

test('collapsed subsystem lifts edges and drops internal ones', () => {
  const scene = project(build(), 'structural', { collapsed: new Set(['api']) });
  const api = byId(scene.nodes).get('api');
  assert.equal(api.collapsed, true);
  assert.equal(api.container, false);
  assert.deepEqual(api.badges, ['2 inside']);
  assert.ok(!scene.nodes.some((n) => n.id === 'svc1'));
  const edges = byId(scene.edges);
  assert.ok(!edges.has('r2'));
  assert.equal(edges.get('r1').to, 'api');
  assert.equal(edges.get('r1').lifted, true);
  assert.equal(edges.get('r3').from, 'api');
  assert.ok(scene.notes.some((s) => /drawn to a collapsed block/.test(s)));
});

test('hidden removes components with their descendants and a connection through them becomes a labelled path summary', () => {
  const scene = project(build(), 'structural', { hidden: new Set(['api']) });
  assert.deepEqual(scene.nodes.map((n) => n.id).sort(), ['db', 'lone', 'web']);
  // web -> svc1 -> svc2 -> db runs through the hidden subsystem's blocks: one dotted may-path, carrying every relationship along it.
  assert.deepEqual(scene.edges.map((e) => [e.id, e.from, e.to, e.line, e.pathSummary?.via, e.witnesses]), [['summary:web->db', 'web', 'db', 'dotted', ['svc1', 'svc2'], ['r1', 'r2', 'r3', 'r4']]]);
  assert.match(scene.edges[0].label ?? '', /^may reach via 2 hidden/);
  assert.ok(scene.notes.some((n) => /1 element is hidden \(Api\); 4 derived interactions touch hidden blocks, and 1 connection through them is drawn as dotted path summary/.test(n)), scene.notes.join(' | '));
});

test('isolate shows only the subsystem and its descendants', () => {
  const scene = project(build(), 'structural', { isolate: 'api' });
  assert.deepEqual(scene.nodes.map((n) => n.id).sort(), ['api', 'svc1', 'svc2']);
  assert.deepEqual(scene.edges.map((e) => e.id), ['r2']);
});

test('declared view filter by relationship kind', () => {
  const text = SPEC.replace('"relationships"', `"views": [{ "id": "flows", "name": "Flows", "projection": "structural", "filter": { "relationshipKinds": ["data-flow"] } }],\n  "relationships"`);
  const model = build(text);
  const views = listViews(model);
  assert.equal(views[0].id, 'flows');
  assert.equal(views[0].declared, true);
  const scene = project(model, 'flows', {});
  assert.deepEqual(scene.edges.map((e) => e.id), ['r2', 'r3']);
  assert.ok(scene.notes.includes('Filtered to relationship kinds: data-flow.'));
});

test('violated claim results mark nodes', () => {
  const results = [{ claimId: 'c', status: 'violated', involved: ['web'], counterexample: { summary: '', entities: ['db', 'r4'] } }];
  const scene = project(build(), 'structural', { claimResults: results });
  const nodes = byId(scene.nodes);
  assert.equal(nodes.get('db').status, 'violated');
  assert.equal(nodes.get('web').status, undefined);
  assert.equal(byId(scene.edges).get('r4').status, 'violated');
});

test('registerProjection adds a projection that listViews reports', () => {
  registerProjection('probe-test', (m, view) => ({ viewId: view.id, projection: 'probe-test', nodes: [], edges: [], legend: [], notes: [] }));
  const model = build();
  assert.ok(listViews(model).some((v) => v.id === 'probe-test'));
  assert.equal(project(model, 'probe-test', {}).projection, 'probe-test');
});

test('same input twice yields identical scene and placement', () => {
  const model = build();
  const a = project(model, 'structural', {});
  const b = project(model, 'structural', {});
  assert.deepEqual(a, b);
  assert.deepEqual(layoutScene(a), layoutScene(b));
});

function overlap(p, q) {
  return Math.abs(p.x - q.x) < (p.w + q.w) / 2 - 1e-9 && Math.abs(p.z - q.z) < (p.d + q.d) / 2 - 1e-9;
}

function encloses(outer, inner) {
  return inner.x - inner.w / 2 >= outer.x - outer.w / 2 - 1e-9
    && inner.x + inner.w / 2 <= outer.x + outer.w / 2 + 1e-9
    && inner.z - inner.d / 2 >= outer.z - outer.d / 2 - 1e-9
    && inner.z + inner.d / 2 <= outer.z + outer.d / 2 + 1e-9;
}

test('layout: sibling leaves do not overlap and containers enclose children', () => {
  const scene = project(build(), 'structural', {});
  const pl = layoutScene(scene);
  const leaves = scene.nodes.filter((n) => !n.container);
  for (let i = 0; i < leaves.length; i++) {
    for (let j = i + 1; j < leaves.length; j++) {
      assert.ok(!overlap(pl[leaves[i].id], pl[leaves[j].id]), `${leaves[i].id} overlaps ${leaves[j].id}`);
    }
  }
  for (const n of scene.nodes) {
    assert.ok(pl[n.id], n.id);
    if (n.parent) assert.ok(encloses(pl[n.parent], pl[n.id]), `${n.parent} encloses ${n.id}`);
  }
  assert.equal(pl.api.level, 0);
  assert.equal(pl.svc1.level, 1);
  assert.equal(pl.web.level, 0);
});

test('layout: flow runs left to right at the root and front to back one level in', () => {
  const scene = project(build(), 'structural', {});
  const pl = layoutScene(scene);
  assert.ok(pl.web.x < pl.api.x);
  assert.ok(pl.svc1.z < pl.svc2.z);
  assert.equal(pl.svc1.x, pl.svc2.x);
});

test('layout: pinned leaf lands at its pin and its container still encloses it', () => {
  const scene = project(build(), 'structural', {});
  const pl = layoutScene(scene, { svc1: [40, -25], api: [999, 999], nope: [1, 1] });
  assert.equal(pl.svc1.x, 40);
  assert.equal(pl.svc1.z, -25);
  assert.ok(encloses(pl.api, pl.svc1));
  assert.ok(encloses(pl.api, pl.svc2));
  assert.notEqual(pl.api.x, 999);
  assert.ok(!('nope' in pl));
});

test('layout handles cycles, self edges and edges across containers', () => {
  const scene = {
    viewId: 'x', projection: 'x', legend: [], notes: [],
    nodes: ['a', 'b', 'c'].map((id) => ({ id, entityId: id, entityKind: 'component', label: id, shape: 'box', color: 'slate', parent: id === 'c' ? 'g' : null, container: false }))
      .concat([{ id: 'g', entityId: 'g', entityKind: 'component', label: 'g', shape: 'container', color: 'slate', parent: null, container: true }]),
    edges: [
      { id: 'e1', entityId: 'e1', entityKind: 'relationship', from: 'a', to: 'b', line: 'solid', color: 'slate' },
      { id: 'e2', entityId: 'e2', entityKind: 'relationship', from: 'b', to: 'a', line: 'solid', color: 'slate' },
      { id: 'e3', entityId: 'e3', entityKind: 'relationship', from: 'b', to: 'b', line: 'solid', color: 'slate' },
      { id: 'e4', entityId: 'e4', entityKind: 'relationship', from: 'b', to: 'c', line: 'solid', color: 'slate' },
    ],
  };
  const pl = layoutScene(scene);
  assert.equal(Object.keys(pl).length, 4);
  for (const p of Object.values(pl)) assert.ok(Number.isFinite(p.x) && Number.isFinite(p.z));
  assert.ok(pl.a.x < pl.b.x);
  assert.ok(pl.b.x < pl.g.x);
});

test('author-entered evidence is never drawn in a positive verification colour', () => {
  const text = SPEC.replace('"relationships"', `"claims": [{ "id": "c1", "kind": "measured", "statement": "s", "evaluate": { "method": "external-evidence" } }],
  "evidence": [
    { "id": "e-for", "claim": "c1", "kind": "document", "ref": "a.pdf" },
    { "id": "e-against", "claim": "c1", "kind": "measurement", "ref": "b.json", "supports": false }
  ],
  "relationships"`);
  const scene = project(build(text), 'claims', { focusClaim: 'c1' });
  const evEdges = scene.edges.filter((e) => e.entityKind === 'evidence');
  assert.equal(evEdges.length, 2);
  assert.ok(evEdges.every((e) => e.color !== 'green'));
  assert.equal(evEdges.find((e) => e.entityId === 'e-for').color, 'steel');
  assert.equal(evEdges.find((e) => e.entityId === 'e-against').color, 'red');
});

test('generated and partially generated implementations are not drawn green or teal', () => {
  const text = SPEC
    .replace('"id": "web", "name": "Web", "category": "client"', '"id": "web", "name": "Web", "category": "client", "implementation": { "status": "generated" }')
    .replace('"id": "lone", "name": "Lone", "category": "logical"', '"id": "lone", "name": "Lone", "category": "logical", "implementation": { "status": "partially-generated" }')
    .replace('"relationships"', `"views": [{ "id": "impl", "name": "Impl", "projection": "structural", "display": { "colorBy": "implementation" } }],\n  "relationships"`);
  const scene = project(build(text), 'impl', {});
  const nodes = byId(scene.nodes);
  assert.equal(nodes.get('web').color, 'amber');
  assert.equal(nodes.get('lone').color, 'violet');
  assert.ok(scene.nodes.every((n) => n.color !== 'green' && n.color !== 'teal'));
});

test('a bundle edge carries every relationship it stands for, sorted, and is backed by the first declared', () => {
  const text = SPEC.replace('{ "id": "r4", "kind": "calls", "from": "svc1", "to": "db" }', '{ "id": "r4", "kind": "calls", "from": "svc1", "to": "db" },\n    { "id": "r0", "kind": "calls", "from": "svc2", "to": "db" }');
  const scene = project(build(text), 'structural', { collapsed: new Set(['api']) });
  const bundle = scene.edges.find((e) => e.from === 'api' && e.to === 'db' && e.kind === 'calls');
  assert.ok(bundle);
  assert.deepEqual(bundle.witnesses, ['r0', 'r4']);
  assert.equal(bundle.entityId, 'r4');
  assert.match(bundle.label ?? '', /×2$/);
  assert.deepEqual(scene.abstraction?.blocks.includes('api'), true);
  const expanded = project(build(text), 'structural', {});
  assert.deepEqual(expanded.edges.filter((e) => e.to === 'db').map((e) => [e.id, e.witnesses]), [['r3', ['r3']], ['r4', ['r4']], ['r0', ['r0']]]);
});
