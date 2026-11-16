import test from 'node:test';
import assert from 'node:assert/strict';
import { layoutScene, chooseLayout, scorePlacement, LAYOUT_METHODS } from '../../src/core/layout.js';

const METHODS = ['layered', 'layered-down', 'packed', 'radial'];

/**
 * Build a scene directly. `containers` is a list of [id, parentId|null];
 * `leaves` a list of [id, parentId|null]; `edges` a list of [from, to].
 */
function mk(containers, leaves, edges) {
  const nodes = [
    ...containers.map(([id, parent]) => ({ id, entityId: id, entityKind: 'component', label: id, shape: 'container', color: 'slate', parent, container: true })),
    ...leaves.map(([id, parent]) => ({ id, entityId: id, entityKind: 'component', label: id, shape: 'box', color: 'slate', parent, container: false })),
  ];
  return {
    viewId: 'x', projection: 'x', legend: [], notes: [], nodes,
    edges: edges.map(([from, to], i) => ({ id: `e${i}`, entityId: `e${i}`, entityKind: 'relationship', from, to, line: 'solid', color: 'slate' })),
  };
}

/** N leaves spread round-robin over M containers (M = 0: all at the root). */
function generated(n, m, edgePairs) {
  const containers = Array.from({ length: m }, (_, i) => [`c${i}`, null]);
  const leaves = Array.from({ length: n }, (_, i) => [`n${i}`, m ? `c${i % m}` : null]);
  return mk(containers, leaves, edgePairs.map(([a, b]) => [`n${a}`, `n${b}`]));
}

function chain(n) {
  return Array.from({ length: n - 1 }, (_, i) => [i, i + 1]);
}

function overlap(a, b) {
  return Math.abs(a.x - b.x) < (a.w + b.w) / 2 - 1e-9 && Math.abs(a.z - b.z) < (a.d + b.d) / 2 - 1e-9;
}

function encloses(outer, inner) {
  return inner.x - inner.w / 2 >= outer.x - outer.w / 2 - 1e-9
    && inner.x + inner.w / 2 <= outer.x + outer.w / 2 + 1e-9
    && inner.z - inner.d / 2 >= outer.z - outer.d / 2 - 1e-9
    && inner.z + inner.d / 2 <= outer.z + outer.d / 2 + 1e-9;
}

function assertSound(scene, pl) {
  for (const n of scene.nodes) {
    assert.ok(pl[n.id], `placed ${n.id}`);
    for (const k of ['x', 'z', 'w', 'd']) assert.ok(Number.isFinite(pl[n.id][k]), `${n.id}.${k} finite`);
  }
  const bySibling = new Map();
  for (const n of scene.nodes) {
    const k = n.parent ?? '';
    if (!bySibling.has(k)) bySibling.set(k, []);
    bySibling.get(k).push(n.id);
  }
  for (const ids of bySibling.values()) {
    for (let i = 0; i < ids.length; i++) {
      for (let j = i + 1; j < ids.length; j++) assert.ok(!overlap(pl[ids[i]], pl[ids[j]]), `${ids[i]} overlaps ${ids[j]}`);
    }
  }
  for (const n of scene.nodes) if (n.parent) assert.ok(encloses(pl[n.parent], pl[n.id]), `${n.parent} encloses ${n.id}`);
}

function bboxRatio(pl) {
  let x0 = Infinity, x1 = -Infinity, z0 = Infinity, z1 = -Infinity;
  for (const p of Object.values(pl)) {
    x0 = Math.min(x0, p.x - p.w / 2); x1 = Math.max(x1, p.x + p.w / 2);
    z0 = Math.min(z0, p.z - p.d / 2); z1 = Math.max(z1, p.z + p.d / 2);
  }
  return (x1 - x0) / (z1 - z0);
}

// A varied scene: two containers, one nested, cross-container edges, a cycle, loose leaves.
function variedScene() {
  return mk(
    [['A', null], ['B', null], ['A1', 'A']],
    [['a1', 'A'], ['a2', 'A'], ['a3', 'A1'], ['a4', 'A1'], ['a5', 'A1'], ['b1', 'B'], ['b2', 'B'], ['b3', 'B'], ['r1', null], ['r2', null], ['r3', null]],
    [['a1', 'a2'], ['a2', 'a3'], ['a3', 'a4'], ['a4', 'a3'], ['a3', 'a3'], ['a1', 'b1'], ['b1', 'b2'], ['b2', 'b3'], ['b3', 'r1'], ['r1', 'a5'], ['r2', 'r3']],
  );
}

const SCENES = {
  varied: variedScene(),
  'zero edges': generated(9, 3, []),
  'single node': generated(1, 0, []),
  'self edge': generated(3, 0, [[1, 1], [0, 2]]),
  cycle: generated(5, 0, [[0, 1], [1, 2], [2, 3], [3, 4], [4, 0]]),
  'cross-container edge': generated(6, 2, [[0, 1], [0, 3], [2, 5]]),
  'three nesting levels': mk(
    [['L0', null], ['L1', 'L0'], ['L2', 'L1']],
    [['p', 'L2'], ['q', 'L2'], ['r', 'L1'], ['s', 'L0'], ['t', null]],
    [['p', 'q'], ['q', 'r'], ['r', 's'], ['s', 't'], ['t', 'p']],
  ),
  'larger graph': generated(40, 5, Array.from({ length: 60 }, (_, i) => [(i * 7) % 40, (i * 13 + 5) % 40])),
};

test('LAYOUT_METHODS lists the four concrete methods, not auto', () => {
  assert.deepEqual(LAYOUT_METHODS.map((m) => m.id), METHODS);
  for (const m of LAYOUT_METHODS) assert.ok(m.label && m.description);
});

for (const method of METHODS) {
  for (const [name, scene] of Object.entries(SCENES)) {
    test(`${method}: ${name} is sound (no sibling overlap, containers enclose children)`, () => {
      assertSound(scene, layoutScene(scene, {}, { method }));
    });
    test(`${method}: ${name} is deterministic`, () => {
      assert.deepEqual(layoutScene(scene, {}, { method }), layoutScene(scene, {}, { method }));
    });
  }

  test(`${method}: levels follow containment depth`, () => {
    const pl = layoutScene(SCENES['three nesting levels'], {}, { method });
    assert.equal(pl.L0.level, 0);
    assert.equal(pl.L1.level, 1);
    assert.equal(pl.p.level, 3);
    assert.equal(pl.t.level, 0);
  });

  test(`${method}: pins are honoured exactly and containers still enclose`, () => {
    const scene = SCENES.varied;
    const pl = layoutScene(scene, { a1: [40, -25], a3: [-30, 33], b2: [7, 7], A: [999, 999], nope: [1, 1] }, { method });
    assert.deepEqual([pl.a1.x, pl.a1.z], [40, -25]);
    assert.deepEqual([pl.a3.x, pl.a3.z], [-30, 33]);
    assert.deepEqual([pl.b2.x, pl.b2.z], [7, 7]);
    assert.ok(!('nope' in pl));
    assert.notEqual(pl.A.x, 999);
    for (const n of scene.nodes) if (n.parent) assert.ok(encloses(pl[n.parent], pl[n.id]), `${n.parent} encloses ${n.id}`);
  });

  test(`${method}: a scene with no nodes gives an empty placement`, () => {
    assert.deepEqual(layoutScene(mk([], [], []), {}, { method }), {});
  });
}

test('layered: default options agree with an explicit layered method', () => {
  for (const scene of Object.values(SCENES)) {
    assert.deepEqual(layoutScene(scene, {}), layoutScene(scene, {}, { method: 'layered' }));
    assert.deepEqual(layoutScene(scene), layoutScene(scene, {}, { method: 'layered', aspect: 1.6 }));
  }
});

test('layered: root flows left to right, layered-down flows front to back', () => {
  const scene = generated(3, 0, [[0, 1], [1, 2]]);
  const across = layoutScene(scene, {}, { method: 'layered' });
  assert.ok(across.n0.x < across.n1.x && across.n1.x < across.n2.x);
  const down = layoutScene(scene, {}, { method: 'layered-down' });
  assert.ok(down.n0.z < down.n1.z && down.n1.z < down.n2.z);
});

test('layoutScene with an unknown method throws', () => {
  assert.throws(() => layoutScene(SCENES.varied, {}, { method: 'spiral' }));
});

test('chooseLayout returns scores for every method and picks the lowest total', () => {
  for (const scene of Object.values(SCENES)) {
    const r = chooseLayout(scene, {}, { aspect: 1.6 });
    assert.deepEqual(Object.keys(r.scores).sort(), [...METHODS].sort());
    for (const s of Object.values(r.scores)) {
      for (const k of ['total', 'aspect', 'edgeLength', 'crossings', 'area']) assert.ok(Number.isFinite(s[k]), k);
    }
    const lowest = Math.min(...METHODS.map((m) => r.scores[m].total));
    assert.equal(r.scores[r.method].total, lowest);
    assert.deepEqual(r.placement, layoutScene(scene, {}, { method: r.method, aspect: 1.6 }));
    assert.deepEqual(layoutScene(scene, {}, { method: 'auto', aspect: 1.6 }), r.placement);
  }
});

test('scorePlacement agrees with the scores chooseLayout reports', () => {
  const scene = SCENES.varied;
  const r = chooseLayout(scene, {}, { aspect: 1.6 });
  assert.deepEqual(scorePlacement(scene, r.placement, { aspect: 1.6 }), r.scores[r.method]);
});

test('scorePlacement prefers a better aspect and fewer crossings', () => {
  const scene = generated(4, 0, [[0, 2], [1, 3]]);
  const crossed = {
    n0: { x: 0, z: 0, w: 2.6, d: 1.6, level: 0 }, n1: { x: 10, z: 0, w: 2.6, d: 1.6, level: 0 },
    n2: { x: 10, z: 10, w: 2.6, d: 1.6, level: 0 }, n3: { x: 0, z: 10, w: 2.6, d: 1.6, level: 0 },
  };
  const apart = { ...crossed, n2: crossed.n3, n3: crossed.n2 };
  assert.equal(scorePlacement(scene, crossed).crossings, 1 / 2 * 1);
  assert.equal(scorePlacement(scene, apart).crossings, 0);
});

test('chooseLayout: a chain of 12 root nodes is not laid out as a strip', () => {
  const scene = generated(12, 0, chain(12));
  const r = chooseLayout(scene, {}, { aspect: 1.6 });
  const ratio = bboxRatio(r.placement);
  assert.ok(ratio >= 0.8 && ratio <= 3.2, `ratio ${ratio} (chosen ${r.method})`);
});

test('packed: a larger target aspect gives a wider bounding box', () => {
  const scene = generated(30, 0, chain(30));
  const narrow = bboxRatio(layoutScene(scene, {}, { method: 'packed', aspect: 1.0 }));
  const wide = bboxRatio(layoutScene(scene, {}, { method: 'packed', aspect: 2.5 }));
  assert.ok(wide > narrow, `${wide} > ${narrow}`);
});

test('layered: a larger target aspect wraps a long chain into fewer rows', () => {
  const scene = generated(16, 0, chain(16));
  const narrow = bboxRatio(layoutScene(scene, {}, { method: 'layered', aspect: 0.8 }));
  const wide = bboxRatio(layoutScene(scene, {}, { method: 'layered', aspect: 4 }));
  assert.ok(wide > narrow, `${wide} > ${narrow}`);
});

test('radial: the best-connected node sits at the centre of its level', () => {
  const scene = generated(7, 0, [[3, 0], [3, 1], [3, 2], [3, 4], [3, 5], [3, 6]]);
  const pl = layoutScene(scene, {}, { method: 'radial' });
  const ps = Object.values(pl);
  const mx = ps.reduce((t, p) => t + p.x, 0) / ps.length;
  const mz = ps.reduce((t, p) => t + p.z, 0) / ps.length;
  const dist = (p) => Math.hypot(p.x - mx, p.z - mz);
  for (const id of ['n0', 'n1', 'n2', 'n4', 'n5', 'n6']) assert.ok(dist(pl.n3) < dist(pl[id]), id);
});

test('performance: 400 nodes / 500 edges', () => {
  const edges = Array.from({ length: 500 }, (_, i) => [(i * 37) % 400, (i * 91 + 13) % 400]);
  const scene = generated(400, 8, edges);
  chooseLayout(scene); // warm up
  let t = performance.now();
  const r = chooseLayout(scene);
  const chooseMs = performance.now() - t;
  assertSound(scene, r.placement);
  t = performance.now();
  layoutScene(scene, {}, { method: 'layered' });
  const oneMs = performance.now() - t;
  assert.ok(chooseMs < 150, `chooseLayout took ${chooseMs} ms`);
  assert.ok(oneMs < 30, `layoutScene took ${oneMs} ms`);
});
