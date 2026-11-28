// Multiscale navigation (WG-5695): a structural view is a hierarchy, a cut, a kind coarsening and a filter. The
// scene draws the derived model at the view's cut (src/core/abstraction.js) and nothing else; expanding or
// collapsing one block changes only what lies inside it; a filter reports everything it removes, drawing a
// connection through hidden blocks as a labelled path summary; claims stated at a cut are shown with their result
// at the cut the view draws; and no presentation state changes a derived fact, a verdict or the semantic hash.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { analyzeSpec } from '../../src/core/analyze.js';
import { evaluateClaim, evaluateClaims } from '../../src/core/claims.js';
import { project, listViews, sceneSemantics, defaultCut } from '../../src/core/projections.js';
import { layoutScene, chooseLayout } from '../../src/core/layout.js';
import { semanticHash } from '../../src/core/hash.js';
import { hierarchyOf, ancestorsIn } from '../../src/core/query.js';
import {
  deriveModel, derivedJson, cutOfExpanded, toggleExpanded, expandedOfCut, declaredCutWithBlocks, pathSummaries, blockReport,
} from '../../src/core/abstraction.js';
import { attachExtracted } from '../../src/core/extraction.js';
import { readSpecFile } from '../../tools/spec-manifest.js';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const SELF_TEXT = readSpecFile(path.join(ROOT, 'specs/exegra/spec.jsonc'));
const FACTS = JSON.parse(fs.readFileSync(path.join(ROOT, 'specs/exegra/extracted/facts.json'), 'utf8'));
/** @type {any} */
let selfModel = null;
/** The self-specification with its extracted facts attached, the model the command line and the application derive from. */
const self = () => (selfModel ??= attachExtracted(analyzeSpec(SELF_TEXT).model, FACTS));

/** @param {any} doc */
function build(doc) {
  const { model, errorCount, diagnostics } = analyzeSpec(JSON.stringify(doc));
  assert.equal(errorCount, 0, JSON.stringify(diagnostics.filter((/** @type {any} */ d) => d.severity === 'error')));
  return model;
}

/** The derived model's blocks and interactions, as the command line prints them. @param {any} d */
const derivedSemantics = (d) => ({
  blocks: d.blocks.map((/** @type {any} */ b) => b.id).sort(),
  interactions: d.interactions.map((/** @type {any} */ i) => ({ key: i.key, witnesses: i.witnesses })).sort((/** @type {any} */ a, /** @type {any} */ b) => (a.key < b.key ? -1 : a.key > b.key ? 1 : 0)),
});

/** The walk of WG-5695 on the self-specification: L0, L1, persistence expanded, a component expanded to its modules, semantic-core expanded. */
function walk() {
  const model = self();
  const persistence = /** @type {any} */ (expandedOfCut(model, 'persistence-expanded')).expanded;
  return [
    ['l0', /** @type {any} */ (expandedOfCut(model, 'l0')).expanded],
    ['l1', /** @type {any} */ (expandedOfCut(model, 'l1')).expanded],
    ['persistence-expanded', persistence],
    ['workspace-service to modules', toggleExpanded(model, 'logical', persistence, 'workspace-service')],
    ['semantic-core-expanded', /** @type {any} */ (expandedOfCut(model, 'semantic-core-expanded')).expanded],
  ];
}

test('at every step of the walk the architecture scene draws exactly the derived model of its cut', () => {
  const model = self();
  for (const [name, expanded] of walk()) {
    const scene = project(model, 'architecture', { cut: { hierarchy: 'logical', expanded } });
    const sem = sceneSemantics(scene);
    const d = deriveModel(model, { hierarchy: 'logical', blocks: sem.cutBlocks });
    assert.deepEqual({ blocks: sem.blocks, interactions: sem.interactions }, derivedSemantics(d), name);
    assert.deepEqual(sem.pathSummaries, [], `${name}: nothing is hidden, so nothing is summarised`);
    // Every container is an element the cut opens, and every drawn edge has a non-empty witness set (I3).
    assert.ok(sem.containers.every((c) => sem.expanded.includes(c)), name);
    assert.ok(scene.edges.every((e) => (e.witnesses ?? []).length > 0), name);
  }
  // The declared steps are named by their cut; the module step is an interactive cut with the modules as blocks.
  const steps = walk().map(([, expanded]) => sceneSemantics(project(model, 'architecture', { cut: { hierarchy: 'logical', expanded } })));
  assert.deepEqual(steps.map((s) => s.cut), ['l0', 'l1', 'persistence-expanded', null, 'semantic-core-expanded']);
  assert.deepEqual(steps[3].blocks.filter((b) => b.startsWith('module:')), model.entities.get('workspace-service').data.implementation.modules.map((/** @type {string} */ m) => `module:${m}`).sort(), 'the component is drawn as its module elements');
  assert.deepEqual(steps[0].blocks.filter((b) => !b.startsWith('module:')).length, 15, 'L0: the system and its 14 actors and external systems');
});

test('L0 draws the system as one block in its environment and every block of L0 and L1 states a purpose and L1 opens the system as a container', () => {
  const model = self();
  const l0 = project(model, 'architecture', { cut: { hierarchy: 'logical', expanded: [] } });
  const sys = l0.nodes.find((n) => n.id === 'exegra');
  assert.equal(sys?.elementKind, 'system');
  assert.equal(sys?.collapsed, true);
  assert.ok(l0.nodes.every((n) => n.parent === null), 'nothing is opened at level 0');
  assert.ok(l0.edges.every((e) => e.from === 'exegra' || e.to === 'exegra'), 'every interaction at level 0 is between the system and its environment');
  for (const id of ['l0', 'l1']) {
    const scene = project(model, 'architecture', { cut: { hierarchy: 'logical', expanded: /** @type {any} */ (expandedOfCut(model, id)).expanded } });
    assert.ok(!scene.nodes.some((n) => (n.marks ?? []).some((m) => m.kind === 'no-purpose')), `${id}: every block states a purpose`);
    for (const n of scene.nodes.filter((x) => x.block)) {
      const r = /** @type {any} */ (blockReport(model, 'logical', /** @type {any} */ (expandedOfCut(model, id)).expanded, n.id));
      assert.ok(r.purpose, `${id}: ${n.id} has a purpose`);
      assert.ok(r.responsibilities.length > 0, `${id}: ${n.id} states its responsibilities`);
    }
  }
  const l1 = project(model, 'architecture', { cut: { hierarchy: 'logical', expanded: ['exegra'] } });
  assert.equal(l1.nodes.find((n) => n.id === 'exegra')?.container, true);
  assert.equal(l1.nodes.find((n) => n.id === 'semantic-core')?.parent, 'exegra');
});

test('expanding or collapsing one block changes no other block of the scene', () => {
  const model = self();
  const h = /** @type {any} */ (hierarchyOf(model, 'logical'));
  /** @param {any} n */
  const strip = (n) => JSON.stringify({ ...n, parent: undefined });
  for (const [name, expanded] of walk()) {
    const before = project(model, 'architecture', { cut: { hierarchy: 'logical', expanded } });
    const cut = /** @type {any} */ (cutOfExpanded(model, 'logical', expanded));
    const composite = cut.blocks.filter((/** @type {string} */ b) => (h.children.get(b) ?? []).length);
    for (const b of composite.slice(0, 8)) {
      const after = project(model, 'architecture', { cut: { hierarchy: 'logical', expanded: toggleExpanded(model, 'logical', expanded, b) } });
      const inside = (/** @type {string} */ id) => id === b || ancestorsIn(h, id).includes(b);
      const untouched = (/** @type {any} */ s) => new Map(s.nodes.filter((/** @type {any} */ n) => !inside(n.id)).map((/** @type {any} */ n) => [n.id, strip({ ...n, badges: undefined, marks: (n.marks ?? []).filter((/** @type {any} */ m) => m.kind !== 'interface-disagrees') })]));
      assert.deepEqual(untouched(after), untouched(before), `${name}: expanding ${b} changes only what is inside it`);
      // Collapsing it again restores the scene exactly.
      const back = project(model, 'architecture', { cut: { hierarchy: 'logical', expanded: toggleExpanded(model, 'logical', toggleExpanded(model, 'logical', expanded, b), b) } });
      assert.deepEqual(sceneSemantics(back), sceneSemantics(before), `${name}: collapsing ${b} again restores the cut`);
    }
  }
});

test('every declared cut of the logical and runtime hierarchies gives the same derived model through the view as through derive', () => {
  const model = self();
  for (const c of model.byKind.cut ?? []) {
    const e = /** @type {any} */ (expandedOfCut(model, c.id));
    const scene = project(model, 'architecture', { cut: { hierarchy: e.hierarchy, expanded: e.expanded } });
    const sem = sceneSemantics(scene);
    assert.equal(sem.cut, c.id);
    // What the scene does not draw it reports: here only a system with no members in the hierarchy (in the runtime
    // hierarchy the system is a root of its own, the hosts holding everything), which is a block with nothing in it.
    const notDrawn = sem.filterReport?.removedBlocks ?? [];
    const h = /** @type {any} */ (hierarchyOf(model, e.hierarchy));
    for (const b of notDrawn) {
      assert.ok(b === model.system.id && !(h.children.get(b) ?? []).length, `${c.id}: ${b} is left out only as a system with no members`);
      assert.ok(scene.notes.some((n) => n.includes('no members and no relationships')), `${c.id}: the scene says why ${b} is not drawn`);
    }
    assert.deepEqual({ blocks: [...sem.blocks, ...notDrawn].sort(), interactions: sem.interactions }, derivedSemantics(deriveModel(model, c.id)), c.id);
  }
  assert.deepEqual(sceneSemantics(project(model, 'architecture', { cut: { hierarchy: 'runtime', expanded: /** @type {any} */ (expandedOfCut(model, 'runtime-hosts')).expanded } })).filterReport?.removedBlocks, ['exegra']);
  assert.equal(declaredCutWithBlocks(model, 'logical', /** @type {any} */ (cutOfExpanded(model, 'logical', ['exegra'])).blocks), 'l1');
});

test('views keep their meaning as cuts and filters: each opens at its declared cut and counts what its filter removes', () => {
  const model = self();
  const views = new Map(listViews(model).map((v) => [v.id, v]));
  assert.deepEqual(['architecture', 'realisation', 'data-and-edit-flow', 'semantic-core-only'].map((id) => /** @type {any} */ (model.entities.get(id)).data.cut), ['l1', 'l1', 'l1', 'semantic-core-expanded']);
  assert.ok(views.has('architecture'));
  // semantic-core-only: only blocks inside the semantic core; every interaction with a block outside is counted.
  const scene = project(model, 'semantic-core-only', {});
  const d = /** @type {any} */ (deriveModel(model, 'semantic-core-expanded'));
  const h = /** @type {any} */ (hierarchyOf(model, 'logical'));
  const inside = (/** @type {string} */ b) => b === 'semantic-core' || ancestorsIn(h, b).includes('semantic-core');
  assert.ok(scene.nodes.every((n) => inside(n.id) || n.container), 'only the semantic core and what contains it is drawn');
  const crossing = d.interactions.filter((/** @type {any} */ i) => inside(i.from) !== inside(i.to));
  assert.equal(scene.filterReport?.droppedInteractions, crossing.length);
  assert.ok(scene.notes.some((n) => n.startsWith(`${crossing.length} derived interactions with a block outside this view's filter are not drawn`)), scene.notes.join(' | '));
  // data-and-edit-flow: the kind filter drops witnesses, and says how many.
  const flow = project(model, 'data-and-edit-flow', {});
  const kinds = new Set(/** @type {any} */ (model.entities.get('data-and-edit-flow')).data.filter.relationshipKinds);
  assert.ok(flow.edges.every((e) => kinds.has(e.kind)));
  assert.ok(flow.notes.some((n) => /relationships? of other kinds between drawn blocks/.test(n)));
});

test('hiding a block on a path draws a labelled path summary through it and the inside badge follows the filter', () => {
  const model = self();
  const l1 = /** @type {any} */ (expandedOfCut(model, 'l1')).expanded;
  const scene = project(model, 'architecture', { cut: { hierarchy: 'logical', expanded: l1 }, hidden: new Set(['persistence']) });
  const sem = sceneSemantics(scene);
  assert.ok(!sem.blocks.includes('persistence'));
  const d = /** @type {any} */ (deriveModel(model, 'l1'));
  const expected = pathSummaries(model, d, new Set(['persistence']));
  assert.deepEqual(sem.pathSummaries.map((s) => [s.from, s.to, s.via, s.witnesses]), expected.map((s) => [s.from, s.to, s.via, s.witnesses]));
  const toFs = scene.edges.find((e) => e.pathSummary && e.from === 'application' && e.to === 'filesystem');
  assert.ok(toFs, 'application reaches the file system only through persistence');
  assert.match(toFs?.label ?? '', /^may reach via 1 hidden \(Persistence\)/);
  assert.equal(toFs?.line, 'dotted');
  assert.equal(sem.filterReport?.pathSummaries, expected.length);
  // Every interaction touching the hidden block is either summarised or counted: none is silently lost (I4).
  const touching = d.interactions.filter((/** @type {any} */ i) => i.from === 'persistence' || i.to === 'persistence');
  assert.ok(scene.notes.some((n) => n.includes(`${touching.length} derived interactions touch hidden blocks`)));
  // Hiding a member of a collapsed block lowers its badge and marks it.
  const hidMember = project(model, 'architecture', { cut: { hierarchy: 'logical', expanded: l1 }, hidden: new Set(['workspace-service']) });
  const before = project(model, 'architecture', { cut: { hierarchy: 'logical', expanded: l1 } });
  const badge = (/** @type {any} */ s) => s.nodes.find((/** @type {any} */ n) => n.id === 'persistence')?.badges?.[0];
  assert.equal(parseInt(badge(hidMember), 10), parseInt(badge(before), 10) - 1);
  assert.ok(hidMember.nodes.find((n) => n.id === 'persistence')?.marks?.some((m) => m.kind === 'hidden-inside'));
});

test('a claim stated at a cut is shown with its result at the drawn cut with its counterexample drawn or as not expressible', () => {
  const doc = {
    exegra: '0.1', system: { id: 'sys', name: 'Sys', purpose: 'p' },
    components: [
      { id: 's1', name: 'S1', kind: 'subsystem', parent: 'sys', category: 'logical', purpose: 'p' }, { id: 's2', name: 'S2', kind: 'subsystem', parent: 'sys', category: 'logical', purpose: 'p' },
      { id: 'a1', name: 'A1', parent: 's1', category: 'logical', purpose: 'p' }, { id: 'a2', name: 'A2', parent: 's1', category: 'logical', purpose: 'p' },
      { id: 'b1', name: 'B1', parent: 's2', category: 'logical', purpose: 'p' }, { id: 'b2', name: 'B2', parent: 's2', category: 'logical', purpose: 'p' },
    ],
    relationships: [{ id: 'a1-b1', kind: 'invokes', from: 'a1', to: 'b1' }, { id: 'b2-a2', kind: 'invokes', from: 'b2', to: 'a2' }],
    cuts: [{ id: 'top', name: 'Top', depth: 1 }],
    claims: [
      { id: 'top-acyclic', kind: 'structural', statement: 's', evaluate: { method: 'acyclic', cut: 'top' } },
      { id: 'a1-alone', kind: 'structural', statement: 's', evaluate: { method: 'no-relationship', cut: 'top', from: 'a1', to: 'b1' } },
    ],
  };
  const model = build(doc);
  const top = /** @type {any} */ (expandedOfCut(model, 'top')).expanded;
  const blocks = /** @type {any} */ (cutOfExpanded(model, 'logical', top)).blocks;
  // The same verdict for the declared cut by id and by its blocks.
  const byId = evaluateClaim(model, 'top-acyclic', { atCut: 'top' });
  const byBlocks = evaluateClaim(model, 'top-acyclic', { atCut: { hierarchy: 'logical', blocks } });
  assert.equal(byId.status, 'violated');
  assert.equal(byBlocks.status, byId.status);
  assert.deepEqual(byBlocks.counterexample?.entities, byId.counterexample?.entities);
  const levelClaims = ['top-acyclic', 'a1-alone'].map((claimId) => ({ claimId, result: evaluateClaim(model, claimId, { atCut: { hierarchy: 'logical', blocks } }) }));
  const scene = project(model, 'structural', { cut: { hierarchy: 'logical', expanded: top }, levelClaims });
  const cyc = /** @type {any} */ (scene.levelClaims?.find((c) => c.claimId === 'top-acyclic'));
  assert.equal(cyc.status, 'violated');
  assert.deepEqual(cyc.notDrawn, []);
  assert.deepEqual([...cyc.drawn].sort(), ['a1-b1', 'b2-a2', 's1', 's2']);
  assert.equal(scene.nodes.find((n) => n.id === 's1')?.status, 'violated');
  assert.ok(scene.edges.filter((e) => e.status === 'violated').length === 2, 'both edges of the block cycle are drawn red');
  const alone = /** @type {any} */ (scene.levelClaims?.find((c) => c.claimId === 'a1-alone'));
  assert.equal(alone.expressible, false, 'a1 is hidden inside s1 at this cut');
  assert.ok(scene.notes.some((n) => /^Claim a1-alone is stated at a cut and is not expressible at this level/.test(n)));
  // Opened one level further, the cycle of blocks is gone and the claim on a1 becomes expressible.
  const fine = /** @type {any} */ (cutOfExpanded(model, 'logical', [...top, 's1', 's2'])).blocks;
  assert.equal(evaluateClaim(model, 'top-acyclic', { atCut: { hierarchy: 'logical', blocks: fine } }).status, 'verified');
  assert.equal(evaluateClaim(model, 'a1-alone', { atCut: { hierarchy: 'logical', blocks: fine } }).status, 'violated');
});

test('no presentation state changes a derived fact or a claim verdict or the semantic hash', () => {
  const model = self();
  const hash = semanticHash(model);
  // Every tenth claim: the verdicts are decided by the same evaluator whatever the claim, and `verify` evaluates them all.
  const sample = model.byKind.claim.filter((/** @type {any} */ _c, /** @type {number} */ i) => i % 10 === 0).map((/** @type {any} */ c) => c.id);
  const verdictsOf = () => JSON.stringify(sample.map((id) => [id, evaluateClaim(model, id, { stamps: null }).status]));
  const verdicts = verdictsOf();
  const derived = JSON.stringify(derivedJson(/** @type {any} */ (deriveModel(model, 'l1'))));
  for (const [, expanded] of walk().slice(0, 4)) {
    const scene = project(model, 'architecture', { cut: { hierarchy: 'logical', expanded }, hidden: new Set(['tooling']), isolate: null });
    for (const method of ['layered', 'layered-down', 'packed', 'radial']) layoutScene(scene, { 'semantic-core': [3, 4] }, { method, aspect: 0.6 });
    chooseLayout(scene, {}, { aspect: 2 });
  }
  assert.equal(semanticHash(model), hash);
  assert.equal(JSON.stringify(derivedJson(/** @type {any} */ (deriveModel(model, 'l1')))), derived);
  assert.equal(verdictsOf(), verdicts);
});

test('the default cut of a view is its declared cut or else the overview of a large model and a within filter opens its element', () => {
  const model = self();
  assert.deepEqual(defaultCut(model, { id: 'x' }), { hierarchy: 'logical', expanded: ['exegra'] }, 'a large model without a declared cut opens with top-level subsystems collapsed');
  assert.deepEqual(defaultCut(model, { id: 'x', cut: 'semantic-core-expanded' }).expanded, ['exegra', 'semantic-core']);
  assert.deepEqual(defaultCut(model, { id: 'x', filter: { within: 'persistence' } }).expanded, ['exegra', 'persistence']);
  assert.equal(defaultCut(model, { id: 'x', hierarchy: 'runtime' }).hierarchy, 'runtime');
});

test('presentation modules compute no lifting or bundling or entity-to-element mapping: they ask the core', () => {
  const forbidden = ['endpointElement', 'restrictInteraction', 'interactionKey', 'combineSummaries', 'summarise(model', 'cutForCollapse', 'relift(', ' lift(', 'blockAt('];
  const dirs = ['src/ui', 'src/render', 'src/app'];
  for (const dir of dirs) {
    for (const f of fs.readdirSync(path.join(ROOT, dir)).filter((x) => x.endsWith('.js'))) {
      const text = fs.readFileSync(path.join(ROOT, dir, f), 'utf8');
      for (const word of forbidden) assert.ok(!text.includes(word), `${dir}/${f} uses ${word.trim()}; lifting and mapping belong to src/core/abstraction.js and src/core/query.js`);
    }
  }
  // The structural projection draws the derived model: it defines no lifting of its own.
  const proj = fs.readFileSync(path.join(ROOT, 'src/core/projections.js'), 'utf8');
  for (const word of ['function lift', 'witnesses.push', 'interactionKey(']) assert.ok(!proj.includes(word), `projections.js: ${word}`);
});

test('at L1 the automatic layout gives the opened system most of the picture with its environment around it', () => {
  const model = self();
  const scene = project(model, 'architecture', { cut: { hierarchy: 'logical', expanded: ['exegra'] } });
  for (const aspect of [1.6, 0.55]) {
    const r = chooseLayout(scene, {}, { aspect });
    const ps = Object.values(r.placement);
    const W = Math.max(...ps.map((p) => p.x + p.w / 2)) - Math.min(...ps.map((p) => p.x - p.w / 2));
    const D = Math.max(...ps.map((p) => p.z + p.d / 2)) - Math.min(...ps.map((p) => p.z - p.d / 2));
    const c = /** @type {any} */ (r.placement.exegra);
    assert.ok(c.w / W >= 0.5 && c.d / D >= 0.5, `aspect ${aspect} (${r.method}): the system spans ${(c.w / W).toFixed(2)} of the width and ${(c.d / D).toFixed(2)} of the depth`);
    for (const n of scene.nodes) {
      const p = /** @type {any} */ (r.placement[n.id]);
      const inside = Math.abs(p.x - c.x) < c.w / 2 && Math.abs(p.z - c.z) < c.d / 2;
      if (n.parent === 'exegra') assert.ok(inside, `${n.id} is drawn inside the system`);
      else if (n.id !== 'exegra') assert.ok(!inside, `${n.id} is drawn around the system, not over it`);
    }
    assert.ok(r.scores[r.method].labels < 0.5, `aspect ${aspect}: few labels collide (${r.scores[r.method].labels.toFixed(2)} per label)`);
  }
});
