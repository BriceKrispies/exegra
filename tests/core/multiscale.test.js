// The recursive element model (docs/model-and-format.md, "Elements, hierarchies, facets and cuts"):
// one element kind with the system as root and module elements derived from implementation.modules,
// named laminar hierarchies, facets that are selected and never contracted, cuts with their abstraction
// maps, and the knowledge status of every element. Each new diagnostic has a negative fixture; the
// abstraction maps of Exegra's own cuts are checked to be total and unique; the composition of cut maps
// is checked as a property over generated laminar hierarchies; and the projects under specs/ keep the
// diagnostics and claim statuses they had before (tests/fixtures/multiscale/baseline.json).

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { analyzeSpec } from '../../src/core/analyze.js';
import { evaluateClaim, evaluateClaims } from '../../src/core/claims.js';
import {
  LOGICAL, elementsOf, hierarchyOf, ancestorsIn, cutBlocksOf, abstractionOf, refinementOf, cutMap, blockOf,
  cutToCut, facetMembers, knowledgeOf, selectComponents, moduleId,
} from '../../src/core/query.js';
import { checkTraceability } from '../../tools/traceability.js';
import { runCommand } from '../../cli/commands.js';
import { readSpecFile } from '../../tools/spec-manifest.js';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const SELF = readSpecFile(path.join(ROOT, 'specs/exegra/spec.jsonc'));
/** @type {any} */
let selfModel = null;
const self = () => (selfModel ??= analyzeSpec(SELF).model);

/** A small specification with two levels below the system, one declared hierarchy, a facet and cuts. */
function base() {
  return {
    exegra: '0.1',
    system: { id: 'sys', name: 'Sys' },
    components: [
      { id: 'core', name: 'Core', kind: 'subsystem', category: 'logical', parent: 'sys', purpose: 'p', implementation: { status: 'manual', modules: ['src/core/'] } },
      { id: 'parser', name: 'Parser', category: 'logical', parent: 'core', purpose: 'p', tags: ['kernel'], implementation: { status: 'manual', modules: ['src/parse.js'] } },
      { id: 'checker', name: 'Checker', category: 'logical', parent: 'core', purpose: 'p', tags: ['kernel'], implementation: { status: 'manual', modules: ['src/check.js', 'src/shared.js'] } },
      { id: 'planned', name: 'Planned', category: 'logical', parent: 'core', purpose: 'p', implementation: { status: 'not-implemented' } },
      { id: 'ui', name: 'UI', kind: 'subsystem', category: 'client', parent: 'sys', purpose: 'p' },
      { id: 'panel', name: 'Panel', category: 'client', parent: 'ui', purpose: 'p', implementation: { status: 'manual', modules: ['src/panel.js'] } },
      { id: 'user', name: 'User', kind: 'actor', category: 'external', purpose: 'p' },
      { id: 'host', name: 'Host', kind: 'external', category: 'external', purpose: 'p' },
    ],
    hierarchies: [{ id: 'placement', name: 'Placement', groups: [{ parent: 'host', members: ['parser', 'checker', 'panel'] }] }],
    facets: [{ id: 'kernel-facet', name: 'Kernel', tag: 'kernel' }],
    cuts: [
      { id: 'top', name: 'Top', expand: [] },
      { id: 'mid', name: 'Mid', depth: 1 },
      { id: 'core-open', name: 'Core open', depth: 1, expand: ['core'] },
      { id: 'leaves', name: 'Leaves', finest: true },
      { id: 'mixed', name: 'Mixed', blocks: ['core', 'panel', 'user', 'host'] },
      { id: 'placement-top', name: 'Placement top', hierarchy: 'placement', expand: [] },
    ],
  };
}

/** @param {any} doc */
const analyze = (doc) => analyzeSpec(JSON.stringify(doc, null, 2));
/** @param {any} doc */
const errors = (doc) => analyze(doc).diagnostics.filter((d) => d.severity === 'error');
/**
 * The doc after a mutation has an error with this code, whose message names every one of `ids`.
 * @param {(d: any) => void} mutate @param {string} code @param {string[]} ids
 */
function refuses(mutate, code, ids) {
  const doc = base();
  mutate(doc);
  const hits = errors(doc).filter((d) => d.code === code);
  assert.ok(hits.length, `${code} expected; got ${JSON.stringify(errors(doc).map((d) => d.code))}`);
  for (const id of ids) assert.ok(hits.some((d) => d.message.includes(`"${id}"`)), `${code} names "${id}": ${hits.map((d) => d.message).join(' | ')}`);
}

// The well-formed fixture every negative fixture mutates validates with no errors, and its cuts have the expected blocks.
// @evidence abstraction-diagnostics-name-offenders
test('a fixture with a declared hierarchy and a facet and every form of cut validates with no errors', () => {
  const r = analyze(base());
  assert.deepEqual(r.diagnostics.filter((d) => d.severity !== 'info').map((d) => `${d.code} ${d.message}`), []);
  const m = /** @type {any} */ (r.model);
  assert.deepEqual(cutMap(m, 'top')?.blocks, ['sys', 'user', 'host']);
  assert.deepEqual(cutMap(m, 'mid')?.blocks, ['core', 'ui', 'user', 'host']);
  assert.deepEqual(cutMap(m, 'core-open')?.blocks, ['parser', 'checker', 'planned', 'ui', 'user', 'host', moduleId('src/core/')]);
  assert.deepEqual(cutMap(m, 'mixed')?.expanded, ['sys', 'ui']);
  assert.equal(blockOf(m, 'mid', moduleId('src/check.js')), 'core');
  assert.equal(blockOf(m, 'mid', 'sys'), null, 'an element the cut opens is not mapped');
  assert.equal(hierarchyOf(m, 'placement')?.parent.get(moduleId('src/check.js')), 'checker', 'a module element follows its component');
  assert.equal(hierarchyOf(m, 'placement')?.parent.get('checker'), 'host');
});

// module.multiple-owners names both components.
// @evidence abstraction-diagnostics-name-offenders
test('a module declared by two components is module.multiple-owners naming both', () => {
  refuses((d) => d.components.find((/** @type {any} */ c) => c.id === 'panel').implementation.modules.push('src/check.js'), 'module.multiple-owners', ['checker', 'panel']);
});

// hierarchy.multiple-parents names the element and both parents.
// @evidence abstraction-diagnostics-name-offenders
test('an element with two parents in one hierarchy is hierarchy.multiple-parents naming the element and both parents', () => {
  refuses((d) => d.hierarchies[0].groups.push({ parent: 'user', members: ['parser'] }), 'hierarchy.multiple-parents', ['parser', 'host', 'user']);
});

// Both cycle codes, naming the elements on the cycle.
// @evidence abstraction-diagnostics-name-offenders
test('a cycle in a declared hierarchy is hierarchy.cycle and in the logical one component.parent-cycle', () => {
  refuses((d) => { d.hierarchies[0].groups = [{ parent: 'parser', members: ['checker'] }, { parent: 'checker', members: ['parser'] }]; }, 'hierarchy.cycle', ['parser', 'checker']);
  refuses((d) => { d.components.find((/** @type {any} */ c) => c.id === 'core').parent = 'parser'; }, 'component.parent-cycle', ['parser']);
});

// hierarchy.unknown-parent and hierarchy.reserved-id.
// @evidence abstraction-diagnostics-name-offenders
test('a groupBy value that maps to no element is hierarchy.unknown-parent and the id logical is reserved', () => {
  refuses((d) => { d.hierarchies[0].groupBy = { property: 'category', parents: { client: 'nowhere' } }; }, 'hierarchy.unknown-parent', ['nowhere']);
  refuses((d) => { d.hierarchies.push({ id: 'logical', name: 'Again' }); }, 'hierarchy.reserved-id', ['logical']);
});

// facet.contraction for a facet as a cut's hierarchy, as a hierarchy parent and as an expanded block.
// facet.contraction for every place a contraction is required.
// @evidence abstraction-diagnostics-name-offenders facets-selected-never-contracted
test('a facet used where a contraction is required is facet.contraction', () => {
  refuses((d) => { d.cuts.push({ id: 'by-facet', name: 'By facet', hierarchy: 'kernel-facet', expand: [] }); }, 'facet.contraction', ['by-facet', 'kernel-facet']);
  refuses((d) => { d.hierarchies[0].groups.push({ parent: 'kernel-facet', members: ['user'] }); }, 'facet.contraction', ['placement', 'kernel-facet']);
  refuses((d) => { d.cuts.push({ id: 'open-facet', name: 'Open facet', expand: ['kernel-facet'] }); }, 'facet.contraction', ['open-facet', 'kernel-facet']);
});

// cut.not-composite and cut.ancestor-not-expanded.
// @evidence abstraction-diagnostics-name-offenders
test('expanding a leaf is cut.not-composite and expanding inside an unexpanded ancestor is cut.ancestor-not-expanded', () => {
  refuses((d) => { d.cuts.push({ id: 'bad', name: 'Bad', depth: 1, expand: ['user'] }); }, 'cut.not-composite', ['user']);
  refuses((d) => { d.cuts.push({ id: 'bad', name: 'Bad', expand: ['core'] }); }, 'cut.ancestor-not-expanded', ['core', 'sys']);
});

// cut.uncovered, cut.not-antichain and cut.form.
// @evidence abstraction-diagnostics-name-offenders
test('a cut that omits an element is cut.uncovered and one with an element and its ancestor is cut.not-antichain', () => {
  refuses((d) => { d.cuts.push({ id: 'bad', name: 'Bad', blocks: ['core', 'user', 'host'] }); }, 'cut.uncovered', ['ui']);
  refuses((d) => { d.cuts.push({ id: 'bad', name: 'Bad', blocks: ['core', 'parser', 'ui', 'user', 'host'] }); }, 'cut.not-antichain', ['parser', 'core']);
  refuses((d) => { d.cuts.push({ id: 'bad', name: 'Bad', blocks: ['core', 'ui', 'user', 'host'], depth: 1 }); }, 'cut.form', ['bad']);
});

// A facet with members and a tag selects both; a tag no facet declares selects its carriers; an unknown facet is refused.
// @evidence facets-selected-never-contracted
test('a selector naming no facet or tag is claim.selector.facet and a facet selects its members with a tag as an implicit facet', () => {
  const claim = (/** @type {any} */ select) => ({ id: 'c', kind: 'structural', statement: 's', evaluate: { method: 'property-defined', select, property: 'purpose' } });
  refuses((d) => { d.claims = [claim({ facet: 'nope' })]; }, 'claim.selector.facet', ['nope']);
  const doc = base();
  doc.facets[0] = /** @type {any} */ ({ ...doc.facets[0], members: ['panel'] });
  doc.claims = /** @type {any} */ ([claim({ facet: 'kernel-facet' })]);
  const r = analyze(doc);
  assert.equal(r.errorCount, 0, JSON.stringify(r.diagnostics.filter((d) => d.severity === 'error')));
  const m = /** @type {any} */ (r.model);
  assert.deepEqual([...facetMembers(m, 'kernel-facet')].sort(), ['checker', 'panel', 'parser'], 'members and the tag overlap freely');
  assert.deepEqual(selectComponents(m, { facet: 'kernel' }).map((c) => c.id), ['parser', 'checker'], 'a tag no facet declares');
  assert.equal(evaluateClaim(m, 'c').status, 'verified');
});

// The claim method agrees with the diagnostics: verified on the fixture, violated with the element that has two parents.
// @evidence abstraction-diagnostics-name-offenders
test('abstraction-well-formed is verified on well-formed hierarchies and cuts and violated with the offending element', () => {
  const claim = { id: 'wf', kind: 'structural', statement: 's', evaluate: { method: 'abstraction-well-formed' } };
  const good = base();
  good.claims = /** @type {any} */ ([claim]);
  assert.equal(evaluateClaim(/** @type {any} */ (analyze(good).model), 'wf').status, 'verified');
  const bad = base();
  bad.claims = /** @type {any} */ ([claim]);
  bad.hierarchies[0].groups.push({ parent: 'user', members: ['parser'] });
  const r = evaluateClaim(/** @type {any} */ (analyze(bad).model), 'wf');
  assert.equal(r.status, 'violated');
  assert.ok(r.counterexample?.entities.includes('parser'));
});

// Every declared cut of Exegra's specification maps each element to exactly one ancestor-or-self block, or opens it.
// @evidence cut-maps-compose
test('every element maps to exactly one block of each declared cut of the self-specification or is opened by it', () => {
  const m = self();
  const elements = [...elementsOf(m).keys()];
  const cuts = (m.byKind.cut ?? []).map((/** @type {any} */ c) => c.id);
  for (const id of ['l0', 'l1', 'persistence-expanded', 'semantic-core-expanded', 'module-level']) assert.ok(cuts.includes(id), id);
  for (const id of cuts) {
    const c = /** @type {any} */ (cutMap(m, id));
    assert.deepEqual(c.problems, [], id);
    const h = /** @type {any} */ (hierarchyOf(m, c.hierarchy));
    const blocks = new Set(c.blocks);
    const opened = new Set(c.expanded);
    for (const e of elements) {
      const b = c.map.get(e);
      if (opened.has(e)) { assert.equal(b, undefined, `${id}: opened ${e}`); continue; }
      assert.ok(b !== undefined && blocks.has(b), `${id}: ${e} maps to a block`);
      assert.ok(b === e || ancestorsIn(h, e).includes(b), `${id}: ${e} maps to its ancestor-or-self`);
      assert.equal(ancestorsIn(h, e).filter((a) => blocks.has(a)).length + (blocks.has(e) ? 1 : 0), 1, `${id}: ${e} meets the cut once`);
    }
  }
  const blocks = (/** @type {string} */ id) => /** @type {any} */ (cutMap(m, id)).blocks;
  assert.ok(blocks('l0').includes('exegra') && blocks('l0').includes('browser-user') && blocks('l0').includes('ai-coding-agent'));
  assert.ok(!blocks('l0').includes('semantic-core'));
  for (const s of ['semantic-core', 'application', 'visualization', 'persistence', 'agent-interface', 'tooling', 'composition-root']) assert.ok(blocks('l1').includes(s), `l1 has ${s}`);
  assert.ok(!blocks('persistence-expanded').includes('persistence') && blocks('persistence-expanded').includes('workspace-service') && blocks('persistence-expanded').includes('semantic-core'));
  assert.ok(!blocks('semantic-core-expanded').includes('semantic-core') && blocks('semantic-core-expanded').includes('queries') && blocks('semantic-core-expanded').includes('persistence'));
  assert.equal(blockOf(m, 'module-level', moduleId('src/core/query.js')), moduleId('src/core/query.js'));
  assert.equal(blockOf(m, 'l1', moduleId('src/core/query.js')), 'semantic-core');
  assert.equal(blockOf(m, 'l0', moduleId('src/core/query.js')), 'exegra');
});

// exegra, subsystem, component, module; main.js under the composition root; builtin-types.js with one owner; no missing, unclaimed or doubly claimed file; the actors and the producer of edit-requested.
// @evidence module-to-element-map-is-a-function
test('the self-specification is a logical hierarchy from exegra down to module elements with each file under one element', () => {
  const m = self();
  const h = /** @type {any} */ (hierarchyOf(m, LOGICAL));
  assert.deepEqual(h.problems, []);
  assert.deepEqual(ancestorsIn(h, moduleId('src/core/query.js')), ['queries', 'semantic-core', 'exegra'], 'system, subsystem, component, module');
  assert.deepEqual(ancestorsIn(h, moduleId('src/app/main.js')), ['composition-root', 'exegra'], 'the composition root sits directly under the system');
  assert.deepEqual(elementsOf(m).get(moduleId('src/core/builtin-types.js'))?.owners, ['generation-readiness']);
  assert.equal(m.entities.get('ai-coding-agent').data.kind, 'actor');
  assert.equal(m.entities.get('browser-user').data.kind, 'actor');
  assert.equal(m.entities.get('edit-requested').data.producedBy, 'browser-user');
  const t = checkTraceability(m, ROOT);
  assert.deepEqual({ missing: t.missingModules, unclaimed: t.unclaimedFiles, multiple: t.multipleOwners, errors: t.errors }, { missing: [], unclaimed: [], multiple: [], errors: [] });
});

// Every placed component under the host its runsIn names; the runtime cuts refine each other; cuts of different hierarchies are incomparable.
// @evidence runtime-hierarchy-from-runs-in
test('the runtime placement hierarchy of the self-specification follows runsIn and has its own valid cuts', () => {
  const m = self();
  const h = /** @type {any} */ (hierarchyOf(m, 'runtime'));
  assert.deepEqual(h.problems, []);
  const host = { browser: 'browser-platform', node: 'nodejs-runtime', both: 'javascript-runtime' };
  for (const c of m.byKind.component) {
    const want = /** @type {any} */ (host)[c.data.runsIn];
    if (want === undefined || want === c.id || c.id === 'browser-platform' || c.id === 'nodejs-runtime') continue;
    assert.equal(h.parent.get(c.id), want, c.id);
  }
  assert.equal(h.parent.get('browser-platform'), 'javascript-runtime');
  assert.equal(h.parent.get('nodejs-runtime'), 'javascript-runtime');
  assert.equal(h.parent.get(moduleId('src/app/main.js')), 'composition-root');
  for (const id of ['runtime-hosts', 'runtime-platforms', 'runtime-placed']) assert.equal(/** @type {any} */ (cutMap(m, id)).hierarchy, 'runtime');
  assert.ok(cutToCut(m, 'runtime-placed', 'runtime-platforms'));
  assert.ok(cutToCut(m, 'runtime-platforms', 'runtime-hosts'));
  assert.equal(cutToCut(m, 'runtime-hosts', 'l0'), null, 'cuts of different hierarchies are not comparable');
});

// module-level, semantic-core-expanded, l1 and l0 compose pairwise; persistence-expanded and semantic-core-expanded are incomparable.
// exegra cut on a declared cut, an ad hoc cut of the runtime hierarchy, an invalid one, and the listing.
// @evidence cut-maps-compose
test('cut maps compose along the chain of cuts of the self-specification and incomparable cuts have no map', () => {
  const m = self();
  const chain = ['module-level', 'semantic-core-expanded', 'l1', 'l0'];
  for (let i = 0; i < chain.length; i++) {
    for (let j = i + 1; j < chain.length; j++) {
      const step = cutToCut(m, chain[i], chain[j]);
      assert.ok(step, `${chain[i]} refines ${chain[j]}`);
      const fine = /** @type {any} */ (cutMap(m, chain[i])).map;
      for (const [e, b] of fine) assert.equal(blockOf(m, chain[j], e), step.get(b), `${chain[i]} -> ${chain[j]} at ${e}`);
    }
  }
  assert.equal(cutToCut(m, 'persistence-expanded', 'semantic-core-expanded'), null);
  assert.equal(cutToCut(m, 'semantic-core-expanded', 'persistence-expanded'), null);
});

/** A deterministic generator (mulberry32). @param {number} seed */
function rng(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

/** A hierarchy from parent indices (-1 for a root), in the shape hierarchyOf returns. @param {number[]} parents */
function forest(parents) {
  const order = parents.map((_, i) => `e${i}`);
  /** @type {Map<string, string>} */
  const parent = new Map();
  /** @type {Map<string, string[]>} */
  const children = new Map();
  parents.forEach((p, i) => {
    if (p < 0) return;
    parent.set(order[i], order[p]);
    if (!children.has(order[p])) children.set(order[p], []);
    /** @type {string[]} */ (children.get(order[p])).push(order[i]);
  });
  const roots = order.filter((e) => !parent.has(e));
  /** @type {Map<string, number>} */
  const depth = new Map();
  order.forEach((e) => { let d = 0; let c = parent.get(e); while (c !== undefined) { d++; c = parent.get(c); } depth.set(e, d); });
  return { id: 'generated', parent, children, roots, depth, order, problems: [] };
}

// Generated forests; every comparable pair of cuts composes, and comparability is exactly inclusion of the opened sets.
// @evidence cut-maps-compose
test('property: for comparable cuts C finer than D of generated laminar hierarchies alpha_D is alpha_C-D composed with alpha_C', () => {
  const random = rng(5692);
  let pairs = 0;
  let incomparable = 0;
  for (let trial = 0; trial < 150; trial++) {
    const n = 2 + Math.floor(random() * 40);
    // Each element's parent is an earlier element or none: every forest over n ordered elements can arise.
    const parents = Array.from({ length: n }, (_, i) => (i === 0 || random() < 0.2 ? -1 : Math.floor(random() * i)));
    const h = forest(parents);
    const composites = h.order.filter((e) => (h.children.get(e)?.length ?? 0) > 0);
    const maxDepth = Math.max(...h.depth.values());
    /** @type {{blocks: string[], opened: Set<string>}[]} */
    const cuts = [];
    const add = (/** @type {any} */ spec) => {
      const r = cutBlocksOf(/** @type {any} */ (h), spec);
      assert.deepEqual(r.problems, [], JSON.stringify({ parents, spec }));
      cuts.push({ blocks: r.blocks, opened: new Set(r.expanded) });
    };
    for (let d = 0; d <= maxDepth + 1; d++) add({ depth: d });
    add({ finest: true });
    for (let k = 0; k < 6; k++) {
      // A random set of composites, closed under ancestors, is a valid expansion.
      const open = new Set();
      for (const c of composites) if (random() < 0.4) { open.add(c); for (const a of ancestorsIn(/** @type {any} */ (h), c)) open.add(a); }
      add({ expand: [...open] });
    }
    // Every cut also round-trips through its blocks.
    for (const c of cuts) assert.deepEqual(cutBlocksOf(/** @type {any} */ (h), { blocks: c.blocks }).problems, []);
    for (const C of cuts) {
      const alphaC = abstractionOf(/** @type {any} */ (h), C.blocks);
      // alpha_C is total on the elements at or below the cut, and only there.
      for (const e of h.order) assert.equal(alphaC.has(e), !C.opened.has(e));
      for (const D of cuts) {
        const step = refinementOf(/** @type {any} */ (h), C.blocks, D.blocks);
        const comparable = [...D.opened].every((e) => C.opened.has(e));
        assert.equal(step !== null, comparable, 'C refines D exactly when D opens nothing C does not');
        if (!step) { incomparable++; continue; }
        const alphaD = abstractionOf(/** @type {any} */ (h), D.blocks);
        for (const [e, b] of alphaC) assert.equal(alphaD.get(e), step.get(b));
        pairs++;
      }
    }
  }
  assert.ok(pairs > 2000, `only ${pairs} comparable pairs`);
  assert.ok(incomparable > 50, `only ${incomparable} incomparable pairs`);
});

// Planned components opaque, a member makes one transparent, declared unknown, actors opaque, module elements transparent leaves.
// @evidence knowledge-status-derived
test('knowledge status: planned elements are opaque and a member makes an element transparent and unknown is declared', () => {
  const m = self();
  for (const c of m.byKind.component) {
    if (c.data.implementation?.status === 'not-implemented') assert.equal(knowledgeOf(m, c.id)?.status, 'opaque', c.id);
  }
  assert.equal(knowledgeOf(m, 'exegra')?.status, 'transparent');
  assert.equal(knowledgeOf(m, 'browser-user')?.status, 'opaque');
  assert.deepEqual(knowledgeOf(m, moduleId('src/core/query.js')), { status: 'transparent', leaf: true, reason: 'A leaf: nothing finer is declared inside it.' });

  const doc = base();
  assert.equal(knowledgeOf(/** @type {any} */ (analyze(doc).model), 'planned')?.status, 'opaque');
  doc.components.push({ id: 'planned-part', name: 'Part', category: 'logical', parent: 'planned', purpose: 'p' });
  assert.equal(knowledgeOf(/** @type {any} */ (analyze(doc).model), 'planned')?.status, 'transparent', 'adding a member makes it transparent');
  const declared = base();
  declared.components.find((/** @type {any} */ c) => c.id === 'panel').knowledge = 'unknown';
  declared.components.find((/** @type {any} */ c) => c.id === 'parser').knowledge = 'opaque';
  const dm = /** @type {any} */ (analyze(declared).model);
  assert.equal(knowledgeOf(dm, 'panel')?.status, 'unknown');
  assert.equal(knowledgeOf(dm, 'parser')?.status, 'transparent', 'declared opaque, but it has a module member');
  assert.equal(knowledgeOf(dm, 'user')?.status, 'opaque');
});

// Two components on one file and a directory over a file are both errors; exegra traceability fails.
// @evidence module-to-element-map-is-a-function
test('traceability: a file covered by two module elements is traceability.multiple-owners and the command fails', async () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-ms-'));
  try {
    for (const f of ['src/a.js', 'src/b.js', 'src/lib/c.js']) {
      fs.mkdirSync(path.dirname(path.join(dir, f)), { recursive: true });
      fs.writeFileSync(path.join(dir, f), '');
    }
    const doc = {
      exegra: '0.1',
      system: { id: 'sys', name: 'Sys' },
      components: [
        { id: 'x', name: 'X', category: 'logical', implementation: { status: 'manual', modules: ['src/lib/'] } },
        { id: 'y', name: 'Y', category: 'logical', implementation: { status: 'manual', modules: ['src/a.js', 'src/b.js'] } },
        { id: 'z', name: 'Z', category: 'logical', implementation: { status: 'manual', modules: ['src/a.js', 'src/lib/c.js'] } },
      ],
    };
    const t = checkTraceability(/** @type {any} */ (analyze(doc).model), dir);
    assert.deepEqual(t.unclaimedFiles, []);
    assert.deepEqual(t.multipleOwners.map((m) => m.file), ['src/a.js', 'src/lib/c.js']);
    assert.deepEqual(t.errors.map((e) => [e.code, e.file, e.components]), [
      ['traceability.multiple-owners', 'src/a.js', ['y', 'z']],
      ['traceability.multiple-owners', 'src/lib/c.js', ['x', 'z']],
    ]);
    const specs = path.join(dir, 'specs');
    fs.mkdirSync(path.join(specs, 'p'), { recursive: true });
    fs.writeFileSync(path.join(specs, 'p', 'spec.jsonc'), JSON.stringify(doc));
    const out = await runCommand('traceability', [], { specs, project: 'p', repoRoot: dir });
    assert.equal(out.ok, false);
    assert.equal(out.error.code, 'traceability.multiple-owners');
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
});

// Benchmark: same hash, diagnostics and claim statuses. Exegra: same diagnostics apart from the listed ones, same statuses for every model-decided claim.
// @evidence specs-keep-meaning-without-new-constructs
test('the projects under specs/ keep the diagnostics and claim statuses they had before the element model', () => {
  const baseline = JSON.parse(fs.readFileSync(path.join(ROOT, 'tests/fixtures/multiscale/baseline.json'), 'utf8'));
  const lines = (/** @type {any[]} */ ds) => ds.map((d) => `${d.severity} ${d.code} ${d.entityId ?? ''}`.trim()).sort();

  // The benchmark declares none of the new constructs: same hash, same diagnostics, same claim statuses.
  const bench = analyzeSpec(fs.readFileSync(path.join(ROOT, 'specs/benchmark/spec.jsonc'), 'utf8'));
  assert.equal(bench.model?.semanticHash, baseline.benchmark.semanticHash);
  assert.deepEqual(lines(bench.diagnostics), [...baseline.benchmark.diagnostics].sort());
  assert.deepEqual(Object.fromEntries(evaluateClaims(/** @type {any} */ (bench.model)).map((r) => [r.claimId, r.status])), baseline.benchmark.claims);

  // Exegra's own specification changed on purpose: its diagnostics differ only in the entries the baseline lists
  // with a justification, and every claim the model decides keeps its status.
  // Informational gaps (gap.*) follow every later edit of the self-specification, so only errors and warnings
  // are compared here; the benchmark above is compared exactly.
  const changed = new Set(Object.keys(baseline.exegra.changedDiagnostics));
  const r = analyzeSpec(SELF);
  const notInfo = (/** @type {string} */ l) => !l.startsWith('info ') && !changed.has(l);
  assert.deepEqual(lines(r.diagnostics).filter(notInfo), [...baseline.exegra.diagnostics].filter(notInfo).sort());
  // Every fifth claim the baseline names: the claims repeat their methods, and `verify` evaluates all of them.
  for (const [id, status] of Object.entries(baseline.exegra.claims).filter((_e, i) => i % 5 === 0)) assert.equal(evaluateClaim(/** @type {any} */ (r.model), id).status, status, id);
});
