// The semantic abstraction engine (src/core/abstraction.js, WG-5694): the derived architectural model at a cut,
// its invariants I1-I9, level-aware claims, the structural projection and message flows that consume the derived
// model, and footprint-driven re-derivation. Goldens for five cuts of Exegra's own specification live in
// tests/fixtures/abstraction/<cut>.json. When the specification's relationships, components or cuts change on
// purpose, regenerate them with the command line and review the diff:
//   for c in l0 l1 persistence-expanded semantic-core-expanded module-level; do
//     node cli/exegra.js derive --project exegra --cut $c | node -e "let s='';process.stdin.on('data',d=>s+=d).on('end',()=>process.stdout.write(JSON.stringify(JSON.parse(s).result,null,1)+'\n'))" > tests/fixtures/abstraction/$c.json
//   done

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { parse as parseJsonc } from 'jsonc-parser';
import { analyzeSpec } from '../../src/core/analyze.js';
import { initEngine, runScenario } from '../../src/core/engine.js';
import { evaluateClaim } from '../../src/core/claims.js';
import { project, listViews } from '../../src/core/projections.js';
import { stepFlow, flowPaths } from '../../src/core/flows.js';
import { selectComponents, ancestorsOf, componentOf } from '../../src/core/query.js';
import {
  deriveModel, derivedJson, abstractionInvariants, rederive, cutForCollapse, baseFacts, blockAt, interactionKey,
  contractPaths, checkRealisations, lift, relift, emptySummary, combineSummaries,
} from '../../src/core/abstraction.js';
import { claimsToRecompute } from '../../src/core/footprints.js';
import { readSpecFile } from '../../tools/spec-manifest.js';
import { attachExtracted } from '../../src/core/extraction.js';

initEngine();

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const SELF_TEXT = readSpecFile(path.join(ROOT, 'specs/exegra/spec.jsonc'));
/** @type {any} */
let selfModel = null;
const self = () => (selfModel ??= analyzeSpec(SELF_TEXT).model);
const CUTS = ['l0', 'l1', 'persistence-expanded', 'semantic-core-expanded', 'module-level'];
const SUBSYSTEMS = ['semantic-core', 'application', 'visualization', 'persistence', 'agent-interface', 'tooling'];

/** @param {any} doc */
const analyze = (doc) => analyzeSpec(JSON.stringify(doc, null, 2));
/** @param {any} doc */
function modelOf(doc) {
  const r = analyze(doc);
  assert.ok(r.model, JSON.stringify(r.diagnostics.filter((d) => d.severity === 'error')));
  return /** @type {any} */ (r.model);
}
/** @param {string} id @param {any} [more] */
const comp = (id, more = {}) => ({ id, name: id, category: 'logical', purpose: 'p', ...more });
/** @param {string} id @param {string} kind @param {string} from @param {string} to @param {any} [more] */
const rel = (id, kind, from, to, more = {}) => ({ id, kind, from, to, description: 'd', ...more });
/** @param {any[]} components @param {any[]} relationships @param {any} [more] */
const spec = (components, relationships, more = {}) => ({ exegra: '0.1', system: { id: 'sys', name: 'Sys' }, components, relationships, ...more });

// ---------------------------------------------------------------------------------------------
// Goldens and an independent recomputation

/**
 * The lift of a cut recomputed from the raw specification text (the audit's method, appendix A): parents from
 * component.parent, an element with members (component children or declared modules) opened per the cut's
 * depth, expand and finest, and each relationship's ends mapped to the first unopened element on their path from
 * the root (or to themselves when every element on it is opened).
 * @param {any} raw @param {{depth?: number, expand?: string[], finest?: boolean}} cut
 */
function independentLift(raw, cut) {
  const parent = new Map();
  const hasMembers = new Set();
  const portOwner = new Map();
  for (const c of raw.components) {
    if (typeof c.parent === 'string') { parent.set(c.id, c.parent); hasMembers.add(c.parent); }
    if (Array.isArray(c.implementation?.modules) && c.implementation.modules.length) hasMembers.add(c.id);
    for (const p of c.ports ?? []) portOwner.set(p.id, c.id);
  }
  const chain = (/** @type {string} */ e) => { const out = [e]; let cur = e; while (parent.has(cur)) { cur = parent.get(cur); out.unshift(cur); } return out; };
  const opened = (/** @type {string} */ e, /** @type {number} */ depth) => hasMembers.has(e) && (cut.finest === true || depth < (cut.depth ?? 0) || (cut.expand ?? []).includes(e));
  const alpha = (/** @type {string} */ e) => { const ch = chain(e); for (let i = 0; i < ch.length; i++) if (!opened(ch[i], i)) return ch[i]; return e; };
  /** @type {Map<string, string[]>} */
  const edges = new Map();
  /** @type {Map<string, string[]>} */
  const fibres = new Map();
  for (const r of raw.relationships) {
    const a = alpha(portOwner.get(r.from) ?? r.from), b = alpha(portOwner.get(r.to) ?? r.to);
    const into = a === b ? fibres : edges;
    const key = a === b ? a : `${a}->${b}:${r.kind}`;
    if (!into.has(key)) into.set(key, []);
    /** @type {string[]} */ (into.get(key)).push(r.id);
  }
  /** @param {Map<string, string[]>} m */
  const sorted = (m) => Object.fromEntries([...m].map(([k, ws]) => [k, [...ws].sort()]).sort((x, y) => (x[0] < y[0] ? -1 : 1)));
  return { edges: sorted(edges), fibres: sorted(fibres) };
}

test('derived models of the five self-specification cuts equal their goldens and an independent recomputation', () => {
  const model = self();
  // The goldens are what the command line derives: the declared relationships plus the extracted facts (WG-5696).
  const withFacts = attachExtracted(model, JSON.parse(fs.readFileSync(path.join(ROOT, 'specs/exegra/extracted/facts.json'), 'utf8')));
  const raw = parseJsonc(SELF_TEXT);
  for (const c of CUTS) {
    const golden = JSON.parse(fs.readFileSync(path.join(ROOT, `tests/fixtures/abstraction/${c}.json`), 'utf8'));
    assert.deepEqual(derivedJson(/** @type {any} */ (deriveModel(withFacts, c))), golden, `cut ${c} differs from its golden; regenerate it as the header of this file says if the change is intended`);
    // The independent recomputation lifts the declared relationships of the specification text alone.
    const d = derivedJson(/** @type {any} */ (deriveModel(model, c)));
    const decl = raw.cuts.find((/** @type {any} */ x) => x.id === c);
    const ind = independentLift(raw, decl);
    assert.deepEqual(Object.fromEntries(d.interactions.map((/** @type {any} */ i) => [i.key, i.witnesses]).sort((x, y) => (x[0] < y[0] ? -1 : 1))), ind.edges, `cut ${c}: interactions and witnesses`);
    assert.deepEqual(Object.fromEntries(Object.entries(d.fibres).filter(([, ws]) => /** @type {any[]} */ (ws).length)), ind.fibres, `cut ${c}: fibres`);
  }
});

test('the CLI derives the model with no renderer code loaded', () => {
  // Every module the process resolves passes through this hook, which reports the renderer's and the UI's.
  const hook = "import { registerHooks } from 'node:module'; registerHooks({ resolve(s, c, n) { const r = n(s, c); if (r.url.includes('/src/render/') || r.url.includes('/src/ui/') || r.url.includes('/src/core/abstraction.js')) process.stderr.write('LOADED ' + r.url + String.fromCharCode(10)); return r; } });";
  const run = spawnSync(process.execPath, ['--import', `data:text/javascript,${encodeURIComponent(hook)}`, 'cli/exegra.js', 'derive', '--project', 'exegra', '--cut', 'l1'], { cwd: ROOT, encoding: 'utf8', maxBuffer: 64 * 1024 * 1024 });
  assert.equal(run.status, 0, run.stderr);
  const loaded = run.stderr.split('\n').filter((l) => l.startsWith('LOADED '));
  assert.ok(loaded.some((l) => l.endsWith('/src/core/abstraction.js')), 'the hook sees the modules the command loads');
  assert.deepEqual(loaded.filter((l) => l.includes('/src/render/') || l.includes('/src/ui/')), []);
  const out = JSON.parse(run.stdout);
  assert.equal(out.ok, true);
  assert.equal(out.result.cut, 'l1');
  assert.deepEqual(out.result, JSON.parse(fs.readFileSync(path.join(ROOT, 'tests/fixtures/abstraction/l1.json'), 'utf8')));
});

// ---------------------------------------------------------------------------------------------
// Invariants on the self-specification and on generated fact bases

/** A small seeded generator (mulberry32). @param {number} seed */
function rng(seed) {
  let a = seed >>> 0;
  return () => { a = (a + 0x6d2b79f5) >>> 0; let t = a; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
}

/** How many generated specifications the property checks run over. */
const SEEDS = 16;
/** @type {Map<number, any>} */
const generatedModels = new Map();
/** The model of a generated specification, shared by the property checks. @param {number} seed */
const generatedModel = (seed) => { if (!generatedModels.has(seed)) generatedModels.set(seed, modelOf(generated(seed))); return generatedModels.get(seed); };

const GEN_KINDS = ['imports', 'invokes', 'notifies', 'composes', 'data-flow', 'reads', 'writes', 'depends-on'];

/**
 * A generated specification: a random laminar hierarchy of subsystems and components, random relationships, and
 * cuts at depths 0 to 3, the finest cut and a random expansion closed under ancestors.
 * @param {number} seed
 */
function generated(seed) {
  const r = rng(seed);
  const pick = (/** @type {any[]} */ xs) => xs[Math.floor(r() * xs.length)];
  /** @type {any[]} */
  const components = [];
  const subs = ['sys'];
  const n = 6 + Math.floor(r() * 14);
  for (let i = 0; i < n; i++) {
    const isSub = r() < 0.35;
    const parent = r() < 0.15 ? undefined : pick(subs);
    const c = comp(`e${i}`, { ...(isSub ? { kind: 'subsystem' } : {}), ...(parent ? { parent } : {}), ...(r() < 0.3 ? { implementation: { status: 'manual', modules: [`src/g${seed}/m${i}.js`] } } : {}) });
    components.push(c);
    if (isSub) subs.push(c.id);
  }
  const ids = components.map((c) => c.id);
  /** @type {any[]} */
  const relationships = [];
  const m = Math.floor(r() * 3 * n);
  for (let i = 0; i < m; i++) {
    const from = pick(ids), to = pick(ids);
    if (from === to) continue;
    relationships.push(rel(`r${i}`, pick(GEN_KINDS), from, to));
  }
  const composite = new Set(components.filter((c) => c.parent).map((c) => c.parent));
  const expand = ['sys', ...components.filter((c) => composite.has(c.id) && (c.parent === 'sys' || !c.parent) && r() < 0.6).map((c) => c.id)].filter((x) => composite.has(x) || x === 'sys');
  const cuts = [0, 1, 2, 3].map((d) => ({ id: `d${d}`, name: `D${d}`, depth: d }));
  cuts.push({ id: 'fin', name: 'Finest', finest: true });
  if (composite.has('sys')) cuts.push({ id: 'mix', name: 'Mixed', expand });
  return spec(components, relationships, { cuts });
}

test('witness completeness and boundary accounting hold on every self-specification cut and on generated fact bases', () => {
  const names = ['witness-completeness', 'boundary-accounting', 'kind-preservation', 'determinism'];
  const own = abstractionInvariants(self(), CUTS, names);
  for (const n of names) assert.deepEqual(own.faults[n], [], n);
  assert.ok(own.interactions > 0);
  for (let seed = 1; seed <= SEEDS; seed++) {
    const r = abstractionInvariants(generatedModel(seed), undefined, names);
    for (const n of names) assert.deepEqual(r.faults[n], [], `seed ${seed}: ${n}`);
  }
  // The pure rule alone: every fact is placed exactly once, crossing facts by their kind.
  const facts = [{ id: 'f1', kind: 'invokes', from: 'a', to: 'b' }, { id: 'f2', kind: 'invokes', from: 'a2', to: 'b' }, { id: 'f3', kind: 'reads', from: 'a', to: 'a2' }];
  const alpha = (/** @type {string} */ e) => (e.startsWith('a') ? 'A' : 'B');
  const l = lift(facts, alpha, (k) => k);
  assert.deepEqual([...l.interactions.entries()], [['A->B:invokes', { from: 'A', to: 'B', kind: 'invokes', witnesses: ['f1', 'f2'] }]]);
  assert.deepEqual([...l.fibres.entries()], [['A', ['f3']]]);
});

test('fibres and witness sets recover the base facts of every block', () => {
  const model = self();
  const { facts } = baseFacts(model);
  for (const c of CUTS) {
    const d = /** @type {any} */ (deriveModel(model, c));
    const alpha = (/** @type {string} */ e) => blockAt(d.level, e);
    for (const b of d.blocks) {
      const touching = facts.filter((f) => alpha(f.from) === b.id || alpha(f.to) === b.id).map((f) => f.id).sort();
      const recovered = [...d.fibres[b.id], ...d.interactions.filter((/** @type {any} */ i) => i.from === b.id || i.to === b.id).flatMap((/** @type {any} */ i) => i.witnesses)].sort();
      assert.deepEqual(recovered, touching, `cut ${c}, block ${b.id}`);
    }
    const all = [...Object.values(d.fibres).flat(), ...d.interactions.flatMap((/** @type {any} */ i) => i.witnesses)].sort();
    assert.deepEqual(all, facts.map((f) => f.id).sort(), `cut ${c}: every relationship exactly once`);
  }
  assert.deepEqual(abstractionInvariants(model, CUTS, ['recoverability', 'interfaces-from-boundaries']).faults, { recoverability: [], 'interfaces-from-boundaries': [] });
});

test('deriving through an intermediate cut equals deriving directly on self-specification cut pairs and generated hierarchies', () => {
  const own = abstractionInvariants(self(), undefined, ['functoriality']);
  assert.deepEqual(own.faults.functoriality, []);
  for (const pair of [['module-level', 'l1'], ['persistence-expanded', 'l0'], ['semantic-core-expanded', 'l1'], ['l1', 'l0'], ['runtime-placed', 'runtime-hosts']]) {
    assert.ok(own.pairs.some(([a, b]) => a === pair[0] && b === pair[1]), `pair ${pair.join(' <= ')} compared`);
  }
  let compared = 0;
  for (let seed = 1; seed <= SEEDS; seed++) {
    const r = abstractionInvariants(generatedModel(seed), undefined, ['functoriality', 'recoverability', 'interfaces-from-boundaries']);
    assert.deepEqual(r.faults, { functoriality: [], recoverability: [], 'interfaces-from-boundaries': [] }, `seed ${seed}`);
    compared += r.pairs.length;
  }
  assert.ok(compared > 60, `${compared} generated cut pairs compared`);
  // The summary is a monoid: identity and associativity on concrete values.
  const s1 = { ...emptySummary(), count: 1, kinds: { invokes: 1 }, contracts: ['c'] };
  const s2 = { ...emptySummary(), count: 2, kinds: { reads: 2 }, provenance: { declared: 2 } };
  const s3 = { ...emptySummary(), count: 1, kinds: { invokes: 1 }, delivery: ['at-least-once'] };
  assert.deepEqual(combineSummaries(emptySummary(), s1), combineSummaries(s1, emptySummary()));
  assert.deepEqual(combineSummaries(combineSummaries(s1, s2), s3), combineSummaries(s1, combineSummaries(s2, s3)));
  assert.deepEqual(combineSummaries(s1, s3), combineSummaries(s3, s1));
  // relift merges witnesses and summaries.
  const merged = relift({ interactions: [{ from: 'a', to: 'b', kind: 'invokes', witnesses: ['x'], summary: s1 }, { from: 'a2', to: 'b', kind: 'invokes', witnesses: ['y'], summary: s3 }], fibres: {} }, (e) => (e.startsWith('a') ? 'A' : 'B'));
  assert.deepEqual(merged.interactions.map((i) => [i.key, i.witnesses, i.summary.count]), [['A->B:invokes', ['x', 'y'], 2]]);
});

// ---------------------------------------------------------------------------------------------
// Interfaces, ports and contracts

test('every declared port of the self-specification is matched or reported unmatched and the write-file path flags its untyped hops', () => {
  const model = self();
  const d = /** @type {any} */ (deriveModel(model, 'module-level'));
  const ports = model.byKind.port ?? [];
  assert.ok(ports.length >= 15);
  for (const p of ports) {
    const row = d.interfaces[p.owner]?.ports.find((/** @type {any} */ x) => x.port === p.id);
    assert.ok(row, `port ${p.id} is reconciled at the block of ${p.owner}`);
    const unmatched = d.diagnostics.some((/** @type {any} */ x) => x.code === 'interface.unrealised-port' && x.port === p.id);
    assert.equal(row.matches.length === 0, unmatched, `port ${p.id}: unmatched exactly when reported`);
  }
  assert.deepEqual(d.interfaces['session'].ports.find((/** @type {any} */ x) => x.port === 'session-write-out').matches, ['out:invokes:write-file']);
  const wf = contractPaths(model).find((c) => c.contract === 'write-file');
  assert.ok(wf);
  const pathHops = wf.paths.map((p) => p.hops.map((h) => h.relationship));
  // Two paths: the browser's save path, and the agent CLI's in-process hop, which declares write-file since WG-5728.
  assert.deepEqual(pathHops, [['agent-cli-calls-workspace-service'], ['session-calls-persistence-client', 'persistence-client-calls-dev-server-plugin', 'dev-server-plugin-calls-workspace-service']]);
  assert.deepEqual(wf.paths[0].flagged, [], 'the agent CLI hop carries the ws-* events of the contract');
  const save = wf.paths[1];
  const hops = save.hops;
  assert.equal(hops[1].status, 'typed');
  assert.ok(hops[1].contractEvents.includes('write-file-request'));
  assert.equal(hops[2].status, 'typed', 'the in-process hop to the workspace service carries ws-* events of the contract (WG-5728)');
  assert.ok(hops[2].contractEvents.includes('ws-write') && hops[2].contractEvents.includes('ws-write-done'));
  assert.deepEqual(save.flagged, ['session-calls-persistence-client'], 'only the session hop, whose events carry no contract, is left flagged');
});

/** Two components joined through ports. @param {any} fromPort @param {any} toPort @param {any} [relMore] */
function portSpec(fromPort, toPort, relMore = {}) {
  return spec(
    [comp('a', { ports: [{ id: 'a-out', name: 'Out', ...fromPort }] }), comp('b', { ports: [{ id: 'b-in', name: 'In', ...toPort }] })],
    [rel('a-to-b', 'invokes', 'a-out', 'b-in', relMore)],
    { contracts: [{ id: 'c1', name: 'C1' }, { id: 'c2', name: 'C2' }], cuts: [{ id: 'fin', name: 'Finest', finest: true }] },
  );
}

test('a relationship can end at a port and incompatible port connections are diagnostics', () => {
  const good = analyze(portSpec({ direction: 'requires', contract: 'c1' }, { direction: 'provides', contract: 'c1' }, { contract: 'c1' }));
  assert.deepEqual(good.diagnostics.filter((d) => d.severity === 'error').map((d) => d.code), []);
  const d = /** @type {any} */ (deriveModel(/** @type {any} */ (good.model), 'fin'));
  assert.deepEqual(d.interactions.map((/** @type {any} */ i) => [i.from, i.to, i.summary.ports]), [['a', 'b', ['a-out', 'b-in']]]);
  assert.deepEqual(d.interfaces.a.ports, [{ port: 'a-out', direction: 'requires', contract: 'c1', matches: ['out:invokes:c1'] }]);
  assert.deepEqual(d.interfaces.b.ports, [{ port: 'b-in', direction: 'provides', contract: 'c1', matches: ['in:invokes:c1'] }]);
  const codes = (/** @type {any} */ doc) => analyze(doc).diagnostics.filter((x) => x.severity === 'error').map((x) => x.code);
  assert.deepEqual(codes(portSpec({ direction: 'requires', contract: 'c1' }, { direction: 'requires', contract: 'c1' })), ['relationship.port-direction']);
  assert.deepEqual(codes(portSpec({ direction: 'requires', contract: 'c1' }, { direction: 'provides', contract: 'c2' })), ['relationship.port-contract']);
  assert.deepEqual(codes(portSpec({ direction: 'requires', contract: 'c1' }, { direction: 'provides', contract: 'c1' }, { contract: 'c2' })), ['relationship.port-contract']);
});

// ---------------------------------------------------------------------------------------------
// One negative fixture per diagnostic

test('negative fixtures produce one explicit diagnostic each', () => {
  const tree = [comp('s1', { kind: 'subsystem', parent: 'sys' }), comp('s2', { kind: 'subsystem', parent: 'sys' }), comp('a', { parent: 's1' }), comp('b', { parent: 's2' })];
  const top = { cuts: [{ id: 'top', name: 'Top', depth: 1 }] };
  const diag = (/** @type {any} */ doc, /** @type {string} */ cut) => /** @type {any} */ (deriveModel(modelOf(doc), cut)).diagnostics.map((/** @type {any} */ x) => x.code);

  // V2: a coarse fact at transparent composites that no member fact witnesses.
  assert.deepEqual(diag(spec(tree, [rel('s1-s2', 'invokes', 's1', 's2')], top), 'top'), ['abstraction.unwitnessed']);
  assert.deepEqual(diag(spec(tree, [rel('s1-s2', 'invokes', 's1', 's2'), rel('a-b', 'invokes', 'a', 'b')], top), 'top'), [], 'witnessed by a member fact');
  // V4: a coarse kind that its member facts do not coarsen to.
  assert.deepEqual(diag(spec(tree, [rel('s1-s2', 'invokes', 's1', 's2'), rel('a-b', 'data-flow', 'a', 'b')], top), 'top'), ['abstraction.kind-not-coarsening']);
  // V3 encapsulation: the declared interface omits a typed boundary interaction.
  const contracts = [{ id: 'c1', name: 'C1' }, { id: 'c2', name: 'C2' }];
  const enc = spec([comp('a', { ports: [{ id: 'a-req', name: 'Req', direction: 'requires', contract: 'c1' }] }), comp('b'), comp('c')],
    [rel('a-b', 'invokes', 'a', 'b', { contract: 'c1' }), rel('a-c', 'invokes', 'a', 'c', { contract: 'c2' })], { contracts, cuts: [{ id: 'fin', name: 'Finest', finest: true }] });
  assert.deepEqual(diag(enc, 'fin'), ['interface.undeclared-boundary']);
  // V3 realisation: a declared port nothing realises.
  const real = spec([comp('a', { ports: [{ id: 'a-prov', name: 'Prov', direction: 'provides', contract: 'c1' }] }), comp('b')],
    [rel('a-b', 'invokes', 'a', 'b')], { contracts, cuts: [{ id: 'fin', name: 'Finest', finest: true }] });
  assert.deepEqual(diag(real, 'fin'), ['interface.unrealised-port']);
  // A realisation map whose path does not exist.
  const missing = analyze(spec([comp('a'), comp('b')], [rel('a-b', 'invokes', 'a', 'b')], { realisations: [{ id: 'rm', interaction: 'a-b', hierarchy: 'logical', path: ['no-such-link'] }] }));
  assert.ok(missing.diagnostics.some((x) => x.code === 'realisation.path-missing' && x.entityId === 'rm'));
  // A level-bound claim that names an element hidden at its cut.
  const hidden = modelOf(spec(tree, [rel('a-b', 'invokes', 'a', 'b')], {
    ...top,
    claims: [{ id: 'cl', kind: 'structural', statement: 's', evaluate: { method: 'no-relationship', cut: 'top', from: 'a', to: 's2' } }],
  }));
  const r = evaluateClaim(hidden, 'cl');
  assert.equal(r.status, 'inconclusive');
  assert.match(r.explanation, /^Not expressible at this level: the "from" selector names "a", which is hidden inside block "s1"/);
  assert.deepEqual(r.diagnostics?.map((x) => x.code), ['claim.not-expressible']);
  // Selecting part of a block is not expressible either.
  const partial = modelOf(spec([...tree, comp('a2', { parent: 's1', tags: ['t'] })], [rel('a-b', 'invokes', 'a', 'b')], {
    ...top,
    claims: [{ id: 'cl', kind: 'structural', statement: 's', evaluate: { method: 'no-relationship', cut: 'top', from: { tag: 't' }, to: 's2' } }],
  }));
  assert.match(evaluateClaim(partial, 'cl').explanation, /picks only part of block "s1"/);
});

// ---------------------------------------------------------------------------------------------
// Level-aware claims

test('core-independent-of-ui restated at L1 keeps its verdict over the same leaves and covers four more components', () => {
  const model = self();
  const restated = evaluateClaim(model, 'core-independent-of-ui');
  assert.equal(restated.status, 'verified', restated.explanation);
  assert.deepEqual(restated.level, { hierarchy: 'logical', cut: 'l1' });
  const claim = /** @type {any} */ (model.entities.get('core-independent-of-ui'));
  const ev = claim.data.evaluate;
  // The hand-written form it replaces, evaluated over the leaves.
  const oldTargets = ['application', 'visualization', 'persistence', 'agent-interface', 'tooling', 'threejs-library', 'vite-dev-server', 'browser-platform', 'browser-storage', 'filesystem', 'playwright-runner', 'ai-coding-agent'];
  const oldEval = { method: 'no-relationship', from: 'semantic-core', to: oldTargets, kinds: ev.kinds, transitive: true };
  const old = { ...claim, data: { ...claim.data, evaluate: oldEval } };
  const fake = { ...model, entities: new Map(model.entities), byKind: { ...model.byKind, claim: model.byKind.claim.map((/** @type {any} */ c) => (c.id === claim.id ? old : c)) } };
  fake.entities.set(claim.id, old);
  assert.equal(evaluateClaim(fake, claim.id).status, 'verified', 'the hand-written form holds over the leaves');
  const oldLeaves = new Set(selectComponents(model, oldTargets).map((c) => c.id));
  const newLeaves = new Set(selectComponents(model, ev.to).map((c) => c.id));
  for (const id of oldLeaves) assert.ok(newLeaves.has(id), `${id} stays covered`);
  for (const id of ['markdown-specification-source', 'external-test-runner', 'sqlite-engine']) assert.ok(newLeaves.has(id), `${id} is now covered`);
  assert.ok(!newLeaves.has('jsonc-parser-library'), 'the parser library is excluded');
  const except = ev.to.except.find((/** @type {any} */ x) => x.id === 'jsonc-parser-library');
  assert.match(except.reason, /parser-depends-on-jsonc-parser/, 'and the exclusion states why');
  for (const x of ev.to.except) assert.ok(x.reason.length > 20, `${x.id} is excluded with a reason`);
  assert.ok(!newLeaves.has('semantic-core') && ![...newLeaves].some((id) => ancestorsOf(model, id).includes('semantic-core')), 'nothing inside the core is a target');
});

test('a spurious coarse path is may-reachable and not verified', () => {
  const doc = spec(
    [comp('x', { kind: 'subsystem', parent: 'sys' }), comp('y', { kind: 'subsystem', parent: 'sys' }), comp('z', { kind: 'subsystem', parent: 'sys' }), comp('x1', { parent: 'x' }), comp('y1', { parent: 'y' }), comp('y2', { parent: 'y' }), comp('z1', { parent: 'z' })],
    [rel('x1-y1', 'invokes', 'x1', 'y1'), rel('y2-z1', 'invokes', 'y2', 'z1')],
    {
      cuts: [{ id: 'top', name: 'Top', depth: 1 }],
      claims: [
        { id: 'coarse-reach', kind: 'structural', statement: 's', evaluate: { method: 'reachable', cut: 'top', from: 'x', to: 'z' } },
        { id: 'leaf-reach', kind: 'structural', statement: 's', evaluate: { method: 'reachable', from: 'x1', to: 'z1' } },
        { id: 'coarse-absence', kind: 'structural', statement: 's', evaluate: { method: 'no-relationship', cut: 'top', from: 'x', to: 'z', transitive: true } },
      ],
    },
  );
  const model = modelOf(doc);
  const coarse = evaluateClaim(model, 'coarse-reach');
  assert.equal(coarse.status, 'inconclusive');
  assert.match(coarse.explanation, /^May-reachable only/);
  assert.deepEqual(coarse.counterexample?.path, ['x', 'x1-y1', 'y', 'y2-z1', 'z']);
  assert.equal(evaluateClaim(model, 'leaf-reach').status, 'violated', 'no base path exists');
  assert.equal(evaluateClaim(model, 'coarse-absence').status, 'inconclusive', 'nor is absence established at the coarse level');
  // Witnessed by a path inside the middle block, the same coarse path is a must-path.
  const witnessed = modelOf({ ...doc, relationships: [...doc.relationships, rel('y1-y2', 'invokes', 'y1', 'y2')] });
  assert.equal(evaluateClaim(witnessed, 'coarse-reach').status, 'verified');
  assert.equal(evaluateClaim(witnessed, 'coarse-absence').status, 'violated');
});

test('a cycle only between two subsystems is reported by acyclic at that cut', () => {
  const model = modelOf(spec(
    [comp('s1', { kind: 'subsystem', parent: 'sys' }), comp('s2', { kind: 'subsystem', parent: 'sys' }), comp('a1', { parent: 's1' }), comp('a2', { parent: 's1' }), comp('b1', { parent: 's2' }), comp('b2', { parent: 's2' })],
    [rel('a1-b1', 'invokes', 'a1', 'b1'), rel('b2-a2', 'invokes', 'b2', 'a2')],
    {
      cuts: [{ id: 'top', name: 'Top', depth: 1 }],
      claims: [
        { id: 'leaf-acyclic', kind: 'structural', statement: 's', evaluate: { method: 'acyclic' } },
        { id: 'top-acyclic', kind: 'structural', statement: 's', evaluate: { method: 'acyclic', cut: 'top' } },
      ],
    },
  ));
  assert.equal(evaluateClaim(model, 'leaf-acyclic').status, 'verified', 'the leaves form no cycle');
  const top = evaluateClaim(model, 'top-acyclic');
  assert.equal(top.status, 'violated');
  assert.deepEqual([...(top.counterexample?.entities ?? [])].sort(), ['a1-b1', 'b2-a2', 's1', 's2']);
  assert.match(top.explanation, /statement about blocks/);
});

// ---------------------------------------------------------------------------------------------
// Presentation consumes the derived model

/** Every subset of a list. @param {string[]} xs @returns {string[][]} */
const subsets = (xs) => xs.reduce((acc, x) => [...acc, ...acc.map((s) => [...s, x])], /** @type {string[][]} */ ([[]]));

test('structural scene edges equal derived edges for every view and collapse set of the self-specification', () => {
  const model = self();
  const views = listViews(model).filter((v) => v.projection === 'structural');
  assert.ok(views.length >= 4);
  const comps = model.byKind.component;
  for (const v of views) {
    const filter = /** @type {any} */ (model.entities.get(v.id))?.data.filter ?? {};
    const inScope = new Set(comps.map((/** @type {any} */ c) => c.id).filter((/** @type {string} */ id) => typeof filter.within !== 'string' || id === filter.within || ancestorsOf(model, id).includes(filter.within)));
    const kinds = Array.isArray(filter.relationshipKinds) && filter.relationshipKinds.length ? filter.relationshipKinds : null;
    for (const set of subsets(SUBSYSTEMS)) {
      const collapsed = new Set(set);
      const scene = project(model, v.id, { collapsed });
      // 1. Independently: each relationship in scope goes to its outermost collapsed visible subsystem, or stays.
      const rep = (/** @type {string} */ id) => [...ancestorsOf(model, id).reverse(), id].find((a) => collapsed.has(a) && inScope.has(a)) ?? id;
      /** @type {Map<string, string[]>} */
      const expected = new Map();
      for (const r of model.byKind.relationship) {
        const f = componentOf(model, r.data.from)?.id, t = componentOf(model, r.data.to)?.id;
        if (!f || !t || !inScope.has(f) || !inScope.has(t) || (kinds && !kinds.includes(r.data.kind))) continue;
        const a = rep(f), b = rep(t);
        if (a === b) continue;
        const key = interactionKey(a, b, r.data.kind);
        expected.set(key, [...(expected.get(key) ?? []), r.id]);
      }
      const drawn = new Map(scene.edges.map((e) => [interactionKey(e.from, e.to, /** @type {string} */ (e.kind)), [...(e.witnesses ?? [])]]));
      assert.deepEqual(new Map([...drawn].sort()), new Map([...expected].map(([k, ws]) => /** @type {[string, string[]]} */ ([k, ws.sort()])).sort()), `${v.id} collapsed ${set.join(',') || 'none'}`);
      // 2. The scene draws the derived model of its cut, restricted by the view's filters.
      assert.deepEqual(scene.abstraction?.blocks, cutForCollapse(model, collapsed, (id) => inScope.has(id)).blocks);
      const d = /** @type {any} */ (deriveModel(model, /** @type {any} */ (scene.abstraction)));
      for (const e of scene.edges) {
        const i = d.interactions.find((/** @type {any} */ x) => x.from === e.from && x.to === e.to && x.kind === e.kind);
        assert.ok(i, `${v.id}: ${e.from} -> ${e.to} is a derived interaction`);
        assert.ok((e.witnesses ?? []).every((w) => i.witnesses.includes(w)));
        assert.ok((e.witnesses ?? []).includes(e.entityId), 'the backing relationship is one of the witnesses');
      }
    }
  }
});

test('flows follow the declared edge of the visual-edit-flow save hop collapsed and expanded', () => {
  const model = self();
  const trace = runScenario(model, 'visual-edit-flow');
  const flows = trace.steps.map((/** @type {any} */ s) => stepFlow(model, s));
  const save = flows.findIndex((f) => f.event === 'write-intent' && f.to.some((r) => r.component === 'persistence-client'));
  assert.ok(save >= 0, 'the scenario sends write-intent to the persistence client, the entry of the save path (WG-5728, WG-5729)');
  assert.equal(flows[save].from, 'session');
  const expanded = project(model, 'architecture', { collapsed: new Set() });
  const collapsed = project(model, 'architecture', { collapsed: new Set(SUBSYSTEMS) });
  const hop = (/** @type {any} */ scene, /** @type {number} */ i) => flowPaths(model, scene, flows[i]).find((p) => 'to' in p && (p.to === 'persistence-client' || p.to === 'persistence'));
  assert.deepEqual(hop(expanded, save), { kind: 'edge', from: 'session', to: 'persistence-client', edgeId: 'session-calls-persistence-client', reverse: false });
  assert.deepEqual(hop(collapsed, save), { kind: 'edge', from: 'application', to: 'persistence', edgeId: 'session-calls-persistence-client', reverse: false }, 'the same witness at both levels');
  // A hop a relationship between the two components witnesses follows the edge at both levels.
  const declared = flows.findIndex((f) => f.from === 'transactions' && f.to.some((r) => r.component === 'session'));
  assert.ok(declared >= 0);
  {
    const paths = [expanded, collapsed].map((s) => flowPaths(model, s, flows[declared]).find((p) => 'to' in p && (p.to === 'session' || p.to === 'application')));
    assert.deepEqual(paths.map((p) => p && 'edgeId' in p ? [p.kind, p.edgeId] : p), [['edge', 'transactions-data-flow-session'], ['edge', 'transactions-data-flow-session']]);
  }
});

// ---------------------------------------------------------------------------------------------
// Realisation maps and connectors

test('realisation maps between a logical and a deployment hierarchy are checked as facts', () => {
  const doc = spec(
    [comp('frontend'), comp('backend'), comp('browser-host', { kind: 'external' }), comp('server-host', { kind: 'external' })],
    [rel('frontend-calls-backend', 'invokes', 'frontend', 'backend'), rel('browser-to-server', 'network-link', 'browser-host', 'server-host'), rel('server-to-browser', 'network-link', 'server-host', 'browser-host')],
    {
      hierarchies: [{ id: 'deployment', name: 'Deployment', groups: [{ parent: 'browser-host', members: ['frontend'] }, { parent: 'server-host', members: ['backend'] }] }],
      realisations: [
        { id: 'over-the-network', interaction: 'frontend-calls-backend', hierarchy: 'deployment', path: ['browser-to-server'] },
        { id: 'wrong-way', interaction: 'frontend-calls-backend', hierarchy: 'deployment', path: ['server-to-browser'] },
        { id: 'broken', interaction: 'frontend-calls-backend', hierarchy: 'deployment', path: ['browser-to-server', 'browser-to-server'] },
      ],
    },
  );
  const r = analyze(doc);
  const model = /** @type {any} */ (r.model);
  const checked = Object.fromEntries(checkRealisations(model).map((x) => [x.id, x]));
  assert.equal(checked['over-the-network'].holds, true);
  assert.deepEqual(checked['wrong-way'].problems.map((p) => p.code), ['realisation.endpoint', 'realisation.endpoint']);
  assert.deepEqual(checked.broken.problems.map((p) => p.code), ['realisation.path-broken']);
  const errors = r.diagnostics.filter((d) => d.severity === 'error').map((d) => `${d.code} ${d.entityId}`).sort();
  assert.deepEqual(errors, ['realisation.endpoint wrong-way', 'realisation.endpoint wrong-way', 'realisation.path-broken broken']);
  // The realisation facts are part of every derived model.
  assert.deepEqual(/** @type {any} */ (deriveModel(model, { hierarchy: 'deployment', depth: 0 })).realisations.map((/** @type {any} */ x) => [x.id, x.holds]), [['broken', false], ['over-the-network', true], ['wrong-way', false]]);
});

test('connector-mediated interactions contract through declared connectors only', () => {
  const model = modelOf(spec(
    [comp('left', { kind: 'subsystem', parent: 'sys' }), comp('producer', { parent: 'left' }), comp('consumer', { parent: 'sys' }), comp('topic', { kind: 'connector', parent: 'sys' }), comp('loner', { parent: 'sys' })],
    [rel('producer-publishes-topic', 'publishes', 'producer', 'topic'), rel('consumer-subscribes-topic', 'subscribes', 'consumer', 'topic'), rel('loner-publishes-topic', 'publishes', 'loner', 'topic')],
    { cuts: [{ id: 'top', name: 'Top', depth: 1 }, { id: 'fin', name: 'Finest', finest: true }] },
  ));
  const top = /** @type {any} */ (deriveModel(model, 'top'));
  assert.deepEqual(top.connectors.map((/** @type {any} */ c) => [c.from, c.to, c.via, c.witnesses]), [
    ['loner', 'consumer', 'topic', ['consumer-subscribes-topic', 'loner-publishes-topic']],
    ['left', 'consumer', 'topic', ['consumer-subscribes-topic', 'producer-publishes-topic']],
  ]);
  assert.ok(!top.interactions.some((/** @type {any} */ i) => i.from === 'left' && i.to === 'consumer'), 'no direct edge is invented');
});

// ---------------------------------------------------------------------------------------------
// Footprints and incremental re-derivation

/**
 * The self-specification's model with one edit applied to its relationships or components, as a new snapshot.
 * @param {any} model @param {{op: string, id: string, data?: any}} edit
 */
function edited(model, edit) {
  const entities = new Map(model.entities);
  let rels = model.byKind.relationship;
  let comps = model.byKind.component;
  const current = entities.get(edit.id);
  if (edit.op === 'delete') { entities.delete(edit.id); rels = rels.filter((/** @type {any} */ r) => r.id !== edit.id); }
  else if (edit.op === 'add') {
    const proto = rels[0];
    const r = { ...proto, id: edit.id, data: { ...edit.data, id: edit.id } };
    entities.set(edit.id, r);
    rels = [...rels, r];
  } else {
    const next = { ...current, data: { ...current.data, ...edit.data } };
    entities.set(edit.id, next);
    if (current.kind === 'relationship') rels = rels.map((/** @type {any} */ r) => (r.id === edit.id ? next : r));
    else comps = comps.map((/** @type {any} */ c) => (c.id === edit.id ? next : c));
  }
  return { ...model, entities, byKind: { ...model.byKind, relationship: rels, component: comps } };
}

test('footprint invalidation equals full re-derivation over a randomised sequence of edits', () => {
  const r = rng(5694);
  const pick = (/** @type {any[]} */ xs) => xs[Math.floor(r() * xs.length)];
  let model = self();
  const leaves = model.byKind.component.filter((/** @type {any} */ c) => c.data.kind !== 'subsystem').map((/** @type {any} */ c) => c.id);
  const kinds = ['invokes', 'imports', 'reads', 'writes', 'data-flow', 'notifies', 'composes', 'depends-on'];
  const graphClaims = model.byKind.claim.filter((/** @type {any} */ c) => ['no-relationship', 'reachable', 'only-via', 'acyclic'].includes(c.data.evaluate?.method)).map((/** @type {any} */ c) => c.id);
  const strip = (/** @type {any} */ x) => { const { semanticHash, ...rest } = x; return rest; };
  /** @type {Map<string, any>} */
  let results = new Map(graphClaims.map((/** @type {string} */ id) => [id, evaluateClaim(model, id)]));
  /** @type {Record<string, any>} */
  let derived = Object.fromEntries(CUTS.map((c) => [c, deriveModel(model, c)]));
  let structural = 0, selective = 0, added = 0;
  for (let step = 0; step < 200; step++) {
    const rels = model.byKind.relationship;
    const roll = r();
    /** @type {{op: string, id: string, data?: any}} */
    let edit;
    if (roll < 0.25) edit = { op: 'set', id: pick(rels).id, data: { kind: pick(kinds) } };
    else if (roll < 0.45) edit = { op: 'set', id: pick(rels).id, data: { to: pick(leaves) } };
    else if (roll < 0.6) edit = { op: 'set', id: pick(rels).id, data: { description: `edit ${step}` } };
    else if (roll < 0.78) { edit = { op: 'add', id: `added-${step}`, data: { kind: pick(kinds), from: pick(leaves), to: pick(leaves), description: 'added' } }; added++; }
    else if (roll < 0.95) edit = { op: 'delete', id: pick(rels).id };
    else edit = { op: 'set', id: pick(leaves), data: { parent: pick(SUBSYSTEMS) } };
    const before = model;
    const after = edited(before, edit);
    const affected = [edit.id];
    for (const c of CUTS) {
      const inc = rederive(derived[c], before, after, affected);
      const full = /** @type {any} */ (deriveModel(after, c));
      assert.deepEqual(derivedJson(inc.derived), derivedJson(full), `step ${step} (${edit.op} ${edit.id}), cut ${c}`);
      if (inc.recomputed.all) { if (c === CUTS[0]) structural++; }
      else {
        // Exactly the interactions whose footprint (witnesses, before or after) holds the edited relationship.
        const holding = new Set([...derived[c].interactions, ...full.interactions].filter((/** @type {any} */ i) => i.witnesses.includes(edit.id)).map((/** @type {any} */ i) => i.key));
        assert.deepEqual(inc.recomputed.interactions, [...holding].sort(), `step ${step}, cut ${c}: recomputed set`);
      }
      derived[c] = inc.derived;
    }
    const dirty = claimsToRecompute([...results.values()], before, after, affected);
    /** @type {Map<string, any>} */
    const next = new Map();
    for (const id of graphClaims) {
      const fresh = evaluateClaim(after, id);
      const kept = dirty.has(id) ? fresh : results.get(id);
      assert.deepEqual(strip(kept), strip(fresh), `step ${step} (${edit.op} ${edit.id}): claim ${id} kept a stale result`);
      next.set(id, kept);
    }
    if (dirty.size < graphClaims.length) selective++;
    results = next;
    model = after;
  }
  assert.ok(structural > 0 && added > 0 && selective > 50, `structural ${structural}, added ${added}, selective ${selective}`);
});

test('per-edit re-derivation is measured against full derivation on the self-specification', (t) => {
  // The recorded measurement (docs/assessment/2026-11-27/m3-abstraction.md) comes from this procedure: 50 seeded
  // relationship edits; for each, the five cuts are derived in full and re-derived from the edit's affected set.
  const r = rng(7);
  let model = self();
  let derived = Object.fromEntries(CUTS.map((c) => [c, deriveModel(model, c)]));
  let full = 0, inc = 0;
  for (let i = 0; i < 50; i++) {
    const rel0 = model.byKind.relationship[Math.floor(r() * model.byKind.relationship.length)];
    const after = edited(model, { op: 'set', id: rel0.id, data: { description: `m ${i}` } });
    let s = performance.now();
    for (const c of CUTS) deriveModel(after, c);
    full += performance.now() - s;
    const again = edited(model, { op: 'set', id: rel0.id, data: { description: `m ${i}` } });
    s = performance.now();
    for (const c of CUTS) derived[c] = rederive(derived[c], model, again, [rel0.id]).derived;
    inc += performance.now() - s;
    model = again;
  }
  t.diagnostic(`full derivation of 5 cuts: ${(full / 50).toFixed(2)} ms per edit; footprint re-derivation: ${(inc / 50).toFixed(2)} ms per edit`);
  assert.ok(Number.isFinite(full) && Number.isFinite(inc));
});
