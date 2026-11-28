// Candidate decompositions (src/core/decomposition.js, WG-5731, M7 structural): generation from the established
// semantics, validity under V1-V4 through the registry, deterministic measurements, boundary evidence, the audit's
// section 5.3 figures, purity and determinism, and the decompose command.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { analyzeSpec } from '../../src/core/analyze.js';
import { initEngine } from '../../src/core/engine.js';
import { semanticHash } from '../../src/core/hash.js';
import { stableStringify } from '../../src/core/stable-json.js';
import { baseFacts } from '../../src/core/abstraction.js';
import { hierarchyOf } from '../../src/core/query.js';
import { readSpecFile } from '../../tools/spec-manifest.js';
import {
  evaluateCandidate, compareCandidates, generateCandidates, candidatesOfData, registerValidityCondition, VALIDITY_CONDITIONS, layering, cyclicComponents,
} from '../../src/core/decomposition.js';

initEngine();

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const FIXTURES = path.join(ROOT, 'tests/fixtures/decomposition');
const readJson = (/** @type {string} */ f) => JSON.parse(fs.readFileSync(path.join(FIXTURES, f), 'utf8'));
/** @type {any} */
let selfModel = null;
const self = () => (selfModel ??= analyzeSpec(readSpecFile(path.join(ROOT, 'specs/exegra/spec.jsonc'))).model);
/** @param {any} doc */
const modelOf = (doc) => {
  const r = analyzeSpec(JSON.stringify(doc, null, 2));
  assert.ok(r.model, JSON.stringify(r.diagnostics.filter((d) => d.severity === 'error')));
  return /** @type {any} */ (r.model);
};
const audit = () => candidatesOfData(readJson('semantic-core-audit.json'));

// ---------------------------------------------------------------------------------------------
// A small system whose every measurement can be checked by hand

const comp = (/** @type {string} */ id, /** @type {any} */ more = {}) => ({ id, name: id, category: 'logical', purpose: 'p', ...more });
const rel = (/** @type {string} */ id, /** @type {string} */ kind, /** @type {string} */ from, /** @type {string} */ to, /** @type {any} */ more = {}) => ({ id, kind, from, to, description: 'd', ...more });
const mod = (/** @type {string} */ p) => ({ implementation: { status: 'manual', modules: [p] } });
const SMALL = {
  exegra: '0.1', system: { id: 'sys', name: 'Sys' },
  contracts: [{ id: 'c1', name: 'C1' }],
  components: [
    comp('core', { kind: 'subsystem' }), comp('ext'),
    comp('a', { parent: 'core', ...mod('src/x/a.js') }), comp('b', { parent: 'core', ...mod('src/x/b.js') }),
    comp('c', { parent: 'core', ...mod('src/y/c.js') }), comp('d', { parent: 'core', ...mod('src/y/d.js') }),
    comp('e', { parent: 'core', ...mod('src/z/e.js') }), comp('f', { parent: 'core', ...mod('src/z/f.js') }),
    comp('bus', { parent: 'core', kind: 'connector', knowledge: 'opaque' }),
  ],
  relationships: [
    rel('a-b', 'invokes', 'a', 'b'), rel('b-a', 'invokes', 'b', 'a'), rel('a-b-again', 'invokes', 'a', 'b'),
    rel('b-c', 'invokes', 'b', 'c', { contract: 'c1' }),
    rel('c-d', 'depends-on', 'c', 'd'), rel('d-c', 'depends-on', 'd', 'c'),
    rel('e-f', 'invokes', 'e', 'f'),
    rel('a-bus', 'publishes', 'a', 'bus'), rel('e-bus', 'subscribes', 'e', 'bus'),
    rel('a-ext', 'invokes', 'a', 'ext'),
  ],
};
const small = () => modelOf(SMALL);
const P = { id: 'p', scope: 'core', blocks: [{ id: 'X', members: ['a', 'b'] }, { id: 'Y', members: ['c', 'd'] }, { id: 'Z', members: ['e', 'f'] }, { id: 'bus', members: ['bus'] }] };

// Every measurement of a small system checked by hand.
// @evidence decomposition-measurements-deterministic
test('a valid candidate is measured by hand-checkable functions of the facts', () => {
  const r = evaluateCandidate(small(), P);
  assert.equal(r.status, 'valid');
  assert.deepEqual(r.conditions.map((c) => `${c.id}:${c.status}`), ['V1:pass', 'V2:pass', 'V3:pass', 'V4:pass', 'V5:pass', 'V6:not-applicable', 'V7:pass']);
  const m = /** @type {any} */ (r.measurements);
  // internal: a-b, b-a, a-b-again, c-d, d-c, e-f; crossing: b-c, a-bus, e-bus; one fact leaves the scope.
  assert.equal(m.facts.internal.all, 6);
  assert.equal(m.facts.crossing.all, 3);
  assert.equal(m.facts.external.all, 1);
  assert.deepEqual([m.facts.crossing.runtime, m.facts.crossing.none], [2, 1]);
  assert.deepEqual([m.facts.internal.static, m.facts.internal.runtime], [2, 4]);
  assert.deepEqual(m.cohesion.overall, { n: 6, d: 9, value: 0.666667 });
  assert.equal(m.coupling.connectedBlockPairs, 3);
  assert.deepEqual(m.blocks, { count: 4, grainElements: 7, singletons: 1, largest: 2, smallest: 1 });
  // the static cycle c <-> d is inside Y, so the blocks have none
  assert.deepEqual(m.cycles.map((c) => [c.class, c.components]), [['static', 0], ['runtime', 0], ['dependency', 0]]);
  // b-c is typed by c1, the other two crossing facts are not
  assert.deepEqual(m.contractCoverage.facts, { n: 1, d: 3, value: 0.333333 });
  assert.deepEqual(m.contractCoverage.blockPairs, { total: 3, covered: 1, partial: 0, uncovered: 2 });
  // a-b-again duplicates a-b
  assert.deepEqual(m.redundancy.declaredDuplicatedByDeclaration, ['a-b-again']);
  assert.equal(m.redundancy.onBoundary, 0);
  assert.deepEqual(m.knowledge.elements, { transparent: 6, opaque: 1, unknown: 0 });
  assert.deepEqual(m.knowledge.boundaryFactProvenance, { declared: 3 });
  // X's interface: out invokes typed c1, out publishes, out invokes to the outside
  assert.equal(m.interface.perBlock.find((/** @type {any} */ p) => p.id === 'X').groups, 3);
});

// Boundary witnesses, back edges by class and uncovered interactions listed per boundary.
// @evidence decomposition-measurements-deterministic
test('evidence names crossing witnesses and cycle back edges and uncovered contracts', () => {
  const m = small();
  const r = evaluateCandidate(m, P);
  const ev = /** @type {any} */ (r.evidence);
  assert.deepEqual(ev.boundaries.map((/** @type {any} */ b) => [b.from, b.to, b.witnesses]), [['X', 'Y', ['b-c']], ['X', 'bus', ['a-bus']], ['Z', 'bus', ['e-bus']]]);
  assert.deepEqual(ev.uncoveredContracts.map((/** @type {any} */ u) => [u.from, u.to, u.facts]), [['X', 'bus', ['a-bus']], ['Z', 'bus', ['e-bus']]]);
  assert.deepEqual(ev.scopeBoundary, [{ block: 'X', facts: ['a-ext'] }]);
  // singletons make the mutual dependencies cycles between blocks, by class
  const cyc = evaluateCandidate(m, { id: 'q', scope: 'core', blocks: ['a', 'b', 'c', 'd', 'e', 'f', 'bus'].map((x) => ({ id: x, members: [x] })) });
  const byClass = Object.fromEntries(/** @type {any} */ (cyc.evidence).cycles.map((/** @type {any} */ c) => [c.class, c.components]));
  assert.deepEqual(Object.keys(byClass), ['static', 'runtime', 'dependency']);
  assert.deepEqual(byClass.static[0].blocks, ['c', 'd']);
  assert.deepEqual(byClass.runtime[0].blocks, ['a', 'b']);
  assert.deepEqual(byClass.dependency.map((/** @type {any} */ c) => c.blocks), [['a', 'b'], ['c', 'd']]);
  const back = byClass.runtime[0].backEdges;
  assert.equal(back.length, 1);
  assert.equal(back[0].witnesses.length, back[0].from === 'a' ? 2 : 1);
  assert.equal(back[0].from, 'b', 'the heavier direction (a to b, two facts) is the layering, the lighter one the back edge');
});

test('layering minimises the witnesses on back edges and is deterministic', () => {
  const w = new Map([['a\0b', 5], ['b\0c', 4], ['c\0a', 1]]);
  assert.deepEqual(layering(['a', 'b', 'c'], w), ['a', 'b', 'c']);
  assert.deepEqual(layering(['c', 'b', 'a'], w), ['a', 'b', 'c']);
  const adj = new Map([['a', new Set(['b'])], ['b', new Set(['a'])], ['c', new Set(['d'])], ['d', new Set()]]);
  assert.deepEqual(cyclicComponents(['a', 'b', 'c', 'd'], adj), [['a', 'b']]);
});

// ---------------------------------------------------------------------------------------------
// Validity: V1 to V4, with the failing condition and witnesses

// The overlapping negative.
// @evidence decomposition-invalid-diagnosed
test('an overlapping candidate is rejected under V1 with the element and both blocks as witnesses', () => {
  const r = evaluateCandidate(small(), { id: 'o', scope: 'core', blocks: [{ id: 'X', members: ['a', 'b', 'c'] }, { id: 'Y', members: ['c', 'd'] }, { id: 'Z', members: ['e', 'f', 'bus'] }] });
  assert.equal(r.status, 'invalid');
  assert.deepEqual(r.failedConditions, ['V1']);
  const f = /** @type {any} */ (r.conditions[0]).failures;
  assert.deepEqual(f.map((/** @type {any} */ x) => x.code), ['overlap']);
  assert.deepEqual(f[0].witnesses, ['X', 'Y', 'c']);
  assert.equal(r.measurements, null);
  assert.deepEqual(r.conditions.slice(1, 4).map((c) => c.status), ['skipped', 'skipped', 'skipped']);
});

// The non-covering negative.
// @evidence decomposition-invalid-diagnosed
test('a non-covering candidate is rejected under V1 naming the elements no block holds', () => {
  const r = evaluateCandidate(small(), { id: 'n', scope: 'core', blocks: [{ id: 'X', members: ['a', 'b'] }, { id: 'Y', members: ['c', 'd'] }] });
  assert.equal(r.status, 'invalid');
  const f = /** @type {any} */ (r.conditions[0]).failures;
  assert.deepEqual(f.map((/** @type {any} */ x) => x.code), ['uncovered']);
  assert.deepEqual(f[0].witnesses, ['bus', 'e', 'f']);
});

// Unknown, outside, below-grain, duplicate, colliding, empty and malformed candidates.
// @evidence decomposition-invalid-diagnosed
test('the other ways a candidate is not a partition each get their own code', () => {
  const m = small();
  const codes = (/** @type {any} */ c) => /** @type {any} */ (evaluateCandidate(m, { scope: 'core', ...c }).conditions[0]).failures.map((/** @type {any} */ x) => x.code);
  const rest = [{ id: 'R', members: ['e', 'f', 'bus', 'c', 'd'] }];
  assert.deepEqual(codes({ id: 'u', blocks: [{ id: 'X', members: ['a', 'b', 'nope'] }, ...rest] }), ['unknown-member']);
  assert.deepEqual(codes({ id: 'u', blocks: [{ id: 'X', members: ['a', 'b', 'ext'] }, ...rest] }), ['outside-scope']);
  assert.deepEqual(codes({ id: 'u', blocks: [{ id: 'X', members: ['a', 'b', 'module:src/x/a.js'] }, ...rest] }), ['below-grain']);
  assert.deepEqual(codes({ id: 'u', blocks: [{ id: 'X', members: ['a', 'b'] }, { id: 'X', members: ['c'] }, ...rest] }), ['duplicate-block']);
  assert.deepEqual(codes({ id: 'u', blocks: [{ id: 'a', members: ['a', 'b'] }, ...rest] }), ['block-id-collision']);
  assert.deepEqual(codes({ id: 'u', blocks: [{ id: 'ext', members: ['a', 'b'] }, ...rest] }), ['block-id-collision']);
  assert.deepEqual(codes({ id: 'u', blocks: [{ id: 'X', members: [] }, ...rest] }), ['empty-block', 'uncovered']);
  assert.deepEqual(codes({ id: 'u', blocks: 'x' }), ['shape.blocks', 'uncovered']);
  assert.deepEqual(codes({ id: 'u', scope: 'ghost', blocks: [] }), ['scope.unknown']);
});

test('a candidate in an unknown scope or with no id is reported, never thrown', () => {
  const r = evaluateCandidate(small(), {});
  assert.equal(r.status, 'invalid');
  assert.ok(/** @type {any} */ (r.conditions[0]).failures.some((/** @type {any} */ x) => x.code === 'shape.id'));
});

test('rest places the elements no block lists and says which', () => {
  const r = evaluateCandidate(small(), { id: 'r', scope: 'core', blocks: [{ id: 'X', members: ['a', 'b'] }, { id: 'Y', members: ['c', 'd'] }], rest: 'Y' });
  assert.equal(r.status, 'valid');
  assert.deepEqual(r.placedByRest, ['bus', 'e', 'f']);
  assert.equal(evaluateCandidate(small(), { id: 'r', scope: 'core', blocks: [{ id: 'X', members: ['a'] }], rest: 'nope' }).status, 'invalid');
});

test('a block named after the element it stands for, or after a composite inside the scope, is allowed', () => {
  const doc = { ...SMALL, components: [...SMALL.components.filter((c) => c.id !== 'core'), comp('core', { kind: 'subsystem' }), comp('mid', { kind: 'subsystem', parent: 'core' }), comp('g', { parent: 'mid', ...mod('src/g.js') })] };
  const r = evaluateCandidate(modelOf(doc), { id: 'm', scope: 'core', grain: 'leaves', blocks: [{ id: 'mid', members: ['g', 'a'] }, { id: 'b', members: ['b'] }, { id: 'rest', members: ['c', 'd', 'e', 'f', 'bus'] }] });
  assert.equal(r.status, 'valid', JSON.stringify(r.conditions.map((c) => c.failures)));
  assert.deepEqual(r.blocks.map((b) => [b.id, b.existing]), [['b', true], ['mid', true], ['rest', false]]);
});

// A condition plugs into the registry and decides validity; a registry without the behavioural conditions reports them as not evaluated.
// @evidence decomposition-invalid-diagnosed
test('a condition registered in the registry decides validity and removing it restores the report', () => {
  const m = small();
  assert.deepEqual(VALIDITY_CONDITIONS.map((c) => c.id), ['V1', 'V2', 'V3', 'V4', 'V5', 'V6', 'V7']);
  const off = registerValidityCondition({ id: 'X1', title: 'stub', needs: ['V1'], check: (ctx) => ctx.candidate.blocks.length > 3 ? [{ code: 'stub.fails', message: 'too many blocks', witnesses: ctx.candidate.blocks.map((b) => b.id) }] : [] });
  try {
    const r = evaluateCandidate(m, P);
    assert.equal(r.status, 'invalid');
    assert.deepEqual(r.failedConditions, ['X1']);
    assert.deepEqual(/** @type {any} */ (r.conditions.find((c) => c.id === 'X1')).failures[0].witnesses, ['X', 'Y', 'Z', 'bus']);
    assert.equal(evaluateCandidate(m, { id: 'few', scope: 'core', blocks: [{ id: 'one', members: ['a', 'b', 'c', 'd', 'e', 'f', 'bus'] }] }).status, 'valid');
  } finally { off(); }
  assert.deepEqual(VALIDITY_CONDITIONS.map((c) => c.id), ['V1', 'V2', 'V3', 'V4', 'V5', 'V6', 'V7']);
  assert.equal(evaluateCandidate(m, P).status, 'valid');
  // A registry without the behavioural conditions never calls a candidate valid: it says they were not evaluated.
  const structural = VALIDITY_CONDITIONS.slice(0, 4);
  const r = evaluateCandidate(m, P, { conditions: structural });
  assert.equal(r.status, 'structurally-valid');
  assert.deepEqual(r.notEvaluated, ['V5', 'V6', 'V7']);
});

// A V3 negative.
// @evidence decomposition-invalid-diagnosed
test('V3 fails when a block that is an element declares a port its boundary does not realise', () => {
  const doc = { ...SMALL, components: SMALL.components.map((c) => (c.id === 'e' ? { ...c, ports: [{ id: 'e-needs', direction: 'requires', contract: 'c1' }] } : c)) };
  const r = evaluateCandidate(modelOf(doc), { id: 'v3', scope: 'core', blocks: [{ id: 'e', members: ['e'] }, { id: 'rest', members: ['a', 'b', 'c', 'd', 'f', 'bus'] }] });
  assert.equal(r.status, 'invalid');
  assert.deepEqual(r.failedConditions, ['V3']);
  assert.deepEqual(/** @type {any} */ (r.conditions.find((c) => c.id === 'V3')).failures[0].witnesses, ['e', 'e-needs']);
});

// ---------------------------------------------------------------------------------------------
// Generation

test('every source generates from the established semantics, and says why one cannot', () => {
  const m = small();
  const g = generateCandidates(m, { scope: 'core' });
  const byId = Object.fromEntries(g.candidates.map((c) => [c.id, c]));
  const partition = (/** @type {any} */ c) => c.blocks.map((/** @type {any} */ b) => b.members.join('+')).sort();
  assert.deepEqual(partition(byId['core-declared']), ['a', 'b', 'bus', 'c', 'd', 'e', 'f']);
  assert.deepEqual(partition(byId['core-directories']), ['a+b', 'bus', 'c+d', 'e+f']);
  assert.deepEqual(partition(byId['core-contract-regions']), ['a+b+bus+e+f', 'c+d']);
  assert.deepEqual(partition(byId['core-connector-regions']), ['a+b+c+d', 'bus', 'e+f']);
  assert.deepEqual(partition(byId['core-cycles-condensed']), ['a+b', 'bus', 'c+d', 'e', 'f']);
  assert.deepEqual(g.skipped.map((s) => s.source), ['refinement'], 'the declared base has single-element blocks only');
  assert.deepEqual(generateCandidates(modelOf({ ...SMALL, relationships: [] }), { scope: 'core', sources: ['cycles', 'contracts', 'connectors'] }).skipped.map((s) => s.source), ['connectors', 'contracts', 'cycles']);
  for (const c of g.candidates) assert.equal(evaluateCandidate(m, c).status, 'valid', c.id);
});

test('cycles are condensed into one block each, and refinements are read off a base candidate', () => {
  const doc = { ...SMALL, relationships: [...SMALL.relationships, rel('d-b', 'invokes', 'd', 'b')] };
  const m = modelOf(doc);
  const g = generateCandidates(m, { scope: 'core', sources: ['cycles'] });
  assert.deepEqual(g.candidates.map((c) => c.id), ['core-cycles-condensed']);
  assert.deepEqual(g.candidates[0].blocks.map((b) => b.members.join('+')).sort(), ['a+b+c+d', 'bus', 'e', 'f']);
  // the base has a block pair in a cycle (X to Y through b-c, Y to X through d-b), a block that falls apart, and an element tied more to another block
  const base = { id: 'base', scope: 'core', blocks: [{ id: 'X', members: ['a', 'b', 'f'] }, { id: 'Y', members: ['c', 'd', 'e'] }, { id: 'bus', members: ['bus'] }] };
  const r = generateCandidates(m, { scope: 'core', sources: ['refinement'], bases: [base] });
  const ops = r.candidates.map((c) => JSON.stringify(c.from?.op));
  assert.ok(ops.some((o) => o.includes('"merge":["X","Y"]')), ops.join('\n'));
  assert.ok(ops.some((o) => o.includes('"split":"X"')), 'f is not connected to a or b');
  assert.ok(ops.some((o) => o.includes('"move":"e"')), 'e depends on f, which lies in X, and on nothing in Y');
  for (const c of r.candidates) { assert.equal(c.from?.candidate, 'base'); assert.equal(evaluateCandidate(m, c).status, 'valid', c.id); }
  assert.ok(r.skipped.some((s) => s.reason.includes('single-element blocks')), 'the declared base has nothing to refine');
});

test('a candidate given as data is read like a generated one', () => {
  assert.equal(candidatesOfData({ scope: 'core', candidates: [P] }).length, 1);
  assert.equal(candidatesOfData([P, P]).length, 2);
  assert.equal(candidatesOfData(P)[0].id, 'p');
});

// ---------------------------------------------------------------------------------------------
// The audit's section 5.3

// The audit section 5.3 figures on the audit-time facts.
// @evidence decomposition-measurements-deterministic
test('the audit figures reproduce on the facts the audit used with 53 crossing and the four-block cycle and the named residual witnesses', () => {
  const m = modelOf(readJson('audit-semantic-core.json'));
  const [first, second] = audit().map((c) => evaluateCandidate(m, c));
  assert.equal(first.status, 'valid');
  // The audit text says 46 internal; the same method over the same 98 relationships between the 41 children gives 45
  // (checked against the old specification by an independent script), and the crossing count is the audit's 53.
  const f = /** @type {any} */ (first.measurements).facts;
  assert.deepEqual([f.internal.dependency, f.crossing.dependency], [45, 53]);
  assert.equal(f.internal.dependency + f.crossing.dependency, 98);
  assert.deepEqual(/** @type {any} */ (first.evidence).cycles.find((/** @type {any} */ c) => c.class === 'dependency').components.map((/** @type {any} */ c) => c.blocks), [['model-kernel', 'simulation', 'verdicts', 'well-formedness']]);
  // the back edges the audit names for the first grouping, exactly
  const named = /** @type {any} */ (first.evidence).cycles.find((/** @type {any} */ c) => c.class === 'dependency').components[0].backEdges.flatMap((/** @type {any} */ e) => e.witnesses).sort();
  assert.deepEqual(named, ['integrity-rules-calls-proof-export', 'lean-call-boundary-calls-formal-semantics', 'parser-reads-claim-method-registry', 'spec-layers-calls-generation-readiness', 'spec-layers-calls-validator', 'validator-calls-metric-claims', 'validator-reads-claim-method-registry']);
  const cycles = /** @type {any} */ (second.evidence).cycles.find((/** @type {any} */ c) => c.class === 'dependency').components;
  assert.deepEqual(cycles.map((/** @type {any} */ c) => c.blocks), [['model-kernel', 'simulation'], ['verdicts', 'well-formedness']]);
  assert.deepEqual(cycles.map((/** @type {any} */ c) => c.backEdges.map((/** @type {any} */ e) => e.witnesses)), [[['lean-call-boundary-calls-formal-semantics']], [['integrity-rules-calls-proof-export', 'validator-calls-metric-claims']]]);
});

// The same groupings on the current specification, recounted independently.
// @evidence decomposition-measurements-deterministic
test('on the current specification the audit groupings are valid and keep the four-block cycle and name their witnesses', () => {
  const m = self();
  const [first, second] = audit().map((c) => evaluateCandidate(m, c, { provenance: ['declared'] }));
  assert.equal(first.status, 'valid');
  assert.equal(second.status, 'valid');
  const dep = (/** @type {any} */ r) => /** @type {any} */ (r.evidence).cycles.find((/** @type {any} */ c) => c.class === 'dependency').components;
  // The cycle of the audit's four blocks now holds `editing` too: the specification declares decomposition-evaluator-calls-transactions,
  // and the evaluator is one of the children the grouping places in simulation, so simulation reaches editing (transactions), which
  // reaches model-kernel and well-formedness. The figures of the audit itself are the audit-time facts' test above.
  assert.deepEqual(dep(first).map((/** @type {any} */ c) => c.blocks), [['editing', 'model-kernel', 'simulation', 'verdicts', 'well-formedness']]);
  assert.ok(dep(first)[0].backEdges.some((/** @type {any} */ e) => e.from === 'simulation' && e.to === 'editing' && e.witnesses.includes('decomposition-evaluator-calls-transactions')));
  const back = dep(second).flatMap((/** @type {any} */ c) => c.backEdges.flatMap((/** @type {any} */ e) => e.witnesses));
  for (const w of ['lean-call-boundary-calls-formal-semantics', 'validator-calls-metric-claims', 'integrity-rules-calls-proof-export']) assert.ok(back.includes(w), w);
  // an independent recount through the parent chain: every declared fact with both ends under a block is internal or crossing
  const h = /** @type {any} */ (hierarchyOf(m));
  const owner = new Map(first.blocks.flatMap((b) => b.members.map((x) => [x, b.id])));
  const blockOf = (/** @type {string} */ e) => { for (let c = e; c; c = h.parent.get(c)) if (owner.has(c)) return owner.get(c); return null; };
  let internal = 0, crossing = 0;
  for (const x of baseFacts(m).facts) {
    if (x.provenance !== 'declared') continue;
    const a = blockOf(x.from), b = blockOf(x.to);
    if (a && b) (a === b ? internal++ : crossing++);
  }
  const f = /** @type {any} */ (first.measurements).facts;
  assert.deepEqual([f.internal.all, f.crossing.all], [internal, crossing]);
  assert.ok(first.placedByRest.length >= 7, 'the planned and later children the audit table does not list');
});

test('semantic-core has at least three valid candidates, one invalid, and the comparison puts them side by side without ranking', () => {
  const m = self();
  const g = generateCandidates(m, { scope: 'semantic-core', bases: audit(), provenance: ['declared'] });
  const chosen = [...audit(), ...g.candidates.filter((c) => ['semantic-core-directories', 'semantic-core-contract-regions'].includes(c.id)),
    { id: 'broken', scope: 'semantic-core', blocks: [{ id: 'one', members: ['parser', 'validator'] }, { id: 'two', members: ['parser'] }] }];
  const cmp = compareCandidates(m, chosen, { provenance: ['declared'] });
  const status = /** @type {any} */ (cmp.rows.find((r) => r.id === 'status')).values;
  assert.equal(status.broken, 'invalid');
  assert.ok(Object.values(status).filter((s) => s === 'valid').length >= 3);
  const broken = cmp.reports.find((r) => r.id === 'broken');
  assert.deepEqual(/** @type {any} */ (broken).conditions[0].failures.map((/** @type {any} */ x) => x.code), ['overlap', 'uncovered']);
  assert.ok(/** @type {any} */ (broken).conditions[0].failures[0].witnesses.includes('parser'));
  assert.deepEqual(cmp.candidates, chosen.map((c) => c.id), 'columns keep the order given');
  for (const r of cmp.rows) assert.deepEqual(Object.keys(r.values), cmp.candidates);
});

// ---------------------------------------------------------------------------------------------
// Purity, determinism, no verdict of meaning

// Model, facts and hash compared before and after.
// @evidence decomposition-evaluation-pure
test('evaluating and generating candidates leaves the model and its facts and its hash as they were', () => {
  const m = self();
  const hash = semanticHash(m);
  const facts = stableStringify(baseFacts(m).facts);
  const entities = stableStringify([...m.entities.values()].map((/** @type {any} */ e) => [e.id, e.data]));
  const rels = m.byKind.relationship.length;
  const g = generateCandidates(m, { scope: 'semantic-core', bases: audit() });
  compareCandidates(m, [...audit(), ...g.candidates.slice(0, 6)]);
  compareCandidates(m, audit(), { provenance: ['declared'] });
  assert.equal(semanticHash(m), hash);
  assert.equal(stableStringify(baseFacts(m).facts), facts);
  assert.equal(stableStringify([...m.entities.values()].map((/** @type {any} */ e) => [e.id, e.data])), entities);
  assert.equal(m.byKind.relationship.length, rels);
});

// Two runs and a shuffled candidate give the same text.
// @evidence decomposition-measurements-deterministic
test('repeated evaluation is byte-identical in any order of blocks and members', () => {
  const m = self();
  const run = () => stableStringify(compareCandidates(m, audit(), { provenance: ['declared'] }));
  const first = run();
  assert.equal(run(), first);
  const shuffled = audit().map((c) => ({ ...c, blocks: [...c.blocks].reverse().map((/** @type {any} */ b) => ({ ...b, members: [...b.members].reverse() })) }));
  assert.equal(stableStringify(compareCandidates(m, shuffled, { provenance: ['declared'] })), first);
  assert.equal(stableStringify(generateCandidates(m, { scope: 'semantic-core' })), stableStringify(generateCandidates(m, { scope: 'semantic-core' })));
});

// No score, rank or meaning key; acceptance is described and not applied.
// @evidence decomposition-evaluation-pure
test('no report ranks or scores or calls a candidate meaningful', () => {
  const m = small();
  const cmp = compareCandidates(m, [P, { id: 'bad', scope: 'core', blocks: [] }]);
  const text = stableStringify(cmp);
  const keys = new Set();
  JSON.stringify(cmp, (k, v) => { keys.add(k); return v; });
  for (const k of keys) assert.doesNotMatch(String(k), /^(score|rank|best|better|recommended|verdict|meaningful)$/i);
  const mentions = text.match(/meaningful/g) ?? [];
  assert.equal(mentions.length, cmp.reports.length + 1, 'only in the notes that say a measurement does not decide it');
  assert.doesNotMatch(text.replace(/Whether a decomposition is meaningful is a judgement they do not make/g, ''), /meaningful/);
  assert.equal(/** @type {any} */ (cmp.reports[0]).acceptance.applied, false);
  assert.equal(/** @type {any} */ (cmp.reports[1]).acceptance, null);
});

test('what accepting a candidate would record is described: a named hierarchy and the components its blocks need', () => {
  const a = /** @type {any} */ (evaluateCandidate(small(), P).acceptance);
  assert.equal(a.hierarchy.id, 'p');
  assert.deepEqual(a.hierarchy.groups.find((/** @type {any} */ g) => g.parent === 'core'), { parent: 'core', members: ['X', 'Y', 'Z', 'bus'] });
  assert.deepEqual(a.components.map((/** @type {any} */ c) => c.id), ['X', 'Y', 'Z']);
});

// ---------------------------------------------------------------------------------------------
// The command

// The command, including an invalid candidate given as data.
// @evidence decomposition-invalid-diagnosed
test('decompose reports candidates and the failing condition of an invalid one and full evidence for one candidate', () => {
  const run = (/** @type {string[]} */ args) => {
    const r = spawnSync(process.execPath, ['cli/exegra.js', 'decompose', '--project', 'exegra', '--scope', 'semantic-core', '--provenance', 'declared', ...args], { cwd: ROOT, encoding: 'utf8', maxBuffer: 64 * 1024 * 1024, env: { ...process.env } });
    assert.equal(r.status, 0, r.stderr + r.stdout.slice(0, 500));
    return JSON.parse(r.stdout);
  };
  const bad = path.join(ROOT, 'tmp-decompose-test.json');
  fs.writeFileSync(bad, JSON.stringify([{ id: 'overlapping', blocks: [{ id: 'a', members: ['parser'] }, { id: 'b', members: ['parser'] }] }]));
  try {
    const all = run(['--file', 'tests/fixtures/decomposition/semantic-core-audit.json', '--source', 'directory']);
    assert.deepEqual(all.result.candidates.map((/** @type {any} */ c) => c.id), ['audit-first', 'audit-second', 'semantic-core-directories']);
    assert.ok(all.result.candidates.every((/** @type {any} */ c) => c.evidence === null), 'evidence only on request');
    assert.deepEqual(all.result.notEvaluated, []);
    const one = run(['--file', 'tests/fixtures/decomposition/semantic-core-audit.json', '--candidate', 'audit-second']);
    assert.equal(one.result.candidates.length, 1);
    assert.ok(one.result.candidates[0].evidence.cycles.length);
    const invalid = run(['--file', 'tmp-decompose-test.json', '--source', 'declared']);
    const o = invalid.result.candidates.find((/** @type {any} */ c) => c.id === 'overlapping');
    assert.equal(o.status, 'invalid');
    assert.equal(o.conditions[0].failures[0].code, 'overlap');
    assert.equal(invalid.semanticHash, all.semanticHash);
  } finally { fs.rmSync(bad, { force: true }); }
});
