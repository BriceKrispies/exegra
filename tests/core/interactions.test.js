// The interaction taxonomy (WG-5693): every relationship kind states a dependency class, a direction and a
// coarsening parent; `calls` is a legacy kind that behaves as `invokes`; relationships carry provenance and
// what they carry; analyses select by class; a connector's publishes and subscribes contract to `notifies`;
// layout follows only dependency-class edges.
import test from 'node:test';
import assert from 'node:assert/strict';
import { analyzeSpec } from '../../src/core/analyze.js';
import { evaluateClaim } from '../../src/core/claims.js';
import { componentGraph, dependencies } from '../../src/core/query.js';
import { layoutScene } from '../../src/core/layout.js';
import { buildModel, isFlowEdge } from '../../src/core/layout/model.js';
import { project } from '../../src/core/projections.js';
import metamodel from '../../src/core/metamodel.json' with { type: 'json' };
import {
  kindInfo, kindClass, kindAncestors, refines, coarsen, effectiveKind, provenanceOf, mediatedInteractions,
  DEPENDENCY_CLASSES, FLOW_DIRECTIONS, PROVENANCES, ROOT_KIND,
} from '../../src/core/interactions.js';

/** A specification text from parts. @param {any} parts */
function spec(parts) {
  return JSON.stringify({ exegra: '0.1', system: { id: 'sys', name: 'Sys' }, ...parts }, null, 1);
}
/** @param {string} id @param {any} [more] */
const comp = (id, more = {}) => ({ id, name: id, category: 'logical', ...more });
/** @param {string} id @param {string} kind @param {string} from @param {string} to @param {any} [more] */
const rel = (id, kind, from, to, more = {}) => ({ id, kind, from, to, ...more });
/** @param {any} r */
const errorsOf = (r) => r.diagnostics.filter((/** @type {any} */ d) => d.severity === 'error');
/** @param {any} r */
const warningCodes = (r) => r.diagnostics.filter((/** @type {any} */ d) => d.severity === 'warning').map((/** @type {any} */ d) => d.code);
/** @param {any} model @param {string} id */
const claimOf = (model, id) => evaluateClaim(model, id);
/** @param {string} id @param {any} evaluate */
const structural = (id, evaluate) => ({ id, kind: 'structural', statement: id, evaluate });

const builtin = /** @type {Record<string, any>} */ (metamodel.vocabulary.relationshipKinds);
const meta = /** @type {any} */ ({ relationshipKinds: builtin });

// ---- the taxonomy ---------------------------------------------------------------------------------

// Every built-in relationship kind states a class a direction and a parent and the kind tree is rooted at interacts-with.
// @evidence interaction-kinds-declare-taxonomy
test('every built-in relationship kind states a class a direction and a parent and the kind tree is rooted at interacts-with', () => {
  for (const [id, k] of Object.entries(builtin)) {
    assert.ok(DEPENDENCY_CLASSES.includes(k.class), `${id} class`);
    assert.ok(FLOW_DIRECTIONS.includes(k.direction?.control) && FLOW_DIRECTIONS.includes(k.direction?.data), `${id} direction`);
    assert.equal(k.dependency, k.class !== 'none', `${id}: the dependency flag is derived from the class`);
    if (id === ROOT_KIND) assert.equal(k.parent, null);
    else {
      assert.equal(typeof k.parent, 'string', `${id} parent`);
      assert.ok(Object.hasOwn(builtin, k.parent), `${id} parent exists`);
      assert.equal(kindAncestors(meta, id).at(-1), ROOT_KIND, `${id} reaches the root`);
    }
  }
  for (const id of ['imports', 'invokes', 'notifies', 'composes', 'network-link', 'data-flow', 'reads', 'writes', 'subscribes', 'publishes', 'observes', 'depends-on', 'calls']) assert.ok(builtin[id], id);
});

// The built-in kinds keep the dependency flag they had and classify as designed.
// @evidence interaction-kinds-declare-taxonomy
test('the built-in kinds keep the dependency flag they had and classify as designed', () => {
  const oldFlags = { 'depends-on': true, calls: true, 'data-flow': false, publishes: false, subscribes: true, reads: true, writes: true, observes: false };
  for (const [id, flag] of Object.entries(oldFlags)) assert.equal(builtin[id].dependency, flag, id);
  assert.equal(kindClass(meta, 'imports'), 'static');
  assert.equal(kindClass(meta, 'depends-on'), 'static');
  for (const id of ['invokes', 'calls', 'reads', 'writes', 'subscribes']) assert.equal(kindClass(meta, id), 'runtime', id);
  for (const id of ['notifies', 'composes', 'data-flow', 'publishes', 'observes', 'network-link', 'exercises']) assert.equal(kindClass(meta, id), 'none', id);
  assert.deepEqual(kindInfo(meta, 'notifies').direction, { control: 'with', data: 'with' });
  assert.deepEqual(kindInfo(meta, 'subscribes').direction, { control: 'against', data: 'against' });
});

// Coarsening a kind relabels it to an ancestor and never changes what analyses read.
// @evidence interaction-kinds-declare-taxonomy
test('coarsening a kind relabels it to an ancestor and never changes what analyses read', () => {
  assert.deepEqual(kindAncestors(meta, 'imports'), ['depends-on', ROOT_KIND]);
  assert.deepEqual(kindAncestors(meta, 'calls'), ['invokes', 'depends-on', ROOT_KIND]);
  assert.ok(refines(meta, 'invokes', 'depends-on'));
  assert.ok(!refines(meta, 'depends-on', 'invokes'));
  assert.equal(coarsen(meta, 'imports', 'depends-on'), 'depends-on');
  assert.equal(coarsen(meta, 'notifies', 'depends-on'), 'notifies');
  assert.equal(kindClass(meta, 'imports'), 'static', 'the class stays that of the original kind');
});

// The three tests below declare vocabulary kinds with class, direction and parent: they need the Lean core built
// from formal/Exegra/Model.lean as changed by WG-5693 (npm run build:formal-wasm).

// A vocabulary kind that states class direction and parent is accepted and its dependency flag is derived.
// @evidence interaction-kinds-declare-taxonomy
test('a vocabulary kind that states class direction and parent is accepted and its dependency flag is derived', () => {
  const text = spec({
    vocabulary: { relationshipKinds: { 'ships-to': { label: 'Ships to', line: 'solid', color: 'blue', class: 'runtime', direction: { control: 'with', data: 'with' }, parent: 'invokes', description: 'Sends a parcel.' } } },
    components: [comp('a'), comp('b')],
    relationships: [rel('r1', 'ships-to', 'a', 'b')],
  });
  const r = analyzeSpec(text);
  assert.deepEqual(errorsOf(r), []);
  const info = kindInfo(/** @type {any} */ (r.model).meta, 'ships-to');
  assert.equal(info.class, 'runtime');
  assert.equal(info.dependency, true);
  assert.equal(info.parent, 'invokes');
  assert.deepEqual(kindAncestors(/** @type {any} */ (r.model).meta, 'ships-to'), ['invokes', 'depends-on', ROOT_KIND]);
  assert.ok(!warningCodes(r).includes('vocabulary.kind-unclassified'));
});

// A vocabulary kind with a partial taxonomy an unknown parent a bad class or a contradicting flag is an error.
// @evidence interaction-kinds-declare-taxonomy
test('a vocabulary kind with a partial taxonomy an unknown parent a bad class or a contradicting flag is an error', () => {
  const base = { label: 'K', line: 'solid', color: 'blue', description: 'k' };
  /** @param {any} kind */
  const codes = (kind) => {
    const r = analyzeSpec(spec({ vocabulary: { relationshipKinds: { k: { ...base, ...kind } } }, components: [comp('a'), comp('b')], relationships: [rel('r1', 'k', 'a', 'b')] }));
    return errorsOf(r).map((/** @type {any} */ d) => d.code);
  };
  const full = { class: 'runtime', direction: { control: 'with', data: 'none' }, parent: 'invokes' };
  assert.deepEqual(codes(full), []);
  assert.deepEqual(codes({ class: 'runtime' }), ['vocabulary.kind-taxonomy', 'vocabulary.kind-taxonomy']);
  assert.deepEqual(codes({ ...full, parent: 'no-such-kind' }), ['vocabulary.kind-taxonomy']);
  assert.deepEqual(codes({ ...full, class: 'sometimes' }), ['vocabulary.kind-taxonomy']);
  assert.deepEqual(codes({ ...full, direction: { control: 'with', data: 'sideways' } }), ['vocabulary.kind-taxonomy']);
  assert.deepEqual(codes({ ...full, parent: null }), ['vocabulary.kind-taxonomy']);
  assert.deepEqual(codes({ ...full, dependency: false }), ['vocabulary.kind-taxonomy'], 'class runtime with dependency false contradicts');
});

// A cycle in the vocabulary kind tree is an error that names the cycle.
// @evidence interaction-kinds-declare-taxonomy
test('a cycle in the vocabulary kind tree is an error that names the cycle', () => {
  /** @param {string} parent */
  const k = (parent) => ({ label: 'K', line: 'solid', color: 'blue', description: 'k', class: 'none', direction: { control: 'none', data: 'none' }, parent });
  const r = analyzeSpec(spec({
    vocabulary: { relationshipKinds: { 'kind-a': k('kind-b'), 'kind-b': k('kind-c'), 'kind-c': k('kind-a') } },
    components: [comp('a'), comp('b')],
    relationships: [rel('r1', 'kind-a', 'a', 'b')],
  }));
  const cyc = errorsOf(r).filter((/** @type {any} */ d) => d.code === 'vocabulary.kind-cycle');
  assert.equal(cyc.length, 1, 'one report per cycle');
  assert.match(cyc[0].message, /kind-a -> kind-b -> kind-c -> kind-a/);
});

// A vocabulary kind written before the taxonomy still works and is warned about not refused.
// @evidence interaction-kinds-declare-taxonomy
test('a vocabulary kind written before the taxonomy still works and is warned about not refused', () => {
  const r = analyzeSpec(spec({
    vocabulary: { relationshipKinds: { mirrors: { label: 'Mirrors', line: 'dotted', color: 'violet', dependency: true, description: 'Mirrors.' } } },
    components: [comp('a'), comp('b')],
    relationships: [rel('r1', 'mirrors', 'a', 'b')],
  }));
  assert.deepEqual(errorsOf(r), []);
  assert.deepEqual(warningCodes(r), ['vocabulary.kind-unclassified']);
  const info = kindInfo(/** @type {any} */ (r.model).meta, 'mirrors');
  assert.equal(info.class, 'runtime', 'a dependency kind of the old shape is runtime');
  assert.equal(info.parent, ROOT_KIND);
  assert.equal(info.classified, false);
});

// ---- the legacy kind ------------------------------------------------------------------------------

/** The same graph and claims, once with `calls` and once with `invokes`. @param {string} kind */
const graphSpec = (kind) => spec({
  components: [comp('a'), comp('b'), comp('c')],
  relationships: [rel('ab', kind, 'a', 'b'), rel('bc', kind, 'b', 'c'), rel('ca', kind, 'c', 'a')],
  claims: [
    structural('no-ab', { method: 'no-relationship', from: 'a', to: 'b' }),
    structural('no-ac-transitive', { method: 'no-relationship', from: 'a', to: 'c', transitive: true }),
    structural('acyclic-default', { method: 'acyclic' }),
    structural('reach', { method: 'reachable', from: 'a', to: 'c' }),
    structural('via', { method: 'only-via', from: 'a', to: 'c', via: 'b' }),
  ],
});

// Calls is a legacy kind: one warning names it there is no error and every verdict equals the one with invokes.
// @evidence legacy-calls-behaves-as-invokes
test('calls is a legacy kind: one warning names it there is no error and every verdict equals the one with invokes', () => {
  const legacy = analyzeSpec(graphSpec('calls'));
  const current = analyzeSpec(graphSpec('invokes'));
  assert.deepEqual(errorsOf(legacy), []);
  const legacyWarnings = legacy.diagnostics.filter((/** @type {any} */ d) => d.code === 'relationship.legacy-kind');
  assert.equal(legacyWarnings.length, 1);
  assert.match(legacyWarnings[0].message, /"calls"/);
  assert.match(legacyWarnings[0].message, /3 relationships/);
  assert.equal(current.diagnostics.filter((/** @type {any} */ d) => d.code === 'relationship.legacy-kind').length, 0);
  for (const id of ['no-ab', 'no-ac-transitive', 'acyclic-default', 'reach', 'via']) {
    assert.equal(claimOf(legacy.model, id).status, claimOf(current.model, id).status, id);
  }
  assert.equal(claimOf(legacy.model, 'acyclic-default').status, 'violated');
  assert.equal(effectiveKind(/** @type {any} */ (legacy.model).meta, 'calls'), 'invokes');
  assert.equal(effectiveKind(/** @type {any} */ (legacy.model).meta, 'imports'), 'imports');
  assert.equal(kindClass(/** @type {any} */ (legacy.model).meta, 'calls'), 'runtime');
});

// ---- provenance -----------------------------------------------------------------------------------

// A relationship states its provenance declared by default and queries expose it.
// @evidence relationships-state-provenance-and-carried-data
test('a relationship states its provenance declared by default and queries expose it', () => {
  const r = analyzeSpec(spec({
    components: [comp('a'), comp('b'), comp('c'), comp('d'), comp('e')],
    relationships: [
      rel('r-default', 'imports', 'a', 'b'),
      rel('r-extracted', 'imports', 'a', 'c', { provenance: 'extracted' }),
      rel('r-observed', 'invokes', 'a', 'd', { provenance: 'observed' }),
      rel('r-derived', 'invokes', 'a', 'e', { provenance: 'derived' }),
      rel('r-assumed', 'invokes', 'b', 'c', { provenance: 'assumed' }),
    ],
  }));
  assert.deepEqual(errorsOf(r), []);
  const model = /** @type {any} */ (r.model);
  assert.deepEqual(PROVENANCES, ['declared', 'extracted', 'observed', 'derived', 'assumed']);
  assert.equal(provenanceOf(model.entities.get('r-default')), 'declared');
  const edges = (componentGraph(model).get('a') ?? []).map((e) => [e.rel, e.provenance]);
  assert.deepEqual(edges, [['r-default', 'declared'], ['r-extracted', 'extracted'], ['r-observed', 'observed'], ['r-derived', 'derived']]);
  assert.equal(componentGraph(model).get('b')?.[0].provenance, 'assumed');
});

// A provenance outside the five values is an error.
// @evidence relationships-state-provenance-and-carried-data
test('a provenance outside the five values is an error', () => {
  const r = analyzeSpec(spec({ components: [comp('a'), comp('b')], relationships: [rel('r1', 'imports', 'a', 'b', { provenance: 'guessed' })] }));
  assert.deepEqual(errorsOf(r).map((/** @type {any} */ d) => d.code), ['property.enum']);
});

// ---- carries --------------------------------------------------------------------------------------

const DATA = {
  records: [{ id: 'order', name: 'Order', owner: 'a', fields: [{ name: 'total', type: 'u32' }] }],
  types: [{ id: 'order-dto', name: 'OrderDto', kind: 'struct', fields: [{ name: 'total', type: 'u32' }] }],
  events: [{ id: 'order-placed', name: 'Order placed' }],
};

// Carries may name records types and events.
// @evidence relationships-state-provenance-and-carried-data
test('carries may name records types and events', () => {
  const r = analyzeSpec(spec({
    components: [comp('a'), comp('b')], ...DATA,
    relationships: [rel('flow', 'data-flow', 'a', 'b', { carries: ['order', 'order-dto', 'order-placed'] })],
  }));
  assert.deepEqual(errorsOf(r), []);
  assert.deepEqual(/** @type {any} */ (r.model).entities.get('flow').data.carries, ['order', 'order-dto', 'order-placed']);
});

// Carries that names a component or nothing is an error.
// @evidence relationships-state-provenance-and-carried-data
test('carries that names a component or nothing is an error', () => {
  /** @param {any} carries */
  const codes = (carries) => errorsOf(analyzeSpec(spec({ components: [comp('a'), comp('b')], ...DATA, relationships: [rel('flow', 'data-flow', 'a', 'b', { carries })] }))).map((/** @type {any} */ d) => d.code);
  assert.deepEqual(codes(['b']), ['ref.kind']);
  assert.deepEqual(codes(['nothing']), ['ref.unresolved']);
});

// ---- class filters --------------------------------------------------------------------------------

const CLASS_SPEC = spec({
  components: [comp('a'), comp('b'), comp('c'), comp('d')],
  relationships: [
    rel('a-imports-b', 'imports', 'a', 'b'),
    rel('b-invokes-a', 'invokes', 'b', 'a'),
    rel('a-composes-c', 'composes', 'a', 'c'),
    rel('c-invokes-a', 'invokes', 'c', 'a'),
    rel('c-notifies-d', 'notifies', 'c', 'd'),
    rel('d-flows-a', 'data-flow', 'd', 'a'),
  ],
  claims: [
    structural('acyclic-static', { method: 'acyclic', classes: ['static'] }),
    structural('acyclic-runtime', { method: 'acyclic', classes: ['runtime'] }),
    structural('acyclic-both-classes', { method: 'acyclic', classes: ['static', 'runtime'] }),
    structural('acyclic-by-kinds', { method: 'acyclic', kinds: ['imports', 'invokes'] }),
    structural('acyclic-default', { method: 'acyclic' }),
    structural('acyclic-none', { method: 'acyclic', classes: ['none'] }),
    structural('acyclic-intersection', { method: 'acyclic', kinds: ['imports', 'invokes'], classes: ['static'] }),
    structural('acyclic-misspelt', { method: 'acyclic', classes: ['runtme'] }),
    structural('no-dependency-a-to-c', { method: 'no-relationship', from: 'a', to: 'c', classes: ['static', 'runtime'] }),
    structural('no-none-a-to-c', { method: 'no-relationship', from: 'a', to: 'c', classes: ['none'] }),
    structural('reach-none-c-to-d', { method: 'reachable', from: 'c', to: 'd', classes: ['none'] }),
    structural('reach-runtime-c-to-d', { method: 'reachable', from: 'c', to: 'd', classes: ['runtime'] }),
  ],
});

// The class filter selects the edges of componentGraph and of dependencies.
// @evidence structural-methods-select-by-dependency-class
test('the class filter selects the edges of componentGraph and of dependencies', () => {
  const r = analyzeSpec(CLASS_SPEC);
  assert.deepEqual(errorsOf(r), []);
  const model = /** @type {any} */ (r.model);
  /** @param {any} opts */
  const edgeIds = (opts) => [...componentGraph(model, opts).values()].flat().map((e) => e.rel).sort();
  assert.deepEqual(edgeIds({ classes: ['static'] }), ['a-imports-b']);
  assert.deepEqual(edgeIds({ classes: ['runtime'] }), ['b-invokes-a', 'c-invokes-a']);
  assert.deepEqual(edgeIds({ classes: ['none'] }), ['a-composes-c', 'c-notifies-d', 'd-flows-a']);
  assert.deepEqual(edgeIds({ classes: ['static', 'runtime'] }), edgeIds({ dependencyOnly: true }), 'static and runtime are exactly the dependency kinds');
  assert.deepEqual(edgeIds({ kinds: ['imports', 'invokes'], classes: ['static'] }), ['a-imports-b'], 'kinds and classes must both hold');
  assert.deepEqual(componentGraph(model, { classes: ['runtime'] }).get('b')?.map((e) => e.class), ['runtime']);
  assert.deepEqual(dependencies(model, 'b', { classes: ['runtime'] }).map((d) => d.id), ['a']);
});

// Acyclic restricted to one class reports cycles of that class only and the kind-based behaviour is unchanged.
// @evidence structural-methods-select-by-dependency-class
test('acyclic restricted to one class reports cycles of that class only and the kind-based behaviour is unchanged', () => {
  const model = /** @type {any} */ (analyzeSpec(CLASS_SPEC).model);
  assert.equal(claimOf(model, 'acyclic-static').status, 'verified', 'one static edge');
  assert.equal(claimOf(model, 'acyclic-runtime').status, 'verified', 'b->a and c->a');
  assert.equal(claimOf(model, 'acyclic-both-classes').status, 'violated', 'a->b (static) and b->a (runtime) close a cycle');
  assert.equal(claimOf(model, 'acyclic-by-kinds').status, 'violated');
  assert.equal(claimOf(model, 'acyclic-default').status, 'violated', 'the default is still the dependency kinds');
  assert.equal(claimOf(model, 'acyclic-none').status, 'violated', 'a->c, c->d, d->a close a cycle of class none');
});

// Classes combine with kinds as an intersection and a misspelt class cannot pass vacuously.
// @evidence structural-methods-select-by-dependency-class
test('classes combine with kinds as an intersection and a misspelt class cannot pass vacuously', () => {
  const model = /** @type {any} */ (analyzeSpec(CLASS_SPEC).model);
  assert.equal(claimOf(model, 'acyclic-intersection').status, 'verified', 'only a->b is both an imports and static, so the cycle through b->a is not followed');
  assert.match(claimOf(model, 'acyclic-intersection').scope, /kinds imports, invokes of class static/);
});

// No-relationship and reachable accept a class filter.
// @evidence structural-methods-select-by-dependency-class
test('no-relationship and reachable accept a class filter', () => {
  const model = /** @type {any} */ (analyzeSpec(CLASS_SPEC).model);
  assert.equal(claimOf(model, 'no-dependency-a-to-c').status, 'verified', 'a reaches c only by composes, whose class is none');
  assert.equal(claimOf(model, 'no-none-a-to-c').status, 'violated');
  assert.equal(claimOf(model, 'reach-none-c-to-d').status, 'verified');
  assert.equal(claimOf(model, 'reach-runtime-c-to-d').status, 'violated', 'c reaches d only by notifies');
  assert.match(claimOf(model, 'no-none-a-to-c').scope, /of class none/);
});

// A misspelt class is inconclusive never verified.
// @evidence structural-methods-select-by-dependency-class
test('a misspelt class is inconclusive never verified', () => {
  const bad = claimOf(/** @type {any} */ (analyzeSpec(CLASS_SPEC).model), 'acyclic-misspelt');
  assert.equal(bad.status, 'inconclusive');
  assert.match(bad.explanation, /Unknown dependency class "runtme"/);
});

// ---- the connector --------------------------------------------------------------------------------

// The connector kind is declared by M1 (WG-5692) as a component kind. Before it merges the component kind enum
// refuses it, so the model is read despite that one error; the query looks only at "the component whose kind is
// connector".
const CONNECTOR_SPEC = spec({
  components: [comp('producer'), comp('bus', { kind: 'connector' }), comp('consumer-1'), comp('consumer-2'), comp('bystander'), comp('lonely-producer')],
  relationships: [
    rel('producer-publishes-bus', 'publishes', 'producer', 'bus', { carries: ['order-placed'] }),
    rel('consumer-1-subscribes-bus', 'subscribes', 'consumer-1', 'bus'),
    rel('consumer-2-subscribes-bus', 'subscribes', 'consumer-2', 'bus'),
    rel('bystander-invokes-producer', 'invokes', 'bystander', 'producer'),
    rel('consumer-1-invokes-bystander', 'invokes', 'consumer-1', 'bystander'),
  ],
  events: [{ id: 'order-placed', name: 'Order placed' }],
});

// A producer a connector and two consumers contract to producer-to-consumer notifies naming the connector.
// @evidence connector-contracts-to-notifies
test('a producer a connector and two consumers contract to producer-to-consumer notifies naming the connector', () => {
  const r = analyzeSpec(CONNECTOR_SPEC);
  assert.deepEqual(errorsOf(r).filter((/** @type {any} */ d) => d.code !== 'property.enum'), [], 'the connector kind is the only thing a pre-M1 enum refuses');
  const model = /** @type {any} */ (r.model);
  const m = mediatedInteractions(model);
  assert.deepEqual(m.map((x) => [x.from, x.to, x.kind, x.connector]), [
    ['producer', 'consumer-1', 'notifies', 'bus'],
    ['producer', 'consumer-2', 'notifies', 'bus'],
  ]);
  assert.deepEqual(m[0].via, ['producer-publishes-bus', 'consumer-1-subscribes-bus']);
  assert.deepEqual(m[0].carries, ['order-placed']);
  assert.equal(m[0].provenance, 'derived');
});

// The contracted graph hides the connector and shows notifies edges the uncontracted graph is unchanged.
// @evidence connector-contracts-to-notifies
test('the contracted graph hides the connector and shows notifies edges the uncontracted graph is unchanged', () => {
  const model = /** @type {any} */ (analyzeSpec(CONNECTOR_SPEC).model);
  const contracted = componentGraph(model, { contractConnectors: true });
  assert.deepEqual(contracted.get('producer')?.map((e) => [e.to, e.kind, e.connector]), [['consumer-1', 'notifies', 'bus'], ['consumer-2', 'notifies', 'bus']]);
  assert.deepEqual(contracted.get('bus'), []);
  assert.deepEqual(contracted.get('consumer-1')?.map((e) => e.rel), ['consumer-1-invokes-bystander'], 'the subscribes edge to the connector is gone');
  assert.deepEqual(componentGraph(model).get('producer')?.map((e) => e.to), ['bus']);
  assert.equal(componentGraph(model, { contractConnectors: true, classes: ['runtime'] }).get('producer')?.length, 0, 'notifies is class none');
});

// No mediated interaction exists without a declared connector element.
// @evidence connector-contracts-to-notifies
test('no mediated interaction exists without a declared connector element', () => {
  // The same specification with the bus an ordinary component: no contraction and no invented direct edge.
  const model = /** @type {any} */ (analyzeSpec(CONNECTOR_SPEC.replace('"kind": "connector"', '"kind": "component"')).model);
  assert.deepEqual(mediatedInteractions(model), []);
  const g = componentGraph(model, { contractConnectors: true });
  assert.deepEqual(g.get('producer')?.map((e) => e.to), ['bus'], 'nothing is contracted, so nothing is hidden either');
});

// A publisher with no subscriber through the same connector is paired with nobody.
// @evidence connector-contracts-to-notifies
test('a publisher with no subscriber through the same connector is paired with nobody', () => {
  const text = spec({
    components: [comp('p'), comp('bus-1', { kind: 'connector' }), comp('bus-2', { kind: 'connector' }), comp('s')],
    relationships: [rel('p-pub', 'publishes', 'p', 'bus-1'), rel('s-sub', 'subscribes', 's', 'bus-2')],
  });
  assert.deepEqual(mediatedInteractions(/** @type {any} */ (analyzeSpec(text).model)), []);
});

// ---- layout ---------------------------------------------------------------------------------------

/** @param {string} id @param {string} from @param {string} to @param {any} [more] */
const edge = (id, from, to, more = {}) => ({ id, entityId: id, entityKind: 'relationship', from, to, line: 'solid', color: 'slate', ...more });
/** @param {string} id */
const leaf = (id) => ({ id, entityId: id, entityKind: 'component', label: id, shape: 'box', color: 'slate', parent: null, container: false });
/** @param {any[]} edges */
const sceneOf = (edges) => /** @type {any} */ ({ viewId: 'x', projection: 'structural', legend: [], notes: [], nodes: ['a', 'b', 'c'].map(leaf), edges });

// Layout orders components by static and runtime edges only.
// @evidence layout-follows-dependency-classes
test('layout orders components by static and runtime edges only', () => {
  assert.equal(isFlowEdge(edge('e', 'a', 'b', { dependencyClass: 'static' })), true);
  assert.equal(isFlowEdge(edge('e', 'a', 'b', { dependencyClass: 'runtime' })), true);
  assert.equal(isFlowEdge(edge('e', 'a', 'b', { dependencyClass: 'none' })), false);
  assert.equal(isFlowEdge(edge('e', 'a', 'b')), true, 'a hand-built scene that states no class keeps its edges');
  assert.equal(isFlowEdge(/** @type {any} */ ({ ...edge('e', 'a', 'b'), entityKind: 'claim' })), false, 'a claim "about" edge is no flow');
  assert.equal(isFlowEdge(/** @type {any} */ ({ ...edge('e', 'a', 'b'), entityKind: 'evidence' })), false);
  const { edgesAt } = buildModel(sceneOf([edge('1', 'a', 'b', { dependencyClass: 'runtime' }), edge('2', 'b', 'c', { dependencyClass: 'none' }), edge('3', 'a', 'c', { entityKind: 'claim' })]));
  assert.deepEqual(edgesAt.get(null), [['a', 'b']]);
});

// An edge of class none against the dependency direction no longer changes the layered order.
// @evidence layout-follows-dependency-classes
test('an edge of class none against the dependency direction no longer changes the layered order', () => {
  const dep = edge('dep', 'a', 'b', { dependencyClass: 'runtime' });
  const dep2 = edge('dep2', 'b', 'c', { dependencyClass: 'runtime' });
  const back = edge('back', 'c', 'a', { dependencyClass: 'none' });
  /** @param {any} scene */
  const xOf = (scene) => {
    const p = layoutScene(scene, {}, { method: 'layered' });
    return ['a', 'b', 'c'].map((id) => p[id].x);
  };
  const withBack = xOf(sceneOf([dep, dep2, back]));
  assert.deepEqual(withBack, xOf(sceneOf([dep, dep2])), 'the none-class edge is ignored, so the placement is that of the chain alone');
  assert.ok(withBack[0] < withBack[1] && withBack[1] < withBack[2], 'a before b before c along the flow');
  assert.deepEqual(withBack, xOf(sceneOf([dep, dep2, back])), 'deterministic');
});

// The structural projection marks each relationship edge with the class of its kind.
// @evidence layout-follows-dependency-classes
test('the structural projection marks each relationship edge with the class of its kind', () => {
  const text = spec({
    components: [comp('a'), comp('b'), comp('c')],
    relationships: [rel('r1', 'imports', 'a', 'b'), rel('r2', 'data-flow', 'b', 'c'), rel('r3', 'calls', 'a', 'c')],
    views: [{ id: 'overview', name: 'Overview', projection: 'structural' }],
  });
  const model = /** @type {any} */ (analyzeSpec(text).model);
  const scene = project(model, 'overview', {});
  assert.deepEqual(Object.fromEntries(scene.edges.map((/** @type {any} */ e) => [e.id, e.dependencyClass])), { r1: 'static', r2: 'none', r3: 'runtime' });
});
