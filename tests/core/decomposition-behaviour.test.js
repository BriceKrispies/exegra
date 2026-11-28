// The behavioural validity of a candidate decomposition (V5, V6, V7), accepting a candidate as a transaction, and the
// generate-evaluate-accept procedure on the three external fixtures (WG-5735, M7; src/core/decomposition.js). Each
// condition has a negative fixture; acceptance is checked against the undo history and the application's own queries;
// the reports under docs/assessment/2026-11-27/m7/ are pinned by what they say about each fixture.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { analyzeSpec } from '../../src/core/analyze.js';
import { Project } from '../../src/core/project.js';
import { initEngine } from '../../src/core/engine.js';
import { semanticHash } from '../../src/core/hash.js';
import { stableStringify } from '../../src/core/stable-json.js';
import { baseFacts, deriveModel } from '../../src/core/abstraction.js';
import { hierarchyOf } from '../../src/core/query.js';
import { evaluateClaim } from '../../src/core/claims.js';
import { evaluateCandidate, compareCandidates, generateCandidates, candidatesOfData, acceptCandidate } from '../../src/core/decomposition.js';

initEngine();

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const EXT = path.join(ROOT, 'tests/fixtures/multiscale-external');
/** @param {string} text */
const stripComments = (text) => text.split(/\r?\n/).filter((l) => !l.trim().startsWith('//')).join('\n');
/** @param {any} doc */
const modelOf = (doc) => {
  const r = analyzeSpec(JSON.stringify(doc, null, 2));
  assert.ok(r.model, JSON.stringify(r.diagnostics.filter((d) => d.severity === 'error')));
  return /** @type {any} */ (r.model);
};
const status = (/** @type {any} */ r, /** @type {string} */ id) => r.conditions.find((/** @type {any} */ c) => c.id === id);

// ---------------------------------------------------------------------------------------------
// V5: messages between blocks

const machine = (/** @type {string} */ id, /** @type {string} */ subject, /** @type {[string, string, string[]][]} */ transitions) => ({
  id, name: id, subject, initial: `${id}-s`, states: [{ id: `${id}-s`, name: 's' }],
  transitions: transitions.map(([t, on, emits]) => ({ id: `${id}-${t}`, from: `${id}-s`, to: `${id}-s`, on, effects: emits.map((e) => ({ emit: e })) })),
});
const events = (/** @type {string[]} */ ids) => ids.map((id) => ({ id, name: id }));

/** front sends ping to store and pong to cache; store and cache are inside back; only front-calls-cache is declared. @param {any[]} [more] */
function pingSpec(more = []) {
  return {
    exegra: '0.1', system: { id: 'sys', name: 'Sys' },
    components: [
      { id: 'front', name: 'Front', category: 'logical', parent: 'sys' },
      { id: 'back', name: 'Back', category: 'logical', kind: 'subsystem', parent: 'sys' },
      { id: 'store', name: 'Store', category: 'storage', parent: 'back' },
      { id: 'cache', name: 'Cache', category: 'storage', parent: 'back' },
    ],
    relationships: [{ id: 'front-calls-cache', kind: 'invokes', from: 'front', to: 'cache' }, ...more],
    events: events(['start', 'ping', 'pong']),
    behaviors: [machine('front-m', 'front', [['go', 'start', ['ping', 'pong']]]), machine('store-m', 'store', [['hear', 'ping', []]]), machine('cache-m', 'cache', [['hear', 'pong', []]])],
    scenarios: [{ id: 'run', name: 'Run', behaviors: ['front-m', 'store-m', 'cache-m'], steps: [{ at: 0, event: 'start' }] }],
  };
}

// V5 negative fixture and its positive.
// @evidence decomposition-behavioural-validity
test('V5 rejects a candidate whose block pair carries a message only over a different witness', () => {
  const m = modelOf(pingSpec([{ id: 'front-calls-store', kind: 'invokes', from: 'front', to: 'store' }]));
  // With the relationship between the two elements themselves the message is witnessed, and a candidate that separates them is valid.
  const split = { id: 'split', scope: 'sys', blocks: [{ id: 'front', members: ['front'] }, { id: 'back', members: ['back'] }] };
  assert.equal(evaluateCandidate(m, split).status, 'valid');
  // Without it, only front-calls-cache joins the two blocks: coarse agreement without structural agreement.
  const bad = evaluateCandidate(modelOf(pingSpec()), split);
  assert.equal(bad.status, 'invalid');
  assert.deepEqual(bad.failedConditions, ['V5']);
  const f = status(bad, 'V5').failures;
  assert.deepEqual(f.map((/** @type {any} */ x) => x.code), ['message.different-witness']);
  for (const w of ['ping', 'front-m', 'store-m', 'front', 'store', 'front-calls-cache']) assert.ok(f[0].witnesses.includes(w), w);
  assert.equal(bad.measurements, null, 'an invalid candidate is not measured');
  assert.equal(bad.acceptance, null);
});

test('V5 holds where the message is internal to a block and reports how many crossed', () => {
  const m = modelOf(pingSpec());
  const r = evaluateCandidate(m, { id: 'inner', scope: 'sys', grain: 'leaves', blocks: [{ id: 'fs', members: ['front', 'store', 'cache'] }] });
  assert.equal(r.status, 'valid');
  assert.deepEqual(status(r, 'V5').detail, { messages: 2, internal: 2, crossing: 0, unplaced: 0 });
});

// ---------------------------------------------------------------------------------------------
// V7: contracts typed on the boundaries between blocks

const CONTRACT = { id: 'c', name: 'C', inputs: [{ name: 'x', type: 'string' }], outputs: [{ name: 'y', type: 'string' }] };
/** @param {boolean} typed */
function contractSpec(typed) {
  const req = typed ? { contract: 'c', role: 'request', payload: [{ name: 'x', type: 'string' }] } : {};
  const res = typed ? { contract: 'c', role: 'response', payload: [{ name: 'y', type: 'string' }] } : {};
  return {
    exegra: '0.1', system: { id: 'sys', name: 'Sys' },
    components: [{ id: 'a', name: 'A', category: 'logical', parent: 'sys' }, { id: 'b', name: 'B', category: 'logical', parent: 'sys' }],
    relationships: [{ id: 'a-calls-b', kind: 'invokes', from: 'a', to: 'b', contract: 'c' }],
    contracts: [CONTRACT],
    events: [{ id: 'go', name: 'go' }, { id: 'req', name: 'req', ...req }, { id: 'res', name: 'res', ...res }],
    behaviors: [machine('a-m', 'a', [['send', 'go', ['req']], ['got', 'res', []]]), machine('b-m', 'b', [['serve', 'req', ['res']]])],
    scenarios: [{ id: 'run', name: 'Run', behaviors: ['a-m', 'b-m'], steps: [{ at: 0, event: 'go' }] }],
  };
}
const AB = { id: 'ab', scope: 'sys', blocks: [{ id: 'a', members: ['a'] }, { id: 'b', members: ['b'] }] };

// V7 negative fixture and its positive.
// @evidence decomposition-behavioural-validity
test('V7 rejects a candidate that puts an untyped contract on the boundary between two blocks with the hop and its events', () => {
  const bad = evaluateCandidate(modelOf(contractSpec(false)), AB);
  assert.equal(bad.status, 'invalid');
  assert.deepEqual(bad.failedConditions, ['V7']);
  const f = status(bad, 'V7').failures;
  assert.deepEqual(f.map((/** @type {any} */ x) => x.code), ['contract.untyped']);
  for (const w of ['a-calls-b', 'c', 'req', 'res', 'a', 'b']) assert.ok(f[0].witnesses.includes(w), w);
  // Typed, the same candidate is valid and the hop is counted as typed.
  const good = evaluateCandidate(modelOf(contractSpec(true)), AB);
  assert.equal(good.status, 'valid');
  assert.deepEqual(status(good, 'V7').detail, { boundary: 1, typed: 1, untyped: 0, unmodelled: 0, outside: { hops: 0, untyped: [] } });
  // Untyped but inside one block, the hop is no boundary of the candidate.
  const inner = evaluateCandidate(modelOf(contractSpec(false)), { id: 'one', scope: 'sys', blocks: [{ id: 'ab', members: ['a', 'b'] }] });
  assert.equal(inner.status, 'valid');
  assert.equal(status(inner, 'V7').detail.boundary, 0);
});

test('V7 does not hold a candidate to a hop between a block and the outside of its scope and reports it', () => {
  const doc = contractSpec(false);
  doc.components = [{ id: 'in', name: 'In', category: 'logical', kind: 'subsystem', parent: 'sys' }, { ...doc.components[0], parent: 'in' }, doc.components[1]];
  const r = evaluateCandidate(modelOf(doc), { id: 'inside', scope: 'in', blocks: [{ id: 'a', members: ['a'] }] });
  assert.equal(r.status, 'valid');
  assert.deepEqual(status(r, 'V7').detail.outside, { hops: 1, untyped: ['a-calls-b'] });
});

// ---------------------------------------------------------------------------------------------
// V6: refinement where a block declares abstract behaviour

const compositionDoc = () => {
  const doc = JSON.parse(stripComments(fs.readFileSync(path.join(ROOT, 'tests/fixtures/composition/spec.jsonc'), 'utf8')));
  // The writer's put is consumed by the abstraction of the store as a whole: V5 asks a relationship between the two elements themselves.
  doc.relationships.push({ id: 'writer-invokes-store', kind: 'invokes', from: 'writer', to: 'store' });
  return doc;
};
const TOP = { id: 'top-split', scope: 'top', blocks: [{ id: 'app', members: ['app'] }, { id: 'store', members: ['store'] }] };

// V6 certificate and counterexample on the composition fixture.
// @evidence decomposition-behavioural-validity
test('V6 checks the abstraction a block declares: a certificate passes and a counterexample rejects with its scenario and events', () => {
  const ok = evaluateCandidate(modelOf(compositionDoc()), TOP);
  assert.equal(ok.status, 'valid');
  assert.equal(status(ok, 'V6').status, 'pass');
  assert.deepEqual(status(ok, 'V6').detail.checked.map((/** @type {any} */ c) => [c.block, c.abstraction, c.verdict]), [['store', 'store-flow', 'certificate'], ['store', 'store-top-flow', 'certificate']]);
  assert.deepEqual(ok.notApplicable, []);
  const doc = compositionDoc();
  doc.behaviors.find((/** @type {any} */ b) => b.id === 'store-flow').variables[0].initial = 't9';
  const bad = evaluateCandidate(modelOf(doc), TOP);
  assert.equal(bad.status, 'invalid');
  assert.deepEqual(bad.failedConditions, ['V6']);
  const f = status(bad, 'V6').failures.find((/** @type {any} */ x) => x.witnesses.includes('store-flow'));
  assert.equal(f.code, 'refinement.counterexample');
  for (const w of ['store-flow', 'store', 'writer-at-store', 'conflicted', 'saved']) assert.ok(f.witnesses.includes(w), w);
  assert.equal(bad.measurements, null);
});

// V6 not applicable with its reason.
// @evidence decomposition-behavioural-validity
test('V6 is not applicable where no block declares abstract behaviour and says why', () => {
  const r = evaluateCandidate(modelOf(contractSpec(true)), AB);
  assert.equal(r.status, 'valid');
  const v6 = status(r, 'V6');
  assert.equal(v6.status, 'not-applicable');
  assert.match(v6.reason, /declares abstract behaviour/);
  assert.deepEqual(r.notApplicable, ['V6']);
  assert.ok(r.notes.some((n) => n.startsWith('V6 does not apply')));
  // Fresh block names stand for no element, so they carry no behaviour either.
  const fresh = evaluateCandidate(modelOf(compositionDoc()), { id: 'fresh', scope: 'top', blocks: [{ id: 'writers', members: ['app'] }, { id: 'keepers', members: ['store'] }] });
  assert.equal(status(fresh, 'V6').status, 'not-applicable');
});

// ---------------------------------------------------------------------------------------------
// Acceptance is a transaction

// Acceptance, undo and redo.
// @evidence decomposition-acceptance-transaction
test('accepting a candidate records a named hierarchy and the components it needs in one undoable transaction', () => {
  const text = JSON.stringify(contractSpec(true), null, 2);
  const project = new Project({ specText: text });
  const h0 = project.semanticHash;
  const cand = { id: 'pair', name: 'The pair', scope: 'sys', grain: /** @type {const} */ ('leaves'), blocks: [{ id: 'both', members: ['a', 'b'] }] };
  const dry = acceptCandidate(project, cand, { dryRun: true });
  assert.ok(dry.ok);
  assert.equal(project.semanticHash, h0, 'a dry run changes nothing');
  assert.equal(project.canUndo, false);
  const accepted = acceptCandidate(project, cand, { label: 'Accept pair' });
  assert.ok(accepted.ok, accepted.message);
  assert.deepEqual(accepted.operations.map((o) => `${o.type}:${o.kind}:${o.data.id}`), ['CreateEntity:component:both', 'CreateEntity:hierarchy:pair', 'CreateEntity:cut:pair-top', 'CreateEntity:cut:pair-cut']);
  const model = /** @type {any} */ (project.model);
  assert.equal(project.history.at(-1).label, 'Accept pair');
  assert.equal(project.history.length, 1, 'one transaction');
  const h = /** @type {any} */ (hierarchyOf(model, 'pair'));
  assert.equal(h.problems.length, 0);
  assert.deepEqual([h.parent.get('a'), h.parent.get('b'), h.parent.get('both')], ['both', 'both', 'sys']);
  // The application's queries read it at once: the cut opens the scope into the new block, and the logical hierarchy is as it was.
  const d = /** @type {any} */ (deriveModel(model, 'pair-cut'));
  assert.deepEqual(d.level.blocks, ['both']);
  assert.deepEqual(d.diagnostics.filter((/** @type {any} */ x) => x.severity === 'error'), []);
  assert.equal(/** @type {any} */ (hierarchyOf(model)).parent.get('a'), 'sys', 'a stays where the logical hierarchy has it');
  // Undo reverses all of it as one step, and redo returns it.
  assert.ok(project.canUndo);
  project.undo();
  assert.equal(project.semanticHash, h0);
  assert.equal(project.model?.entities.has('pair'), false);
  project.redo();
  assert.equal(project.semanticHash, accepted.transaction.semanticHash);
});

// Refusals.
// @evidence decomposition-acceptance-transaction
test('a candidate that is not valid is not accepted and neither is one that cannot be recorded', () => {
  const project = new Project({ specText: JSON.stringify(contractSpec(false)) });
  const h0 = project.semanticHash;
  const bad = acceptCandidate(project, AB);
  assert.equal(bad.ok, false);
  assert.equal(bad.code, 'accept.not-valid');
  assert.match(/** @type {string} */ (bad.message), /V7 failed/);
  assert.equal(project.semanticHash, h0);
  const doc = contractSpec(true);
  doc.components = [{ ...doc.components[0], implementation: { status: 'manual', modules: ['src/a.js'] } }, doc.components[1]];
  const modules = acceptCandidate(new Project({ specText: JSON.stringify(doc) }), { id: 'mods', scope: 'sys', grain: 'modules', blocks: [{ id: 'm', members: ['module:src/a.js'] }] });
  assert.equal(modules.ok, false);
  assert.equal(modules.code, 'accept.unrecordable');
});

// What a hierarchy cannot record is listed.
// @evidence decomposition-acceptance-transaction
test('a module element the candidate places in a block stays with its component and is listed with the elements it empties', () => {
  const doc = {
    exegra: '0.1', system: { id: 'sys', name: 'Sys' },
    components: [
      { id: 'core', name: 'Core', category: 'logical', kind: 'subsystem', implementation: { status: 'manual', modules: ['src/core/types.js'] } },
      { id: 'mid', name: 'Mid', category: 'logical', kind: 'subsystem', parent: 'core' },
      { id: 'x', name: 'X', category: 'logical', parent: 'mid' },
      { id: 'y', name: 'Y', category: 'logical', parent: 'core' },
    ],
    relationships: [{ id: 'x-y', kind: 'invokes', from: 'x', to: 'y' }],
  };
  const m = modelOf(doc);
  const r = evaluateCandidate(m, { id: 'regroup', scope: 'core', grain: 'children', blocks: [{ id: 'all', members: ['mid', 'y', 'module:src/core/types.js'] }] });
  assert.equal(r.status, 'valid');
  const a = /** @type {any} */ (r.acceptance);
  assert.deepEqual(a.unrecorded, [{ element: 'module:src/core/types.js', block: 'all' }]);
  const project = new Project({ specText: JSON.stringify(doc) });
  const done = acceptCandidate(project, { id: 'regroup', scope: 'core', grain: 'children', blocks: [{ id: 'all', members: ['mid', 'y', 'module:src/core/types.js'] }] });
  assert.ok(done.ok, done.message);
  const d = /** @type {any} */ (deriveModel(/** @type {any} */ (project.model), 'regroup-cut'));
  assert.ok(d.level.blocks.includes('module:src/core/types.js'), 'the module element stands as a block of its own at the cut');
});

// ---------------------------------------------------------------------------------------------
// The external fixtures

/** @param {string} name @param {string} scope */
function external(name, scope) {
  const text = fs.readFileSync(path.join(EXT, `${name}.jsonc`), 'utf8');
  const model = /** @type {any} */ (analyzeSpec(text).model);
  const common = { scope, grain: /** @type {const} */ ('leaves') };
  const given = candidatesOfData(JSON.parse(fs.readFileSync(path.join(EXT, `${name}-candidates.json`), 'utf8'))).map((c) => ({ ...common, ...c }));
  const generated = generateCandidates(model, { ...common, bases: given });
  const all = [...given, ...generated.candidates];
  const hash = semanticHash(model);
  const facts = stableStringify(baseFacts(model).facts);
  const cmp = compareCandidates(model, all, { ...common, evidence: true });
  // Evaluating leaves the fact base and its hash alone, and repeating it is byte-identical.
  assert.equal(semanticHash(model), hash);
  assert.equal(stableStringify(baseFacts(model).facts), facts);
  assert.equal(stableStringify(compareCandidates(model, all, { ...common, evidence: true })), stableStringify(cmp));
  const byId = Object.fromEntries(cmp.reports.map((r) => [r.id, r]));
  return { text, model, all, cmp, byId, common, generated };
}
/** The accepted project, with the transaction undone and redone. @param {string} text @param {any} cand @param {any} common */
function accept(text, cand, common) {
  const project = new Project({ specText: text });
  const h0 = project.semanticHash;
  const r = acceptCandidate(project, cand, common);
  assert.ok(r.ok, r.message);
  const h1 = project.semanticHash;
  project.undo();
  assert.equal(project.semanticHash, h0, 'undo restores the specification');
  project.redo();
  assert.equal(project.semanticHash, h1);
  assert.equal(analyzeSpec(project.specText).errorCount, 0);
  return { project, model: /** @type {any} */ (project.model) };
}
/** A claim at the accepted cut, added by a second transaction. @param {Project} project @param {string} id @param {string} cut @param {string} from @param {string} to @param {string[]} kinds */
function claimAt(project, id, cut, from, to, kinds) {
  const tx = project.apply([{ type: 'AddClaim', data: { id, kind: 'structural', statement: 'x', subjects: [from, to], evaluate: { method: 'no-relationship', cut, from, to, kinds } } }]);
  assert.ok(tx.ok, tx.message);
  return evaluateClaim(/** @type {any} */ (project.model), id);
}

// The compiler.
// @evidence decomposition-external-fixtures
test('compiler: candidates and validity and measurements then acceptance with a level-bound claim and functional composition intact', () => {
  const { text, byId, common, cmp } = external('compiler', 'compiler');
  assert.deepEqual(['compiler-pipeline-thirds', 'compiler-front-and-back', 'compiler-syntax-first', 'compiler-declared'].map((i) => byId[i].status), ['valid', 'valid', 'valid', 'valid']);
  assert.equal(byId['compiler-overlap'].status, 'invalid');
  assert.deepEqual(status(byId['compiler-overlap'], 'V1').failures[0].witnesses, ['analysis', 'lexer', 'syntax']);
  assert.equal(status(byId['compiler-pipeline-thirds'], 'V6').status, 'not-applicable', 'the compiler declares no abstract behaviour');
  const m = (/** @type {string} */ id) => /** @type {any} */ (byId[id].measurements);
  assert.deepEqual([m('compiler-pipeline-thirds').blocks.count, m('compiler-pipeline-thirds').facts.internal.all, m('compiler-pipeline-thirds').facts.crossing.all], [4, 2, 5]);
  assert.deepEqual([m('compiler-front-and-back').facts.internal.all, m('compiler-front-and-back').facts.crossing.all], [3, 5]);
  assert.equal(m('compiler-pipeline-thirds').cycles.every((/** @type {any} */ c) => !c.cyclic), true, 'a pipeline has no cycle among stages');
  assert.deepEqual(cmp.candidates.slice(0, 4), ['compiler-pipeline-thirds', 'compiler-front-and-back', 'compiler-syntax-first', 'compiler-overlap'], 'columns keep the order given');
  const { project, model } = accept(text, { ...common, ...candidatesOfData(JSON.parse(fs.readFileSync(path.join(EXT, 'compiler-candidates.json'), 'utf8')))[0] }, common);
  const d = deriveModel(model, 'compiler-pipeline-thirds-cut');
  // The scope (the system) is opened, so the cut also holds what the candidate did not place: the two stages' parents it emptied
  // and the two teams of the ownership hierarchy, which are roots.
  assert.deepEqual(d?.level.blocks.slice().sort(), ['analysis-and-optimisation', 'backend', 'diagnostics', 'emission', 'frontend', 'syntax', 'team-back', 'team-front']);
  assert.deepEqual(/** @type {any} */ (cmp.reports.find((r) => r.id === 'compiler-pipeline-thirds')).acceptance.emptied, ['backend', 'frontend']);
  assert.deepEqual(d?.diagnostics.filter((x) => x.severity === 'error'), []);
  const claim = claimAt(project, 'no-flow-back', 'compiler-pipeline-thirds-cut', 'emission', 'syntax', ['data-flow', 'invokes']);
  assert.equal(claim.status, 'verified');
  assert.deepEqual(claim.level, { hierarchy: 'compiler-pipeline-thirds', cut: 'compiler-pipeline-thirds-cut' });
  assert.equal(analyzeSpec(project.specText).diagnostics.filter((x) => x.code.startsWith('function.')).length, 0, 'the functions still compose');
});

// The distributed application.
// @evidence decomposition-external-fixtures
test('distributed: candidates over services and machines then acceptance that keeps the realisation maps whole', () => {
  const { text, byId, common, cmp } = external('distributed', 'shop');
  for (const id of ['shop-by-tier', 'shop-services-and-machines', 'shop-by-zone', 'shop-declared']) assert.equal(byId[id].status, 'valid', id);
  assert.equal(byId['shop-uncovered'].status, 'invalid');
  assert.deepEqual(status(byId['shop-uncovered'], 'V1').failures[0].witnesses, ['db-host']);
  const m = (/** @type {string} */ id) => /** @type {any} */ (byId[id].measurements);
  assert.deepEqual([m('shop-services-and-machines').facts.crossing.all, m('shop-services-and-machines').cohesion.overall.value], [0, 1], 'services and machines share no relationship, the deployment links lie among machines');
  assert.deepEqual([m('shop-by-tier').facts.internal.all, m('shop-by-tier').facts.crossing.all], [4, 2]);
  const cand = { ...common, ...candidatesOfData(JSON.parse(fs.readFileSync(path.join(EXT, 'distributed-candidates.json'), 'utf8')))[0] };
  const { project, model } = accept(text, cand, common);
  const d = /** @type {any} */ (deriveModel(model, 'shop-by-tier-cut'));
  assert.equal(d.realisations.length, 3, 'the three realisation maps');
  assert.ok(d.realisations.every((/** @type {any} */ r) => r.ok !== false), JSON.stringify(d.realisations));
  assert.deepEqual(d.diagnostics.filter((/** @type {any} */ x) => x.severity === 'error'), []);
  assert.deepEqual(/** @type {any} */ (hierarchyOf(model, 'deployment')).problems, [], 'the deployment hierarchy is as it was');
  const claim = claimAt(project, 'no-call-up', 'shop-by-tier-cut', 'back-office', 'presentation', ['invokes']);
  assert.equal(claim.status, 'verified');
  assert.ok(cmp.reports.every((r) => r.id.startsWith('shop-')));
});

// The event-driven system.
// @evidence decomposition-external-fixtures
test('event-driven: connectors contract the paths and V5 to V7 decide candidates and the accepted cut keeps the contractions', () => {
  const { text, byId, common, generated } = external('event-driven', 'telemetry-platform');
  assert.equal(byId['telemetry-by-role'].status, 'valid');
  assert.equal(status(byId['telemetry-by-role'], 'V6').status, 'pass', 'the block processing declares abstract behaviour that refines its members');
  assert.deepEqual(status(byId['telemetry-by-role'], 'V6').detail.checked.map((/** @type {any} */ c) => [c.block, c.abstraction, c.verdict]), [['processing', 'processing-flow', 'certificate']]);
  assert.equal(status(byId['telemetry-samples-and-alerts'], 'V6').status, 'not-applicable');
  // Separating the gateway from the filter it invokes under the untyped contract is a V7 failure with the hop as witness.
  const apart = byId['telemetry-gateway-apart'];
  assert.deepEqual(apart.failedConditions, ['V7']);
  assert.ok(status(apart, 'V7').failures[0].witnesses.includes('gateway-invokes-filter'));
  assert.deepEqual(byId['telemetry-uncovered'].failedConditions, ['V1']);
  // The connector-bounded regions keep every topic with a block of its own; the generated candidates are decided like the given ones.
  assert.equal(byId['telemetry-platform-connector-regions'].status, 'valid');
  assert.equal(byId['telemetry-platform-contract-regions'].status, 'invalid');
  assert.deepEqual(byId['telemetry-platform-contract-regions'].failedConditions, ['V7']);
  assert.ok(generated.candidates.some((c) => c.source === 'refinement'));
  const cand = { ...common, ...candidatesOfData(JSON.parse(fs.readFileSync(path.join(EXT, 'event-driven-candidates.json'), 'utf8')))[0] };
  const { project, model } = accept(text, cand, common);
  const d = /** @type {any} */ (deriveModel(model, 'telemetry-by-role-cut'));
  // The contractions are read at the cut's blocks: each publishes-then-subscribes pair lifts to its blocks and names its connector.
  assert.deepEqual(d.connectors.map((/** @type {any} */ c) => `${c.from}>${c.to}@${c.connector}`).sort(), [
    'processing>consumers@alerts-topic', 'processing>consumers@alerts-topic', 'producers>consumers@telemetry-topic', 'producers>consumers@telemetry-topic', 'producers>processing@telemetry-topic',
  ], 'publishes then subscribes through a declared connector contracts to a notification, naming the connector');
  assert.deepEqual(d.diagnostics.filter((/** @type {any} */ x) => x.severity === 'error'), []);
  const claim = claimAt(project, 'consumers-do-not-reach-producers', 'telemetry-by-role-cut', 'consumers', 'producers', ['invokes', 'notifies', 'publishes', 'subscribes', 'reads']);
  assert.equal(claim.status, 'verified');
});

// The reports under docs/assessment/2026-11-27/m7.
// @evidence decomposition-external-fixtures
test('the recorded reports say what the runs said', () => {
  const dir = path.join(ROOT, 'docs/assessment/2026-11-27/m7');
  for (const [name, accepted, n] of [['compiler', 'compiler-pipeline-thirds', 16], ['distributed', 'shop-by-tier', 11], ['event-driven', 'telemetry-by-role', 24]]) {
    const c = JSON.parse(fs.readFileSync(path.join(dir, `${name}-candidates.json`), 'utf8'));
    assert.equal(c.candidates.length, n, name);
    assert.deepEqual(c.purity.hashBefore, c.purity.hashAfter);
    assert.ok(c.purity.factsUnchanged && c.purity.repeatedIdentical);
    const a = JSON.parse(fs.readFileSync(path.join(dir, `${name}-accept.json`), 'utf8'));
    assert.equal(a.accepted, accepted);
    assert.ok(a.semanticHash.undoRestores && a.semanticHash.redoRestores);
    assert.deepEqual(a.validate, { errors: 0, warnings: 0 });
    assert.equal(a.levelBoundClaims[`${accepted}-level-claim@${accepted}-cut`].status, 'verified');
    const md = fs.readFileSync(path.join(dir, `${name}.md`), 'utf8');
    assert.match(md, /## Multiscale requirements this run exercised/);
    assert.doesNotMatch(md.replace(/Whether a decomposition is meaningful is a judgement they do not make/, ''), /meaningful/);
  }
  const self = JSON.parse(fs.readFileSync(path.join(dir, 'self-spec-accepted.json'), 'utf8'));
  assert.equal(self.levelBoundClaim['core-independent-of-ui@audit-second-cut'].status, 'verified');
  assert.deepEqual(self.validate, { errors: 0, warnings: 0 });
});
