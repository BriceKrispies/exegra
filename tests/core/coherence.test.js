// Structure-behaviour coherence (V5) and contract conformance at boundaries (V7), src/core/coherence.js
// (WG-5728). Message interactions come from the behaviours alone; V5 asks each to be witnessed by a
// relationship between its own two elements, at the base and at every cut; V7 asks the events crossing a
// relationship that declares a contract to be typed by it. Small specifications give the negative fixtures;
// the self-specification pins the corrected state.
import test from 'node:test';
import assert from 'node:assert/strict';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { parse as parseJsonc } from 'jsonc-parser';
import { analyzeSpec } from '../../src/core/analyze.js';
import { initEngine } from '../../src/core/engine.js';
import { readSpecFile } from '../../tools/spec-manifest.js';
import { messageInteractions, checkCoherence, coherenceReport, checkContractConformance, isMessageKind } from '../../src/core/coherence.js';

initEngine();

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');

/** One state machine: `transitions` are [id, on, emitted events]. */
const machine = (/** @type {string} */ id, /** @type {string} */ subject, /** @type {[string, string, string[]][]} */ transitions) => ({
  id, name: id, subject, initial: `${id}-s`,
  states: [{ id: `${id}-s`, name: 's' }],
  transitions: transitions.map(([t, on, emits]) => ({ id: `${id}-${t}`, from: `${id}-s`, to: `${id}-s`, on, effects: emits.map((e) => ({ emit: e })) })),
});
const events = (/** @type {string[]} */ ids) => ids.map((id) => ({ id, name: id }));

/**
 * `front` sends `ping` to `store` and `pong` to `cache`; `store` and `cache` are inside the subsystem `back`.
 * Only front-calls-cache is declared. `ping` is a message with no relationship of its own, and at the cut
 * {front, back} the coarse interaction front to back exists, over the cache pair: a different witness.
 * @param {any[]} [extraRelationships]
 */
function specOf(extraRelationships = []) {
  return {
    exegra: '0.1', system: { id: 'sys', name: 'Sys' },
    components: [
      { id: 'front', name: 'Front', category: 'logical' },
      { id: 'back', name: 'Back', category: 'logical', kind: 'subsystem' },
      { id: 'store', name: 'Store', category: 'storage', parent: 'back' },
      { id: 'cache', name: 'Cache', category: 'storage', parent: 'back' },
    ],
    relationships: [{ id: 'front-calls-cache', kind: 'invokes', from: 'front', to: 'cache' }, ...extraRelationships],
    events: events(['start', 'ping', 'pong']),
    behaviors: [
      machine('front-m', 'front', [['go', 'start', ['ping', 'pong']]]),
      machine('store-m', 'store', [['hear', 'ping', []]]),
      machine('cache-m', 'cache', [['hear', 'pong', []]]),
    ],
    scenarios: [{ id: 'run', name: 'Run', behaviors: ['front-m', 'store-m', 'cache-m'], steps: [{ at: 0, event: 'start' }] }],
  };
}
const modelOf = (/** @type {any} */ doc) => {
  const r = analyzeSpec(JSON.stringify(doc));
  assert.ok(r.model, JSON.stringify(r.diagnostics.filter((d) => d.severity === 'error')));
  return /** @type {any} */ (r.model);
};

test('message interactions are derived from emit and consume pairs of behaviors with different subjects', () => {
  const m = modelOf(specOf());
  assert.deepEqual(messageInteractions(m).map((x) => [x.event, x.emitter, x.consumer, x.from, x.to]), [
    ['ping', 'front-m', 'store-m', 'front', 'store'],
    ['pong', 'front-m', 'cache-m', 'front', 'cache'],
  ]);
  // An event a behavior consumes from itself is not a cross-element message.
  const own = specOf();
  own.behaviors.push(machine('front-loop', 'front', [['again', 'start', ['loop']], ['hear', 'loop', []]]));
  own.events.push(...events(['loop']));
  assert.ok(!messageInteractions(modelOf(own)).some((x) => x.event === 'loop'));
});

test('message class is a property of the kind: kinds that move control or data, not imports', () => {
  const m = modelOf(specOf());
  for (const k of ['invokes', 'calls', 'notifies', 'publishes', 'subscribes', 'data-flow', 'reads', 'writes', 'observes', 'composes']) assert.ok(isMessageKind(m.meta, k), k);
  for (const k of ['imports', 'depends-on']) assert.ok(!isMessageKind(m.meta, k), k);
});

test('V5 reports a message with no relationship between its elements at the base', () => {
  const r = checkCoherence(modelOf(specOf()), null);
  assert.deepEqual(r.findings.map((f) => [f.event, f.emitter, f.consumer, f.from, f.to, f.status, f.cut]), [['ping', 'front-m', 'store-m', 'front', 'store', 'unwitnessed', 'base']]);
  // Declaring the relationship clears it, in the other direction too: a response runs against an invocation.
  assert.deepEqual(checkCoherence(modelOf(specOf([{ id: 'store-calls-front', kind: 'invokes', from: 'store', to: 'front' }])), null).findings, []);
  // A relationship that moves nothing (an import) is no witness.
  assert.equal(checkCoherence(modelOf(specOf([{ id: 'front-imports-store', kind: 'imports', from: 'front', to: 'store' }])), null).findings.length, 1);
});

test('a coarse edge over a different witness is reported at the cut and not accepted', () => {
  const m = modelOf(specOf());
  const cut = { hierarchy: 'logical', blocks: ['front', 'back'] };
  const r = checkCoherence(m, cut);
  assert.equal(r.internal, 0);
  assert.deepEqual(r.findings.map((f) => [f.event, f.fromBlock, f.toBlock, f.status, f.coarseWitnesses]), [['ping', 'front', 'back', 'different-witness', ['front-calls-cache']]]);
  assert.match(r.findings[0].message, /different witness/);
  // The message the relationship really witnesses passes at the same cut.
  assert.ok(!r.findings.some((f) => f.event === 'pong'));
  // Where both ends lie in one block the message is internal to it and is not a boundary message.
  const inner = checkCoherence(m, { hierarchy: 'logical', blocks: ['front', 'store', 'cache'] });
  assert.equal(inner.internal, 0);
  const one = checkCoherence(m, { hierarchy: 'logical', blocks: ['back', 'front'] });
  assert.equal(one.findings.length, 1);
  // The report lists the message once with every level that reports it.
  const all = coherenceReport(m);
  assert.equal(all.ok, false);
  assert.deepEqual(all.unwitnessed.map((u) => [u.event, u.from, u.to]), [['ping', 'front', 'store']]);
  assert.ok(all.unwitnessed[0].cuts.some((c) => c.cut === 'base' && c.status === 'unwitnessed'));
  // The relationship that witnesses the message itself clears it at every level.
  assert.equal(coherenceReport(modelOf(specOf([{ id: 'front-calls-store', kind: 'invokes', from: 'front', to: 'store' }]))).ok, true);
});

test('the self-specification has no unwitnessed message at the base or at any declared cut', () => {
  const { model } = analyzeSpec(readSpecFile(path.join(ROOT, 'specs/exegra/spec.jsonc')));
  assert.ok(model);
  const report = coherenceReport(/** @type {any} */ (model));
  assert.ok(report.messages > 100, 'the behaviors exchange more than a hundred cross-element messages');
  assert.deepEqual(report.unwitnessed, []);
  assert.ok(report.levels.some((l) => l.cut === 'base') && report.levels.some((l) => l.cut === 'l1') && report.levels.some((l) => l.cut === 'runtime-platforms'));
  // The save path: the session speaks the persistence client's write-intent, the entry of the persistence path (WG-5728, WG-5729).
  const save = messageInteractions(/** @type {any} */ (model)).filter((x) => x.event === 'write-intent');
  // Two session machines (WG-5733) and two persistence levels (the abstraction and its entry member) exchange it.
  assert.deepEqual([...new Set(save.map((x) => `${x.from}->${x.to}`))], ['session->persistence-client']);
});

// ---------------------------------------------------------------------------------------------
// V7

const CONTRACT = { id: 'c', name: 'C', inputs: [{ name: 'x', type: 'string' }], outputs: [{ name: 'y', type: 'string' }] };

/** `a` invokes `b` under contract c; the events a and b exchange are untyped unless `typed`. @param {boolean} typed */
function contractSpec(typed) {
  const req = typed ? { contract: 'c', role: 'request', payload: [{ name: 'x', type: 'string' }] } : {};
  const res = typed ? { contract: 'c', role: 'response', payload: [{ name: 'y', type: 'string' }] } : {};
  return {
    exegra: '0.1', system: { id: 'sys', name: 'Sys' },
    components: [{ id: 'a', name: 'A', category: 'logical' }, { id: 'b', name: 'B', category: 'logical' }],
    relationships: [{ id: 'a-calls-b', kind: 'invokes', from: 'a', to: 'b', contract: 'c' }],
    contracts: [CONTRACT],
    events: [{ id: 'go', name: 'go' }, { id: 'req', name: 'req', ...req }, { id: 'res', name: 'res', ...res }],
    behaviors: [machine('a-m', 'a', [['send', 'go', ['req']], ['got', 'res', []]]), machine('b-m', 'b', [['serve', 'req', ['res']]])],
    scenarios: [{ id: 'run', name: 'Run', behaviors: ['a-m', 'b-m'], steps: [{ at: 0, event: 'go' }] }],
  };
}

test('V7 reports a hop whose events are not typed by its declared contract', () => {
  const bad = checkContractConformance(modelOf(contractSpec(false)));
  assert.equal(bad.ok, false);
  assert.deepEqual(bad.findings.map((f) => [f.contract, f.relationship, f.from, f.to, f.status, f.events]), [['c', 'a-calls-b', 'a', 'b', 'untyped', ['req', 'res']]]);
  assert.match(bad.findings[0].message, /not typed by it/);
  const good = checkContractConformance(modelOf(contractSpec(true)));
  assert.deepEqual(good, { ok: true, hops: 1, findings: [], unmodelled: [] });
});

test('V7 lists a contracted hop no behavior exchanges events over apart from the untyped ones', () => {
  const doc = contractSpec(false);
  doc.behaviors = [machine('a-m', 'a', [['send', 'go', []]])];
  const r = checkContractConformance(modelOf(doc));
  assert.equal(r.ok, true, 'nothing crosses, so nothing is untyped');
  assert.deepEqual(r.unmodelled.map((f) => [f.relationship, f.status]), [['a-calls-b', 'unmodelled']]);
});

test('the write-file workspace hops of the self-specification carry events of the contract', () => {
  const { model } = analyzeSpec(readSpecFile(path.join(ROOT, 'specs/exegra/spec.jsonc')));
  const m = /** @type {any} */ (model);
  const r = checkContractConformance(m);
  const flagged = r.findings.filter((f) => f.contract === 'write-file').map((f) => f.relationship);
  assert.ok(!flagged.includes('dev-server-plugin-calls-workspace-service'), 'the plugin to workspace hop is typed');
  assert.ok(!flagged.includes('agent-cli-calls-workspace-service'), 'the apply command to workspace hop is typed');
  assert.equal(m.entities.get('agent-cli-calls-workspace-service').data.contract, 'write-file', 'the command declares the contract on its workspace hop');
  for (const id of ['ws-write', 'ws-write-done', 'ws-write-error']) assert.equal(m.entities.get(id).data.contract, 'write-file', id);
  // Without the contract on the events the same hops are reported.
  const stripped = JSON.parse(JSON.stringify(readSpecJson()));
  for (const e of stripped.events) if (e.id.startsWith('ws-write') && e.contract) { delete e.contract; delete e.role; delete e.correlation; }
  const again = checkContractConformance(modelOf(stripped));
  const reported = again.findings.filter((f) => f.contract === 'write-file').map((f) => f.relationship);
  assert.ok(reported.includes('dev-server-plugin-calls-workspace-service') && reported.includes('agent-cli-calls-workspace-service'), reported.join(', '));
});

/** The self-specification as one JSON document, for a variant with an edit. */
function readSpecJson() {
  return parseJsonc(readSpecFile(path.join(ROOT, 'specs/exegra/spec.jsonc')));
}

test('the CLI reports V5 and V7 on the self-specification', () => {
  const run = (/** @type {string[]} */ args) => {
    const r = spawnSync(process.execPath, ['cli/exegra.js', ...args, '--project', 'exegra'], { cwd: ROOT, encoding: 'utf8' });
    assert.equal(r.status, 0, r.stderr);
    return JSON.parse(r.stdout);
  };
  const v5 = run(['coherence']);
  assert.equal(v5.command, 'coherence');
  assert.equal(v5.result.ok, true);
  assert.deepEqual(v5.result.unwitnessed, []);
  const one = run(['coherence', '--cut', 'l1']);
  assert.equal(one.result.cut, 'l1');
  assert.deepEqual(one.result.findings, []);
  const v7 = run(['boundary-contracts']);
  assert.equal(v7.command, 'boundary-contracts');
  assert.ok(Array.isArray(v7.result.findings) && v7.result.hops > 0);
  assert.ok(!v7.result.findings.some((f) => f.relationship === 'agent-cli-calls-workspace-service'));
});
