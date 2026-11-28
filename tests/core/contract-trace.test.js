// Contract events: events that are requests, responses and errors of a contract (src/core/contract-trace.js,
// src/core/type-expr.js). Validation checks the declarations, the trace check reads a simulated trace, and
// the request log renders it. Exegra's own scenario write-with-stale-base-hash is the worked example.
import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { analyzeSpec } from '../../src/core/analyze.js';
import { initEngine, runScenario } from '../../src/core/engine.js';
import { checkTrace } from '../../src/core/claims.js';
import { requestLog } from '../../src/core/contract-trace.js';
import { readSpecFile } from '../../tools/spec-manifest.js';

initEngine();

const ECHO = {
  id: 'echo', name: 'Echo', binding: { method: 'POST', path: '/echo' },
  inputs: [{ name: 'text', type: 'string' }, { name: 'mode', type: "'loud' | 'quiet'" }, { name: 'note', type: 'string', optional: true }, { name: 'id', type: 'number', optional: true }],
  outputs: [{ name: 'reply', type: 'string' }, { name: 'length', type: 'number' }, { name: 'id', type: 'number' }],
  errors: [{ name: 'too-long / empty', condition: 'The text is empty or too long.' }],
};

/** @param {any[]} events @param {any[]} [behaviors] @param {any[]} [scenarios] */
function specWith(events, behaviors = [], scenarios = []) {
  return JSON.stringify({
    exegra: '0.1', system: { id: 'echo-system', name: 'Echo system' },
    components: [{ id: 'caller', name: 'Caller', category: 'logical' }, { id: 'echoer', name: 'Echoer', category: 'logical' }],
    contracts: [ECHO], events, behaviors, scenarios,
  });
}
const ev = (id, role, payload, extra = {}) => ({ id, name: id, contract: 'echo', role, payload, ...extra });
const diag = (text) => analyzeSpec(text).diagnostics.filter((d) => d.severity === 'error');

// A request with an unknown field, a missing input, a wrong type, a response with a foreign field and an error code outside the contract are each reported at the event; a conforming model has no such diagnostic.
// @evidence contract-events-validated
test('validate reports contract events that do not fit their contract', () => {
  const good = specWith([
    ev('say', 'request', [{ name: 'text', type: 'string' }, { name: 'mode', type: "'loud'" }]),
    ev('said', 'response', [{ name: 'reply', type: 'string' }, { name: 'length', type: 'number' }]),
    ev('refused', 'error', [{ name: 'code', type: "'empty' | 'too-long'" }, { name: 'limit', type: 'number' }]),
  ]);
  assert.deepEqual(diag(good), [], 'a conforming model has no error');

  const bad = analyzeSpec(specWith([
    ev('unknown-field', 'request', [{ name: 'text', type: 'string' }, { name: 'mode', type: "'loud'" }, { name: 'volume', type: 'number' }]),
    ev('missing-input', 'request', [{ name: 'text', type: 'string' }]),
    ev('wrong-type', 'request', [{ name: 'text', type: 'number' }, { name: 'mode', type: 'string' }]),
    ev('foreign-output', 'response', [{ name: 'text', type: 'string' }]),
    ev('no-code', 'error', [{ name: 'limit', type: 'number' }]),
    ev('foreign-code', 'error', [{ name: 'code', type: "'empty' | 'boom'" }]),
    ev('no-role', undefined, [], { role: undefined }),
    ev('bad-correlation', 'response', [{ name: 'reply', type: 'string' }], { correlation: 'id' }),
  ]));
  const errors = bad.diagnostics.filter((d) => d.severity === 'error');
  const at = (id) => errors.filter((d) => d.entityId === id).map((d) => d.code);
  assert.deepEqual(at('unknown-field'), ['event.contract-field']);
  assert.deepEqual(at('missing-input'), ['event.contract-missing']);
  assert.deepEqual(at('wrong-type'), ['event.contract-type', 'event.contract-type']);
  assert.deepEqual(at('foreign-output'), ['event.contract-field']);
  assert.deepEqual(at('no-code'), ['event.error-code']);
  assert.deepEqual(at('foreign-code'), ['event.error-code']);
  assert.deepEqual(at('no-role'), ['event.role-missing']);
  assert.deepEqual(at('bad-correlation'), ['event.correlation']);
  assert.ok(errors.every((d) => d.loc && d.path.length > 0), 'every diagnostic has a position and a path');
  assert.deepEqual(errors.find((d) => d.entityId === 'unknown-field').path.slice(-2), ['payload', 2]);

  const unknown = diag(specWith([{ id: 'x', name: 'X', contract: 'nothing', role: 'request' }]));
  assert.deepEqual(unknown.map((d) => d.code), ['ref.unresolved'], 'an unknown contract is a reference error');
});

/** A hand-made trace of delivered events, as the engine returns it. */
function traceOf(model, steps) {
  return {
    scenarioId: 'none', faults: [], outcome: 'quiescent',
    steps: steps.map(([id, payload, kind = 'deliver'], index) => ({ index, time: index, kind, event: { id, payload, seq: index, source: {} }, fired: [], ignored: [], faults: [], responsible: [] })),
  };
}

// A wrong-typed value, an error code outside the contract and a response with no earlier request are failed automatic checks with their step; Exegra's own write-with-stale-base-hash scenario passes them.
// @evidence trace-contract-conformance
test('simulate checks values error codes and request response pairing', () => {
  const { model } = analyzeSpec(specWith([
    ev('say', 'request', [{ name: 'text', type: 'string' }, { name: 'mode', type: "'loud' | 'quiet'" }, { name: 'id', type: 'number' }], { correlation: 'id' }),
    ev('said', 'response', [{ name: 'reply', type: 'string' }, { name: 'id', type: 'number' }], { correlation: 'id' }),
    ev('refused', 'error', [{ name: 'code', type: 'string' }, { name: 'id', type: 'number' }], { correlation: 'id' }),
  ]));
  const fails = (steps) => checkTrace(model, traceOf(model, steps)).filter((c) => !c.holds);

  const fine = checkTrace(model, traceOf(model, [
    ['say', { text: 'a', mode: 'loud', id: 1 }], ['say', { text: 'b', mode: 'quiet', id: 2 }],
    ['said', { reply: 'B', id: 2 }], ['refused', { code: 'empty', id: 1 }],
  ]));
  assert.deepEqual(fine.map((c) => [c.claimId, c.holds, c.automatic]), [['contract-conformance', true, true]], 'responses are matched by the correlation field, in any order');

  const wrongType = fails([['say', { text: 5, mode: 'shout', id: 1 }]]);
  assert.deepEqual(wrongType.map((c) => c.stepIndex), [0, 0]);
  assert.match(wrongType[0].explanation, /"text".*does not fit string/);
  assert.match(wrongType[1].explanation, /"mode".*does not fit 'loud' \| 'quiet'/);

  const badCode = fails([['say', { text: 'a', mode: 'loud', id: 1 }], ['refused', { code: 'boom', id: 1 }]]);
  assert.equal(badCode.length, 1);
  assert.equal(badCode[0].stepIndex, 1);
  assert.match(badCode[0].explanation, /"boom" is not among the contract's errors \(too-long, empty\)/);

  const orphan = fails([['said', { reply: 'x', id: 7 }]]);
  assert.equal(orphan[0].stepIndex, 0);
  assert.match(orphan[0].explanation, /answers no earlier unanswered request/);
  const twice = fails([['say', { text: 'a', mode: 'loud', id: 1 }], ['said', { reply: 'x', id: 1 }], ['said', { reply: 'y', id: 1 }]]);
  assert.deepEqual(twice.map((c) => c.stepIndex), [2], 'a request is answered once');
  assert.deepEqual(fails([['say', { text: 'a', mode: 'loud', id: 1 }, 'drop']]), [], 'a dropped request was never delivered');

  // Exegra's own scenario conforms, and every claim check it had before is unchanged in kind.
  const own = analyzeSpec(readSpecFile(new URL('../../specs/exegra/spec.jsonc', import.meta.url))).model;
  assert.ok(own);
  const checks = checkTrace(own, runScenario(own, 'write-with-stale-base-hash'));
  assert.deepEqual(checks.filter((c) => !c.holds), []);
  assert.ok(checks.some((c) => c.automatic && c.holds));
  // visual-edit-flow saves through the session's write-intent, a write-file request since WG-5732 typed the session's
  // hop; preferences-remembered (the store of the selection and view) exchanges no contract event at all.
  const quiet = runScenario(own, 'preferences-remembered');
  assert.ok(quiet.steps.length > 0, 'the scenario runs');
  assert.deepEqual(checkTrace(own, quiet).filter((c) => c.automatic), [], 'a scenario without contract events gets no contract check');
});

// The trace of write-with-stale-base-hash renders as a request, a refused write and a retry, using the contract's binding; a trace without contract events renders no lines.
// @evidence trace-contract-conformance
test('the request log renders contract events with binding and outcome', () => {
  const own = analyzeSpec(readSpecFile(new URL('../../specs/exegra/spec.jsonc', import.meta.url))).model;
  assert.ok(own);
  const lines = requestLog(own, runScenario(own, 'write-with-stale-base-hash')).map((e) => e.text);
  // Since WG-5732 typed the session's hop under write-file, the session's write-intent is a request of the contract
  // (rendered with the contract's binding) just before the persistence client's write-file-request, and the session's
  // save-succeeded is a response after write-file-ok: each write shows the session's request and answer around the
  // HTTP ones.
  assert.deepEqual(lines, [
    '→ POST /__exegra/write {name: "exegra", file: "spec", text: "9b2f1c0e", baseHash: "stale", requestId: 1}',
    '→ POST /__exegra/write {name: "exegra", file: "spec", text: "9b2f1c0e", baseHash: "stale", requestId: 1}',
    '← refused conflict {current: "h1", requestId: 1}',
    '→ POST /__exegra/write {name: "exegra", file: "spec", text: "9b2f1c0e", baseHash: "h1", requestId: 2}',
    '→ POST /__exegra/write {name: "exegra", file: "spec", text: "9b2f1c0e", baseHash: "h1", requestId: 2}',
    '← ok {ok: true, hash: "9b2f1c0e", requestId: 2}',
    '← ok {file: "spec", hash: "9b2f1c0e", requestId: 2}',
  ]);
  assert.deepEqual(requestLog(own, runScenario(own, 'preferences-remembered')), [], 'steps that are not contract events give no line');

  // Without a binding the request is named after its event.
  const { model } = analyzeSpec(specWith([ev('say', 'request', [{ name: 'text', type: 'string' }, { name: 'mode', type: "'loud'" }])]).replace('"binding":{"method":"POST","path":"/echo"},', ''));
  assert.ok(model);
  assert.equal(requestLog(model, traceOf(model, [['say', { text: 'a', mode: 'loud' }]]))[0].text, '→ say {text: "a", mode: "loud"}');
});
