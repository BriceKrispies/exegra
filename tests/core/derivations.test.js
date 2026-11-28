import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { analyzeSpec } from '../../src/core/analyze.js';
import { readinessGaps } from '../../src/core/readiness.js';
import { wordsOf, routeShape, runDerivation } from '../../src/core/derivation.js';
import { spec, FIXTURES, READINESS_FIXTURES } from '../fixtures/derivations/fixtures.js';

// Derived and facade contracts (WG-4935, NC-4 and NC-5 of WG-4895). The passing fixture is the specification of
// specc's golden fixture for derived contracts (crates/spec-compiler/tests/fixtures/derived/spec.jsonc in Strata):
// a pure, a read and two command derivations over a load and a commit contract, and a facade; and a read with a need
// loop (WG-4939), a read with a header step and a target contract (WG-4968).

const errors = (/** @type {any} */ r) => r.diagnostics.filter((/** @type {any} */ d) => d.severity === 'error');
const codes = (/** @type {any} */ ds) => ds.map((/** @type {any} */ d) => d.code);
const CODES = ['derivation.kind', 'derivation.signature', 'derivation.load', 'derivation.commit', 'derivation.bounds', 'contract.facade-route'];

// A derived contract without derivation: exactly one derivation.kind error; further fixtures give an unknown kind, a derivation on a generated contract and a commit on a read derivation.
// @evidence derivation-construct-rules # a derived contract without a derivation is reported once as derivation.kind
// An input of another type than the function parameter: exactly one derivation.signature error; further fixtures rename an input, change an output type, drop an error a decide variant needs, name an insufficient variant decide lacks and a fault that is no error.
// @evidence derivation-construct-rules # a function parameter of another type than the input is reported once as derivation.signature
// A load contract with an input nothing fills: exactly one derivation.load error; further fixtures load through a facade and drop an error of the load contract.
// @evidence derivation-construct-rules # a load contract with an input nothing fills is reported once as derivation.load
// A conflict error the commit contract lacks: exactly one derivation.commit error; further fixtures commit through a contract with an input nothing fills, add an output nothing gives and drop the conflict error from the contract.
// @evidence derivation-construct-rules # a conflict error the commit contract does not have is reported once as derivation.commit
// Negative need rounds: exactly one derivation.bounds error; further fixtures leave out retries and give fractional need rounds.
// @evidence derivation-construct-rules # a negative number of need rounds is reported once as derivation.bounds
// A facade whose route no served contract states: exactly one contract.facade-route error; further fixtures give a facade implementedBy, drop its bffRoute and let two served contracts state its route.
// @evidence derivation-construct-rules # a facade whose route no served contract states is reported once as contract.facade-route
// A derivation naming an undeclared function, and one naming an undeclared decide: no error without system.generation, the gap listed by readiness, and exactly one error with it.
// @evidence derivation-construct-rules # a derivation naming a function that is not declared is reported once as ready.derived-function-missing only when generation is set
// A header read derivation validates; a needs function reading a load output without a header, a pure derivation with a header and a header load output named like an input are each reported once.
// @evidence format-gaps-rules # a header whose load output is named like an input is reported once as derivation.load
// A target contract validates; with a derivation, as a load contract, as a commit contract, or as the only contract a facade names, each is reported once.
// @evidence format-gaps-rules # a load contract that is a target is reported once as derivation.load
// The specification of specc's derived fixture (a pure, a read and two command derivations over load-counters and commit-bump, and the facade edit-counter lowered onto mutate-counter) has no error and no readiness gap, with and without system.generation.
// @evidence derivation-construct-rules
test('pure and read and command derivations over a load and a commit contract and a facade validate with nothing missing for generation', () => {
  for (const generation of [false, true]) {
    const r = analyzeSpec(spec(undefined, { generation }));
    assert.deepEqual(errors(r).map((/** @type {any} */ d) => `${d.code} ${d.message}`), []);
    assert.deepEqual(readinessGaps(/** @type {any} */ (r.model)), []);
  }
});

const generationChecked = new Set();
for (const [title, code, mutate] of FIXTURES) {
  // The generation switch is checked once per family of reported codes (the part before the dot); the other cases run without it.
  const modes = generationChecked.has(code.split(".")[0]) ? [false] : [false, true];
  generationChecked.add(code.split(".")[0]);
  for (const generation of modes) {
    test(`${title} is reported once as ${code}${generation ? ' (generation set)' : ''}`, () => {
      const r = analyzeSpec(spec(mutate, { generation }));
      assert.deepEqual(codes(errors(r)), [code], r.diagnostics.map((/** @type {any} */ d) => `${d.code} ${d.message}`).join('\n'));
      assert.ok(errors(r)[0].loc && errors(r)[0].loc.line > 1);
    });
  }
}

for (const [title, code, mutate] of READINESS_FIXTURES) {
  test(`${title} is reported once as ${code} only when generation is set`, () => {
    const off = analyzeSpec(spec(mutate, { generation: false }));
    assert.deepEqual(codes(errors(off)), [], off.diagnostics.map((/** @type {any} */ d) => `${d.code} ${d.message}`).join('\n'));
    assert.deepEqual(codes(readinessGaps(/** @type {any} */ (off.model))), [code]);
    const on = analyzeSpec(spec(mutate, { generation: true }));
    assert.deepEqual(codes(errors(on)), [code], on.diagnostics.map((/** @type {any} */ d) => `${d.code} ${d.message}`).join('\n'));
  });
}

// Every derivation.* code, contract.facade-route and ready.derived-function-missing has a negative fixture.
// @evidence derivation-construct-rules
test('every derivation code has a negative fixture', () => {
  const have = new Set(FIXTURES.map(([, code]) => code));
  assert.deepEqual(CODES.filter((c) => !have.has(c)), []);
  assert.ok(READINESS_FIXTURES.some(([, code]) => code === 'ready.derived-function-missing'));
});

// VersionConflict and version-conflict have the same words; a bffRoute is read as its method, path and shape, and one without a shape or with an unknown method is no route.
// @evidence derivation-construct-rules
test('error variants and contract errors are matched by their words and a route by its method and path and shape', () => {
  assert.equal(wordsOf('VersionConflict'), 'version-conflict');
  assert.equal(wordsOf('version-conflict'), 'version-conflict');
  assert.equal(wordsOf('HTTPError'), 'http-error');
  assert.deepEqual(routeShape('POST /api/records records update post'), { method: 'POST', path: '/api/records', shape: 'records' });
  assert.deepEqual(routeShape('GET /api/view view'), { method: 'GET', path: '/api/view', shape: 'view' });
  assert.equal(routeShape('POST /api/login'), undefined);
  assert.equal(routeShape('FETCH /api/view view'), undefined);
});

// docs/model-and-format.md names every derivation code and shows every kind.
// @evidence derivation-construct-rules
test('the format documentation states every derivation code and kind', () => {
  const doc = fs.readFileSync(new URL('../../docs/model-and-format.md', import.meta.url), 'utf8');
  for (const code of [...CODES, 'ready.derived-function-missing']) assert.ok(doc.includes(`\`${code}\``), `code ${code} is documented`);
  for (const kind of ['pure', 'read', 'command']) assert.ok(doc.includes(`"kind": "${kind}"`), `kind ${kind} is documented`);
});

/** A store of named counters: a load gives the counters the needs name (all of them for the header, which asks for none beyond what every load holds, here the revision). */
const counterStore = (/** @type {Record<string, number>} */ counters, /** @type {string[]} */ conflicts = []) => ({
  load: (/** @type {any[]} */ needs) => ({ outputs: { counters: new Map(Object.entries(counters).filter(([k]) => needs.some((n) => n.name === k))), revision: 5 } }),
  commit: () => (conflicts.length ? { error: { name: /** @type {string} */ (conflicts.shift()) } } : { outputs: { revision: 6 } }),
});
const model = () => /** @type {any} */ (analyzeSpec(spec()).model);

// runDerivation loads the header with no needs, then the needs in one round; a command asks for the extra need decide names and counts only that against need rounds; a commit that lost its race is decided again, at most retries times.
// @evidence format-gaps-rules
test('a read with a header loads once with no needs then its needs together in one round which no need round counts', () => {
  const found = runDerivation(model(), 'read-counter-header', { name: 'a' }, { load: (needs) => ({ outputs: { counters: new Map([['a', 3]]), revision: 5 } }) });
  assert.deepEqual(found, { decided: 3, loads: [[], [{ name: 'a' }]], rounds: 0, conflicts: 0 });
  const missing = runDerivation(model(), 'read-counter-header', { name: 'b' }, { load: () => ({ outputs: { counters: new Map([['a', 3]]), revision: 5 } }) });
  assert.deepEqual(missing, { error: { name: 'missing', value: { name: 'b' } }, loads: [[], []], rounds: 0, conflicts: 0 });
  // Without a header there is no load before the needs.
  const plain = runDerivation(model(), 'read-counter', { name: 'a' }, counterStore({ a: 3 }));
  assert.deepEqual(plain.loads, [[{ name: 'a' }]]);
});

test('a command asks for the extra need decide names, and loads again counting only those against need rounds', () => {
  const r = /** @type {any} */ (runDerivation(model(), 'copy-counter', { source: 'a', target: 'b' }, counterStore({ a: 3, b: 1 })));
  assert.deepEqual(r.loads, [[{ name: 'a' }], [{ name: 'a' }, { name: 'b' }]]);
  assert.deepEqual([r.rounds, r.conflicts, r.decided, r.outputs], [1, 0, { name: 'b', value: 3 }, { revision: 6 }]);
  const spent = runDerivation(model(), 'copy-counter-once', { source: 'a', target: 'b' }, counterStore({ a: 3, b: 1 }));
  assert.deepEqual(/** @type {any} */ (spent).error, { name: 'missing', value: { name: 'b' } });
});

test('a commit that lost its race is decided again, at most retries times', () => {
  const again = /** @type {any} */ (runDerivation(model(), 'copy-counter', { source: 'a', target: 'a' }, counterStore({ a: 3 }, ['conflict', 'conflict'])));
  assert.equal(again.conflicts, 2);
  assert.equal(again.loads.length, 3);
  const spent = /** @type {any} */ (runDerivation(model(), 'copy-counter', { source: 'a', target: 'a' }, counterStore({ a: 3 }, ['conflict', 'conflict', 'conflict', 'conflict'])));
  assert.deepEqual([spent.error, spent.conflicts], [{ name: 'conflict' }, 3]);
});
