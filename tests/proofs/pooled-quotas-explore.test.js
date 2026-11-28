// The exhaustive exploration of pooled quotas (WG-5278; tests/core/pooled-quotas.test.js holds the rest): the claims
// of the Harbourline fixture are decided by the verified explorer of the Lean semantics, run through the
// WebAssembly core, and a seeded wrong rule (eligibility effective only from the next day, or a four-day window)
// makes the explorer return a counterexample. Each run explores every subset of the injected events, so these
// re-checks run with the proofs (npm run test:proofs, npm run verify, the Check workflow), not in the routine suite.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { parse } from 'jsonc-parser';
import { analyzeSpec } from '../../src/core/analyze.js';
import { call, initLean } from '../../src/core/lean.js';
import { proofPlan, exploreRequest } from '../../src/core/proof-export.js';

initLean();

const FIXTURE = fs.readFileSync(new URL('../fixtures/pooled-quotas/harbourline.jsonc', import.meta.url), 'utf8');

/** The fixture as an object, changed by `mutate`, as JSON text. */
function spec(mutate = (/** @type {any} */ _d) => {}) {
  const d = parse(FIXTURE);
  mutate(d);
  return JSON.stringify(d, null, 2);
}

const errors = (/** @type {any} */ r) => r.diagnostics.filter((/** @type {any} */ d) => d.severity === 'error');
/** The model of the fixture, changed by `mutate`; it must have no errors. */
function model(mutate = (/** @type {any} */ _d) => {}) {
  const r = analyzeSpec(spec(mutate));
  assert.deepEqual(errors(r).map((/** @type {any} */ d) => `${d.code} ${d.message}`), []);
  return /** @type {any} */ (r.model);
}
const pool = (/** @type {any} */ d) => d.quotaPools[0];

/** Explore a scenario's state-invariant claims: claim id -> the explorer's result. @param {any} m @param {string} scenarioId */
function explore(m, scenarioId) {
  const plan = proofPlan(m, scenarioId);
  const r = call('engine.explore', JSON.parse(exploreRequest(plan)));
  assert.ok(r.ok, /** @type {any} */ (r).error);
  return new Map(/** @type {any} */ (r).value.results.map((/** @type {any} */ x) => [x.id, x]));
}

const BURST = 'burst-eligible-never-throttled-after-set';
const THREE = 'three-days-over-throttles';

test('exploration decides that a burst-eligible client is never throttled after eligibility was set', () => {
  const results = explore(model(), 'burst-exploration');
  assert.equal(results.get(BURST)?.verdict, 'holds');
  assert.equal(results.get(THREE)?.verdict, 'holds');
  assert.ok(results.get(BURST).states > 100, 'every subset of the injected usage and eligibility events was explored');
});

test('exploration finds a counterexample when eligibility takes effect only from the next day', () => {
  const results = explore(model((/** @type {any} */ d) => { pool(d).exemption.effective = 'next-window'; }), 'burst-exploration');
  const r = results.get(BURST);
  assert.equal(r?.verdict, 'counterexample');
  assert.ok(r.faults.includes('m1-burst-day2'), 'eligibility set on the day the third over-share day ends');
  assert.ok(['m1-runs-day0', 'm1-runs-day1', 'm1-runs-day2'].every((f) => r.faults.includes(f)));
});

test('exploration finds a counterexample when the over-share window is four days instead of three', () => {
  const results = explore(model((/** @type {any} */ d) => { pool(d).overShare.consecutive = 4; }), 'burst-exploration');
  assert.equal(results.get(THREE)?.verdict, 'counterexample');
  assert.equal(results.get(BURST)?.verdict, 'holds');
});
