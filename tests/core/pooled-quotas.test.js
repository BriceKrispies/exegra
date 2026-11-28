// Pooled quotas (WG-5278; docs/model-and-format.md, Pooled quotas): limits shared by a reseller's client
// tenants, with fair share, headroom, the over-share rule with its window and the exemption set by a
// named role. The fixture tests/fixtures/pooled-quotas/harbourline.jsonc states Harbourline BR-12; the
// pool runs as machines (Exegra.Lower.poolMachines, formal/Exegra/Lower/Input.lean), so its claims are decided by exhaustive
// exploration of the scenario's injected usage and eligibility events with the verified explorer of the Lean semantics;
// those explorations are in tests/proofs/pooled-quotas-explore.test.js (npm run test:proofs, npm run verify). Each
// validation rule has a mutation that breaks exactly it once.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { parse } from 'jsonc-parser';
import { analyzeSpec } from '../../src/core/analyze.js';
import { initLean } from '../../src/core/lean.js';
import { runScenario } from '../../src/core/engine.js';
import { poolMachineIds, POOL_VARIABLES } from '../../src/core/pool-rules.js';
import { engineInput } from '../../src/core/engine.js';

initLean();

const metamodel = JSON.parse(fs.readFileSync(new URL('../../src/core/metamodel.json', import.meta.url), 'utf8'));
const FIXTURE = fs.readFileSync(new URL('../fixtures/pooled-quotas/harbourline.jsonc', import.meta.url), 'utf8');

/** The fixture as an object, changed by `mutate`, as JSON text. */
function spec(mutate = (/** @type {any} */ _d) => {}) {
  const d = parse(FIXTURE);
  mutate(d);
  return JSON.stringify(d, null, 2);
}

/** The model of the fixture, changed by `mutate`; it must have no errors. */
function model(mutate = (/** @type {any} */ _d) => {}) {
  const r = analyzeSpec(spec(mutate));
  assert.deepEqual(errors(r).map((/** @type {any} */ d) => `${d.code} ${d.message}`), []);
  return /** @type {any} */ (r.model);
}

const errors = (/** @type {any} */ r) => r.diagnostics.filter((/** @type {any} */ d) => d.severity === 'error');
const show = (/** @type {any} */ r) => r.diagnostics.map((/** @type {any} */ d) => `${d.severity} ${d.code} ${d.message}`).join('\n');
const pool = (/** @type {any} */ d) => d.quotaPools[0];

test('quota pools are entities of the metamodel with a section of their own and scenarios list the pools they run', () => {
  assert.equal(metamodel.sections.quotaPools?.entity, 'quotaPool');
  for (const p of ['memberClass', 'groupedBy', 'heldBy', 'window', 'windowEnd', 'limits', 'overShare', 'throttle', 'exemption', 'modelMembers']) assert.ok(metamodel.entities.quotaPool.properties[p], p);
  assert.deepEqual(metamodel.entities.quotaPool.properties.exemption.fields.effective.values, ['same-window', 'next-window']);
  assert.deepEqual(metamodel.entities.scenario.properties.pools.items.ref, ['quotaPool']);
});

test('the Harbourline fixture states BR-12 as a pool and validates with no errors and no warnings', () => {
  const r = analyzeSpec(spec());
  assert.deepEqual(r.diagnostics.filter((/** @type {any} */ d) => d.severity !== 'info').map((/** @type {any} */ d) => `${d.code} ${d.message}`), []);
  const d = parse(FIXTURE);
  for (const s of d.scenarios) for (const st of s.steps) assert.deepEqual(Object.keys(st.payload ?? {}).filter((k) => !['member', 'amount'].includes(k)), [], 'no scenario input says who is eligible or throttled');
});

test('a pool runs as one machine per pooled limit and modelled member with the pool variables', () => {
  const m = model();
  assert.deepEqual(poolMachineIds(m.entities.get('reseller-pool')), ['reseller-pool-runs-m1', 'reseller-pool-runs-m2', 'reseller-pool-storage-m1', 'reseller-pool-storage-m2']);
  const input = engineInput(m, 'burst-exploration');
  const machines = input.behaviors;
  assert.deepEqual(machines.map((x) => [x.subject, x.initial, x.states.join(' '), x.variables.map((v) => v.name).join(' ')]), machines.map(() => ['limit-store', 'normal', 'normal throttled', POOL_VARIABLES.join(' ')]));
  assert.deepEqual(machines.map((b) => b.id), poolMachineIds(m.entities.get('reseller-pool')), 'the scenario runs the pool machines');
});

test('a client over its fair share is admitted while the pool has headroom and throttled after three days and released after two under', () => {
  const trace = runScenario(model(), 'throttle-and-release');
  assert.equal(trace.outcome, 'quiescent');
  const m1 = (/** @type {any} */ cfg) => cfg.machines['reseller-pool-runs-m1'];
  const after = (/** @type {number} */ t) => trace.steps.filter((s) => s.time <= t).at(-1)?.config;
  assert.deepEqual([m1(after(30)).state, m1(after(30)).vars.throttledOn, m1(after(30)).vars.admitted], ['throttled', 2, 3], 'three runs of 15 against a share of 10 were admitted on headroom, then the third day end throttled');
  assert.deepEqual([m1(after(36)).vars.refused, m1(after(36)).vars.usage], [1, 5], 'throttled to its fair share: 12 refused, 5 admitted');
  assert.equal(m1(after(40)).state, 'throttled', 'one day under is not enough');
  assert.deepEqual([m1(trace.final).state, m1(trace.final).vars.throttledOn], ['normal', -1], 'two days under release the throttle');
});

test('a retroactive exemption lifts a throttle already in force and the default one does not', () => {
  const setOnDay3 = (/** @type {any} */ d) => {
    const s = d.scenarios.find((/** @type {any} */ x) => x.id === 'throttle-and-release');
    s.steps.splice(6, 0, { at: 33, event: 'burst-eligibility-set', payload: { member: 'm1' } });
  };
  const state = (/** @type {any} */ m) => runScenario(m, 'throttle-and-release').steps.find((s) => s.time === 33)?.config.machines['reseller-pool-runs-m1'].state;
  assert.equal(state(model(setOnDay3)), 'throttled');
  assert.equal(state(model((/** @type {any} */ d) => { setOnDay3(d); pool(d).exemption.retroactive = true; })), 'normal');
});

/** Each rule, a mutation that breaks it once, the code it reports and the path it reports at. */
const RULES = [
  ['a pool with no limit', 'pool.limits', 'quotaPools.0.limits', (/** @type {any} */ d) => { pool(d).limits = []; d.scenarios = []; d.claims = []; }],
  ['two limits with one name', 'pool.limits', 'quotaPools.0.limits.1.name', (/** @type {any} */ d) => { pool(d).limits[1].name = 'runs'; }],
  ['a limit with both a quota and an amount per member', 'pool.limit-contribution', 'quotaPools.0.limits.0', (/** @type {any} */ d) => { pool(d).limits[0].perMember = 10; }],
  ['a limit whose amount per member is not positive', 'pool.limit-contribution', 'quotaPools.0.limits.1.perMember', (/** @type {any} */ d) => { pool(d).limits[1].perMember = 0; }],
  ['a pooled quota counted per principal', 'pool.quota-scope', 'quotaPools.0.limits.0.quota', (/** @type {any} */ d) => { d.quotas[0].scope = 'principal'; }],
  ['a pooled quota with another window', 'pool.quota-window', 'quotaPools.0.limits.0.quota', (/** @type {any} */ d) => { d.quotas[0].window = '1 h'; }],
  ['a pooled quota stated as a level', 'pool.limit-kind', 'quotaPools.0.limits.0.kind', (/** @type {any} */ d) => { pool(d).limits[0].kind = 'level'; }],
  ['a pooled quota held by another component', 'pool.held-by', 'quotaPools.0.heldBy', (/** @type {any} */ d) => { d.components.push({ id: 'edge-counter', name: 'Edge counter', category: 'storage' }); d.quotas[0].heldBy = 'edge-counter'; }],
  ['a usage event with no amount', 'pool.event-payload', 'quotaPools.0.limits.1.usage', (/** @type {any} */ d) => { d.events.find((/** @type {any} */ e) => e.id === 'storage-changed').payload.pop(); }],
  ['an exemption event with no member', 'pool.event-payload', 'quotaPools.0.exemption.event', (/** @type {any} */ d) => { d.events.find((/** @type {any} */ e) => e.id === 'burst-eligibility-set').payload = []; d.faults = d.faults.filter((/** @type {any} */ f) => f.event !== 'burst-eligibility-set'); d.scenarios[0].faults = d.scenarios[0].faults.filter((/** @type {string} */ f) => !f.includes('burst')); }],
  ['a level with no usage event', 'pool.usage-event', 'quotaPools.0.limits.1', (/** @type {any} */ d) => { delete pool(d).limits[1].usage; }],
  ['a window that is not a duration', 'pool.window', 'quotaPools.0.window', (/** @type {any} */ d) => { pool(d).window = 'a day'; }],
  ['an over-share rule of zero days', 'pool.over-share', 'quotaPools.0.overShare.consecutive', (/** @type {any} */ d) => { pool(d).overShare.consecutive = 0; }],
  ['a throttle with no release', 'pool.release', 'quotaPools.0.throttle.release', (/** @type {any} */ d) => { pool(d).throttle.release = 'later'; }],
  ['five modelled members', 'pool.model-members', 'quotaPools.0.modelMembers', (/** @type {any} */ d) => { pool(d).modelMembers = 5; }],
  ['an exemption set by a role without its capability', 'pool.exemption-capability', 'quotaPools.0.exemption.capability', (/** @type {any} */ d) => { d.roles.push({ id: 'support', name: 'Support', level: 'platform', holders: ['person'], capabilities: [] }); pool(d).exemption.setBy = 'support'; }],
  ['a pool machine id that is already an entity', 'pool.machine-id', 'quotaPools.0.limits', (/** @type {any} */ d) => { d.assumptions.push({ id: 'reseller-pool-runs-m2', statement: 'Clash.' }); }],
  ['a claim reading a variable a pool machine does not have', 'expr.reference', 'claims.0.evaluate.expr', (/** @type {any} */ d) => { d.claims[0].evaluate.expr = 'reseller-pool-runs-m1.eligible == 1'; }],
];

for (const [title, code, at, mutate] of RULES) {
  test(`pooled quotas: ${title} is reported once as ${code} at ${at}`, () => {
    const r = analyzeSpec(spec(/** @type {any} */ (mutate)));
    assert.deepEqual(errors(r).map((/** @type {any} */ d) => [d.code, d.path.join('.')]), [[code, at]], show(r));
  });
}

test('a scenario may run a pool and no behavior but not neither', () => {
  const r = analyzeSpec(spec((/** @type {any} */ d) => { d.scenarios[1].pools = []; d.claims[1].evaluate.scenarios = ['burst-exploration']; }));
  assert.deepEqual(errors(r).map((/** @type {any} */ d) => d.code), ['scenario.empty'], show(r));
});
