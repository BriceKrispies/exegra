// The producers of the facts claim statuses rest on, and how a read treats them (milestone M0 of
// docs/foundations.md, "Stop overclaiming"). Each test encodes an inflation the 2026-11-26 assessment
// demonstrated and asserts the honest result:
//   - skip-aware test evidence on the fresh path (TAP) and the reuse path (recorded outcomes) alike;
//   - recorded results and Lean theorem checks stamped, and read as stale when the stamp is not current;
//   - the lean-theorem rule refusing an empty `about`, an opaque constant and code that is not the definition;
//   - open-startedness of a metric claim's class computed from the workloads, never assumed;
//   - admit and verify treating any fall from a positive status, a removal and a changed counterexample as a regression.
// None of these needs Lean: claims are evaluated on hand-built models (evaluateClaims reads only entities,
// byKind, meta and a precomputed semanticHash) and the CLI pieces are pure functions.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync, execFileSync } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { evaluateClaims } from '../../src/core/claims.js';
import { tapTests, countPassingTests, mergeRecordedResults } from '../../cli/commands.js';
import { nodeOutcome, testsVerdict } from '../../cli/outcomes.js';
import { compare, claimBaseline, verifyRegressions, counterexampleFingerprint } from '../../cli/admit.js';
import { recordsStamp, treeStamp, formalSourcesHash, currentStamps } from '../../tools/tree-stamp.js';
import { evaluateMetricClaim, openStartedClass } from '../../src/core/metric-claims.js';
import { evaluateRuns, rat, parseRational, claimStatus } from '../../src/core/metric-stats.js';

const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
const FIXTURE = 'tests/fixtures/skipped-tests/demo.test.js';
/** The patterns of the demo whose only relevant test did not execute. */
const NOT_EXECUTED = ['inner real check', 'trivially|real check', 'publishes'];

/** node --test in a clean environment: no tool flag, and not as a child of this test run. @param {string[]} args */
function nodeTest(args) {
  const env = { ...process.env };
  delete env.HAS_TOOL;
  delete env.NODE_TEST_CONTEXT;
  const r = spawnSync(process.execPath, ['--test', ...args], { cwd: repoRoot, encoding: 'utf8', env, windowsHide: true });
  assert.equal(r.status, 0, `${r.stdout}${r.stderr}`);
  return String(r.stdout);
}

// A model by hand, as the assessment's demos build one.
/** @param {string} kind @param {string} id @param {any} data */
const ent = (kind, id, data) => ({ kind, id, data, loc: { line: 1, column: 1 }, path: [] });
/** @param {any[]} entities */
function modelOf(entities) {
  /** @type {Record<string, any[]>} */
  const byKind = {};
  for (const e of entities) (byKind[e.kind] ??= []).push(e);
  return /** @type {any} */ ({ semanticHash: 'fixture', entities: new Map(entities.map((e) => [e.id, e])), byKind, meta: { verificationMethods: {} } });
}
/** @param {any} model @param {any} opts */
const byId = (model, opts) => Object.fromEntries(evaluateClaims(model, opts).map((r) => [r.claimId, r]));

// ---------------------------------------------------------------------------------------------------------
// 1. Skip-aware test evidence

test('a reference whose matched test skipped or is a todo is not a pass on the fresh path', () => {
  for (const pattern of NOT_EXECUTED) {
    const out = nodeTest(['--test-reporter=tap', `--test-name-pattern=${pattern}`, FIXTURE]);
    const verdict = testsVerdict(tapTests(out, FIXTURE));
    assert.equal(verdict.outcome, 'skipped', `pattern "${pattern}": ${JSON.stringify(tapTests(out, FIXTURE))}`);
  }
  // A describe block whose only test skipped prints a plain "ok" line for the suite: it is not a test.
  const suite = nodeTest(['--test-reporter=tap', '--test-name-pattern=inner real check', FIXTURE]);
  assert.equal(countPassingTests(suite, FIXTURE), 0);
  assert.equal(countPassingTests(nodeTest(['--test-reporter=tap', '--test-name-pattern=publishes', FIXTURE]), FIXTURE), 0, 'a todo is not a pass');
  // The whole file: one test passes, the others did not execute, so the reference was not executed in full.
  assert.equal(testsVerdict(tapTests(nodeTest(['--test-reporter=tap', FIXTURE]), FIXTURE)).outcome, 'skipped');
  // The one test that executes still passes on its own.
  assert.equal(testsVerdict(tapTests(nodeTest(['--test-reporter=tap', '--test-name-pattern=trivially', FIXTURE]), FIXTURE)).outcome, 'pass');
});

test('a reference whose matched test skipped or is a todo is not a pass on the reuse path', () => {
  // The recorded outcomes `npm test` writes, produced by its own reporter over the fixture.
  const doc = JSON.parse(nodeTest(['--test-reporter=./tools/outcomes-node-reporter.js', FIXTURE]));
  assert.ok(doc.files[FIXTURE], 'the reporter recorded the fixture');
  for (const pattern of NOT_EXECUTED) {
    assert.equal(nodeOutcome(doc, `${FIXTURE}#${pattern}`)?.outcome, 'skipped', `pattern "${pattern}"`);
  }
  assert.equal(nodeOutcome(doc, FIXTURE)?.outcome, 'skipped', 'the whole file');
  assert.equal(nodeOutcome(doc, `${FIXTURE}#trivially`)?.outcome, 'pass');
  // An outcome file written before the reporter flagged suites and todos: the suite is still told from its test.
  const legacy = { ...doc, files: { [FIXTURE]: { fileOutcome: 'pass', tests: [
    { name: 'inner real check', path: 'suite whose only test is skipped inner real check', nesting: 1, outcome: 'skipped' },
    { name: 'suite whose only test is skipped', path: 'suite whose only test is skipped', nesting: 0, outcome: 'pass' },
  ] } } };
  assert.equal(nodeOutcome(legacy, `${FIXTURE}#suite whose`)?.outcome, 'skipped');
});

test('a test that skipped now is recorded as not run and no older pass supports its claim', () => {
  const results = mergeRecordedResults(
    { 'ev-real-check': { outcome: 'pass', ranAt: '2026-11-19T00:00:00.000Z', stamp: 'S0' } },
    [{ id: 'ev-real-check', outcome: 'skipped', detail: 'every matching test (1) skipped itself or is a todo, so nothing was executed', ranAt: '2026-11-26T00:00:00.000Z' }],
    'S1',
  );
  assert.equal(results['ev-real-check'].outcome, 'not-run');
  assert.equal(results['ev-real-check'].stamp, 'S1');
  const model = modelOf([
    ent('claim', 'c-real', { kind: 'invariant', statement: 'The real check holds.', evaluate: { method: 'external-evidence' } }),
    ent('evidence', 'ev-real-check', { claim: 'c-real', kind: 'test', ref: `${FIXTURE}#the real check of the claim` }),
  ]);
  const r = byId(model, { recorded: { results }, stamps: { tree: 'S1', formal: 'F' } })['c-real'];
  assert.notEqual(r.status, 'supported');
  assert.equal(r.status, 'inconclusive');
});

// ---------------------------------------------------------------------------------------------------------
// 2. Provenance of recorded results

const EVIDENCE_MODEL = () => modelOf([
  ent('claim', 'c-tested', { kind: 'invariant', statement: 'The tested property holds.', evaluate: { method: 'external-evidence' } }),
  ent('evidence', 'ev-tested', { claim: 'c-tested', kind: 'test', ref: 'tests/core/a.test.js#works' }),
  ent('claim', 'c-failing', { kind: 'invariant', statement: 'A property whose test failed.', evaluate: { method: 'external-evidence' } }),
  ent('evidence', 'ev-failing', { claim: 'c-failing', kind: 'test', ref: 'tests/core/a.test.js#broken' }),
]);

test('a recorded result whose stamp is not the current stamp leaves its claim not evaluated as stale', () => {
  const model = EVIDENCE_MODEL();
  const stamps = { tree: 'CURRENT', formal: 'F' };
  const fresh = byId(model, { recorded: { results: { 'ev-tested': { outcome: 'pass', stamp: 'CURRENT' } } }, stamps })['c-tested'];
  assert.equal(fresh.status, 'supported');
  assert.equal(fresh.freshness, 'fresh');
  for (const rec of [{ outcome: 'pass', stamp: 'EARLIER' }, { outcome: 'pass' }]) {
    const r = byId(model, { recorded: { results: { 'ev-tested': rec } }, stamps })['c-tested'];
    assert.equal(r.status, 'not-evaluated', JSON.stringify(rec));
    assert.match(r.explanation, /^Stale: /);
    assert.equal(r.freshness, 'stale');
    assert.deepEqual(r.diagnostics?.map((d) => d.code), ['claim.stale-evidence']);
    assert.equal(r.evidence[0].stale, true);
  }
  // Staleness never improves a status: a stale failure still contradicts the claim.
  const failed = byId(model, { recorded: { results: { 'ev-failing': { outcome: 'fail', stamp: 'EARLIER' } } }, stamps })['c-failing'];
  assert.equal(failed.status, 'violated');
});

test('without a current stamp recorded results are reported with unverifiable freshness', () => {
  const r = byId(EVIDENCE_MODEL(), { recorded: { results: { 'ev-tested': { outcome: 'pass', stamp: 'ANY' } } }, stamps: null })['c-tested'];
  assert.equal(r.status, 'supported', 'the browser bundle keeps displaying the recorded result');
  assert.equal(r.freshness, 'unverifiable');
  assert.match(r.explanation, /Freshness unverifiable/);
  assert.deepEqual(r.diagnostics?.map((d) => [d.code, d.severity]), [['claim.freshness-unverifiable', 'info']]);
});

test('an outcome an external tool recorded on another tree does not support its claim', () => {
  const model = modelOf([ent('claim', 'req-1', { kind: 'requirement', statement: 'The requirement is met.', evaluate: { method: 'tla-check' } })]);
  model.meta.verificationMethods = { 'tla-check': { label: 'TLA+' } };
  const recorded = { tool: 'checker', claims: { 'req-1': { outcome: 'pass' } } };
  const stale = byId(model, { recorded, stamps: { tree: 'NOW', formal: 'F' } })['req-1'];
  assert.equal(stale.status, 'not-evaluated');
  assert.match(stale.explanation, /^Stale: /);
  const fresh = byId(model, { recorded: { ...recorded, claims: { 'req-1': { outcome: 'pass', stamp: 'NOW' } } }, stamps: { tree: 'NOW', formal: 'F' } })['req-1'];
  assert.equal(fresh.status, 'supported');
});

test('the records stamp ignores the files Exegra writes from its results and the formal hash follows formal sources', () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-records-stamp-'));
  try {
    execFileSync('git', ['init', '-q'], { cwd: root, stdio: 'ignore' });
    fs.mkdirSync(path.join(root, 'specs', 'p', 'evidence'), { recursive: true });
    fs.mkdirSync(path.join(root, 'formal', 'Exegra'), { recursive: true });
    fs.writeFileSync(path.join(root, 'specs', 'p', 'spec.jsonc'), '{}');
    fs.writeFileSync(path.join(root, 'formal', 'Exegra', 'A.lean'), 'theorem t : True := trivial');
    const records = recordsStamp(root);
    const tree = treeStamp(root);
    const formal = formalSourcesHash(root);
    fs.writeFileSync(path.join(root, 'specs', 'p', 'evidence', 'results.json'), '{"results":{}}');
    fs.mkdirSync(path.join(root, 'specs', 'p', 'generated'));
    fs.writeFileSync(path.join(root, 'specs', 'p', 'generated', 'claims-report.md'), '# report');
    assert.equal(recordsStamp(root), records, 'writing results and generated artifacts does not make the results stale');
    assert.notEqual(treeStamp(root), tree, 'the full tree stamp sees them');
    fs.writeFileSync(path.join(root, 'specs', 'p', 'spec.jsonc'), '{"x":1}');
    assert.notEqual(recordsStamp(root), records, 'an edit of the specification does');
    assert.equal(formalSourcesHash(root), formal, 'formal/ did not change');
    fs.writeFileSync(path.join(root, 'formal', 'Exegra', 'A.lean'), 'theorem t : True := sorry');
    assert.notEqual(formalSourcesHash(root), formal, 'replacing a proof changes the formal hash');
    assert.deepEqual(currentStamps(path.join(os.tmpdir(), 'exegra-no-such-dir')), { tree: null, formal: null });
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
  // verify writes the stamp into every result it records.
  const merged = mergeRecordedResults({}, [{ id: 'a', outcome: 'pass', ranAt: 't' }, { id: 'b', outcome: 'fail', detail: 'x', ranAt: 't' }], 'STAMP');
  assert.deepEqual(Object.values(merged).map((r) => r.stamp), ['STAMP', 'STAMP']);
});

// ---------------------------------------------------------------------------------------------------------
// 3. The lean-theorem checker

const OK_FACTS = { found: true, kind: 'theorem', kernel: 'ok', axioms: ['propext'], lean: '4.35.0', checkedAt: 'T', formalHash: 'F1', statementHash: 'H' };
/** @param {string} id @param {string} theorem @param {string[]} [about] */
const leanClaim = (id, theorem, about) => ent('claim', id, { kind: 'invariant', statement: `${id}.`, evaluate: { method: 'lean-theorem', theorem, ...(about ? { about } : {}) } });

test('the lean-theorem rule refuses a claim with no about list and an about constant that is not the code that runs', () => {
  const model = modelOf([
    leanClaim('no-about', 'Nat.add_comm'),
    leanClaim('empty-about', 'Exegra.Api.registry_names_nodup', []),
    leanClaim('opaque-about', 'Exegra.thm_opaque', ['Exegra.opaqueRun']),
    leanClaim('implemented-by', 'Exegra.thm_impl', ['Exegra.fastRun']),
    leanClaim('extern', 'Exegra.thm_extern', ['Exegra.cRun']),
    leanClaim('partial', 'Exegra.thm_partial', ['Exegra.loopRun']),
    leanClaim('sound', 'Exegra.runInput_terminates', ['Exegra.runInput']),
  ]);
  const about = (/** @type {string} */ n, /** @type {any} */ extra = {}) => ({ [n]: { kind: 'definition', inStatement: true, ...extra } });
  const theorems = {
    'Nat.add_comm': { ...OK_FACTS },
    'Exegra.Api.registry_names_nodup': { ...OK_FACTS, about: {} },
    'Exegra.thm_opaque': { ...OK_FACTS, about: { 'Exegra.opaqueRun': { kind: 'opaque', inStatement: true } } },
    'Exegra.thm_impl': { ...OK_FACTS, about: about('Exegra.fastRun', { implementedBy: 'Exegra.fastRunImpl' }) },
    'Exegra.thm_extern': { ...OK_FACTS, about: about('Exegra.cRun', { extern: true }) },
    'Exegra.thm_partial': { ...OK_FACTS, about: about('Exegra.loopRun', { partial: true }) },
    'Exegra.runInput_terminates': { ...OK_FACTS, about: about('Exegra.runInput') },
  };
  const r = byId(model, { recorded: { theorems }, stamps: { tree: 'T', formal: 'F1' } });
  for (const id of ['no-about', 'empty-about']) {
    assert.equal(r[id].status, 'violated', id);
    assert.match(r[id].explanation, /names no implementation constant/);
  }
  assert.match(r['opaque-about'].explanation, /opaque constant/);
  assert.match(r['implemented-by'].explanation, /implemented_by Exegra\.fastRunImpl/);
  assert.match(r.extern.explanation, /is extern/);
  assert.match(r.partial.explanation, /partial definition/);
  for (const id of ['opaque-about', 'implemented-by', 'extern', 'partial']) assert.equal(r[id].status, 'violated', id);
  assert.equal(r.sound.status, 'proved', r.sound.explanation);
  assert.match(r.sound.explanation, /statement hash H/);
});

test('a recorded Lean check of other formal sources does not keep its claim proved', () => {
  const model = modelOf([leanClaim('terminates', 'Exegra.runInput_terminates', ['Exegra.runInput'])]);
  const rec = { ...OK_FACTS, about: { 'Exegra.runInput': { kind: 'definition', inStatement: true } } };
  // Recorded on formal/ with hash F1; the proof has since been replaced (the sources hash to F2) and Lean did not run.
  for (const recorded of [{ theorems: { 'Exegra.runInput_terminates': rec } }, { theorems: { 'Exegra.runInput_terminates': { ...rec, formalHash: undefined } } }]) {
    const r = byId(model, { recorded, stamps: { tree: 'T', formal: 'F2' } }).terminates;
    assert.equal(r.status, 'not-evaluated');
    assert.match(r.explanation, /^Stale: /);
    assert.equal(r.freshness, 'stale');
    assert.deepEqual(r.diagnostics?.map((d) => d.code), ['claim.stale-theorem']);
  }
  const current = byId(model, { recorded: { theorems: { 'Exegra.runInput_terminates': rec } }, stamps: { tree: 'T', formal: 'F1' } }).terminates;
  assert.equal(current.status, 'proved');
  assert.equal(current.freshness, 'fresh');
});

// ---------------------------------------------------------------------------------------------------------
// 4. Metric claims: open-startedness

/** A version-2 input with one request class started by `workload`. @param {any} workload @param {any[]} [behaviors] */
const metricInput = (workload, behaviors = []) => ({
  version: 2, time: { unit: 'us', perSecond: 1000000 }, scenario: { seed: '1', steps: [], output: 'metrics' },
  behaviors, workloads: [workload], faults: [],
  requests: [{ id: 'req', start: { event: 'ask' }, key: 'request', ends: [{ event: 'answer', outcome: 'ok' }] }],
});

/** The 100 runs of metric-demo1: 60 normal (p99 20 ms) and 40 that collapse (12 requests measured, p99 +inf). */
function collapsingEngine() {
  let r = 0;
  return (/** @type {string} */ text) => {
    const seed = JSON.parse(text).scenario.seed;
    const collapsed = r++ % 100 >= 60;
    const q = collapsed ? { value: null, infinite: true } : { value: 20000 };
    return { seed, truncated: false, metrics: { requests: { req: { measured: collapsed ? 12 : 5000, duplicate: 0, responseTime: { infinite: collapsed ? 12 : 0, quantiles: { '0.99': q } } } } } };
  };
}
const P99_CLAIM = { metric: { kind: 'response-time', of: 'req', statistic: 'p99' }, op: '<=', bound: '30000', runs: 100, fraction: '0.95', confidence: '0.95', seed: '0' };

test('a closed-workload class whose runs collapse reads violated: underpowered runs are kept and fail', () => {
  const closed = metricInput({ id: 'clients', kind: 'closed', event: 'ask', population: 50 });
  assert.equal(openStartedClass(closed, P99_CLAIM.metric), false);
  const res = evaluateMetricClaim(collapsingEngine(), { scenarios: [closed] }, P99_CLAIM);
  assert.equal(res.status, 'violated');
  assert.equal(res.scenarios[0].kept, 100);
  assert.equal(res.scenarios[0].leftOut, 0);
  // metric-demo1 as written: the statistics alone, with openStarted not stated, also fail.
  const runs = [
    ...Array.from({ length: 60 }, (_, i) => ({ seed: `g${i}`, value: rat(20000n), samples: 5000, underpowered: false })),
    ...Array.from({ length: 40 }, (_, i) => ({ seed: `c${i}`, value: /** @type {'inf'} */ ('inf'), samples: 12, underpowered: true, infinite: 12 })),
  ];
  const unstated = evaluateRuns(runs, { op: '<=', bound: rat(30000n), fraction: parseRational('0.95'), confidence: parseRational('0.95') });
  assert.equal(unstated.verdict, 'fails');
  assert.equal(claimStatus([unstated]).status, 'violated');
});

test('open-startedness is computed from the workloads that can start the class', () => {
  const open = metricInput({ id: 'arrivals', kind: 'open', event: 'ask' });
  assert.equal(openStartedClass(open, P99_CLAIM.metric), true);
  // Only for an open-started class is an underpowered run left out.
  const res = evaluateMetricClaim(collapsingEngine(), { scenarios: [open] }, P99_CLAIM);
  assert.equal(res.scenarios[0].leftOut, 40);
  // Anything else that can put the start event in the queue makes the class not open-started.
  const echo = [{ id: 'b', transitions: [{ id: 't', effects: [{ emit: 'ask' }] }] }];
  assert.equal(openStartedClass(metricInput({ id: 'arrivals', kind: 'open', event: 'ask' }, echo), P99_CLAIM.metric), false, 'a behavior emits it');
  assert.equal(openStartedClass(metricInput({ id: 'clients', kind: 'population', start: { event: 'ask' } }), P99_CLAIM.metric), false, 'a population starts it');
  assert.equal(openStartedClass({ ...open, scenario: { ...open.scenario, steps: [{ at: 0, event: 'ask' }] } }, P99_CLAIM.metric), false, 'a scenario step injects it');
  assert.equal(openStartedClass(open, { kind: 'waiting-time', of: 'cpu' }), false, 'not a request-class metric');
  // A run with duplicate starts is never left out: its sample count depended on the system.
  const dup = evaluateRuns([{ seed: 's', value: rat(1n), underpowered: true, duplicates: 3 }], { op: '<=', bound: rat(2n), fraction: parseRational('0.5'), confidence: parseRational('0.5'), openStarted: true });
  assert.equal(dup.leftOut, 0);
  assert.equal(dup.passes, 0);
});

// ---------------------------------------------------------------------------------------------------------
// 5. Regression gating

/** An admit snapshot by hand: claim statuses only, over an empty model. @param {Record<string, string>} statuses */
function side(statuses) {
  const claims = new Map(Object.entries(statuses).map(([id, status]) => [id, { id, status, explanation: '' }]));
  return /** @type {any} */ ({ claims, errors: new Map(), warnings: new Map(), gaps: new Map(), violations: new Map(), model: modelOf([]) });
}

test('admit rejects a claim that falls to not evaluated and a positive claim that is removed', () => {
  const r = compare(side({ a: 'supported', b: 'proved', c: 'verified', d: 'inconclusive' }), side({ a: 'not-evaluated', b: 'not-evaluated', d: 'not-evaluated' }));
  assert.equal(r.verdict, 'rejected');
  assert.deepEqual(r.reasons.map((x) => [x.code, x.id]), [
    ['admit.claim-regressed', 'a'], ['admit.claim-regressed', 'b'], ['admit.claim-removed', 'c'],
  ]);
  // A removal is a decision the caller can state explicitly; a fall in status is not.
  const accepted = compare(side({ c: 'verified' }), side({}), { accept: ['admit.claim-removed'] });
  assert.equal(accepted.verdict, 'admitted');
  assert.deepEqual(accepted.acknowledged.map((x) => x.code), ['admit.claim-removed']);
});

test('verify fails on a fall from a positive status a removal and a changed counterexample of an expected violation', () => {
  const cx = (/** @type {string[]} */ entities) => ({ summary: `Components not in Lean: ${entities.join(', ')}.`, entities });
  const before = claimBaseline([
    { claimId: 'p', status: 'proved' }, { claimId: 's', status: 'supported' }, { claimId: 'v', status: 'verified' },
    { claimId: 'gone', status: 'supported' }, { claimId: 'known', status: 'violated', counterexample: cx(['claim-evaluator']) },
    { claimId: 'weak', status: 'inconclusive' },
  ]);
  assert.equal(before.known.counterexample, counterexampleFingerprint(cx(['claim-evaluator'])));
  const after = claimBaseline([
    { claimId: 'p', status: 'not-evaluated' }, { claimId: 's', status: 'inconclusive' }, { claimId: 'v', status: 'verified' },
    { claimId: 'known', status: 'violated', counterexample: cx(['claim-evaluator', 'new-js-kernel']) },
    { claimId: 'weak', status: 'not-evaluated' },
  ]);
  const found = verifyRegressions(before, after, { expectViolated: ['known'] });
  assert.deepEqual(found.map((x) => [x.code, x.id]), [
    ['verify.claim-removed', 'gone'], ['verify.counterexample-changed', 'known'],
    ['verify.claim-regressed', 'p'], ['verify.claim-regressed', 's'],
  ]);
  assert.deepEqual(verifyRegressions(before, before, { expectViolated: ['known'] }), [], 'an unchanged run passes');
  assert.deepEqual(verifyRegressions(before, after, { expectViolated: ['known'], accept: ['gone', 'known', 'p', 's'] }), [], 'each named change is accepted');
  // The same counterexample with its entities in another order is the same violation.
  assert.equal(counterexampleFingerprint({ summary: 'x', entities: ['b', 'a'] }), counterexampleFingerprint({ summary: 'x', entities: ['a', 'b'] }));
});
