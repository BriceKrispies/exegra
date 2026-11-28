// Every status-inflation demo of the 2026-11-26 assessment (docs/assessment/2026-11-26/demos/) yields its honest
// status (WG-5684, criterion 5). Each case is run on the demo's own model: the entities and recorded facts the demo
// builds, given here with stamps so that a recorded fact is fresh unless the demo makes it stale. The statuses are
// the Lean verdict (formal/Exegra/Verdict.lean). refines-ignore.mjs and replay-blind.mjs belong to WG-5683 (P5),
// metric-demo2.mjs and metric-demo3.mjs to P6.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { evaluateClaims } from '../../src/core/claims.js';
import { tapTests } from '../../cli/commands.js';
import { testsVerdict, referenceFact } from '../../cli/outcomes.js';
import { evaluateMetricClaim, metricVerdict } from '../../src/core/metric-claims.js';
import { evaluateRuns, rat, parseRational } from '../../src/core/metric-stats.js';
import { publishingProblems } from './pages-site.test.js';

const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
const DEMOS = 'docs/assessment/2026-11-26/demos';
const STAMPS = { tree: 'TREE', formal: 'FORMAL' };

/** @param {string} kind @param {string} id @param {any} data */
const ent = (kind, id, data) => ({ kind, id, data: { id, ...data }, owner: null, path: [], loc: { line: 1, column: 1, offset: 0, length: 1 } });
/** @param {any[]} entities @param {any} [meta] */
function modelOf(entities, meta = {}) {
  /** @type {Record<string, any[]>} */
  const byKind = {};
  for (const e of entities) (byKind[e.kind] ??= []).push(e);
  return /** @type {any} */ ({
    semanticHash: 'demo', entities: new Map(entities.map((e) => [e.id, e])), byKind, refs: [], exprs: [],
    meta: { relationshipKinds: {}, categories: {}, verificationMethods: {}, entities: {}, sections: {}, ...meta },
  });
}
/** @param {any} model @param {any} opts */
const byId = (model, opts) => Object.fromEntries(evaluateClaims(model, opts).map((r) => [r.claimId, r]));

// ---------------------------------------------------------------------------------------------------------
// skipped-test-counts-as-pass.test.js

test('skipped-test-counts-as-pass: a skipped, todo or suite-only reference is not run, and its claim is not supported', () => {
  const file = `${DEMOS}/skipped-test-counts-as-pass.test.js`;
  const env = { ...process.env };
  delete env.HAS_TOOL;
  delete env.NODE_TEST_CONTEXT;
  // The references whose only relevant test did not execute: a skip, a skip inside a suite, a todo, and a pattern
  // that matches an executed helper and a skipped check together.
  for (const pattern of ['the real check', 'inner real check', 'publishes', 'trivially|real check']) {
    const r = spawnSync(process.execPath, ['--test', '--test-reporter=tap', `--test-name-pattern=${pattern}`, file], { cwd: repoRoot, encoding: 'utf8', env, windowsHide: true });
    assert.equal(r.status, 0, `${r.stdout}${r.stderr}`);
    const verdict = testsVerdict(tapTests(String(r.stdout), file));
    assert.equal(verdict.outcome, 'skipped', `pattern "${pattern}"`);
    // As a fact: not run. A claim resting on it is not supported.
    const fact = referenceFact('ev-real-check', /** @type {any} */ (verdict.outcome), 'TREE', STAMPS);
    assert.equal(fact.outcome, 'not-run');
    const model = modelOf([
      ent('claim', 'c-real', { kind: 'invariant', statement: 'The real check holds.', evaluate: { method: 'external-evidence' } }),
      ent('evidence', 'ev-real-check', { claim: 'c-real', kind: 'test', ref: `${file}#${pattern}` }),
    ]);
    const c = byId(model, { recorded: { results: { 'ev-real-check': { outcome: 'not-run', stamp: 'TREE' } } }, stamps: STAMPS })['c-real'];
    assert.equal(c.status, 'inconclusive', pattern);
    assert.equal(c.verdict.strength, 'undecided', pattern);
  }
});

// ---------------------------------------------------------------------------------------------------------
// status-inflation.mjs

/** The model of status-inflation.mjs, with its recorded facts stamped on the current tree. */
function inflation() {
  const claims = [
    ent('claim', 'pages-like', { kind: 'structural', statement: 'Every push to main publishes the production build.', evaluate: { method: 'external-evidence' } }),
    ent('claim', 'p-equals-np', { kind: 'structural', statement: 'P = NP.', evaluate: { method: 'external-evidence' } }),
    ent('claim', 'doc-only', { kind: 'measured', statement: 'p99 ack latency < 50 ms in production.', evaluate: { method: 'external-evidence' } }),
    ent('claim', 'half-tested', { kind: 'invariant', statement: 'A and B both hold.', evaluate: { method: 'external-evidence' } }),
    ent('claim', 'lean-no-about', { kind: 'invariant', statement: 'The simulator never loses a message.', evaluate: { method: 'lean-theorem', theorem: 'Nat.add_comm' } }),
    ent('claim', 'lean-stale', { kind: 'invariant', statement: 'runInput terminates.', evaluate: { method: 'lean-theorem', theorem: 'Exegra.runInput_terminates', about: ['Exegra.runInput'] } }),
  ];
  const evidence = [
    ent('evidence', 'ev-yaml-regex', { claim: 'pages-like', kind: 'test', ref: 'tests/core/pages-site.test.js#the Pages workflow runs on every push to main' }),
    ent('evidence', 'ev-unrelated', { claim: 'p-equals-np', kind: 'test', ref: 'tests/core/expr.test.js' }),
    ent('evidence', 'ev-doc', { claim: 'doc-only', kind: 'document', ref: 'illustrative://no-such-report' }),
    ent('evidence', 'ev-a', { claim: 'half-tested', kind: 'test', ref: 'tests/a.test.js' }),
    ent('evidence', 'ev-b', { claim: 'half-tested', kind: 'test', ref: 'tests/b.test.js' }),
  ];
  const facts = { found: true, kind: 'theorem', kernel: 'ok', axioms: ['propext'], lean: '4.x', checkedAt: '2026-11-25T15:21:09Z' };
  const recorded = {
    results: { 'ev-yaml-regex': { outcome: 'pass', stamp: 'TREE' }, 'ev-unrelated': { outcome: 'pass', stamp: 'TREE' }, 'ev-a': { outcome: 'pass', stamp: 'TREE' } /* ev-b: never run */ },
    theorems: {
      // checked on the current formal/ sources: refused for naming no code
      'Nat.add_comm': { ...facts, formalHash: 'FORMAL' },
      // checked on earlier sources: the proof may have been replaced since
      'Exegra.runInput_terminates': { ...facts, formalHash: 'EARLIER', about: { 'Exegra.runInput': { kind: 'definition', inStatement: true } } },
    },
  };
  return byId(modelOf([...claims, ...evidence]), { recorded, stamps: STAMPS });
}

test('status-inflation: a passing test of a workflow is checked on instances, not established', () => {
  const r = inflation()['pages-like'];
  assert.equal(r.verdict.strength, 'checkedOnInstances');
  assert.equal(r.verdict.established, false);
});

test('status-inflation: an unrelated passing test gives P = NP at most checked on instances, never established', () => {
  const r = inflation()['p-equals-np'];
  assert.equal(r.verdict.strength, 'checkedOnInstances');
  assert.equal(r.verdict.established, false);
  assert.notEqual(r.status, 'proved');
});

test('status-inflation: a document alone is asserted', () => {
  const r = inflation()['doc-only'];
  assert.equal(r.verdict.strength, 'asserted');
  assert.equal(r.status, 'asserted');
  assert.equal(r.verdict.established, false);
});

test('status-inflation: a conjunction with an untested part takes its weakest part and is undecided', () => {
  const r = inflation()['half-tested'];
  assert.equal(r.verdict.strength, 'undecided');
  assert.notEqual(r.status, 'supported');
  assert.match(r.explanation, /ev-b/);
});

test('status-inflation: a theorem whose claim names no code is refused', () => {
  const r = inflation()['lean-no-about'];
  assert.equal(r.status, 'violated');
  assert.equal(r.verdict.strength, 'refuted');
  assert.match(r.explanation, /Lean refuses "Nat\.add_comm"/);
  assert.match(r.explanation, /names no implementation constant/);
});

test('status-inflation: a theorem check of other sources is stale, not proved', () => {
  const r = inflation()['lean-stale'];
  assert.equal(r.verdict.freshness, 'stale');
  assert.notEqual(r.status, 'proved');
  assert.notEqual(r.verdict.strength, 'proved');
  assert.equal(r.verdict.established, false);
  assert.match(r.explanation, /^Stale: /);
});

// ---------------------------------------------------------------------------------------------------------
// metric-demo1.mjs

test('metric-demo1: a closed-workload class whose runs collapse is violated', () => {
  // The runs of the demo: 60 normal (p99 20 ms) and 40 that collapse (12 requests measured, p99 +inf), for a class
  // that is not open-started.
  const runs = [
    ...Array.from({ length: 60 }, (_, i) => ({ seed: `g${i}`, value: rat(20000n), samples: 5000, underpowered: false })),
    ...Array.from({ length: 40 }, (_, i) => ({ seed: `c${i}`, value: /** @type {'inf'} */ ('inf'), samples: 12, underpowered: true, infinite: 12 })),
  ];
  const asSpecified = evaluateRuns(runs, { op: '<=', bound: rat(30000n), fraction: parseRational('0.95'), confidence: parseRational('0.95'), openStarted: false });
  const v = metricVerdict({ scenarios: [asSpecified], negatives: [], controlNegatives: [] });
  assert.equal(v.label, 'violated');
  assert.equal(v.strength, 'refuted');
  // The same through the claim evaluation of metric-claims.js, with open-startedness computed from the workload.
  let n = 0;
  const engine = (/** @type {string} */ text) => {
    const seed = JSON.parse(text).scenario.seed;
    const collapsed = n++ % 100 >= 60;
    const q = collapsed ? { value: null, infinite: true } : { value: 20000 };
    return { seed, truncated: false, metrics: { requests: { req: { measured: collapsed ? 12 : 5000, duplicate: 0, responseTime: { infinite: collapsed ? 12 : 0, quantiles: { '0.99': q } } } } } };
  };
  const input = {
    version: 2, time: { unit: 'us', perSecond: 1000000 }, scenario: { seed: '1', steps: [], output: 'metrics' }, behaviors: [], faults: [],
    workloads: [{ id: 'clients', kind: 'closed', event: 'ask', population: 50 }],
    requests: [{ id: 'req', start: { event: 'ask' }, key: 'request', ends: [{ event: 'answer', outcome: 'ok' }] }],
  };
  const res = evaluateMetricClaim(engine, { scenarios: [input] }, { metric: { kind: 'response-time', of: 'req', statistic: 'p99' }, op: '<=', bound: '30000', runs: 100, fraction: '0.95', confidence: '0.95', seed: '0' });
  assert.equal(metricVerdict(res).label, 'violated');
});

// ---------------------------------------------------------------------------------------------------------
// pages-mutants.mjs

test('pages-mutants: the workflow checks fail on all five mutants', () => {
  const orig = fs.readFileSync(path.join(repoRoot, '.github', 'workflows', 'pages.yml'), 'utf8');
  // The five mutants exactly as the demo writes them.
  const mutants = {
    'deploy job never runs (if: false)': orig.replace("if: github.ref == 'refs/heads/main'", 'if: false'),
    'validation failure ignored (|| true)': orig.replace('validate --project exegra --pretty', 'validate --project exegra --pretty || true'),
    'push limited to a path that never changes': orig.replace('branches: [main]', 'branches: [main]\n    paths: [does-not-exist/**]'),
    'deploy no longer waits for build (needs removed)': orig.replace('    needs: build\n', ''),
    'whole workflow disabled at job level': orig.replace('    runs-on: ubuntu-latest\n    steps:', '    if: false\n    runs-on: ubuntu-latest\n    steps:'),
  };
  assert.deepEqual(publishingProblems(orig), [], 'the workflow itself passes');
  for (const [name, text] of Object.entries(mutants)) {
    assert.notEqual(text, orig, `the mutant "${name}" applies`);
    assert.ok(publishingProblems(text).length > 0, `the checks fail on "${name}"`);
  }
});

// ---------------------------------------------------------------------------------------------------------
// composition-assumptions.mjs

/** The model of composition-assumptions.mjs. */
function composition() {
  const entities = [
    ent('component', 'X', { name: 'X', category: 'svc' }),
    ent('component', 'S', { name: 'S', category: 'svc', kind: 'subsystem' }),
    ent('component', 's1', { name: 's1', category: 'svc', parent: 'S' }),
    ent('component', 'Y', { name: 'Y', category: 'svc' }),
    ent('relationship', 'r1', { kind: 'calls', from: 'X', to: 'S' }),
    ent('relationship', 'r2', { kind: 'calls', from: 's1', to: 'Y' }),
    ent('assumption', 'a-yes', { statement: 'X calls Y on every request.' }),
    ent('assumption', 'a-no', { statement: 'X never calls Y, directly or indirectly.' }),
    ent('claim', 'c1', { kind: 'structural', statement: 'X never depends on Y, even indirectly.', assumptions: ['a-no'], evaluate: { method: 'no-relationship', from: 'X', to: 'Y', transitive: true } }),
    ent('claim', 'c2', { kind: 'structural', statement: 'Calls are acyclic.', assumptions: ['a-yes'], evaluate: { method: 'acyclic' } }),
    ent('claim', 'c3', { kind: 'structural', statement: 'X never depends on Y (no assumptions).', assumptions: [], evaluate: { method: 'no-relationship', from: 'X', to: 'Y', transitive: true } }),
    ent('claim', 'c4', { kind: 'structural', statement: 'X reaches S.', evaluate: { method: 'reachable', from: 'X', to: 'S' } }),
    ent('claim', 'c5', { kind: 'structural', statement: 'S reaches Y.', evaluate: { method: 'reachable', from: 'S', to: 'Y' } }),
  ];
  return modelOf(entities, { relationshipKinds: { calls: { label: 'calls', dependency: true } }, categories: { svc: { label: 'svc' } } });
}

test('composition-assumptions: c1 and c2 show their open assumptions and are not established', () => {
  const r = byId(composition(), { stamps: STAMPS });
  assert.deepEqual(r.c1.verdict.openAssumptions, ['a-no']);
  assert.deepEqual(r.c2.verdict.openAssumptions, ['a-yes']);
  assert.equal(r.c1.verdict.established, false);
  assert.equal(r.c2.verdict.established, false);
  assert.deepEqual(r.c3.verdict.openAssumptions, []);
});

test('composition-assumptions: with a-no recorded as refuted, c1 reads undecided', () => {
  const recorded = { assumptions: { 'a-no': { outcome: 'fail', stamp: 'TREE', kind: 'test', detail: 'X reaches Y through S' } } };
  const r = byId(composition(), { recorded, stamps: STAMPS });
  assert.equal(r.c1.verdict.strength, 'undecided');
  assert.notEqual(r.c1.status, 'verified');
  assert.notEqual(r.c1.status, 'violated');
  // The other claims are not touched by a-no.
  assert.notEqual(r.c2.verdict.strength, 'undecided');
});
