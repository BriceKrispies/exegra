// Claim statuses are decided in Lean, not in JavaScript (WG-5684, criterion 3). The registered Lean function
// `claims.status` is replaced at the call boundary by a stub that returns sentinel statuses: if any status in
// evaluateClaims' output were computed in JavaScript, it would not be a sentinel. The same holds for regressions:
// admit and verify ask the Lean function `verdict.isRegression`.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { overrideLeanFunction } from '../../src/core/lean.js';
import { evaluateClaims, evaluateClaim } from '../../src/core/claims.js';
import { compare, claimBaseline, verifyRegressions } from '../../cli/admit.js';

const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');

/** @param {string} kind @param {string} id @param {any} data */
const ent = (kind, id, data) => ({ kind, id, data: { id, ...data }, owner: null, path: [], loc: { line: 1, column: 1, offset: 0, length: 1 } });

/** A model with a claim of every family: structural, evidence (tests and a document), lean-theorem, metric, none. */
function model() {
  const entities = [
    ent('component', 'x', { name: 'X', category: 'svc' }),
    ent('component', 'y', { name: 'Y', category: 'svc' }),
    ent('relationship', 'r1', { kind: 'calls', from: 'x', to: 'y' }),
    ent('claim', 'c-structural', { kind: 'structural', statement: 'X never calls Y.', evaluate: { method: 'no-relationship', from: 'x', to: 'y' } }),
    ent('claim', 'c-reachable', { kind: 'structural', statement: 'X reaches Y.', evaluate: { method: 'reachable', from: 'x', to: 'y' } }),
    ent('claim', 'c-tested', { kind: 'invariant', statement: 'A and B hold.', evaluate: { method: 'external-evidence' } }),
    ent('evidence', 'ev-a', { claim: 'c-tested', kind: 'test', ref: 'tests/a.test.js' }),
    ent('evidence', 'ev-b', { claim: 'c-tested', kind: 'test', ref: 'tests/b.test.js' }),
    ent('claim', 'c-doc', { kind: 'measured', statement: 'p99 < 50 ms.', evaluate: { method: 'external-evidence' } }),
    ent('evidence', 'ev-doc', { claim: 'c-doc', kind: 'document', ref: 'illustrative://report' }),
    ent('claim', 'c-lean', { kind: 'invariant', statement: 'It terminates.', evaluate: { method: 'lean-theorem', theorem: 'Exegra.t', about: ['Exegra.f'] } }),
    ent('claim', 'c-none', { kind: 'invariant', statement: 'Declared only.' }),
    ent('claim', 'c-unknown', { kind: 'invariant', statement: 'Unknown method.', evaluate: { method: 'magic' } }),
  ];
  /** @type {Record<string, any[]>} */
  const byKind = {};
  for (const e of entities) (byKind[e.kind] ??= []).push(e);
  return /** @type {any} */ ({
    semanticHash: 'boundary', entities: new Map(entities.map((e) => [e.id, e])), byKind, refs: [], exprs: [],
    meta: { relationshipKinds: { calls: { label: 'calls', dependency: true } }, categories: { svc: { label: 'svc' } }, verificationMethods: {}, entities: {}, sections: {} },
  });
}

const RECORDED = {
  results: { 'ev-a': { outcome: 'pass', stamp: 'T' }, 'ev-b': { outcome: 'fail', stamp: 'T' } },
  theorems: { 'Exegra.t': { found: true, kind: 'theorem', kernel: 'ok', axioms: ['propext'], about: { 'Exegra.f': { kind: 'definition', inStatement: true } }, formalHash: 'F' } },
};
const STAMPS = { tree: 'T', formal: 'F' };
const SENTINELS = ['sentinel-0', 'sentinel-1', 'sentinel-2'];

/** A stub of claims.status: the i-th claim of each call gets SENTINELS[i % 3]. @param {{calls: number}} seen */
const stub = (seen) => (/** @type {any} */ args) => {
  seen.calls += 1;
  return args.claims.map((/** @type {any} */ _c, /** @type {number} */ i) => ({
    strength: 'undecided', subject: 'model', openAssumptions: [], freshness: 'fresh', established: false,
    label: SENTINELS[i % 3], refused: [], theorems: [], factFreshness: [],
  }));
};

// Stubs claims.status and verdict.isRegression at the call boundary and checks that every status and regression is the stub's; no claimStatus in src/core or cli.
// @evidence claim-statuses-decided-in-lean #
test('every status in evaluateClaims output is the one the Lean function claims.status returned', () => {
  const seen = { calls: 0 };
  const restore = overrideLeanFunction('claims.status', stub(seen));
  try {
    const results = evaluateClaims(model(), { recorded: RECORDED, stamps: STAMPS });
    assert.equal(results.length, 7);
    assert.equal(seen.calls, 1, 'one call decides every claim');
    results.forEach((r, i) => {
      assert.equal(r.status, SENTINELS[i % 3], `${r.claimId}: ${r.status} is not the sentinel`);
      assert.equal(r.verdict?.strength, 'undecided', r.claimId);
    });
    // c-structural is violated by the model and c-tested has a failing test: JavaScript does not overrule Lean.
    assert.ok(results.every((r) => SENTINELS.includes(r.status)));
    const one = evaluateClaim(model(), 'c-reachable', { recorded: RECORDED, stamps: STAMPS });
    assert.equal(one.status, SENTINELS[0]);
  } finally {
    restore();
  }
  // With the Lean function back, the statuses are Lean's own, and none is a sentinel.
  const real = evaluateClaims(model(), { recorded: RECORDED, stamps: STAMPS });
  assert.ok(real.every((r) => !SENTINELS.includes(r.status)));
  const by = Object.fromEntries(real.map((r) => [r.claimId, r]));
  assert.equal(by['c-structural'].status, 'violated');
  assert.equal(by['c-reachable'].status, 'verified');
  assert.equal(by['c-tested'].status, 'violated');
  assert.equal(by['c-doc'].status, 'asserted');
  assert.equal(by['c-lean'].status, 'proved');
});

test('admit and verify decide regressions by calling the Lean function verdict.isRegression', () => {
  const tuple = (/** @type {string} */ strength) => ({ strength, subject: 'implementation', openAssumptions: [], freshness: 'fresh' });
  const side = (/** @type {Record<string, string>} */ claims) => /** @type {any} */ ({
    claims: new Map(Object.entries(claims).map(([id, s]) => [id, { id, status: s === 'proved' ? 'proved' : 'not-evaluated', explanation: '', verdict: tuple(s) }])),
    errors: new Map(), warnings: new Map(), gaps: new Map(), violations: new Map(), model: model(),
  });
  // Lean says: proved to undecided is a regression, and so is any removal.
  const real = compare(side({ a: 'proved', b: 'proved' }), side({ a: 'undecided' }));
  assert.deepEqual(real.reasons.map((x) => [x.code, x.id]), [['admit.claim-regressed', 'a'], ['admit.claim-removed', 'b']]);
  // A stub that calls nothing a regression: admit reports none, even for the same fall and the removal.
  let restore = overrideLeanFunction('verdict.isRegression', (/** @type {any} */ args) => args.pairs.map(() => false));
  try {
    const none = compare(side({ a: 'proved', b: 'proved' }), side({ a: 'undecided' }));
    assert.deepEqual(none.reasons, []);
    const base = claimBaseline([{ claimId: 'p', status: 'proved', verdict: tuple('proved') }]);
    assert.deepEqual(verifyRegressions(base, {}), []);
  } finally {
    restore();
  }
  // A stub that calls everything a regression: an unchanged claim is reported, which no JavaScript rule would do.
  restore = overrideLeanFunction('verdict.isRegression', (/** @type {any} */ args) => args.pairs.map(() => true));
  try {
    const all = compare(side({ a: 'proved' }), side({ a: 'proved' }));
    assert.deepEqual(all.reasons.map((x) => [x.code, x.id]), [['admit.claim-regressed', 'a']]);
    const base = claimBaseline([{ claimId: 'p', status: 'proved', verdict: tuple('proved') }]);
    assert.deepEqual(verifyRegressions(base, base).map((x) => [x.code, x.id]), [['verify.claim-regressed', 'p']]);
  } finally {
    restore();
  }
});

test('no JavaScript status rule is left: claimStatus is gone from src/core and cli', () => {
  /** @param {string} dir @returns {string[]} */
  const files = (dir) => fs.readdirSync(dir, { withFileTypes: true }).flatMap((d) => (d.isDirectory() ? files(path.join(dir, d.name)) : d.name.endsWith('.js') ? [path.join(dir, d.name)] : []));
  const hits = [...files(path.join(repoRoot, 'src', 'core')), ...files(path.join(repoRoot, 'cli'))]
    .filter((f) => fs.readFileSync(f, 'utf8').includes('claimStatus'))
    .map((f) => path.relative(repoRoot, f));
  assert.deepEqual(hits, []);
});
