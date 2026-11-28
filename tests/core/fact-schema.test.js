// Facts have a Lean-defined schema (Exegra.Verdict.Fact: kind, subject, target, stamps, outcome), the trusted
// producers emit it, and a fact that does not decode is refused with a diagnostic (WG-5684, criterion 4).

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { decodeFacts } from '../../src/core/verdict.js';
import { evaluateClaims } from '../../src/core/claims.js';
import { referenceFact } from '../../cli/outcomes.js';
import { theoremCheckFact } from '../../tools/lean-theorems.js';
import { factStamps } from '../../tools/tree-stamp.js';
import { importScanFacts } from '../../tools/import-scan.js';

const CURRENT = { tree: 'TREE', formal: 'FORMAL' };

test('the facts the trusted producers emit decode against the Lean schema', () => {
  const facts = [
    // the test-runner adapters: a pass, a failure, a skip, a reference that matched no test
    referenceFact('ev-a', 'pass', 'TREE', CURRENT),
    referenceFact('ev-b', 'fail', 'OLD', CURRENT),
    referenceFact('ev-c', 'skipped', 'TREE', CURRENT),
    referenceFact('ev-d', 'none', null, CURRENT),
    // the Lean theorem checker
    theoremCheckFact('c-lean', { found: true, kind: 'theorem', kernel: 'ok', axioms: ['propext'], formalHash: 'FORMAL', about: { 'Exegra.f': { kind: 'definition', inStatement: true } } }, ['Exegra.f'], CURRENT),
    // the import scan
    ...importScanFacts({ undeclared: [{ from: 'src/core/derivation-cache.js', component: 'derivation-cache', imports: 'node:fs', target: 'filesystem' }], checked: 1 }, 'TREE', CURRENT),
  ];
  assert.deepEqual(decodeFacts(facts), facts.map(() => ({ ok: true })));
  // The tree stamp: a fact's stamps against the current ones, for either stamp.
  assert.deepEqual(factStamps('X', CURRENT), { recorded: 'X', current: 'TREE' });
  assert.deepEqual(factStamps(undefined, CURRENT, 'formal'), { recorded: null, current: 'FORMAL' });
  assert.deepEqual(factStamps('X', { tree: null, formal: null }), { recorded: 'X', current: null });
  // The adapters' outcomes: a skip is not run, a reference that matched nothing is a failure.
  assert.equal(referenceFact('ev-c', 'skipped', 'TREE', CURRENT).outcome, 'not-run');
  assert.equal(referenceFact('ev-d', 'none', null, CURRENT).outcome, 'fail');
});

test('a fact that does not decode is refused with the reason', () => {
  const good = referenceFact('ev-a', 'pass', 'TREE', CURRENT);
  const bad = [
    [{ ...good, kind: 'rumour' }, /unknown fact kind/],
    [{ ...good, subject: 'everything' }, /subject must be/],
    [{ ...good, target: { part: 'a', assumption: 'b' } }, /target must be/],
    [{ ...good, target: 'ev-a' }, /target must be/],
    [{ ...good, stamps: 'TREE' }, /stamps must be an object/],
    [{ ...good, stamps: { recorded: 1, current: 'TREE' } }, /stamps.recorded must be a string or null/],
    [{ ...good, outcome: 'probably' }, /outcome must be/],
    ['a fact', /a fact must be an object/],
  ];
  const decoded = decodeFacts(bad.map(([f]) => f));
  bad.forEach(([, re], i) => {
    const d = /** @type {any} */ (decoded[i]);
    assert.ok('error' in d, `fact ${i} was not refused`);
    assert.match(d.error, /** @type {RegExp} */ (re));
  });
});

test('a fact that does not decode is left out of the verdict and reported as claim.fact-refused', () => {
  /** @param {string} kind @param {string} id @param {any} data */
  const ent = (kind, id, data) => ({ kind, id, data, loc: { line: 1, column: 1 }, path: [] });
  const entities = [
    ent('assumption', 'a-safe', { statement: 'It is safe.' }),
    ent('claim', 'c', { kind: 'invariant', statement: 'It holds.', assumptions: ['a-safe'], evaluate: { method: 'external-evidence' } }),
    ent('evidence', 'ev', { claim: 'c', kind: 'test', ref: 'tests/core/a.test.js' }),
  ];
  /** @type {Record<string, any[]>} */
  const byKind = {};
  for (const e of entities) (byKind[e.kind] ??= []).push(e);
  const model = /** @type {any} */ ({ semanticHash: 'fixture', entities: new Map(entities.map((e) => [e.id, e])), byKind, meta: { verificationMethods: {} } });
  const recorded = { results: { ev: { outcome: 'pass', stamp: 'TREE' } } };
  // A malformed fact about the assumption (an outcome the schema does not know) would refute it if it were read.
  const assumptionFacts = [{ assumption: 'a-safe', outcome: /** @type {any} */ ('refuted!'), stamp: 'TREE' }];
  const [r] = evaluateClaims(model, { recorded, stamps: CURRENT, assumptionFacts });
  assert.equal(r.status, 'supported', r.explanation);
  assert.deepEqual(r.verdict?.openAssumptions, ['a-safe']);
  const d = r.diagnostics?.find((x) => x.code === 'claim.fact-refused');
  assert.ok(d, JSON.stringify(r.diagnostics));
  assert.equal(d.severity, 'warning');
  assert.match(d.message, /assumption "a-safe"/);
  assert.match(d.message, /outcome must be/);
});
