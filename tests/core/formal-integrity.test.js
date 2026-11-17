// Integrity rules in Lean (formal/Exegra/Integrity.lean, tools/prove-integrity.js) on the fixture
// tests/fixtures/integrity:
//
// - every rule holds and Lean proves it by reflection, kernel-checked, with standard axioms only;
// - every mutation of mutations.json makes its rule fail, and Lean refutes the rule from the stated
//   counterexample alone;
// - differential: on seeded random mutations of the fixture, the Lean checker and the JavaScript
//   evaluator give the same verdict and the same counterexamples for every rule, and each rule is
//   seen both holding and failing.
//
// Every check needs Lake. Without it the test is skipped with a message: a skip is not a pass.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { Project } from '../../src/core/project.js';
import { analyzeSpec } from '../../src/core/analyze.js';
import { OPERATIONS, Tx } from '../../src/core/operations.js';
import { evaluateIntegrity } from '../../src/core/integrity.js';
import { exportRule, integrityRequest, witnessNumbers } from '../../src/core/integrity-export.js';
import { proveIntegrity } from '../../tools/prove-integrity.js';
import { lakeAvailable, FORMAL, LEAN_BIN } from '../../tools/prove.js';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const DIR = path.join(HERE, '..', 'fixtures', 'integrity');
const SPEC = fs.readFileSync(path.join(DIR, 'spec.jsonc'), 'utf8');
const MUTATIONS = JSON.parse(fs.readFileSync(path.join(DIR, 'mutations.json'), 'utf8')).mutations;
const NO_LAKE = 'lake is not available (install elan with the toolchain in formal/lean-toolchain); integrity proofs were not checked';

/** @param {string} text @param {any[]} ops */
function mutated(text, ops) {
  const p = new Project({ specText: text });
  const tx = new Tx(p.specText, p.layoutText, /** @type {any} */ (p.model));
  for (const op of ops) OPERATIONS[/** @type {keyof typeof OPERATIONS} */ (op.type)].apply(tx, op);
  const a = analyzeSpec(tx.specText);
  assert.ok(a.model && a.errorCount === 0, `the mutation validates: ${a.diagnostics.filter((d) => d.severity === 'error').map((d) => d.message).join('; ')}`);
  return /** @type {any} */ (a.model);
}

test('every fixture rule holds, proved in Lean by reflection with standard axioms only', (t) => {
  if (!lakeAvailable()) { t.skip(NO_LAKE); return; }
  const model = mutated(SPEC, []);
  const ids = model.byKind.integrityRule.map((/** @type {any} */ r) => r.id);
  const out = proveIntegrity(model, ids);
  for (const r of out) {
    assert.equal(r.result, 'holds', `${r.ruleId}: ${r.explanation}`);
    assert.equal(r.differential.agree, true);
    assert.equal(r.differential.searchTree, true);
    assert.deepEqual(r.theorems, ['facts_search_tree', 'holds']);
    assert.ok(r.axioms.every((/** @type {string} */ a) => ['propext', 'Classical.choice', 'Quot.sound'].includes(a)), `${r.ruleId}: ${r.axioms}`);
    const text = fs.readFileSync(path.join(FORMAL, r.file.replace(/^formal\//, '')), 'utf8');
    assert.match(text, /holds_of_eval \(by decide \+kernel\)/);
    assert.doesNotMatch(text, /native_decide/);
  }
});

test('every mutation is refuted in Lean from its stated counterexample', (t) => {
  if (!lakeAvailable()) { t.skip(NO_LAKE); return; }
  for (const m of MUTATIONS) {
    const model = mutated(SPEC, m.ops);
    const [r] = proveIntegrity(model, [m.rule], { maxWitnesses: 50 });
    assert.equal(r.result, 'violated', `${m.rule}: ${r.explanation}`);
    assert.equal(r.differential.agree, true);
    assert.equal(r.provedWitnesses, r.counterexamples, 'every witness was refuted');
    const want = JSON.stringify(m.expect);
    assert.ok(r.witnesses.some((/** @type {any[]} */ w) => JSON.stringify(Object.fromEntries(w.map((b) => [b.variable, b.entity]))) === want), `${m.rule}: Lean refuted ${want}`);
    assert.ok(r.axioms.every((/** @type {string} */ a) => ['propext', 'Classical.choice', 'Quot.sound'].includes(a)));
  }
});

/** A small deterministic generator (mulberry32). @param {number} seed */
function rng(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let x = a;
    x = Math.imul(x ^ (x >>> 15), x | 1);
    x ^= x + Math.imul(x ^ (x >>> 7), x | 61);
    return ((x ^ (x >>> 14)) >>> 0) / 4294967296;
  };
}

test('differential: Lean and JavaScript agree on every rule of seeded random mutations', (t) => {
  if (!lakeAvailable()) { t.skip(NO_LAKE); return; }
  assert.equal(spawnSync('lake', ['build'], { cwd: FORMAL, encoding: 'utf8', windowsHide: true }).status, 0, 'lake build');
  const rand = rng(396);
  /** @template T @param {T[]} xs @returns {T} */
  const pick = (xs) => xs[Math.floor(rand() * xs.length)];
  /** @param {string[]} xs */
  const subset = (xs) => xs.filter(() => rand() < 0.3);
  const decisions = ['dec-0', 'dec-1', 'dec-2', 'dec-3'];
  const gaps = ['g-1', 'g-2', 'g-3'];
  const holders = [...decisions, ...gaps, 's-1', 's-2', 'area-1'];
  const all = [...holders];
  const op = () => {
    switch (Math.floor(rand() * 6)) {
      case 0: return { type: 'SetProperty', id: pick(holders), property: 'basis', value: subset(all) };
      case 1: return { type: 'SetProperty', id: pick(decisions), property: pick(['closes', 'narrows']), value: subset(all) };
      case 2: return { type: 'SetProperty', id: pick(gaps), property: 'resolvedBy', value: rand() < 0.3 ? null : pick(decisions) };
      case 3: return { type: 'SetProperty', id: pick(decisions), property: 'status', value: pick(['stated', 'confirmed', 'superseded']) };
      case 4: return { type: 'SetProperty', id: pick(holders), property: 'origin', value: rand() < 0.5 ? null : 'proposed' };
      default: return { type: 'SetProperty', id: pick(['s-1', 's-2']), property: 'encodes', value: subset(all) };
    }
  };
  /** @type {Map<string, Set<boolean>>} */
  const seen = new Map();
  for (let i = 0; i < 25; i++) {
    const ops = Array.from({ length: 1 + Math.floor(rand() * 3) }, op);
    const model = mutated(SPEC, ops);
    for (const r of evaluateIntegrity(model)) {
      const ex = exportRule(model, r.ruleId);
      const run = spawnSync(LEAN_BIN, ['integrity'], { input: integrityRequest(ex), encoding: 'utf8', windowsHide: true });
      assert.equal(run.status, 0, run.stderr);
      const lean = JSON.parse(run.stdout).results[0];
      const js = new Set(r.counterexamples.map((c) => witnessNumbers(ex, c.values).join(',')));
      const ln = new Set(lean.witnesses.map((/** @type {number[]} */ w) => w.join(',')));
      const ctx = `${r.ruleId} after ${JSON.stringify(ops)}`;
      assert.equal(lean.holds, r.status === 'holds', ctx);
      assert.deepEqual([...ln].sort(), [...js].sort(), ctx);
      if (!seen.has(r.ruleId)) seen.set(r.ruleId, new Set());
      /** @type {Set<boolean>} */ (seen.get(r.ruleId)).add(lean.holds);
    }
  }
  for (const [id, s] of seen) assert.equal(s.size, 2, `rule "${id}" was seen both holding and failing`);
});
