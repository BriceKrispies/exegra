// The lean-theorem claim method: Lean checks a named theorem of the Lean core (tools/lean-theorems.js)
// and src/core/claims.js derives the status from what Lean reported. A real theorem of
// formal/Exegra/Properties.lean about Exegra.runInput is proved; theorems that use sorry,
// native_decide or an axiom of their own, a theorem whose statement does not mention the named
// implementation constant, and a name that does not exist are refused (violated); a claim with no
// recorded check is not evaluated. The checks that need Lean skip when `lake` is not on the PATH;
// the rule itself is also tested on recorded facts without Lean.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { analyzeSpec } from '../../src/core/analyze.js';
import { evaluateClaims, theoremRequests } from '../../src/core/claims.js';
import { checkTheorems } from '../../tools/lean-theorems.js';
import { REPO_ROOT } from '../../tools/conformance.js';

const PRELUDE = fs.readFileSync(path.join(REPO_ROOT, 'tests', 'fixtures', 'lean-theorem', 'Refused.lean'), 'utf8');

/** @param {string} id @param {string} theorem @param {string[]} [about] */
const claim = (id, theorem, about) => ({
  id, kind: 'invariant', statement: `${id}.`, subjects: ['core'],
  evaluate: { method: 'lean-theorem', theorem, ...(about ? { about } : {}) },
});

const SPEC = JSON.stringify({
  exegra: '0.1',
  system: { id: 'lean-fixture', name: 'Lean fixture' },
  components: [{ id: 'core', name: 'Core', category: 'logical', implementation: { status: 'manual', language: 'lean' } }],
  claims: [
    claim('terminates', 'Exegra.runInput_terminates', ['Exegra.runInput']),
    claim('with-sorry', 'ExegraFixture.uses_sorry', ['Exegra.runInput']),
    claim('with-native-decide', 'ExegraFixture.uses_native_decide', ['Exegra.runInput']),
    claim('with-own-axiom', 'ExegraFixture.uses_custom_axiom', ['Exegra.runInput']),
    claim('off-topic', 'ExegraFixture.off_topic', ['Exegra.runInput']),
    claim('missing', 'Exegra.no_such_theorem'),
  ],
});

function model() {
  const { model: m, errorCount, diagnostics } = analyzeSpec(SPEC);
  assert.equal(errorCount, 0, JSON.stringify(diagnostics.filter((d) => d.severity === 'error')));
  return /** @type {NonNullable<typeof m>} */ (m);
}

/** @param {any} recorded */
const statuses = (recorded) => Object.fromEntries(evaluateClaims(model(), { recorded }).map((r) => [r.claimId, r]));

const lake = spawnSync('lake', ['--version'], { encoding: 'utf8', windowsHide: true });
const noLean = lake.error || lake.status !== 0 ? 'lake is not on the PATH (install elan with the toolchain of formal/lean-toolchain)' : false;

test('a lean-theorem claim with no recorded check is not evaluated', () => {
  const r = statuses(undefined);
  for (const id of ['terminates', 'with-sorry', 'missing']) assert.equal(r[id].status, 'not-evaluated', id);
  assert.match(r.terminates.explanation, /exegra verify/);
  assert.deepEqual(theoremRequests(model()).find((q) => q.theorem === 'Exegra.runInput_terminates'), { theorem: 'Exegra.runInput_terminates', about: ['Exegra.runInput'] });
});

test('the rule on recorded facts: proved needs a kernel-checked theorem with standard axioms that mentions the named code', () => {
  const ok = { found: true, kind: 'theorem', kernel: 'ok', axioms: ['propext', 'Quot.sound'], about: { 'Exegra.runInput': { kind: 'definition', inStatement: true } }, lean: '4.35.0', checkedAt: 'T' };
  /** @param {any} rec */
  const one = (rec) => statuses({ theorems: { 'Exegra.runInput_terminates': rec } }).terminates;
  assert.equal(one(ok).status, 'proved');
  assert.equal(one({ ...ok, axioms: [...ok.axioms, 'sorryAx'] }).status, 'violated');
  assert.equal(one({ ...ok, axioms: ['Lean.ofReduceBool'] }).status, 'violated');
  assert.match(one({ ...ok, axioms: ['Exegra.x._native.native_decide.ax_1_1'] }).explanation, /native_decide/);
  assert.equal(one({ ...ok, kernel: 'error: (kernel) declaration type mismatch' }).status, 'violated');
  assert.equal(one({ ...ok, kind: 'axiom' }).status, 'violated');
  assert.equal(one({ ...ok, about: { 'Exegra.runInput': { kind: 'definition', inStatement: false } } }).status, 'violated');
  assert.equal(one({ ...ok, about: { 'Exegra.runInput': { kind: 'theorem', inStatement: true } } }).status, 'violated');
  assert.equal(one({ ...ok, about: {} }).status, 'not-evaluated', 'a constant the check did not cover');
  assert.equal(one({ found: false }).status, 'violated');
});

test('Lean proves a real theorem about Exegra.runInput and refuses sorry, native_decide, its own axioms and an off-topic statement', { skip: noLean }, () => {
  const check = checkTheorems(theoremRequests(model()), { prelude: PRELUDE });
  assert.ok(check.available, check.available ? '' : check.reason);
  const rec = /** @type {any} */ (check).results;
  assert.deepEqual(rec['ExegraFixture.uses_sorry'].axioms.includes('sorryAx'), true);
  // Lean 4.35 records each native_decide as an auxiliary axiom <theorem>._native.native_decide.ax_<n>_<m>.
  assert.ok(rec['ExegraFixture.uses_native_decide'].axioms.some((/** @type {string} */ a) => /native_decide|ofReduceBool/.test(a)));
  assert.ok(rec['ExegraFixture.uses_custom_axiom'].axioms.includes('ExegraFixture.always_ok'));
  assert.equal(rec['Exegra.runInput_terminates'].kernel, 'ok');

  const r = statuses({ theorems: rec });
  assert.equal(r.terminates.status, 'proved', r.terminates.explanation);
  assert.match(r.terminates.explanation, /Exegra\.runInput/);
  assert.equal(r['with-sorry'].status, 'violated');
  assert.match(r['with-sorry'].explanation, /sorry/);
  assert.equal(r['with-native-decide'].status, 'violated');
  assert.match(r['with-native-decide'].explanation, /native_decide/);
  assert.equal(r['with-own-axiom'].status, 'violated');
  assert.match(r['with-own-axiom'].explanation, /always_ok/);
  assert.equal(r['off-topic'].status, 'violated');
  assert.match(r['off-topic'].explanation, /does not mention the implementation constant "Exegra\.runInput"/);
  assert.equal(r.missing.status, 'violated');
});
