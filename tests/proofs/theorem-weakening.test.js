// The refusal of a weakened theorem (WG-5684, criterion 11): variants of counter_le checked by Lean (lake), compared
// by admit. These runs check theorems in Lean, so they run with the proofs (npm run test:proofs, npm run verify,
// the Check workflow), not in the routine suite.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { analyzeSpec } from '../../src/core/analyze.js';
import { evaluateClaims } from '../../src/core/claims.js';
import { compare, snapshot, theoremChanges, acknowledge } from '../../cli/admit.js';
import { checkTheorems } from '../../tools/lean-theorems.js';

const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');

const lake = spawnSync('lake', ['--version'], { cwd: path.join(repoRoot, 'formal'), encoding: 'utf8', windowsHide: true });
const noLean = lake.error || lake.status !== 0 ? 'lake is not available in formal/' : false;

const INV = (/** @type {string} */ p) => `(counter L).lts.Invariant (fun s => ${p})`;
const PROOF_STRONG = `by
  refine safe_of_inductive (M := (counter L).lts) (I := fun s => ∃ n, s = [n] ∧ 0 ≤ n ∧ n ≤ L)
    (P := fun s => 0 ≤ getAt s 0 ∧ getAt s 0 ≤ L) ⟨?_, ?_⟩ ?_
  · intro s hs
    exact ⟨0, hs, by omega, hL⟩
  · intro s i t hs hst
    obtain ⟨n, rfl, h0, hn⟩ := hs
    obtain ⟨hg, rfl⟩ := hst
    have hc : (counter L).cmds[i] = incTo L := only_cmd
    rw [hc, incTo_guard] at hg
    have hlt : n < L := of_decide_eq_true hg
    rw [hc, incTo_exec]
    exact ⟨n + 1, rfl, by omega, by omega⟩
  · intro s hs
    obtain ⟨n, rfl, h0, hn⟩ := hs
    exact ⟨h0, hn⟩`;

/** Every variant in one prelude, each under its own name. */
const PRELUDE = `
namespace ExegraFixture
open Exegra.Core Exegra.Core.Examples LTS
-- the theorem as it was
theorem orig (L : Int) (hL : 0 ≤ L) : ${INV('getAt s 0 ≤ L')} := Exegra.Core.Examples.counter_le L hL
-- its hypothesis changed from 0 ≤ L to 0 ≤ L ∧ L ≤ 10
theorem bounded (L : Int) (hL : 0 ≤ L ∧ L ≤ 10) : ${INV('getAt s 0 ≤ L')} := Exegra.Core.Examples.counter_le L hL.1
-- the same statement with another proof
theorem reproved (L : Int) (hL : 0 ≤ L) : ${INV('getAt s 0 ≤ L')} := by exact Exegra.Core.Examples.counter_le L hL
-- the conjunct L ≤ 10 of the bounded hypothesis dropped, with the implication from the new statement to the old
theorem unbounded_again (L : Int) (hL : 0 ≤ L) : ${INV('getAt s 0 ≤ L')} := Exegra.Core.Examples.counter_le L hL
theorem unbounded_again_implies_previous :
    (∀ L : Int, 0 ≤ L → ${INV('getAt s 0 ≤ L')}) → (∀ L : Int, 0 ≤ L ∧ L ≤ 10 → ${INV('getAt s 0 ≤ L')}) :=
  fun h L hL => h L hL.1
-- an axiom used by the proof
axiom extra_le : ∀ L : Int, 0 ≤ L → 0 ≤ L
theorem with_axiom (L : Int) (hL : 0 ≤ L) : ${INV('getAt s 0 ≤ L')} := Exegra.Core.Examples.counter_le L (extra_le L hL)
-- the conclusion strengthened, with counter_le_implies_previous
theorem stronger (L : Int) (hL : 0 ≤ L) : ${INV('0 ≤ getAt s 0 ∧ getAt s 0 ≤ L')} := ${PROOF_STRONG}
theorem counter_le_implies_previous :
    (∀ L : Int, 0 ≤ L → ${INV('0 ≤ getAt s 0 ∧ getAt s 0 ≤ L')}) → (∀ L : Int, 0 ≤ L → ${INV('getAt s 0 ≤ L')}) :=
  fun h L hL s hs => (h L hL s hs).2
end ExegraFixture
`;

const ABOUT = ['Exegra.Core.Examples.counter'];
/** A model with one lean-theorem claim on `theorem`. @param {string} theorem @param {string} [supersedes] */
function leanModel(theorem, supersedes) {
  const claim = { id: 'counter', kind: 'invariant', statement: 'The counter never exceeds its limit.', evaluate: { method: 'lean-theorem', theorem, about: ABOUT, ...(supersedes ? { supersedes } : {}) } };
  const { model } = analyzeSpec(JSON.stringify({ exegra: '0.1', system: { id: 'w', name: 'W' }, components: [], claims: [claim] }));
  assert.ok(model);
  return model;
}

test('a weakened theorem is refused unless --accept names the claim; a proof change, a strengthening with its implication and a dropped conjunct are admitted', { skip: noLean }, () => {
  const names = ['orig', 'bounded', 'reproved', 'unbounded_again', 'with_axiom', 'stronger'];
  const requests = names.map((n) => ({
    theorem: `ExegraFixture.${n}`, about: ABOUT,
    ...(n === 'unbounded_again' ? { supersedes: 'ExegraFixture.unbounded_again_implies_previous' } : n === 'stronger' ? { supersedes: 'ExegraFixture.counter_le_implies_previous' } : {}),
  }));
  const check = checkTheorems(requests, { prelude: PRELUDE });
  assert.ok(check.available, check.available ? '' : check.reason);
  const rec = /** @type {any} */ (check).results;
  for (const n of names) assert.equal(rec[`ExegraFixture.${n}`].kernel, 'ok', n);
  const t = (/** @type {string} */ n) => `ExegraFixture.${n}`;
  /** The change from the claim on `from` to the claim on `to`. @param {string} from @param {string} to @param {string} [sup] */
  const change = (from, to, sup) => theoremChanges(leanModel(t(from)), leanModel(t(to), sup), rec, rec);

  // The hypothesis 0 ≤ L made 0 ≤ L ∧ L ≤ 10: refused.
  const hyp = change('orig', 'bounded');
  assert.deepEqual(hyp.reasons.map((r) => [r.code, r.id, r.weakening]), [['admit.theorem-weakened', 'counter', 'statement-changed']]);
  assert.deepEqual(acknowledge(hyp.reasons, ['admit.theorem-weakened']).open.length, 1, 'the code alone does not accept it');
  assert.deepEqual(acknowledge(hyp.reasons, ['counter']).open, [], '--accept counter does');

  // A proof-only change: same statement hash, no guarantee change.
  const proof = change('orig', 'reproved');
  assert.equal(rec[t('orig')].statementHash, rec[t('reproved')].statementHash);
  assert.deepEqual(proof.reasons, []);
  assert.deepEqual(proof.guaranteeChanges, []);

  // Dropping the conjunct L ≤ 10 together with the implication theorem: admitted, listed as a guarantee change.
  const dropped = change('bounded', 'unbounded_again', t('unbounded_again_implies_previous'));
  assert.deepEqual(dropped.reasons, []);
  assert.deepEqual(dropped.guaranteeChanges.map((g) => [g.claim, g.change]), [['counter', 'theorem-statement']]);
  // Without the implication the same change is refused.
  assert.equal(change('bounded', 'unbounded_again').reasons.length, 1);

  // An axiom used by the proof: refused.
  const axiom = change('orig', 'with_axiom');
  assert.deepEqual(axiom.reasons.map((r) => r.weakening), ['axioms-gained']);

  // The conclusion strengthened together with counter_le_implies_previous: admitted.
  const strong = change('orig', 'stronger', t('counter_le_implies_previous'));
  assert.deepEqual(strong.reasons, []);
  assert.deepEqual(strong.guaranteeChanges.map((g) => g.change), ['theorem-statement']);

  // Through admit's comparison: the weakening is a reason, and --accept counter admits it.
  const side = (/** @type {any} */ model) => snapshot(model, [], evaluateClaims(model));
  const b = side(leanModel(t('orig')));
  const a = side(leanModel(t('bounded')));
  const refused = compare(b, a, { theorems: { old: rec, new: rec } });
  assert.ok(refused.reasons.some((r) => r.code === 'admit.theorem-weakened' && r.id === 'counter'));
  const accepted = compare(b, a, { theorems: { old: rec, new: rec }, accept: ['counter', 'admit.guarantee-weakened'] });
  assert.ok(!accepted.reasons.some((r) => r.code === 'admit.theorem-weakened'));
  assert.ok(accepted.acknowledged.some((r) => r.code === 'admit.theorem-weakened'));
  assert.ok(accepted.guaranteeChanges.some((g) => g.claim === 'counter' && g.change === 'theorem-statement'));
});
