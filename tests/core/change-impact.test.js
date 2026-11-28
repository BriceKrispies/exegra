// Change impact (WG-5684, criteria 7 to 11): the dependency graph of claims, the claims a change re-marks
// (decided in Lean, formal/Exegra/Impact.lean), incremental re-verification, admission of change sets over every
// artifact kind, and the refusal of a weakened theorem.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { analyzeSpec } from '../../src/core/analyze.js';
import { Project } from '../../src/core/project.js';
import { evaluateClaims } from '../../src/core/claims.js';
import { changeImpact, dependencyGraph } from '../../src/core/impact.js';
import { executeEvidence } from '../../cli/evidence-run.js';
import { runCommand } from '../../cli/commands.js';
import { compare, snapshot, theoremChanges, acknowledge } from '../../cli/admit.js';
import { checkTheorems } from '../../tools/lean-theorems.js';

const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
const FIXTURE = path.join(repoRoot, 'tests', 'fixtures', 'change-impact');
const SPEC = fs.readFileSync(path.join(FIXTURE, 'spec.jsonc'), 'utf8');
const RECORDED = JSON.parse(fs.readFileSync(path.join(FIXTURE, 'results.json'), 'utf8'));
const EXPECTED = JSON.parse(fs.readFileSync(path.join(FIXTURE, 'expected.json'), 'utf8'));

function before() {
  const { model, errorCount, diagnostics } = analyzeSpec(SPEC);
  assert.equal(errorCount, 0, JSON.stringify(diagnostics.filter((d) => d.severity === 'error')));
  assert.ok(model);
  return model;
}

/** The model after applying a change set's operations. @param {any[]} ops */
function after(ops) {
  const project = new Project({ name: 'change-impact', specText: SPEC, layoutText: null });
  if (!ops.length) return /** @type {any} */ (project.model);
  const tx = project.apply(ops, { origin: 'cli' });
  assert.ok(tx.ok, tx.message);
  return /** @type {any} */ (project.model);
}

/** @param {any} change */
const impactOf = (change) => changeImpact(before(), after(change.ops ?? []), { files: change.files ?? [], recorded: RECORDED });

test('the dependency graph has the node kinds and edges of the fixture', () => {
  const g = dependencyGraph(before(), { recorded: RECORDED });
  const has = (/** @type {string} */ a, /** @type {string} */ b) => g.edges.some(([x, y]) => `${x.kind}:${x.id}` === a && `${y.kind}:${y.id}` === b);
  assert.ok(has('claim:c1', 'assumption:a1'), 'a claim depends on the assumptions it cites');
  assert.ok(has('assumption:a3', 'claim:c6'), 'an assumption depends on the claim that discharges it');
  assert.ok(has('claim:c4', 'leanDecl:ChangeImpact.f1_thm'), 'a lean-theorem claim depends on its theorem');
  assert.ok(has('leanDecl:ChangeImpact.f1_thm', 'file:tests/fixtures/change-impact/F1.lean'), 'a theorem depends on the file defining it');
  assert.ok(has('leanDecl:ChangeImpact.f1_thm', 'leanDecl:ChangeImpact.f1'), 'a theorem depends on the declarations its statement uses');
  assert.ok(has('claim:c5', 'evidence:ev-t1'), 'a claim depends on its evidence');
  assert.ok(has('evidence:ev-t1', 'file:tests/fixtures/change-impact/t1.test.js'), 'test evidence depends on the files its test covers');
  assert.ok(has('evidence:ev-m2', 'measurement:ev-m2') && has('measurement:ev-m2', 'file:tests/fixtures/change-impact/m2.csv'), 'a measurement depends on its file');
  assert.ok(!g.edges.some(([x]) => x.kind === 'claim' && x.id === 'c8'), 'c8 has no dependency');
});

for (const c of EXPECTED.changes) {
  test(`change impact on the fixture: ${c.name} re-marks exactly ${JSON.stringify(c.remark)}`, () => {
    const r = impactOf(c.change);
    assert.deepEqual(new Set(r.remark), new Set(c.remark));
    assert.deepEqual(r.guaranteeChanges.map((/** @type {any} */ g) => ({ claim: g.claim, change: g.change })), c.guaranteeChanges);
  });
}

/** A temporary specs directory holding the fixture as project "ci", with its recorded results. @param {(specs: string, dir: string) => Promise<void>} body */
async function withFixture(body) {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-change-impact-'));
  const noLean = process.env.EXEGRA_NO_LEAN;
  process.env.EXEGRA_NO_LEAN = '1';
  try {
    const specs = path.join(dir, 'specs');
    fs.mkdirSync(path.join(specs, 'ci', 'evidence'), { recursive: true });
    fs.writeFileSync(path.join(specs, 'ci', 'spec.jsonc'), SPEC);
    fs.writeFileSync(path.join(specs, 'ci', 'evidence', 'results.json'), JSON.stringify(RECORDED));
    await body(specs, dir);
  } finally {
    if (noLean === undefined) delete process.env.EXEGRA_NO_LEAN;
    else process.env.EXEGRA_NO_LEAN = noLean;
    fs.rmSync(dir, { recursive: true, force: true });
  }
}

test('exegra impact --change prints the claims to re-mark', () => withFixture(async (specs, dir) => {
  const file = path.join(dir, 'change.json');
  fs.writeFileSync(file, JSON.stringify(EXPECTED.changes[0].change));
  const out = await runCommand('impact', ['--project', 'ci', '--change', file], { specs });
  assert.equal(out.ok, true, JSON.stringify(out));
  assert.deepEqual(out.result.remark, ['c1', 'c3', 'c6', 'c7']);
  // A change set naming changed entities and files directly.
  fs.writeFileSync(file, JSON.stringify({ entities: ['a2'], files: ['tests/fixtures/change-impact/F1.lean'] }));
  const named = await runCommand('impact', ['--project', 'ci', '--change', file], { specs });
  assert.deepEqual(named.result.remark, ['c2', 'c3', 'c4']);
}));

test('incremental re-verification: after the a1 edit only the evidence of c1, c3, c6 and c7 runs', () => {
  const remark = new Set(impactOf(EXPECTED.changes[0].change).remark);
  const model = after(EXPECTED.changes[0].change.ops);
  /** @type {string[]} */
  const calls = [];
  const out = executeEvidence(model, {
    run: (ref) => { calls.push(ref); return { outcome: 'pass', obtained: 'run' }; },
    remark, priorResults: RECORDED.results, priorStamp: RECORDED.stamp, now: () => 'NOW',
  });
  const refs = (/** @type {string[]} */ ids) => ids.map((id) => /** @type {any} */ (model.entities.get(id)).data.ref).sort();
  assert.deepEqual(calls.sort(), refs(['ev-c1', 'ev-c3', 'ev-c6', 'ev-c7']), 'the runner adapter is called for exactly these references');
  assert.equal(calls.length, 4);
  assert.deepEqual(out.reused.sort(), ['ev-c2', 'ev-t1'], 'the others reuse their fresh results');
  assert.ok(out.runs.filter((r) => out.reused.includes(r.id)).every((r) => r.obtained === 'impact' && r.outcome === 'pass'));
  // A result that was not fresh on the last verified tree is not reused: it runs.
  const stale = { ...RECORDED.results, 'ev-c2': { ...RECORDED.results['ev-c2'], stamp: 'OLDER' } };
  const again = [];
  executeEvidence(model, { run: (ref) => { again.push(ref); return { outcome: 'pass' }; }, remark, priorResults: stale, priorStamp: RECORDED.stamp });
  assert.equal(again.length, 5);
  // Without a change set every test reference runs.
  const all = [];
  executeEvidence(model, { run: (ref) => { all.push(ref); return { outcome: 'pass' }; }, remark: null, priorResults: RECORDED.results, priorStamp: RECORDED.stamp });
  assert.equal(all.length, 6);
});

test('admit takes a change set touching the specification, Lean, test and measurement files, and lists guarantee changes apart', () => withFixture(async (specs, dir) => {
  const file = path.join(dir, 'change.json');
  const change = {
    ops: EXPECTED.changes.find((/** @type {any} */ c) => c.name === "edit c8's statement").change.ops,
    files: ['tests/fixtures/change-impact/F1.lean', 'tests/fixtures/change-impact/t1.test.js', 'tests/fixtures/change-impact/m2.csv'],
  };
  fs.writeFileSync(file, JSON.stringify(change));
  const rejected = await runCommand('admit', ['--project', 'ci', '--change', file], { specs });
  assert.equal(rejected.ok, false);
  assert.deepEqual(rejected.result.reasons.map((/** @type {any} */ r) => [r.code, r.id]), [['admit.guarantee-weakened', 'c8']]);
  const out = await runCommand('admit', ['--project', 'ci', '--change', file, '--accept', 'admit.guarantee-weakened'], { specs });
  assert.equal(out.ok, true, JSON.stringify(out.error ?? out.result?.reasons));
  assert.equal(out.result.verdict, 'admitted');
  assert.deepEqual(out.result.impact.remark, ['c2', 'c4', 'c5', 'c8']);
  assert.deepEqual(out.result.guaranteeChanges.map((/** @type {any} */ g) => [g.claim, g.change]), [['c8', 'statement']]);
  assert.equal(out.result.guaranteeChanges[0].after, 'The fixture has one claim with no dependency.');
}));

// ---------------------------------------------------------------------------------------------------------
// Theorem weakening (criterion 11), on variants of counter_le checked by Lean.

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
