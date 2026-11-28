// Change impact (WG-5684, criteria 7 to 11): the dependency graph of claims, the claims a change re-marks
// (decided in Lean, formal/Exegra/Impact.lean), incremental re-verification, admission of change sets over every
// artifact kind. The refusal of a weakened theorem runs Lean (tests/proofs/theorem-weakening.test.js).

import { test } from 'node:test';
import assert from 'node:assert/strict';
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
