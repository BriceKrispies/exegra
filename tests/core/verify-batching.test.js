// The evidence step of `exegra verify` in batches (WG-5717): one process per test file, outcomes attributed per
// reference from the runner's output, and a recorded pass reused only while what its file covered is unchanged.
// The fixtures are tests/fixtures/verify-batch/, copied to a scratch root so a test can edit them.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { runCommand } from '../../cli/commands.js';
import { createCoverHasher, planReuse, runTestBatches } from '../../cli/test-batch.js';
import { declaredTestNames, evidenceRefDiagnostics, refNamesATest } from '../../tools/test-names.js';

const FIXTURE = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', 'fixtures', 'verify-batch');

/** A scratch copy of the fixture; the caller removes it. */
function scratch() {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-batch-'));
  for (const f of fs.readdirSync(FIXTURE)) fs.copyFileSync(path.join(FIXTURE, f), path.join(root, f));
  return root;
}

/** @param {string} root @param {string[]} refs @param {string[]} [log] */
async function runRefs(root, refs, log = []) {
  const evidence = refs.map((ref, i) => ({ id: `ev${i}`, ref }));
  const hasher = createCoverHasher(root);
  const batch = await runTestBatches(evidence, { repoRoot: root, skipBrowser: false, log: (m) => log.push(m), hasher });
  return { evidence, hasher, ...batch };
}

// A fixture file with passing, failing, skipped and suite-nested tests and a name that matches nothing: each reference gets its own outcome, a failing test elsewhere in the file does not fail the others, a skipped test stays skipped, and the run starts one process per test file.
// @evidence verify-batches-test-runs
test('each reference gets the outcome of its own tests from one process per file', async () => {
  const root = scratch();
  try {
    const log = /** @type {string[]} */ ([]);
    const refs = [
      'mixed.test.js#passes one', 'mixed.test.js#passes two', 'mixed.test.js#fails alone', 'mixed.test.js#skips itself',
      'mixed.test.js#no such test', 'mixed.test.js#group', 'plain.test.js',
    ];
    const { results } = await runRefs(root, refs, log);
    const by = (/** @type {string} */ ref) => /** @type {any} */ (results.get(`ev${refs.indexOf(ref)}`));
    assert.equal(by('mixed.test.js#passes one').outcome, 'pass');
    assert.equal(by('mixed.test.js#passes two').outcome, 'pass', 'a failing test elsewhere in the file does not fail it');
    assert.equal(by('mixed.test.js#fails alone').outcome, 'fail');
    assert.match(by('mixed.test.js#fails alone').detail, /fails alone/);
    assert.equal(by('mixed.test.js#skips itself').outcome, 'skipped', 'a skipped test stays skipped');
    assert.equal(by('mixed.test.js#no such test').outcome, 'fail');
    assert.match(by('mixed.test.js#no such test').detail, /matched no test/);
    assert.equal(by('mixed.test.js#group').outcome, 'pass', 'a suite name selects its tests');
    assert.equal(by('plain.test.js').outcome, 'pass');
    const runs = log.filter((m) => m.startsWith('verify: running '));
    assert.equal(runs.length, 2, `one process per test file: ${runs.join(' | ')}`);
    assert.ok(runs.some((m) => m.includes('mixed.test.js (6 references)')));
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
});

// Three fixture test files, one loading a module, one reading a data file, one with neither: editing the module reruns only the first, editing the data file only the second, restoring a file restores the reuse; a reference with no coverage, a changed reference and a recorded failure run again.
// @evidence verify-reuses-unchanged-passes
test('a recorded pass is reused until a file its test covered changes and then only that file reruns', async () => {
  const root = scratch();
  try {
    const refs = ['uses-lib.test.js#lib answers', 'reads-data.test.js#data parses', 'plain.test.js#plain'];
    const first = await runRefs(root, refs);
    const priorResults = Object.fromEntries(first.evidence.map((e) => [e.id, { outcome: 'pass', ref: e.ref, ranAt: 'T', coverage: e.ref.split('#')[0] }]));
    for (const e of first.evidence) assert.equal(first.results.get(e.id)?.outcome, 'pass', e.ref);
    const priorCoverage = first.coverage;
    assert.ok(priorCoverage['uses-lib.test.js'].covers.includes('lib.js'), 'a module the test loaded is covered');
    assert.ok(priorCoverage['reads-data.test.js'].covers.includes('data.json'), 'a file the test read is covered');
    assert.ok(!priorCoverage['plain.test.js'].covers.includes('lib.js'));
    /** @param {string[]} subset */
    const plan = (subset = refs, env = priorCoverage, results = priorResults) => planReuse(
      first.evidence.filter((e) => subset.includes(e.ref)), { priorResults: results, priorCoverage: env, hasher: createCoverHasher(root) });
    const ranFiles = (/** @type {{run: {ref: string}[]}} */ p) => [...new Set(p.run.map((e) => e.ref.split('#')[0]))].sort();

    assert.deepEqual(ranFiles(plan()), [], 'nothing changed: every reference is reused');
    assert.equal(plan().reused.size, 3);

    fs.writeFileSync(path.join(root, 'lib.js'), 'export const answer = 42;\n');
    assert.deepEqual(ranFiles(plan()), ['uses-lib.test.js'], 'a changed module reruns the references that loaded it');

    fs.writeFileSync(path.join(root, 'lib.js'), 'export const answer = 41;\n');
    fs.writeFileSync(path.join(root, 'data.json'), '{ "ok": false }\n');
    assert.deepEqual(ranFiles(plan()), ['reads-data.test.js'], 'a changed data file reruns the references that read it');

    fs.writeFileSync(path.join(root, 'data.json'), '{ "ok": true }\n');
    assert.deepEqual(ranFiles(plan()), [], 'restoring the file restores the reuse');

    const noCoverage = { ...priorCoverage };
    delete noCoverage['plain.test.js'];
    assert.deepEqual(ranFiles(plan(refs, noCoverage)), ['plain.test.js'], 'a reference with no recorded coverage runs');
    const renamed = { ...priorResults, ev2: { ...priorResults.ev2, ref: 'plain.test.js#another' } };
    assert.deepEqual(ranFiles(plan(refs, priorCoverage, renamed)), ['plain.test.js'], 'a reference that changed since it was recorded runs');
    const failed = { ...priorResults, ev0: { ...priorResults.ev0, outcome: 'fail' } };
    assert.deepEqual(ranFiles(plan(refs, priorCoverage, failed)), ['uses-lib.test.js'], 'a recorded failure is run again');
    const skipped = { ...priorResults, ev0: { ...priorResults.ev0, outcome: 'not-run', detail: 'needs a tool' } };
    const skipPlan = plan(refs, priorCoverage, skipped);
    assert.deepEqual(ranFiles(skipPlan), [], 'a recorded skip on unchanged inputs is reused as a skip');
    assert.equal(skipPlan.reused.get('ev0')?.outcome, 'skipped');
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
});

// The static scan of a fixture test file, suite names in front of test names, run-time names, and the diagnostic for a reference to a test that was renamed away, with none for the declared one or a missing file.
// @evidence evidence-ref-names-a-test
test('validate refuses a reference whose name matches no test its file declares', () => {
  const source = fs.readFileSync(path.join(FIXTURE, 'mixed.test.js'), 'utf8');
  assert.deepEqual(declaredTestNames(source), {
    tests: ['passes one', 'passes two', 'fails alone', 'skips itself', 'inner passes'], suites: ['group'], dynamic: false,
  });
  assert.equal(refNamesATest('tests/core/x.test.js#passes one', source), true);
  assert.equal(refNamesATest('tests/core/x.test.js#group inner', source), true, 'a suite name in front of a test name');
  assert.equal(refNamesATest('tests/core/x.test.js#renamed since', source), false);
  assert.equal(refNamesATest('tests/core/x.test.js', source), true, 'a whole file names every test');
  assert.equal(refNamesATest('tests/core/x.test.js#anything', "for (const n of names) test(`case ${n}`, () => {});"), true, 'names built at run time are not refused');

  const model = /** @type {any} */ ({
    byKind: {
      evidence: [
        { id: 'ev-good', data: { kind: 'test', ref: 'tests/fixtures/verify-batch/mixed.test.js#passes one', claim: 'c' } },
        { id: 'ev-bad', data: { kind: 'test', ref: 'tests/fixtures/verify-batch/mixed.test.js#a test that was renamed away', claim: 'c' } },
        { id: 'ev-absent-file', data: { kind: 'test', ref: 'tests/fixtures/verify-batch/missing.test.js#x', claim: 'c' } },
      ],
    },
  });
  const diagnostics = evidenceRefDiagnostics(model, path.resolve(FIXTURE, '..', '..', '..'));
  assert.deepEqual(diagnostics.map((d) => [d.code, d.entityId]), [['evidence.ref-no-test', 'ev-bad']]);
});

// exegra validate on a fixture specification with one declared and one renamed-away reference reports exactly evidence.ref-no-test for the second.
// @evidence evidence-ref-names-a-test
test('the validate command reports the reference that names no test and only that one', async () => {
  const out = await runCommand('validate', ['--spec', path.join(FIXTURE, 'spec.jsonc')], { cwd: process.cwd(), project: 'ref-names' });
  assert.equal(out.ok, false);
  const errors = out.diagnostics.filter((/** @type {any} */ d) => d.severity === 'error');
  assert.deepEqual(errors.map((/** @type {any} */ d) => [d.code, d.entityId]), [['evidence.ref-no-test', 'ev-renamed-away']]);
});
