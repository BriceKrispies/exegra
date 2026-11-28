// Reuse of recorded test outcomes by `exegra verify`: the freshness rule (cli/outcomes.js), the tree stamp
// (tools/tree-stamp.js) it compares, and how the recording says how an outcome was obtained.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { createOutcomeReuse, nodeOutcome, playwrightOutcome, staleReason, OUTCOMES_DIR } from '../../cli/outcomes.js';
import { treeStamp } from '../../tools/tree-stamp.js';
import { mergeRecordedResults } from '../../cli/commands.js';

const t = (name, outcome, path = name) => ({ name, path, nesting: 0, outcome });
const nodeDoc = (files, stamp = 'S') => ({ kind: 'node', finishedAt: 'T', treeBefore: stamp, treeAfter: stamp, complete: true, files });

test('a node reference is answered from the recorded tests it matches', () => {
  const doc = nodeDoc({
    'tests/core/a.test.js': { fileOutcome: 'pass', tests: [t('parses text', 'pass'), t('refuses cycles', 'pass'), t('needs lake', 'skipped')] },
  });
  assert.deepEqual(nodeOutcome(doc, 'tests/core/a.test.js#parses|refuses'), { outcome: 'pass', ranAt: 'T' });
  assert.deepEqual(nodeOutcome(doc, 'tests/core/a.test.js#refuses'), { outcome: 'pass', ranAt: 'T' });
  assert.equal(nodeOutcome(doc, 'tests/core/a.test.js#needs lake')?.outcome, 'skipped');
  assert.equal(nodeOutcome(doc, 'tests/core/a.test.js#pars|needs lake')?.outcome, 'skipped', 'a match part of which skipped is not a pass');
});

// A recorded file with one passing and one skipped test answers a whole-file reference with skipped, naming how many matched tests did not execute.
// @evidence test-evidence-skip-aware
test('a whole-file reference to a file with a self-skipping test is not a pass', () => {
  const doc = nodeDoc({
    'tests/core/a.test.js': { fileOutcome: 'pass', tests: [t('parses text', 'pass'), t('needs lake', 'skipped')] },
  });
  assert.equal(nodeOutcome(doc, 'tests/core/a.test.js')?.outcome, 'skipped');
  assert.match(nodeOutcome(doc, 'tests/core/a.test.js')?.detail ?? '', /1 of 2 matching tests/);
});

test('a reference the recorded run cannot answer is not assumed to pass', () => {
  const doc = nodeDoc({
    'tests/core/a.test.js': { fileOutcome: 'pass', tests: [t('works', 'pass'), t('broken', 'fail')] },
    'tests/core/b.test.js': { fileOutcome: 'fail', tests: [t('fine', 'pass')] },
  });
  assert.equal(nodeOutcome(doc, 'tests/core/a.test.js#nothing like it'), null, 'matches no recorded test');
  assert.equal(nodeOutcome(doc, 'tests/core/a.test.js#broken'), null, 'a failure is run again for its detail');
  assert.equal(nodeOutcome(doc, 'tests/core/a.test.js'), null, 'a failure anywhere in the file');
  assert.equal(nodeOutcome(doc, 'tests/core/b.test.js#fine'), null, 'a file that failed as a whole');
  assert.equal(nodeOutcome(doc, 'tests/core/c.test.js'), null, 'a file absent from the run');
  assert.equal(nodeOutcome(doc, 'tests/core/a.test.js#(unclosed'), null, 'a pattern that is no expression');
});

test('a test matches by the name of its suite too', () => {
  const doc = nodeDoc({ 'tests/core/a.test.js': { fileOutcome: 'pass', tests: [t('inner case', 'pass', 'outer suite inner case')] } });
  assert.equal(nodeOutcome(doc, 'tests/core/a.test.js#outer suite')?.outcome, 'pass');
});

test('a browser reference matches the full title case-insensitively and needs a pass', () => {
  const doc = {
    kind: 'playwright', finishedAt: 'T', treeBefore: 'S', treeAfter: 'S', complete: true,
    tests: [
      { file: 'tests/browser/x.spec.js', project: 'desktop', title: ' desktop tests/browser/x.spec.js Renders the model', outcome: 'pass' },
      { file: 'tests/browser/x.spec.js', project: 'desktop', title: ' desktop tests/browser/x.spec.js sleeps', outcome: 'skipped' },
      { file: 'tests/browser/y.spec.js', project: 'desktop', title: ' desktop tests/browser/y.spec.js bad', outcome: 'fail' },
    ],
  };
  assert.equal(playwrightOutcome(doc, 'tests/browser/x.spec.js#renders the model')?.outcome, 'pass');
  assert.equal(playwrightOutcome(doc, 'tests/browser/x.spec.js#sleeps'), null, 'all skipped proves nothing; run it');
  assert.equal(playwrightOutcome(doc, 'tests/browser/y.spec.js#bad'), null);
  assert.equal(playwrightOutcome(doc, 'tests/browser/x.spec.js#absent'), null);
});

test('an outcome file is stale unless complete, undisturbed and stamped with the current tree', () => {
  assert.equal(staleReason(nodeDoc({}), 'S'), null);
  assert.match(staleReason(nodeDoc({}), 'OTHER') ?? '', /changed after/);
  assert.match(staleReason({ ...nodeDoc({}), treeAfter: 'X' }, 'X') ?? '', /while the recorded run ran/);
  assert.match(staleReason({ ...nodeDoc({}), complete: false }, 'S') ?? '', /partial/);
  assert.match(staleReason(null, 'S') ?? '', /no recorded/);
});

test('the tree stamp follows content and untracked files and generated outputs but not ignored files', () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-stamp-'));
  try {
    const git = (/** @type {string[]} */ ...args) => execFileSync('git', args, { cwd: root, stdio: 'ignore' });
    git('init', '-q');
    fs.writeFileSync(path.join(root, '.gitignore'), 'junk/\nsrc/engine/\n');
    fs.writeFileSync(path.join(root, 'a.js'), 'one');
    const base = treeStamp(root);
    assert.equal(treeStamp(root), base, 'deterministic');
    fs.mkdirSync(path.join(root, 'junk'));
    fs.writeFileSync(path.join(root, 'junk', 'x'), 'ignored');
    assert.equal(treeStamp(root), base, 'an ignored file does not matter');
    fs.writeFileSync(path.join(root, 'new.js'), 'untracked');
    const withNew = treeStamp(root);
    assert.notEqual(withNew, base, 'an untracked file counts');
    fs.writeFileSync(path.join(root, 'a.js'), 'two');
    assert.notEqual(treeStamp(root), withNew, 'an edit counts');
    fs.writeFileSync(path.join(root, 'a.js'), 'one');
    assert.equal(treeStamp(root), withNew, 'restoring the content restores the stamp');
    fs.mkdirSync(path.join(root, 'src', 'engine', 'lean'), { recursive: true });
    fs.writeFileSync(path.join(root, 'src', 'engine', 'lean', 'build-info.json'), '{}');
    assert.notEqual(treeStamp(root), withNew, 'a generated output the tests load counts');
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
});

// An outcome file stamped with the current tree answers a reference; with another stamp it answers nothing. Companion tests cover a reference matching no recorded test, failures, skipped tests, mixed matches and the stamp itself.
// @evidence verify-reuses-fresh-outcomes-only
test('outcomes are used only while the tree is the one they ran on', () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-reuse-'));
  try {
    fs.mkdirSync(path.join(root, OUTCOMES_DIR));
    const doc = nodeDoc({ 'tests/core/a.test.js': { fileOutcome: 'pass', tests: [t('works', 'pass')] } }, 'S1');
    fs.writeFileSync(path.join(root, OUTCOMES_DIR, 'node.json'), JSON.stringify(doc));
    const fresh = createOutcomeReuse(root, 'S1');
    assert.equal(fresh.lookup('tests/core/a.test.js#works', false)?.outcome, 'pass');
    assert.equal(fresh.lookup('tests/browser/x.spec.js', true), null, 'no browser outcomes recorded');
    const stale = createOutcomeReuse(root, 'S2');
    assert.equal(stale.lookup('tests/core/a.test.js#works', false), null, 'a file changed after the run');
    assert.match(stale.notes.node, /after the recorded run/);
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
});

test('the recorded results say whether an outcome was run or reused', () => {
  const results = mergeRecordedResults({}, [
    { id: 'a', outcome: 'pass', ranAt: 't1', obtained: 'reused' },
    { id: 'b', outcome: 'pass', ranAt: 't2', obtained: 'run' },
  ]);
  assert.deepEqual(results, { a: { outcome: 'pass', ranAt: 't1', obtained: 'reused' }, b: { outcome: 'pass', ranAt: 't2', obtained: 'run' } });
});
