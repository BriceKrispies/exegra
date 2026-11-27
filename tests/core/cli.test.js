// The agent CLI (cli/commands.js). Each test copies a small fixture spec into a
// temporary specs directory and calls runCommand directly with that directory.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { runCommand, exitCodeOf, parseTestCounts, countPassingTests, countPassedBrowserTests, mergeRecordedResults } from '../../cli/commands.js';
import { Project } from '../../src/core/project.js';
import { OPERATIONS } from '../../src/core/operations.js';

/** A small, valid specification: a client calls a server; the server answers two ticks later. */
function fixtureDocument() {
  return {
    exegra: '0.1',
    system: { id: 'demo-system', name: 'Demo system' },
    components: [
      { id: 'client', name: 'Client', category: 'logical' },
      { id: 'server', name: 'Server', category: 'logical' },
    ],
    relationships: [{ id: 'client-calls-server', kind: 'calls', from: 'client', to: 'server' }],
    events: [
      { id: 'start', name: 'Start' },
      { id: 'request', name: 'Request', payload: [{ name: 'n', type: 'number' }] },
      { id: 'ack', name: 'Acknowledge' },
    ],
    behaviors: [
      {
        id: 'client-machine',
        name: 'Client machine',
        subject: 'client',
        initial: 'idle',
        variables: [{ name: 'sent', type: 'number', initial: 0 }],
        states: [
          { id: 'idle', name: 'Idle' },
          { id: 'waiting', name: 'Waiting' },
          { id: 'done', name: 'Done' },
        ],
        transitions: [
          {
            id: 'send',
            from: 'idle',
            to: 'waiting',
            on: 'start',
            effects: [
              { set: 'sent', to: 'sent + 1' },
              { emit: 'request', after: 1, payload: { n: 'sent' } },
            ],
          },
          { id: 'receive-ack', from: 'waiting', to: 'done', on: 'ack' },
        ],
      },
      {
        id: 'server-machine',
        name: 'Server machine',
        subject: 'server',
        initial: 'listening',
        states: [
          { id: 'listening', name: 'Listening' },
          { id: 'served', name: 'Served' },
        ],
        transitions: [
          { id: 'serve', from: 'listening', to: 'served', on: 'request', effects: [{ emit: 'ack', after: 2 }] },
        ],
      },
    ],
    scenarios: [
      {
        id: 'basic-exchange',
        name: 'Basic exchange',
        behaviors: ['client-machine', 'server-machine'],
        steps: [{ at: 0, event: 'start' }],
      },
    ],
    faults: [],
  };
}

/**
 * A fresh specs directory holding project "fixture".
 * @returns {{specs: string, file: string, text: string, cleanup: () => void}}
 */
function setup() {
  const specs = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-cli-'));
  const dir = path.join(specs, 'fixture');
  fs.mkdirSync(dir, { recursive: true });
  const file = path.join(dir, 'spec.jsonc');
  const text = `${JSON.stringify(fixtureDocument(), null, 2)}\n`;
  fs.writeFileSync(file, text, 'utf8');
  return { specs, file, text, cleanup: () => fs.rmSync(specs, { recursive: true, force: true }) };
}

const opts = (specs) => ({ specs, project: 'fixture' });

test('validate reports ok for a well-formed project', async () => {
  const env = setup();
  try {
    const out = await runCommand('validate', [], opts(env.specs));
    assert.equal(out.ok, true);
    assert.equal(out.command, 'validate');
    assert.equal(out.project, 'fixture');
    assert.equal(out.result.errors, 0);
    assert.match(out.semanticHash, /^[0-9a-f]{14}$/);
  } finally {
    env.cleanup();
  }
});

test('list --kind component returns components in declaration order without data', async () => {
  const env = setup();
  try {
    const out = await runCommand('list', ['--kind', 'component'], opts(env.specs));
    assert.equal(out.ok, true);
    assert.deepEqual(out.result.map((e) => e.id), ['client', 'server']);
    assert.equal(out.result[0].kind, 'component');
    assert.equal('data' in out.result[0], false);
  } finally {
    env.cleanup();
  }
});

test('show returns data, inbound references and component relationships', async () => {
  const env = setup();
  try {
    const out = await runCommand('show', ['server'], opts(env.specs));
    assert.equal(out.ok, true);
    assert.equal(out.result.data.name, 'Server');
    assert.ok(out.result.referencedBy.some((r) => r.from === 'client-calls-server'));
    assert.deepEqual(out.result.relationships.map((r) => [r.id, r.direction, r.other]), [['client-calls-server', 'in', 'client']]);
    assert.deepEqual(out.result.children, []);
    assert.deepEqual(out.result.ancestors, []);
  } finally {
    env.cleanup();
  }
});

test('deps --transitive follows dependency relationships', async () => {
  const env = setup();
  try {
    const out = await runCommand('deps', ['client', '--transitive'], opts(env.specs));
    assert.equal(out.ok, true);
    assert.deepEqual(out.result, [{ id: 'server', via: 'client-calls-server', depth: 1 }]);
  } finally {
    env.cleanup();
  }
});

test('apply SetProperty writes the spec file and a fresh Project sees the new value', async () => {
  const env = setup();
  try {
    const out = await runCommand('apply', ['--ops', JSON.stringify({ type: 'SetProperty', id: 'server', property: 'name', value: 'Renamed server' })], opts(env.specs));
    assert.equal(out.ok, true, JSON.stringify(out));
    assert.deepEqual(out.result.written, ['spec']);
    assert.equal(out.result.dryRun, false);
    assert.equal(out.result.semanticChanged, true);
    assert.notEqual(out.result.semanticHashBefore, out.result.semanticHashAfter);
    const reloaded = new Project({ specText: fs.readFileSync(env.file, 'utf8') });
    assert.equal(reloaded.model.entities.get('server').data.name, 'Renamed server');
  } finally {
    env.cleanup();
  }
});

test('apply with a stale --expect-hash fails with revision.stale and leaves the file byte-identical', async () => {
  const env = setup();
  try {
    const out = await runCommand('apply', [
      '--ops', JSON.stringify({ type: 'SetProperty', id: 'server', property: 'name', value: 'Other' }),
      '--expect-hash', '00000000000000',
    ], opts(env.specs));
    assert.equal(out.ok, false);
    assert.equal(out.error.code, 'revision.stale');
    assert.equal(fs.readFileSync(env.file, 'utf8'), env.text);
  } finally {
    env.cleanup();
  }
});

test('apply of an invalid operation fails with diagnostics and leaves the file byte-identical', async () => {
  const env = setup();
  try {
    const out = await runCommand('apply', ['--ops', JSON.stringify({ type: 'SetProperty', id: 'server', property: 'parent', value: 'missing-parent' })], opts(env.specs));
    assert.equal(out.ok, false);
    assert.ok(out.diagnostics.length > 0);
    assert.equal(fs.readFileSync(env.file, 'utf8'), env.text);
  } finally {
    env.cleanup();
  }
});

test('apply --dry-run validates but writes nothing', async () => {
  const env = setup();
  try {
    const out = await runCommand('apply', ['--dry-run', '--ops', JSON.stringify({ type: 'SetProperty', id: 'server', property: 'name', value: 'Dry' })], opts(env.specs));
    assert.equal(out.ok, true);
    assert.equal(out.result.dryRun, true);
    assert.deepEqual(out.result.written, []);
    assert.equal(fs.readFileSync(env.file, 'utf8'), env.text);
  } finally {
    env.cleanup();
  }
});

test('plan-delete describes the cascade without changing the file', async () => {
  const env = setup();
  try {
    const out = await runCommand('plan-delete', ['client'], opts(env.specs));
    assert.equal(out.ok, true);
    assert.ok(out.result.entities.includes('client'));
    assert.ok(out.result.entities.includes('client-calls-server'));
    assert.equal(fs.readFileSync(env.file, 'utf8'), env.text);
  } finally {
    env.cleanup();
  }
});

test('simulate runs a scenario and reports its outcome and steps', async () => {
  const env = setup();
  try {
    const out = await runCommand('simulate', ['basic-exchange', '--steps'], opts(env.specs));
    assert.equal(out.ok, true);
    assert.equal(out.result.scenarioId, 'basic-exchange');
    assert.equal(out.result.outcome, 'quiescent');
    assert.ok(out.result.stepCount > 0);
    assert.equal(out.result.steps.length, out.result.stepCount);
  } finally {
    env.cleanup();
  }
});

test('ops lists every operation in OPERATIONS', async () => {
  const out = await runCommand('ops', [], {});
  assert.equal(out.ok, true);
  assert.deepEqual(out.result.operations.map((o) => o.type), Object.keys(OPERATIONS));
});

test('an unknown command is a usage error with exit code 2', async () => {
  const out = await runCommand('frobnicate', [], {});
  assert.equal(out.ok, false);
  assert.equal(out.error.code, 'usage.unknown-command');
  assert.equal(exitCodeOf(out), 2);
});

test('parseTestCounts reads tap and spec summaries, so an empty run is detectable', () => {
  assert.deepEqual(parseTestCounts('ok 1 - a\n# tests 3\n# suites 0\n# pass 2\n# fail 0\n# skipped 1\n'), { tests: 3, pass: 2, fail: 0 });
  assert.deepEqual(parseTestCounts('ℹ tests 0\nℹ suites 0\nℹ pass 0\nℹ fail 0\n'), { tests: 0, pass: 0, fail: 0 });
  assert.deepEqual(parseTestCounts('ℹ tests 4\nℹ pass 3\nℹ fail 1\n'), { tests: 4, pass: 3, fail: 1 });
  assert.equal(parseTestCounts('no summary here'), null);
});

test('countPassingTests ignores the entry for the test file, so a pattern that matches nothing counts zero', () => {
  // What node prints when --test-name-pattern matches no test: only the file itself is "ok".
  const empty = 'TAP version 13\n1..0\n# Subtest: tests\\\\core\\\\sim.test.js\nok 1 - tests\\\\core\\\\sim.test.js\n  ---\n  type: \'test\'\n  ...\n1..1\n# tests 1\n# pass 1\n';
  assert.equal(countPassingTests(empty, 'tests/core/sim.test.js'), 0);
  const one = 'TAP version 13\n# Subtest: reset returns to the initial configuration\nok 1 - reset returns to the initial configuration\n1..1\n# tests 1\n# pass 1\n';
  assert.equal(countPassingTests(one, 'tests/core/sim.test.js'), 1);
  // A skipped test ran nothing, so it is not evidence.
  const skipped = 'TAP version 13\nok 1 - the engines agree # SKIP binaries not built\n1..1\n';
  assert.equal(countPassingTests(skipped, 'tests/core/formal-semantics.test.js'), 0);
});

test('countPassedBrowserTests counts the passed tests of a playwright summary, so a skipped or empty run is not a pass', () => {
  assert.equal(countPassedBrowserTests('Running 2 tests using 1 worker\n  ok 1 a (1s)\n  ok 2 b (1s)\n\n  2 passed (3s)\n'), 2);
  assert.equal(countPassedBrowserTests('Running 1 test using 1 worker\n  -  1 a\n\n  1 skipped\n'), 0);
  assert.equal(countPassedBrowserTests('\x1b[32m  1 passed\x1b[39m (2s)\n'), 1);
  assert.equal(countPassedBrowserTests(''), 0);
});

test('markdown renders a document of a specification that holds documents, and refuses one that holds none', async () => {
  const env = setup();
  try {
    const none = await runCommand('markdown', [], opts(env.specs));
    assert.equal(none.ok, false);
    assert.equal(none.error.code, 'markdown.none');
    const doc = {
      exegra: '0.1',
      system: { id: 'docs', name: 'Docs' },
      documents: [{ id: 'd', path: 'spec/area.md', role: 'requirements' }],
      sections: [{ id: 's', title: 'Area', level: 1, document: 'd', order: 1, body: '\nIntro.\n\n{{entity:g-1}}\n' }],
      goals: [{ id: 'g-1', ref: 'G-1', statement: '**Lead.** A goal.\n- A sub-point.', stage: 'R1' }],
    };
    fs.writeFileSync(env.file, JSON.stringify(doc), 'utf8');
    const list = await runCommand('markdown', [], opts(env.specs));
    assert.deepEqual(list.result.documents, ['spec/area.md']);
    const one = await runCommand('markdown', ['spec/area.md'], opts(env.specs));
    assert.equal(one.result.text, '# Area\n\nIntro.\n\n- **G-1** **Lead.** A goal.\n  - A sub-point. *(R1)*\n');
    const out = path.join(env.specs, 'rendered');
    assert.equal((await runCommand('markdown', ['--out', out], opts(env.specs))).result.written, 1);
    assert.equal(fs.readFileSync(path.join(out, 'spec', 'area.md'), 'utf8'), one.result.text);
    assert.equal((await runCommand('markdown', ['nope.md'], opts(env.specs))).error.code, 'markdown.unknown');
  } finally {
    env.cleanup();
  }
});

test('a skipped verify run records the evidence as not run instead of keeping an older pass', () => {
  const prior = {
    'browser-login': { outcome: 'pass', ranAt: '2026-11-10T09:00:00.000Z', stamp: 'OLD' },
    'node-model': { outcome: 'fail', detail: 'old failure', ranAt: '2026-11-10T09:00:00.000Z', stamp: 'OLD' },
  };
  const runs = [
    { id: 'browser-login', outcome: /** @type {const} */ ('skipped'), ranAt: '2026-11-17T10:00:00.000Z', attempted: false },
    { id: 'node-model', outcome: /** @type {const} */ ('pass'), ranAt: '2026-11-17T10:00:01.000Z' },
    { id: 'browser-new', outcome: /** @type {const} */ ('skipped'), ranAt: '2026-11-17T10:00:02.000Z', attempted: false },
  ];
  const results = mergeRecordedResults(prior, runs, 'NEW');
  assert.deepEqual(results, {
    'browser-login': { outcome: 'not-run', detail: 'not started (--skip-browser)', ranAt: '2026-11-17T10:00:00.000Z', stamp: 'NEW' },
    'node-model': { outcome: 'pass', ranAt: '2026-11-17T10:00:01.000Z', stamp: 'NEW' },
    'browser-new': { outcome: 'not-run', detail: 'not started (--skip-browser)', ranAt: '2026-11-17T10:00:02.000Z', stamp: 'NEW' },
  });
  // A browser test that was not started keeps a result recorded on this very tree.
  const same = mergeRecordedResults({ 'browser-login': { outcome: 'pass', ranAt: 't0', stamp: 'NEW' } }, [runs[0]], 'NEW');
  assert.deepEqual(same['browser-login'], { outcome: 'pass', ranAt: 't0', stamp: 'NEW' });
});

test('a run that failed records its detail, and a skipped run is recorded as not run', () => {
  const results = mergeRecordedResults({}, [
    { id: 'a', outcome: 'fail', detail: 'boom', ranAt: 't1' },
    { id: 'b', outcome: 'pass', ranAt: 't2' },
    { id: 'c', outcome: 'skipped', ranAt: 't3' },
  ]);
  assert.deepEqual(results, {
    a: { outcome: 'fail', detail: 'boom', ranAt: 't1' },
    b: { outcome: 'pass', ranAt: 't2' },
    c: { outcome: 'not-run', detail: 'the matching test skipped itself', ranAt: 't3' },
  });
});
