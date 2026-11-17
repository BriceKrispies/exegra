// Realisation roots (tools/realisation-roots.js): modules and test evidence in
// other repositories, declared through project.jsonc. The fixture
// tests/fixtures/external-root holds two fake roots and a bun-shaped JUnit report.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { runCommand } from '../../cli/commands.js';
import { checkTraceability } from '../../tools/traceability.js';
import { parseJUnit } from '../../tools/junit.js';
import { resolveRoots, splitRootRef, decide, RootsError } from '../../tools/realisation-roots.js';
import { Project } from '../../src/core/project.js';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const FIXTURE = path.resolve(HERE, '..', 'fixtures', 'external-root');
const REPORT = 'apps/api/reports/junit.xml';
const TEST_FILE = 'platform:apps/api/test/tenant.test.ts';

/** Evidence id -> [ref, expected outcome]. */
const EVIDENCE = {
  'ev-pass': [`${TEST_FILE}#tenant > isolation > rejects a cross-tenant read`, 'pass'],
  'ev-fail': [`${TEST_FILE}#tenant > isolation > scopes writes & reads`, 'fail'],
  'ev-describe': [`${TEST_FILE}#tenant > isolation`, 'fail'],
  'ev-environment': [`${TEST_FILE}#tenant > connects to postgres`, 'not-run'],
  'ev-skipped': [`${TEST_FILE}#tenant > later`, 'not-run'],
  'ev-error': [`${TEST_FILE}#tenant > loads fixtures`, 'not-run'],
  'ev-absent': ['platform:apps/api/test/other.test.ts', 'not-run'],
  'ev-top': [`${TEST_FILE}#top level`, 'pass'],
  'ev-undeclared': ['nowhere:test/a.test.ts', 'not-run'],
};

/** @param {Record<string, [string, string]>} evidence */
function spec(evidence = EVIDENCE) {
  return {
    exegra: '0.1',
    system: { id: 'remote-like', name: 'Externally realised system' },
    components: [
      { id: 'tenant-service', name: 'Tenant service', category: 'logical',
        implementation: { status: 'manual', modules: ['platform:apps/api/src/tenant/service.ts', 'platform:apps/api/src/gone.ts'] } },
      { id: 'tenant-schema', name: 'Tenant schema', category: 'storage',
        implementation: { status: 'manual', modules: ['database:migrations/', 'nowhere:x.ts'] } },
    ],
    claims: Object.keys(evidence).map((id) => ({ id: `c-${id}`, kind: 'invariant', statement: id, evaluate: { method: 'external-evidence' } })),
    evidence: Object.entries(evidence).map(([id, [ref]]) => ({ id, claim: `c-${id}`, kind: 'test', ref })),
  };
}

/**
 * A temporary specs directory with project "ext" whose project.jsonc declares the roots.
 * @param {Record<string, any>} roots @param {(dirs: {specs: string, tmp: string}) => Promise<void>} fn
 */
async function withProject(roots, fn, document = spec()) {
  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-ext-'));
  try {
    const specs = path.join(tmp, 'specs');
    fs.mkdirSync(path.join(specs, 'ext'), { recursive: true });
    fs.writeFileSync(path.join(specs, 'ext', 'spec.jsonc'), JSON.stringify(document, null, 2));
    fs.writeFileSync(path.join(specs, 'ext', 'project.jsonc'), `// realised in other repositories\n${JSON.stringify({ roots }, null, 2)}\n`);
    await fn({ specs, tmp });
  } finally {
    fs.rmSync(tmp, { recursive: true, force: true });
  }
}

const ROOTS = {
  platform: { path: path.join(FIXTURE, 'platform'), include: ['apps/*/src/**/*.ts'], exclude: ['**/*.test.ts'], tests: { junit: REPORT, base: 'apps/api' } },
  database: { path: path.join(FIXTURE, 'database') },
};

/** @param {any} document */
const modelOf = (document) => /** @type {any} */ (new Project({ name: 'ext', specText: JSON.stringify(document) }).model);

test('traceability: modules are checked in their root, an undeclared alias is missing, only roots with include globs report unclaimed files', async () => {
  await withProject(ROOTS, async ({ specs }) => {
    const out = await runCommand('traceability', [], { specs, project: 'ext' });
    assert.equal(out.ok, true, JSON.stringify(out));
    const r = out.result;
    assert.equal(r.checkedModules, 4);
    assert.deepEqual(r.missingModules, [
      { component: 'tenant-service', module: 'platform:apps/api/src/gone.ts', root: 'platform' },
      { component: 'tenant-schema', module: 'nowhere:x.ts', root: 'nowhere', reason: 'root not declared' },
    ]);
    // service.test.ts is excluded; the database root has no include globs, so it is not scanned.
    assert.deepEqual(r.unclaimedFiles, ['platform:apps/api/src/tenant/unclaimed.ts']);
    assert.equal(r.claimedFiles, 1);
    assert.equal(r.roots.platform.scanned, true);
    assert.equal(r.roots.database.scanned, false);
    assert.equal(r.roots.database.checkedModules, 1);
    assert.equal(r.roots.platform.found, true);
  });
});

test('traceability: a scanned root skips node_modules, and a root path that does not exist reports its modules missing', async () => {
  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-ext-'));
  try {
    fs.cpSync(path.join(FIXTURE, 'platform'), path.join(tmp, 'platform'), { recursive: true });
    fs.mkdirSync(path.join(tmp, 'platform', 'apps', 'api', 'src', 'node_modules'), { recursive: true });
    fs.writeFileSync(path.join(tmp, 'platform', 'apps', 'api', 'src', 'node_modules', 'dep.ts'), '');
    const roots = resolveRoots({ dir: tmp, value: { roots: { platform: { path: 'platform', include: ['apps/**/*.ts'] }, database: { path: 'missing' } } } });
    const r = checkTraceability(modelOf(spec()), tmp, roots);
    assert.ok(!r.unclaimedFiles.some((f) => f.includes('node_modules')));
    assert.ok(r.unclaimedFiles.includes('platform:apps/api/test/tenant.test.ts'), 'no exclude: the test file is unclaimed');
    assert.equal(r.roots?.database.found, false);
    assert.ok(r.missingModules.some((m) => m.module === 'database:migrations/'));
  } finally {
    fs.rmSync(tmp, { recursive: true, force: true });
  }
});

test('traceability: with no roots declared the result is the same as before', () => {
  const repo = path.resolve(HERE, '..', '..');
  const model = modelOf(spec());
  assert.deepEqual(checkTraceability(model, repo, []), checkTraceability(model, repo));
  assert.deepEqual(resolveRoots(null), []);
  assert.deepEqual(resolveRoots({ dir: repo, value: { spec: '../x/spec.jsonc' } }), []);
  assert.equal(checkTraceability(model, repo).roots, undefined);
});

test('a malformed roots declaration is refused', async () => {
  for (const bad of [{ roots: [] }, { roots: { Platform: { path: 'x' } } }, { roots: { p: {} } }, { roots: { p: { path: 'x', tests: {} } } },
    { roots: { p: { path: 'x', tests: { junit: 'j.xml', command: 'bun test' } } } }, { roots: { p: { path: 'x', notRunWhen: ['('] } } }]) {
    assert.throws(() => resolveRoots({ dir: '.', value: bad }), RootsError, JSON.stringify(bad));
  }
  await withProject({ p: { path: 'x', include: 'src' } }, async ({ specs }) => {
    const out = await runCommand('traceability', [], { specs, project: 'ext' });
    assert.equal(out.error?.code, 'roots.invalid');
  });
});

test('splitRootRef only takes an alias before the first "#"', () => {
  assert.deepEqual(splitRootRef('platform:a/b.ts#x > y'), { alias: 'platform', rest: 'a/b.ts#x > y' });
  assert.equal(splitRootRef('tests/core/a.test.js#name: with colon'), null);
  assert.equal(splitRootRef('C:/abs/path.ts'), null);
});

test('junit: a bun report parses into cases with the describe path, file and status', () => {
  const cases = parseJUnit(fs.readFileSync(path.join(FIXTURE, 'platform', REPORT), 'utf8'));
  assert.equal(cases.length, 7);
  const byName = Object.fromEntries(cases.map((c) => [c.name, c]));
  assert.deepEqual(byName['rejects a cross-tenant read'].suites, ['tenant', 'isolation']);
  assert.equal(byName['rejects a cross-tenant read'].file, 'test/tenant.test.ts');
  assert.equal(byName['scopes writes & reads'].status, 'fail');
  assert.match(byName['scopes writes & reads'].message, /Expected: "t1"/);
  assert.equal(byName['loads fixtures'].status, 'error');
  assert.match(byName['loads fixtures'].message, /hook timed out after 5000ms/);
  assert.equal(byName.later.status, 'skipped');
  assert.deepEqual(byName['top level'].suites, []);
});

test('junit: each evidence entry is pass, fail or not-run; a failure matching an environmental pattern is not-run', () => {
  const [root] = resolveRoots({ dir: FIXTURE, value: { roots: { platform: { path: 'platform', tests: { junit: REPORT, base: 'apps/api' } } } } });
  const cases = parseJUnit(fs.readFileSync(path.join(FIXTURE, 'platform', REPORT), 'utf8')).map((c) => ({ ...c, file: `apps/api/${c.file}` }));
  for (const [id, [ref, expected]] of Object.entries(EVIDENCE)) {
    if (id === 'ev-undeclared') continue;
    const rest = /** @type {{rest: string}} */ (splitRootRef(ref)).rest;
    assert.equal(decide(rest, cases, root).outcome, expected, id);
  }
  // A root that declares its own patterns replaces the defaults.
  const [strict] = resolveRoots({ dir: FIXTURE, value: { roots: { platform: { path: 'platform', notRunWhen: ['docker'] } } } });
  assert.equal(decide('apps/api/test/tenant.test.ts#tenant > connects to postgres', cases, strict).outcome, 'fail');
});

test('junit: verify --ingest-only records pass, fail and not-run, fails only on the real failure, and not-run leaves a claim without a result', async () => {
  await withProject(ROOTS, async ({ specs }) => {
    const out = await runCommand('verify', ['--ingest-only'], { specs, project: 'ext' });
    assert.equal(out.ok, false);
    assert.equal(out.error?.code, 'verify.failed');
    assert.match(String(out.error?.message), /2 evidence item\(s\) failed/);
    const outcomes = Object.fromEntries(out.result.evidence.map((/** @type {any} */ e) => [e.id, e.outcome]));
    assert.deepEqual(outcomes, Object.fromEntries(Object.entries(EVIDENCE).map(([id, [, o]]) => [id, o])));
    assert.deepEqual(out.result.notRun.sort(), ['ev-absent', 'ev-environment', 'ev-error', 'ev-skipped', 'ev-undeclared']);
    assert.equal(out.result.roots.platform.ran, false);
    const recorded = JSON.parse(fs.readFileSync(path.join(specs, 'ext', 'evidence', 'results.json'), 'utf8'));
    assert.equal(recorded.results['ev-environment'].outcome, 'not-run');
    assert.match(recorded.results['ev-environment'].detail, /ECONNREFUSED/);
    assert.equal(recorded.results['ev-pass'].root, 'platform');
    assert.deepEqual(recorded.results['ev-pass'].reports, [REPORT]);
    const claims = await runCommand('claims', [], { specs, project: 'ext' });
    const status = Object.fromEntries(claims.result.map((/** @type {any} */ c) => [c.claimId, c.status]));
    assert.equal(status['c-ev-pass'], 'supported');
    assert.equal(status['c-ev-fail'], 'violated');
    assert.equal(status['c-ev-environment'], 'inconclusive');
    // Ingesting is deterministic: the same report gives the same recorded file.
    await runCommand('verify', ['--ingest-only'], { specs, project: 'ext' });
    assert.deepEqual(JSON.parse(fs.readFileSync(path.join(specs, 'ext', 'evidence', 'results.json'), 'utf8')).results, recorded.results);
  });
  const passing = { 'ev-pass': EVIDENCE['ev-pass'], 'ev-environment': EVIDENCE['ev-environment'] };
  await withProject(ROOTS, async ({ specs }) => {
    const out = await runCommand('verify', ['--ingest-only'], { specs, project: 'ext' });
    assert.equal(out.ok, true, 'not-run is not a failure');
  }, { ...spec(passing), components: [] });
});

test('junit: verify runs a root\'s test command, and a command that writes no report leaves its evidence not-run', async () => {
  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-ext-run-'));
  try {
    const root = path.join(tmp, 'platform');
    fs.cpSync(path.join(FIXTURE, 'platform'), root, { recursive: true });
    const source = fs.readFileSync(path.join(root, REPORT), 'utf8');
    fs.rmSync(path.join(root, REPORT));
    fs.writeFileSync(path.join(root, 'report.src'), source);
    // No mkdir: bun, like this writer, needs the report directory to exist already.
    const writer = "require('fs').copyFileSync('../../report.src','reports/junit.xml');process.exit(1)";
    const evidence = { 'ev-pass': EVIDENCE['ev-pass'], 'ev-fail': EVIDENCE['ev-fail'] };
    const roots = { platform: { path: root, tests: { command: [process.execPath, '-e', writer], cwd: 'apps/api', junit: REPORT } } };
    await withProject(roots, async ({ specs }) => {
      const out = await runCommand('verify', [], { specs, project: 'ext' });
      assert.equal(out.result.roots.platform.ran, true);
      assert.equal(out.result.evidence.find((/** @type {any} */ e) => e.id === 'ev-pass').outcome, 'pass');
      assert.equal(out.result.evidence.find((/** @type {any} */ e) => e.id === 'ev-fail').outcome, 'fail');
    }, { ...spec(evidence), components: [] });
    const silent = { platform: { path: root, tests: { command: [process.execPath, '-e', 'process.exit(1)'], cwd: 'apps/api', junit: 'apps/api/reports/none.xml' } } };
    await withProject(silent, async ({ specs }) => {
      const out = await runCommand('verify', [], { specs, project: 'ext' });
      assert.equal(out.ok, true);
      const ev = out.result.evidence.find((/** @type {any} */ e) => e.id === 'ev-pass');
      assert.equal(ev.outcome, 'not-run');
      assert.match(ev.detail, /wrote no report/);
    }, { ...spec(evidence), components: [] });
  } finally {
    fs.rmSync(tmp, { recursive: true, force: true });
  }
});

test('a project.jsonc that only declares roots keeps the specification in the project directory', async () => {
  await withProject(ROOTS, async ({ specs }) => {
    const out = await runCommand('validate', [], { specs, project: 'ext' });
    assert.equal(out.ok, true, JSON.stringify(out.error));
  });
});
