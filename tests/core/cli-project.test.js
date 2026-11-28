// Registering a project from a script, and giving one inline (cli/commands.js `project`, `--spec`, `--product`).
// Each test works in a temporary directory holding a specs/ directory and the specification beside it.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { runCommand, exitCodeOf } from '../../cli/commands.js';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const FIXTURES = path.join(HERE, '..', 'fixtures', 'layers');
const PLATFORM = fs.readFileSync(path.join(FIXTURES, 'platform.jsonc'), 'utf8');
const BADGES = fs.readFileSync(path.join(FIXTURES, 'products', 'badges.jsonc'), 'utf8');

/** @param {(ctx: {dir: string, specs: string, spec: string, product: string}) => Promise<void>} body */
async function withDir(body) {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-cli-project-'));
  const cwd = process.cwd();
  try {
    const specs = path.join(dir, 'specs');
    fs.mkdirSync(specs);
    fs.writeFileSync(path.join(dir, 'platform.jsonc'), PLATFORM);
    fs.mkdirSync(path.join(dir, 'products'));
    fs.writeFileSync(path.join(dir, 'products', 'badges.jsonc'), BADGES);
    process.chdir(dir);
    await body({ dir, specs, spec: 'platform.jsonc', product: 'products' });
  } finally {
    process.chdir(cwd);
    fs.rmSync(dir, { recursive: true, force: true });
  }
}

// project add writes a relative link that validate reads as a layered project; project list shows it.
// @evidence cli-registers-projects-from-scripts
test('project add registers a spec file and product files stored relative to the project directory', () =>
  withDir(async ({ specs, spec, product }) => {
    const added = await runCommand('project', ['add', 'strata', '--spec', spec, '--product', product], { specs });
    assert.equal(added.ok, true, JSON.stringify(added));
    assert.equal(added.project, 'strata');
    assert.deepEqual(JSON.parse(fs.readFileSync(path.join(specs, 'strata', 'project.jsonc'), 'utf8')), { spec: '../../platform.jsonc', products: ['../../products'] });
    const validated = await runCommand('validate', [], { specs, project: 'strata' });
    assert.equal(validated.ok, true, JSON.stringify(validated));
    assert.equal(validated.result.products[0].product, 'badges', 'the registered project is layered');
    const listed = await runCommand('project', ['list'], { specs });
    assert.deepEqual(listed.result.map((/** @type {any} */ p) => [p.name, p.products]), [['strata', ['../../products']]]);
  }));

// Existing project, bad names and unreadable files are refused; --force replaces.
// @evidence cli-registers-projects-from-scripts
test('project add refuses to overwrite a project unless --force and refuses a bad name or an unreadable file', () =>
  withDir(async ({ specs, spec }) => {
    assert.equal((await runCommand('project', ['add', 'strata', '--spec', spec], { specs })).ok, true);
    const again = await runCommand('project', ['add', 'strata', '--spec', spec], { specs });
    assert.equal(again.ok, false);
    assert.equal(again.error?.code, 'project.exists');
    const forced = await runCommand('project', ['add', 'strata', '--spec', spec, '--product', 'products', '--force'], { specs });
    assert.equal(forced.ok, true);
    assert.equal(forced.result.replaced, true);
    assert.deepEqual(JSON.parse(fs.readFileSync(path.join(specs, 'strata', 'project.jsonc'), 'utf8')).products, ['../../products']);

    for (const bad of ['Strata', '../x', 'a b', '_x', 'x'.repeat(65)]) {
      const r = await runCommand('project', ['add', bad, '--spec', spec], { specs });
      assert.equal(r.ok, false, bad);
      assert.equal(r.error?.code, 'name.invalid', bad);
    }
    const missing = await runCommand('project', ['add', 'other', '--spec', 'nope.jsonc'], { specs });
    assert.equal(missing.ok, false);
    assert.equal(fs.existsSync(path.join(specs, 'other')), false, 'nothing is written for a spec that cannot be read');
    const noSpec = await runCommand('project', ['add', 'other'], { specs });
    assert.equal(exitCodeOf(noSpec), 2);
  }));

// A project with its own spec.jsonc is never given a link.
// @evidence cli-registers-projects-from-scripts
test('project add refuses a name whose project keeps its own spec.jsonc', () =>
  withDir(async ({ specs, spec }) => {
    fs.mkdirSync(path.join(specs, 'own'));
    fs.writeFileSync(path.join(specs, 'own', 'spec.jsonc'), PLATFORM);
    const r = await runCommand('project', ['add', 'own', '--spec', spec, '--force'], { specs });
    assert.equal(r.error?.code, 'project.exists');
    assert.equal(fs.existsSync(path.join(specs, 'own', 'project.jsonc')), false);
  }));

// remove deletes the link only.
// @evidence cli-registers-projects-from-scripts
test('project remove deletes the link and the directory only when nothing else is in it', () =>
  withDir(async ({ specs, spec }) => {
    await runCommand('project', ['add', 'strata', '--spec', spec], { specs });
    const removed = await runCommand('project', ['remove', 'strata'], { specs });
    assert.equal(removed.ok, true);
    assert.equal(removed.result.removedDirectory, true);
    assert.equal(fs.existsSync(path.join(specs, 'strata')), false);
    assert.equal(fs.existsSync(path.join(specs, '..', 'platform.jsonc')), true, 'the specification itself is not touched');

    await runCommand('project', ['add', 'strata', '--spec', spec], { specs });
    fs.writeFileSync(path.join(specs, 'strata', 'layout.jsonc'), '{}');
    const kept = await runCommand('project', ['remove', 'strata'], { specs });
    assert.equal(kept.result.removedDirectory, false);
    assert.equal(fs.existsSync(path.join(specs, 'strata', 'layout.jsonc')), true);

    const gone = await runCommand('project', ['remove', 'strata'], { specs });
    assert.equal(gone.error?.code, 'project.not-found');
  }));

// Inline projects on read-only commands; writers refuse the options.
// @evidence cli-registers-projects-from-scripts
test('validate and other read-only commands accept the project inline with --spec and --product', () =>
  withDir(async ({ specs, spec, product }) => {
    const alone = await runCommand('validate', ['--spec', spec], { specs });
    assert.equal(alone.ok, true, JSON.stringify(alone));
    assert.equal(alone.project, null);
    assert.equal(fs.readdirSync(specs).length, 0, 'nothing is registered');
    const layered = await runCommand('validate', ['--spec', spec, '--product', product], { specs });
    assert.equal(layered.ok, true, JSON.stringify(layered));
    assert.equal(layered.result.products[0].product, 'badges');
    const shown = await runCommand('show', ['badges__badge', '--spec', spec, '--product', 'products/badges.jsonc'], { specs });
    assert.equal(shown.ok, true, JSON.stringify(shown));

    const both = await runCommand('validate', ['--spec', spec, '--project', 'x'], { specs });
    assert.equal(exitCodeOf(both), 2);
    const orphan = await runCommand('validate', ['--product', product], { specs });
    assert.equal(exitCodeOf(orphan), 2);
    const gone = await runCommand('validate', ['--spec', 'nope.jsonc'], { specs });
    assert.equal(gone.error?.code, 'project.not-found');
    const writer = await runCommand('apply', ['--spec', spec], { specs });
    assert.equal(exitCodeOf(writer), 2, 'a command that writes does not take the project inline');
  }));
