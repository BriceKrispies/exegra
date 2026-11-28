// A specification kept as a manifest of part files (tools/spec-manifest.js, tools/workspace.js).
import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { SpecManifestError, planWrite, resolveSpecText } from '../../tools/spec-manifest.js';
import { createWorkspace } from '../../tools/workspace.js';

const FIXTURES = path.join(path.dirname(fileURLToPath(import.meta.url)), '..', 'fixtures', 'spec-manifest');
const resolveFixture = (/** @type {string} */ name) => {
  const file = path.join(FIXTURES, name, 'spec.jsonc');
  return resolveSpecText(file, fs.readFileSync(file, 'utf8'));
};

test('parts assemble in manifest order and array sections concatenate', () => {
  const r = resolveFixture('ok');
  assert.equal(r.manifest, true);
  assert.equal(
    r.text,
    '{\n  "system": { "id": "s" },\n  "claims": [\n    {"id":"m-1","kind":"invariant"},\n    {"id":"r-1","kind":"requirement"},\n    {"id":"r-2","kind":"requirement"}\n  ],\n  "goals": []\n}\n',
  );
});

test('a missing part is refused, naming it', () => {
  assert.throws(() => resolveFixture('missing-part'), (e) => e instanceof SpecManifestError && e.code === 'missing-part' && /gone\.jsonc/.test(e.message));
});

test('a section that is not an array in two parts is refused, naming both files', () => {
  assert.throws(() => resolveFixture('object-twice'), (e) => e instanceof SpecManifestError && e.code === 'duplicate-section' && /a\.jsonc/.test(e.message) && /b\.jsonc/.test(e.message));
});

test('an id repeated across parts is refused naming both files', () => {
  assert.throws(() => resolveFixture('duplicate-id'), (e) => e instanceof SpecManifestError && e.code === 'duplicate-id' && /c-1/.test(e.message) && /a\.jsonc/.test(e.message) && /b\.jsonc/.test(e.message));
});

test('a file that is not a manifest is its own text', () => {
  const file = path.join(FIXTURES, 'ok', 'a.jsonc');
  const text = fs.readFileSync(file, 'utf8');
  const r = resolveSpecText(file, text);
  assert.equal(r.manifest, false);
  assert.equal(r.text, text);
});

test('an edit is written back to the part that holds the entity and new entities go where the table says', () => {
  const r = resolveFixture('ok');
  const edited = r.text
    .replace('{"id":"m-1","kind":"invariant"}', '{"id":"m-1","kind":"invariant","statement":"x"}')
    .replace('{"id":"r-2","kind":"requirement"}', '{"id":"r-2","kind":"requirement"},\n    {"id":"r-3","kind":"requirement"},\n    {"id":"m-2","kind":"temporal"}');
  const changed = planWrite(r, edited);
  const byName = Object.fromEntries(changed.map((c) => [path.basename(c.file), c.text]));
  assert.deepEqual(Object.keys(byName).sort(), ['a.jsonc', 'b.jsonc']);
  assert.match(byName['a.jsonc'], /"m-1","kind":"invariant","statement":"x"/);
  assert.match(byName['a.jsonc'], /"m-2"/);
  assert.doesNotMatch(byName['a.jsonc'], /"r-3"/);
  assert.match(byName['b.jsonc'], /"r-3"/);
  assert.match(byName['b.jsonc'], /^\/\/ requirements/);
  // The parts, written back, assemble to the edited text.
  const again = resolveSpecText(r.file, fs.readFileSync(r.file, 'utf8'), (p) => byName[path.basename(p)] ?? fs.readFileSync(p, 'utf8'));
  assert.deepEqual(JSON.parse(again.text).claims.map((c) => c.id).sort(), ['m-1', 'm-2', 'r-1', 'r-2', 'r-3']);
});

test('the workspace reads a manifest and writes an edit to the parts, and refuses a bad manifest', async () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-manifest-'));
  try {
    fs.cpSync(path.join(FIXTURES, 'ok'), path.join(dir, 'spec'), { recursive: true });
    fs.mkdirSync(path.join(dir, 'specs', 'p'), { recursive: true });
    fs.writeFileSync(path.join(dir, 'specs', 'p', 'project.jsonc'), '{ "spec": "../../spec/spec.jsonc" }\n');
    const ws = createWorkspace(path.join(dir, 'specs'));
    const data = await ws.read('p');
    assert.equal(JSON.parse(data.spec.text).claims.length, 3);
    const edited = data.spec.text.replace('{"id":"r-1","kind":"requirement"}', '{"id":"r-1","kind":"requirement","statement":"y"}');
    const w = await ws.write('p', 'spec', edited, data.spec.hash);
    assert.equal(w.ok, true);
    assert.match(fs.readFileSync(path.join(dir, 'spec', 'b.jsonc'), 'utf8'), /"statement":"y"/);
    assert.doesNotMatch(fs.readFileSync(path.join(dir, 'spec', 'a.jsonc'), 'utf8'), /"statement":"y"/);
    // The manifest itself is untouched, and a stale base is a conflict.
    assert.equal((await ws.write('p', 'spec', edited, data.spec.hash)).conflict, true);
    fs.writeFileSync(path.join(dir, 'spec', 'spec.jsonc'), '{ "specParts": ["a.jsonc", "nope.jsonc"] }\n');
    await assert.rejects(ws.read('p'), (e) => e.code === 'spec.invalid' && /nope\.jsonc/.test(e.message));
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
});

test('a production build bundles the self-specification resolved and the shipped application derives the CLI model from it', async () => {
  const { spawnSync } = await import('node:child_process');
  const { exegraLinkedSpecs } = await import('../../tools/vite-plugin-exegra.js');
  const { Project } = await import('../../src/core/project.js');
  const { deriveModel } = await import('../../src/core/abstraction.js');
  const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
  const specsDir = path.join(root, 'specs');
  // The plugin as vite build runs it: the virtual module of bundled specifications.
  const plugin = exegraLinkedSpecs({ specsDir });
  plugin.configResolved({ command: 'build' });
  const code = /** @type {string} */ (await plugin.load(/** @type {string} */ (plugin.resolveId('virtual:exegra-linked-specs'))));
  const linked = JSON.parse(code.replace(/^export default /, '').replace(/;\s*$/, ''));
  assert.equal(typeof linked.exegra, 'string', 'the manifest self-specification is bundled resolved');
  assert.ok(!linked.exegra.includes('"specParts"'), 'the bundled text is the assembled specification, not the manifest');
  // The shipped session builds its Project from that text and the bundled fact file (src/app/session.js, SHIPPED and SHIPPED_FACTS).
  const extracted = JSON.parse(fs.readFileSync(path.join(specsDir, 'exegra', 'extracted', 'facts.json'), 'utf8'));
  const shipped = new Project({ name: 'exegra', specText: linked.exegra, extracted });
  assert.equal(shipped.errorCount, 0);
  const cli = (/** @type {string[]} */ args) => JSON.parse(spawnSync(process.execPath, ['cli/exegra.js', ...args, '--project', 'exegra'], { cwd: root, encoding: 'utf8', maxBuffer: 64 * 1024 * 1024 }).stdout);
  const derived = cli(['derive', '--cut', 'l1']);
  assert.equal(shipped.semanticHash, derived.semanticHash, 'the shipped model has the semantic hash the command line reports');
  const d = /** @type {any} */ (deriveModel(/** @type {any} */ (shipped.model), 'l1'));
  assert.deepEqual(d.interactions.map((/** @type {any} */ i) => [i.key, i.witnesses]), derived.result.interactions.map((/** @type {any} */ i) => [i.key, i.witnesses]), 'and derives the same interactions at L1, the extracted imports included');
  assert.ok(d.interactions.some((/** @type {any} */ i) => i.kind === 'imports'));
});
