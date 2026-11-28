// Exegra's own specification kept as a manifest of part files (WG-5704): the split, the placement of new entities,
// undo across parts, the guard on the part directory, and the source locations the commands print.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { parse as parseJsonc } from 'jsonc-parser';
import { analyzeSpec } from '../../src/core/analyze.js';
import { semanticHash } from '../../src/core/hash.js';
import { Project } from '../../src/core/project.js';
import { assembleParts, planWrite, readManifest, resolveSpecText } from '../../tools/spec-manifest.js';
import { countComments, splitSpec } from '../../tools/split-spec.js';
import { decide, partDirs } from '../../tools/spec-guard.js';
import { stampedFiles } from '../../tools/tree-stamp.js';
import { createWorkspace } from '../../tools/workspace.js';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const MANIFEST = path.join(ROOT, 'specs', 'exegra', 'spec.jsonc');
const PART_LIMIT = 120 * 1024;

const manifestText = fs.readFileSync(MANIFEST, 'utf8');
const resolved = resolveSpecText(MANIFEST, manifestText);
const hashOf = (/** @type {string} */ text) => semanticHash(/** @type {any} */ (analyzeSpec(text).model));

/** The resolved specification after `changed` part files are written over it, held in memory. */
function written(/** @type {import('../../tools/spec-manifest.js').ResolvedSpec} */ before, /** @type {{file: string, text: string}[]} */ changed) {
  const overlay = new Map(changed.map((c) => [c.file, c.text]));
  return resolveSpecText(MANIFEST, manifestText, (p) => overlay.get(p) ?? before.parts.find((x) => x.file === p)?.text ?? fs.readFileSync(p, 'utf8'));
}

/**
 * The text the parts resolve to and the transaction's text hold the same document. They need not be the same string: a new
 * entity is last in its section in the transaction's text, but in the part it is written to it stands after that part's own
 * entities, so the concatenation of the parts puts it elsewhere in the section. The semantic hash does not depend on that order.
 */
function sameDocument(/** @type {string} */ actual, /** @type {string} */ expected) {
  const sorted = (/** @type {any} */ d) => Object.fromEntries(Object.keys(d).sort().map((k) => [k, Array.isArray(d[k]) ? [...d[k]].sort((a, b) => String(a.id).localeCompare(String(b.id))) : d[k]]));
  assert.deepEqual(sorted(parseJsonc(actual)), sorted(parseJsonc(expected)));
  assert.equal(hashOf(actual), hashOf(expected));
}

test('the self-specification is a manifest of part files none over 120 KB all listed and none stray', () => {
  assert.equal(resolved.manifest, true);
  const { parts } = readManifest(manifestText, MANIFEST);
  assert.ok(parts.length >= 20);
  for (const p of resolved.parts) assert.ok(Buffer.byteLength(p.text.split(String.fromCharCode(13)).join("")) <= PART_LIMIT, `${path.basename(p.file)} is ${Buffer.byteLength(p.text)} bytes`);
  const listed = new Set(parts.map((p) => path.resolve(path.dirname(MANIFEST), p)));
  for (const f of fs.readdirSync(path.join(path.dirname(MANIFEST), 'parts'))) assert.ok(listed.has(path.join(path.dirname(MANIFEST), 'parts', f)), `${f} is in parts/ but not listed`);
  assert.ok(Buffer.byteLength(manifestText) < 32 * 1024, 'the manifest is small');
});

test('splitting a specification keeps its semantic hash and its content and every comment of an entity', () => {
  const text = resolved.text;
  const { manifest, parts, table } = splitSpec(text);
  assert.ok(parts.size >= 20);
  const files = [...parts].map(([file, t]) => ({ file, text: t }));
  const again = assembleParts(files).text;
  assert.equal(hashOf(again), hashOf(text), 'the semantic hash is the same');
  const sorted = (/** @type {any} */ d) => Object.fromEntries(Object.keys(d).sort().map((k) => [k, Array.isArray(d[k]) ? [...d[k]].sort((a, b) => String(a.id).localeCompare(String(b.id))) : d[k]]));
  assert.deepEqual(sorted(parseJsonc(again)), sorted(parseJsonc(text)), 'the document is the same');
  // Every comment of the text is in a part; each part and the manifest add one description (the manifest three lines).
  const total = countComments(manifest) + files.reduce((n, f) => n + countComments(f.text), 0);
  assert.equal(total, countComments(text) + parts.size + 3);
  assert.ok(Object.keys(table).length >= 20);
});

test('apply places a new component and claim and evidence and relationship in the part its placement names and undo and redo restore the text exactly', () => {
  const project = new Project({ name: 'exegra', specText: resolved.text, layoutText: null });
  const hashBefore = project.semanticHash;
  const result = project.apply([
    { type: 'CreateEntity', kind: 'component', data: { id: 'zz-t-tool', name: 'T tool', parent: 'tooling', category: 'logical', runsIn: 'node', purpose: 'p', responsibilities: ['r'] } },
    { type: 'CreateEntity', kind: 'component', data: { id: 'zz-t-core', name: 'T core', parent: 'semantic-core', category: 'logical', runsIn: 'both', purpose: 'p', responsibilities: ['r'] } },
    { type: 'CreateEntity', kind: 'component', data: { id: 'zz-t-leaf', name: 'T leaf', parent: 'zz-t-core', category: 'logical', runsIn: 'both', purpose: 'p', responsibilities: ['r'] } },
    { type: 'CreateRelationship', kind: 'invokes', from: 'zz-t-tool', to: 'agent-cli', id: 'zz-t-rel', description: 'd' },
    { type: 'AddClaim', data: { id: 'zz-t-claim', kind: 'structural', statement: 's', rationale: 'r', subjects: ['zz-t-leaf', 'zz-t-tool'], evaluate: { method: 'external-evidence' } } },
    { type: 'CreateEntity', kind: 'evidence', data: { id: 'zz-t-evidence', claim: 'zz-t-claim', kind: 'test', ref: 'tests/core/spec-split.test.js#x', description: 'd' } },
    { type: 'SetProperty', id: 'parser', property: 'purpose', value: 'Edited in place.' },
  ]);
  assert.equal(result.ok, true, JSON.stringify(result));
  const edited = project.specText;
  const changed = planWrite(resolved, edited);
  const where = (/** @type {string} */ id) => changed.filter((c) => c.text.includes(`"id": "${id}"`)).map((c) => path.basename(c.file));
  assert.deepEqual(where('zz-t-tool'), ['structure-tooling.jsonc']);
  assert.deepEqual(where('zz-t-rel'), ['structure-tooling.jsonc']);
  assert.deepEqual(where('zz-t-core'), ['structure-core-model.jsonc']);
  assert.deepEqual(where('zz-t-leaf'), ['structure-core-model.jsonc'], 'a child of a component created in the same transaction follows it');
  assert.deepEqual(where('zz-t-claim'), ['claims-core-derivation.jsonc']);
  assert.deepEqual(where('zz-t-evidence'), ['claims-core-derivation.jsonc'], 'evidence goes where its claim went');
  assert.deepEqual(changed.map((c) => path.basename(c.file)).sort(), ['claims-core-derivation.jsonc', 'structure-core-model.jsonc', 'structure-tooling.jsonc']);
  // The edit of an existing component stays in the part that holds it, and the comments between entities are kept.
  const model = changed.find((c) => path.basename(c.file) === 'structure-core-model.jsonc');
  assert.match(model?.text ?? '', /Edited in place\./);
  const original = resolved.parts.find((p) => path.basename(p.file) === 'structure-core-model.jsonc');
  assert.equal(countComments(model?.text ?? ''), countComments(original?.text ?? ''));
  // The parts, written back, resolve to the edited text.
  const afterWrite = written(resolved, changed);
  sameDocument(afterWrite.text, edited);
  assert.equal(hashOf(afterWrite.text), project.semanticHash);
  // Undo gives the previous text, and writing it restores every part byte for byte.
  assert.ok(project.undo());
  assert.equal(project.specText, resolved.text);
  assert.equal(project.semanticHash, hashBefore);
  const reverted = planWrite(afterWrite, project.specText);
  const afterUndo = written(afterWrite, reverted);
  for (const p of afterUndo.parts) assert.equal(p.text, resolved.parts.find((x) => x.file === p.file)?.text, path.basename(p.file));
  // Redo gives the edit again.
  assert.ok(project.redo());
  assert.equal(project.specText, edited);
  sameDocument(written(afterUndo, planWrite(afterUndo, project.specText)).text, edited);
});

test('a new entity with no rule goes to its default part', () => {
  const project = new Project({ name: 'exegra', specText: resolved.text, layoutText: null });
  const result = project.apply([
    { type: 'CreateEntity', kind: 'component', data: { id: 'zz-t-top', name: 'T top', category: 'logical', runsIn: 'node', purpose: 'p', responsibilities: ['r'] } },
    { type: 'AddClaim', data: { id: 'zz-t-claim2', kind: 'structural', statement: 's', rationale: 'r', subjects: ['zz-t-top'], evaluate: { method: 'external-evidence' } } },
  ]);
  assert.equal(result.ok, true, JSON.stringify(result));
  const changed = planWrite(resolved, project.specText);
  const where = (/** @type {string} */ id) => changed.filter((c) => c.text.includes(`"id": "${id}"`)).map((c) => path.basename(c.file));
  assert.deepEqual(where('zz-t-top'), ['structure-top.jsonc']);
  assert.deepEqual(where('zz-t-claim2'), ['claims-app-ui.jsonc']);
});

test('the workspace writes an apply of the self-specification to part files and a stale base is refused', async () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-split-'));
  try {
    const base = path.dirname(MANIFEST);
    fs.mkdirSync(path.join(dir, 'specs', 'exegra'), { recursive: true });
    fs.cpSync(path.join(base, 'parts'), path.join(dir, 'specs', 'exegra', 'parts'), { recursive: true });
    fs.copyFileSync(MANIFEST, path.join(dir, 'specs', 'exegra', 'spec.jsonc'));
    const ws = createWorkspace(path.join(dir, 'specs'));
    const data = await ws.read('exegra');
    assert.equal(data.spec.text, resolved.text);
    const project = new Project({ name: 'exegra', specText: data.spec.text, layoutText: null });
    assert.equal(project.apply({ type: 'SetProperty', id: 'parser', property: 'purpose', value: 'Edited.' }).ok, true);
    const w = await ws.write('exegra', 'spec', project.specText, data.spec.hash);
    assert.equal(w.ok, true);
    assert.equal(fs.readFileSync(path.join(dir, 'specs', 'exegra', 'spec.jsonc'), 'utf8'), manifestText, 'the manifest is untouched');
    const touched = resolved.parts.filter((p) => fs.readFileSync(path.join(dir, 'specs', 'exegra', 'parts', path.basename(p.file)), 'utf8') !== p.text);
    assert.deepEqual(touched.map((p) => path.basename(p.file)), ['structure-core-model.jsonc']);
    assert.equal((await ws.write('exegra', 'spec', project.specText, data.spec.hash)).conflict, true);
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
});

test('an entity is located in the part file and the line that hold it', () => {
  const offset = resolved.text.indexOf('"id": "transactions"');
  assert.ok(offset > 0);
  const at = resolved.locate(offset);
  assert.ok(at);
  assert.equal(path.basename(at.file), 'structure-core-model.jsonc');
  const line = fs.readFileSync(at.file, 'utf8').split('\n')[at.line - 1];
  assert.match(line, /^\s*"id": "transactions"/);
  assert.equal(resolveSpecText(path.join(ROOT, 'specs', 'benchmark', 'spec.jsonc'), '{}').locate(1), null);
});

test('the guard refuses the part files and the directory that holds them and leaves the command line open', () => {
  assert.deepEqual(partDirs(ROOT), ['specs/exegra/parts']);
  const call = (/** @type {string} */ tool_name, /** @type {any} */ tool_input) => decide({ tool_name, tool_input }, { root: ROOT }).allow;
  const part = path.join(ROOT, 'specs', 'exegra', 'parts', 'claims-app-ui.jsonc');
  assert.equal(call('Read', { file_path: part }), false);
  assert.equal(call('Edit', { file_path: part }), false);
  assert.equal(call('Write', { file_path: part }), false);
  assert.equal(call('Read', { file_path: part, limit: 40 }), true, 'the header of a part may be read');
  assert.equal(call('Grep', { pattern: 'x', path: path.join(ROOT, 'specs', 'exegra', 'parts') }), false);
  assert.equal(call('Grep', { pattern: 'x', path: 'specs/exegra/parts/' }), false);
  assert.equal(call('Bash', { command: 'cat specs/exegra/parts/contracts.jsonc' }), false);
  assert.equal(call('Bash', { command: 'grep -rn foo specs/exegra/parts' }), false);
  assert.equal(call('Bash', { command: 'node cli/exegra.js get --project exegra parser' }), true);
  assert.equal(call('Grep', { pattern: 'x', path: path.join(ROOT, 'src') }), true);
});

test('the tree stamp covers the part files', () => {
  const files = stampedFiles(ROOT);
  for (const p of resolved.parts) assert.ok(files.includes(`specs/exegra/parts/${path.basename(p.file)}`), path.basename(p.file));
});
