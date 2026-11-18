import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { createWorkspace, hashText } from '../../tools/workspace.js';

const SPEC = '{\n  "system": { "name": "Demo" }\n}\n';

/** Runs fn against a fresh specs directory holding one project, "demo". */
async function withWorkspace(fn) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'exegra-ws-'));
  try {
    await fs.mkdir(path.join(dir, 'demo'), { recursive: true });
    await fs.writeFile(path.join(dir, 'demo', 'spec.jsonc'), SPEC, 'utf8');
    return await fn(createWorkspace(dir), dir);
  } finally {
    await fs.rm(dir, { recursive: true, force: true });
  }
}

test('invalid project names are rejected', () =>
  withWorkspace(async (ws) => {
    for (const name of ['', 'Demo', '../demo', 'a/b', 'a\\b', '-demo', '.hidden', 'de mo', 'x'.repeat(65)]) {
      await assert.rejects(ws.read(name), { code: 'name.invalid' }, `read(${JSON.stringify(name)})`);
      assert.throws(() => ws.resolve(name, 'spec.jsonc'), { code: 'name.invalid' });
    }
  }));

test('resolve rejects paths that leave the project', () =>
  withWorkspace(async (ws, dir) => {
    assert.throws(() => ws.resolve('demo', '../x'), { code: 'path.unsafe' });
    assert.throws(() => ws.resolve('demo', 'a/../../x'), { code: 'path.unsafe' });
    assert.throws(() => ws.resolve('demo', '..'), { code: 'path.unsafe' });
    assert.throws(() => ws.resolve('demo', path.join(dir, 'outside.txt')), { code: 'path.unsafe' });
    assert.equal(
      ws.resolve('demo', 'evidence/results.json'),
      path.join(dir, 'demo', 'evidence', 'results.json'),
    );
  }));

test('write with the current baseHash succeeds and changes the hash', () =>
  withWorkspace(async (ws) => {
    const { spec } = await ws.read('demo');
    const next = SPEC.replace('Demo', 'Demo 2');
    const result = await ws.write('demo', 'spec', next, spec.hash);
    assert.equal(result.ok, true);
    assert.equal(result.hash, hashText(next));
    assert.notEqual(result.hash, spec.hash);
    assert.equal((await ws.read('demo')).spec.text, next);
  }));

test('write with a stale baseHash conflicts and leaves the file untouched', () =>
  withWorkspace(async (ws) => {
    const first = await ws.read('demo');
    const text1 = SPEC.replace('Demo', 'One');
    const saved = await ws.write('demo', 'spec', text1, first.spec.hash);
    assert.equal(saved.ok, true);

    const result = await ws.write('demo', 'spec', 'stale write', first.spec.hash);
    assert.equal(result.ok, false);
    assert.equal(result.conflict, true);
    assert.equal(result.current.text, text1);
    assert.equal(result.current.hash, saved.hash);
    assert.equal((await ws.read('demo')).spec.text, text1);
  }));

test('creating a new file with baseHash null', () =>
  withWorkspace(async (ws) => {
    const layout = '{ "positions": {} }\n';
    const created = await ws.write('demo', 'layout', layout, null);
    assert.equal(created.ok, true);
    assert.equal((await ws.read('demo')).layout.text, layout);

    const again = await ws.write('demo', 'layout', '{}\n', null);
    assert.equal(again.ok, false);
    assert.equal(again.conflict, true);
    assert.equal(again.current.hash, hashText(layout));
  }));

test('write rejects files other than spec and layout', () =>
  withWorkspace(async (ws) => {
    await assert.rejects(ws.write('demo', 'recorded', '{}', null), { code: 'file.unknown' });
    await assert.rejects(ws.write('demo', '../spec', '{}', null), { code: 'file.unknown' });
  }));

test('writeGenerated rejects paths outside generated/ and other extensions', () =>
  withWorkspace(async (ws, dir) => {
    for (const bad of ['../x.json', 'sub/../../x.json', '/abs/x.json', 'notes.txt', 'x.json.exe']) {
      await assert.rejects(ws.writeGenerated('demo', { [bad]: '{}\n' }), { code: 'path.unsafe' }, bad);
    }
    // One bad key rejects the whole call: nothing is written.
    await assert.rejects(
      ws.writeGenerated('demo', { 'ok.json': '{}\n', '../bad.md': '# bad\n' }),
      { code: 'path.unsafe' },
    );
    await assert.rejects(fs.access(path.join(dir, 'demo', 'generated', 'ok.json')));

    const files = { 'ok.json': '{}\n', 'sub/note.md': '# Note\n' };
    const first = await ws.writeGenerated('demo', files);
    assert.deepEqual(first, { ok: true, written: ['ok.json', 'sub/note.md'] });
    const second = await ws.writeGenerated('demo', files);
    assert.deepEqual(second.written, []);
  }));

test('export then import into a new name round-trips the texts', () =>
  withWorkspace(async (ws) => {
    const layout = '{ "positions": { "a": [1, 2] } }\n';
    const recorded = { results: { e1: { outcome: 'pass' } } };
    await ws.write('demo', 'layout', layout, null);
    await ws.writeRecorded('demo', recorded);

    const bundle = await ws.exportProject('demo');
    assert.equal(bundle.format, 'exegra-project');
    assert.equal(bundle.version, 1);
    assert.equal(bundle.name, 'demo');

    assert.deepEqual(await ws.importProject('copy', bundle), { ok: true });
    const copy = await ws.read('copy');
    assert.equal(copy.spec.text, SPEC);
    assert.equal(copy.layout.text, layout);
    assert.deepEqual(copy.recorded, recorded);
  }));

test('import rejects unknown file keys and writes nothing', () =>
  withWorkspace(async (ws, dir) => {
    const bundle = {
      format: 'exegra-project',
      version: 1,
      name: 'evil',
      files: { 'spec.jsonc': SPEC, 'secrets.txt': 'x' },
    };
    const result = await ws.importProject('evil', bundle);
    assert.equal(result.ok, false);
    assert.equal(typeof result.error, 'string');
    await assert.rejects(fs.access(path.join(dir, 'evil')));
  }));

test('the journal gains one line per successful write', () =>
  withWorkspace(async (ws, dir) => {
    const journal = path.join(dir, 'demo', '.history', 'journal.jsonl');
    await assert.rejects(fs.access(journal));

    const base = (await ws.read('demo')).spec.hash;
    const first = await ws.write('demo', 'spec', SPEC.replace('Demo', 'A'), base, {
      label: 'first',
      origin: 'test',
    });
    const second = await ws.write('demo', 'spec', SPEC.replace('Demo', 'B'), first.hash);
    const conflict = await ws.write('demo', 'spec', 'stale', base);
    assert.equal(conflict.conflict, true);

    const lines = (await fs.readFile(journal, 'utf8')).split('\n').filter(Boolean).map((line) => JSON.parse(line));
    assert.equal(lines.length, 2);
    assert.deepEqual(lines.map((line) => line.seq), [1, 2]);
    assert.equal(lines[0].label, 'first');
    assert.equal(lines[0].origin, 'test');
    assert.equal(lines[0].hash, first.hash);
    assert.equal(lines[1].baseHash, first.hash);
    assert.equal(lines[1].hash, second.hash);
  }));

// ---- a project whose specification lives in another repository ---------------------

/** A specs directory with project "linked" whose project.jsonc names ../../other/spec.jsonc. */
async function withLinked(fn) {
  const top = await fs.mkdtemp(path.join(os.tmpdir(), 'exegra-link-'));
  const specs = path.join(top, 'exegra', 'specs');
  const external = path.join(top, 'other', 'spec.jsonc');
  try {
    await fs.mkdir(path.join(specs, 'linked'), { recursive: true });
    await fs.mkdir(path.dirname(external), { recursive: true });
    await fs.writeFile(external, SPEC, 'utf8');
    await fs.writeFile(path.join(specs, 'linked', 'project.jsonc'), '// the specification lives in its own repository\n{ "spec": "../../../other/spec.jsonc" }\n', 'utf8');
    return await fn(createWorkspace(specs), { specs, external });
  } finally {
    await fs.rm(top, { recursive: true, force: true });
  }
}

test('a linked project reads, lists and writes the file its project.jsonc names', () =>
  withLinked(async (ws, { specs, external }) => {
    assert.equal(ws.specFile('linked'), external);
    assert.deepEqual(await ws.listProjects(), [{ name: 'linked', title: 'Demo' }]);
    const r = await ws.read('linked');
    assert.equal(r.spec.text, SPEC);
    assert.equal(r.spec.path, '../other/spec.jsonc');
    const next = SPEC.replace('Demo', 'Linked');
    assert.equal((await ws.write('linked', 'spec', next, r.spec.hash)).ok, true);
    assert.equal(await fs.readFile(external, 'utf8'), next, 'the write lands in the other repository');
    assert.equal((await ws.write('linked', 'spec', SPEC, r.spec.hash)).conflict, true, 'a stale base hash still conflicts');
    // Layout and the journal stay in the project directory.
    assert.equal((await ws.write('linked', 'layout', '{}', null)).ok, true);
    await fs.access(path.join(specs, 'linked', 'layout.jsonc'));
    await fs.access(path.join(specs, 'linked', '.history', 'journal.jsonl'));
    await assert.rejects(fs.access(path.join(specs, 'linked', 'spec.jsonc')), 'no copy appears in specs/');
    const bundle = await ws.exportProject('linked');
    assert.equal(bundle.files['spec.jsonc'], next);
  }));

test('a project.jsonc that is malformed, or sits beside a spec.jsonc, is refused', () =>
  withLinked(async (ws, { specs }) => {
    await fs.writeFile(path.join(specs, 'linked', 'spec.jsonc'), SPEC, 'utf8');
    await assert.rejects(ws.read('linked'), { code: 'project.invalid' });
    await fs.rm(path.join(specs, 'linked', 'spec.jsonc'));
    for (const bad of ['{}', '{ "spec": "C:/abs/spec.jsonc" }', '{ "spec": "../../other/spec.json" }', 'not json']) {
      await fs.writeFile(path.join(specs, 'linked', 'project.jsonc'), bad, 'utf8');
      await assert.rejects(ws.read('linked'), { code: 'project.invalid' }, bad);
    }
  }));

test('watching a linked project reports a change to the file in the other repository', () =>
  withLinked(async (ws, { external }) => {
    const changes = [];
    const stop = ws.watch('linked', (c) => changes.push(c));
    try {
      await new Promise((r) => setTimeout(r, 50));
      await fs.writeFile(external, SPEC.replace('Demo', 'Changed'), 'utf8');
      for (let i = 0; i < 40 && !changes.length; i++) await new Promise((r) => setTimeout(r, 50));
      assert.equal(changes[0]?.file, 'spec');
      assert.equal(changes[0]?.hash, hashText(SPEC.replace('Demo', 'Changed')));
    } finally {
      stop();
    }
  }));

test('a journal line that cannot be appended is reported and the file write still stands', () =>
  withWorkspace(async (ws, dir) => {
    // A directory at the journal path makes the append fail after the file was replaced.
    await fs.mkdir(path.join(dir, 'demo', '.history', 'journal.jsonl'), { recursive: true });
    const text = '{\n  "system": { "name": "Changed" }\n}\n';
    const res = await ws.write('demo', 'spec', text, hashText(SPEC), { origin: 'cli' });
    assert.equal(res.ok, true);
    assert.equal(res.hash, hashText(text));
    assert.equal(res.journal.written, false);
    assert.match(res.journal.message, /^The journal line was not written: /);
    assert.equal((await ws.read('demo')).spec.text, text);
  }));

test('a write whose journal line is appended reports the sequence number', () =>
  withWorkspace(async (ws) => {
    const first = await ws.write('demo', 'spec', SPEC, hashText(SPEC), { origin: 'cli' });
    assert.deepEqual(first.journal, { written: true, seq: 1 });
  }));
