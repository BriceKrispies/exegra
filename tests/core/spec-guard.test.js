// The PreToolUse guard (tools/spec-guard.js): refused and allowed calls, in process and as the hook script.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { decide } from '../../tools/spec-guard.js';

const REPO = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const GUARD = path.join(REPO, 'tools', 'spec-guard.js');
const SPEC = path.join(REPO, 'specs', 'exegra', 'spec.jsonc');

/** A repository root holding a plain spec and a manifest spec with two parts. */
function fakeRepo() {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-guard-'));
  fs.mkdirSync(path.join(root, 'specs', 'plain'), { recursive: true });
  fs.mkdirSync(path.join(root, 'specs', 'split'), { recursive: true });
  fs.writeFileSync(path.join(root, 'specs', 'plain', 'spec.jsonc'), '// header\n{}\n');
  fs.writeFileSync(path.join(root, 'specs', 'split', 'spec.jsonc'), '{ "specParts": ["intent.jsonc", "boundary.jsonc"] }\n');
  fs.writeFileSync(path.join(root, 'specs', 'split', 'intent.jsonc'), '{}\n');
  fs.writeFileSync(path.join(root, 'specs', 'split', 'boundary.jsonc'), '{}\n');
  return root;
}

const call = (tool_name, tool_input, root) => decide({ tool_name, tool_input }, { root });
const withRepo = (body) => {
  const root = fakeRepo();
  try { body(root); } finally { fs.rmSync(root, { recursive: true, force: true }); }
};

// Refused calls, including manifest parts and shell readers.
// @evidence guard-refuses-direct-spec-access
test('Read Edit Write and MultiEdit of a spec file are refused with the replacement commands', () => withRepo((root) => {
  const f = path.join(root, 'specs', 'plain', 'spec.jsonc');
  for (const tool of ['Read', 'Edit', 'Write', 'MultiEdit']) {
    const v = call(tool, { file_path: f }, root);
    assert.equal(v.allow, false, tool);
    for (const word of ['get', 'find', 'refs', 'apply', '--dry-run']) assert.ok(v.reason.includes(word), `${tool}: ${word}`);
  }
  assert.equal(call('Read', { file_path: f.replace(/\//g, '\\') }, root).allow, false);
}));

test('the part files of a manifest spec are guarded too', () => withRepo((root) => {
  for (const part of ['spec.jsonc', 'intent.jsonc', 'boundary.jsonc']) {
    assert.equal(call('Edit', { file_path: path.join(root, 'specs', 'split', part) }, root).allow, false, part);
  }
}));

test('a Read of the header (limit <= 60 from the top) is allowed; a longer or later one is not', () => withRepo((root) => {
  const file_path = path.join(root, 'specs', 'plain', 'spec.jsonc');
  assert.equal(call('Read', { file_path, limit: 40 }, root).allow, true);
  assert.equal(call('Read', { file_path, offset: 1, limit: 60 }, root).allow, true);
  assert.equal(call('Read', { file_path, limit: 400 }, root).allow, false);
  assert.equal(call('Read', { file_path, offset: 500, limit: 20 }, root).allow, false);
}));

test('other files are unaffected', () => withRepo((root) => {
  for (const tool of ['Read', 'Edit', 'Write']) {
    assert.equal(call(tool, { file_path: path.join(root, 'AGENTS.md') }, root).allow, true);
    assert.equal(call(tool, { file_path: path.join(root, 'specs', 'plain', 'notes.md') }, root).allow, true);
  }
}));

test('Grep is refused only when it targets a spec explicitly', () => withRepo((root) => {
  assert.equal(call('Grep', { pattern: 'x', path: path.join(root, 'specs', 'plain', 'spec.jsonc') }, root).allow, false);
  assert.equal(call('Grep', { pattern: 'x', path: path.join(root, 'specs', 'plain') }, root).allow, false);
  assert.equal(call('Grep', { pattern: 'x', glob: '**/spec.jsonc' }, root).allow, false);
  assert.equal(call('Grep', { pattern: 'x' }, root).allow, true);
  assert.equal(call('Grep', { pattern: 'x', path: path.join(root, 'src') }, root).allow, true);
  assert.equal(call('Grep', { pattern: 'x', glob: '*.js' }, root).allow, true);
}));

test('shell commands that print or edit a spec are refused; the CLI and jsonc-parser scripts are allowed', () => withRepo((root) => {
  const bash = (command) => call('Bash', { command }, root).allow;
  for (const c of [
    'cat specs/plain/spec.jsonc', 'type specs\\plain\\spec.jsonc', 'Get-Content specs/plain/spec.jsonc', "sed -n '1,50p' specs/plain/spec.jsonc",
    'head -n 20 specs/plain/spec.jsonc', 'tail specs/plain/spec.jsonc', 'less specs/plain/spec.jsonc', 'grep claim specs/plain/spec.jsonc',
    "sed -i 's/a/b/' specs/plain/spec.jsonc", 'cat specs/split/intent.jsonc', 'echo x > specs/plain/spec.jsonc',
  ]) assert.equal(bash(c), false, c);
  for (const c of [
    'node cli/exegra.js get --project plain x', 'node cli/exegra.js apply --project plain --file ops.json --dry-run',
    "node -e \"require('jsonc-parser').parse(require('fs').readFileSync('specs/plain/spec.jsonc','utf8'))\"",
    'ls specs', 'git status', 'cat AGENTS.md', 'grep -n specParts tools/spec-manifest.js',
  ]) assert.equal(bash(c), true, c);
}));

// Allowed calls and the exit codes of the hook script.
// @evidence guard-leaves-other-calls-alone
test('the hook script exits 2 with the reason on stderr to refuse and 0 silently to allow', () => {
  const run = (payload) => spawnSync(process.execPath, [GUARD], { input: JSON.stringify(payload), encoding: 'utf8', cwd: REPO });
  const refused = run({ tool_name: 'Read', tool_input: { file_path: SPEC } });
  assert.equal(refused.status, 2);
  assert.match(refused.stderr, /exegra\.js get/);
  assert.equal(refused.stdout, '');
  const allowed = run({ tool_name: 'Read', tool_input: { file_path: path.join(REPO, 'AGENTS.md') } });
  assert.equal(allowed.status, 0);
  assert.equal(allowed.stderr, '');
  assert.equal(run({ tool_name: 'Read', tool_input: { file_path: SPEC, limit: 30 } }).status, 0);
  assert.equal(spawnSync(process.execPath, [GUARD], { input: 'not json', encoding: 'utf8' }).status, 0);
});

test('the repository wires the guard under hooks.PreToolUse', () => {
  const settings = JSON.parse(fs.readFileSync(path.join(REPO, '.claude', 'settings.json'), 'utf8'));
  const entry = settings.hooks.PreToolUse.find((h) => h.hooks.some((x) => /spec-guard\.js/.test(x.command)));
  assert.ok(entry);
  for (const tool of ['Read', 'Edit', 'Write', 'MultiEdit', 'Grep', 'Glob', 'Bash']) assert.ok(entry.matcher.split('|').includes(tool), tool);
});
