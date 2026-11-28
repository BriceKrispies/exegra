// get, find and refs (cli/read-commands.js) over a small fixture specification.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { runCommand } from '../../cli/commands.js';
import { Project } from '../../src/core/project.js';

const SPECS = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../fixtures/front-door');
const opts = { specs: SPECS, project: 'fixture' };
const ids = (out) => out.result.entities.map((e) => e.id);

// get returns the declaration and both reference lists.
// @evidence cli-get-prints-entities-with-references
test('get prints the named entities with declaration and references both ways', async () => {
  const out = await runCommand('get', ['server', 'client-calls-server'], opts);
  assert.equal(out.ok, true);
  assert.deepEqual(out.result.map((e) => e.id), ['server', 'client-calls-server']);
  const [server, rel] = out.result;
  assert.equal(server.kind, 'component');
  assert.equal(server.data.name, 'Server');
  assert.equal(typeof server.source.line, 'number');
  assert.deepEqual(server.referencedBy.map((r) => [r.from, r.path]).sort(), [['client-calls-server', 'to'], ['server-reads-cache', 'from']]);
  assert.deepEqual(rel.refersTo.map((r) => [r.path, r.target]).sort(), [['from', 'client'], ['to', 'server']]);
});

test('get of an unknown id or no id fails', async () => {
  assert.equal((await runCommand('get', ['nope'], opts)).error.code, 'entity.unknown');
  assert.equal((await runCommand('get', [], opts)).error.code, 'usage.missing-argument');
});

test('find --kind lists the entities of a kind, without data', async () => {
  const out = await runCommand('find', ['--kind', 'component'], opts);
  assert.deepEqual(ids(out), ['client', 'server', 'cache']);
  assert.equal('data' in out.result.entities[0], false);
  assert.equal(out.result.total, 3);
  assert.equal(out.result.truncated, false);
});

test('find --where matches a property; repeated flags must all hold', async () => {
  assert.deepEqual(ids(await runCommand('find', ['--where', 'kind=reads'], opts)), ['server-reads-cache']);
  assert.deepEqual(ids(await runCommand('find', ['--kind', 'relationship', '--where', 'kind=calls', '--where', 'to=server'], opts)), ['client-calls-server']);
  assert.deepEqual(ids(await runCommand('find', ['--kind', 'relationship', '--where', 'kind=calls', '--where', 'to=cache'], opts)), []);
  assert.equal((await runCommand('find', ['--where', 'novalue'], opts)).error.code, 'usage.invalid-argument');
});

test('find --refers-to and --referenced-by follow references', async () => {
  assert.deepEqual(ids(await runCommand('find', ['--refers-to', 'server'], opts)).sort(), ['client-calls-server', 'server-reads-cache']);
  assert.deepEqual(ids(await runCommand('find', ['--referenced-by', 'server-reads-cache'], opts)).sort(), ['cache', 'server']);
});

test('find --text searches the text of an entity, ignoring case', async () => {
  assert.deepEqual(ids(await runCommand('find', ['--text', 'RECENT ANSWERS'], opts)), ['cache']);
  assert.deepEqual(ids(await runCommand('find', ['--text', 'no such words'], opts)), []);
});

// Each filter is exercised on a fixture specification.
// @evidence cli-find-filters-entities
test('find --fields adds only the requested data fields and --limit truncates', async () => {
  const out = await runCommand('find', ['--kind', 'component', '--fields', 'name,purpose,missing', '--limit', '2'], opts);
  assert.equal(out.result.returned, 2);
  assert.equal(out.result.total, 3);
  assert.equal(out.result.truncated, true);
  assert.deepEqual(Object.keys(out.result.entities[0].fields), ['name', 'purpose', 'missing']);
  assert.equal(out.result.entities[0].fields.name, 'Client');
  assert.equal(out.result.entities[0].fields.missing, null);
  assert.equal((await runCommand('find', ['--limit', '0'], opts)).error.code, 'usage.invalid-argument');
  assert.equal((await runCommand('find', ['--kind', 'nonsense'], opts)).error.code, 'usage.invalid-argument');
});

// Compared with the references of a Project built from the same text.
// @evidence cli-refs-equals-model-refs
test('refs equals what model.refs holds for the entity', async () => {
  const text = fs.readFileSync(path.join(SPECS, 'fixture', 'spec.jsonc'), 'utf8');
  const model = new Project({ name: 'fixture', specText: text, layoutText: null, layers: [] }).model;
  for (const id of ['server', 'client-calls-server', 'cache']) {
    const out = await runCommand('refs', [id], opts);
    assert.equal(out.ok, true);
    assert.deepEqual(out.result.outbound.map((r) => r.target).sort(), model.refs.filter((r) => r.from === id).map((r) => r.target).sort());
    assert.deepEqual(out.result.inbound.map((r) => r.from).sort(), model.refs.filter((r) => r.target === id).map((r) => r.from).sort());
  }
  assert.equal((await runCommand('refs', ['nope'], opts)).error.code, 'entity.unknown');
});
