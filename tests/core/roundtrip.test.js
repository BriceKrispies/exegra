// Bidirectional editing: typed operations are source-preserving text edits, the
// text is the one authority, and both directions resolve to the same semantic
// state. These tests are the executable evidence for the self-specification
// claim "edit-representations-equivalent".
import test from 'node:test';
import assert from 'node:assert/strict';
import { Project } from '../../src/core/project.js';
import { analyzeSpec } from '../../src/core/analyze.js';
import { semanticHash, normalize } from '../../src/core/hash.js';
import { planDelete } from '../../src/core/operations.js';

const SPEC = `{
  // Header comment that must survive every edit.
  "exegra": "0.1",
  "system": { "id": "sys", "name": "Sys" },
  "components": [
    // the group
    { "id": "grp", "name": "Group", "kind": "subsystem", "category": "logical", "purpose": "g" },
    {
      "id": "api",          // trailing comment on the id
      "name": "API",
      "category": "computational",
      "parent": "grp",
      "purpose": "Serves requests."
    },
    { "id": "db", "name": "DB", "category": "storage", "purpose": "Stores." },
    { "id": "cache",   "name": "Cache",   "category": "storage", "purpose": "Caches."   }
  ],
  "relationships": [
    { "id": "api-writes-db", "kind": "writes", "from": "api", "to": "db", "description": "w" },
    { "id": "api-reads-cache", "kind": "reads", "from": "api", "to": "cache", "description": "r" }
  ],
  "claims": [
    { "id": "no-db-to-api", "kind": "structural", "statement": "s", "subjects": ["db", "api"],
      "evaluate": { "method": "no-relationship", "from": "db", "to": ["api"] } }
  ]
}
`;

const fresh = () => new Project({ specText: SPEC });

test('a visual edit (SetProperty) changes exactly one value in the source', () => {
  const p = fresh();
  const r = p.apply({ type: 'SetProperty', id: 'api', property: 'name', value: 'Gateway' });
  assert.equal(r.ok, true);
  assert.equal(r.semanticChanged, true);
  assert.equal(p.specText, SPEC.replace('"name": "API"', '"name": "Gateway"'));
});

test('a source edit produces the expected graph change', () => {
  const p = fresh();
  const text = SPEC.replace('{ "id": "cache",   "name": "Cache",   "category": "storage", "purpose": "Caches."   }',
    '{ "id": "cache",   "name": "Cache",   "category": "storage", "purpose": "Caches."   },\n    { "id": "queue", "name": "Queue", "category": "transport", "purpose": "Queues." }');
  const r = p.apply({ type: 'ReplaceSource', text });
  assert.equal(r.ok, true, r.message);
  assert.equal(p.model?.entities.get('queue')?.data.category, 'transport');
  assert.deepEqual(r.affected, ['queue']);
});

test('the visual and the textual route to the same change yield equal semantic state', () => {
  const viaOps = fresh();
  viaOps.apply([
    { type: 'CreateEntity', kind: 'component', data: { id: 'queue', name: 'Queue', category: 'transport', purpose: 'Queues.' } },
    { type: 'CreateRelationship', kind: 'publishes', from: 'api', to: 'queue', description: 'p' },
    { type: 'SetProperty', id: 'db', property: 'owner', value: 'data-team' },
  ]);
  const viaText = fresh();
  // A human writes the same facts differently: other order, other formatting, comments.
  const text = SPEC
    .replace('{ "id": "db", "name": "DB", "category": "storage", "purpose": "Stores." }', '{ "owner": "data-team", "id": "db", "name": "DB", "category": "storage", "purpose": "Stores." }')
    .replace('"components": [', '"components": [\n    /* new */ { "purpose": "Queues.", "category": "transport", "name": "Queue", "id": "queue" },')
    .replace('"relationships": [', '"relationships": [\n    { "id": "api-publishes-queue", "from": "api", "to": "queue", "kind": "publishes", "description": "p" },');
  const r = viaText.apply({ type: 'ReplaceSource', text });
  assert.equal(r.ok, true, r.message);
  assert.deepEqual(normalize(/** @type {any} */ (viaOps.model)), normalize(/** @type {any} */ (viaText.model)));
  assert.equal(viaOps.semanticHash, viaText.semanticHash);
});

test('comments and unrelated formatting survive create, rename, connect and delete', () => {
  const p = fresh();
  p.apply({ type: 'CreateEntity', kind: 'component', data: { id: 'queue', name: 'Queue', category: 'transport', purpose: 'q' } });
  p.apply({ type: 'CreateRelationship', kind: 'publishes', from: 'api', to: 'queue', description: 'p' });
  p.apply({ type: 'RenameEntity', id: 'db', newId: 'database' });
  p.apply({ type: 'DeleteEntity', id: 'queue', cascade: true });
  for (const fragment of [
    '// Header comment that must survive every edit.',
    '// the group',
    '"id": "api",          // trailing comment on the id',
    '{ "id": "cache",   "name": "Cache",   "category": "storage", "purpose": "Caches."   }',
    '{ "id": "api-reads-cache", "kind": "reads", "from": "api", "to": "cache", "description": "r" }',
  ]) assert.ok(p.specText.includes(fragment), `lost: ${fragment}`);
  // Only the rename remains as a difference from the original text.
  assert.equal(p.specText, SPEC.replaceAll('"db"', '"database"'));
});

test('renaming an id rewrites every reference, including those inside claim evaluations', () => {
  const p = fresh();
  const r = p.apply({ type: 'RenameEntity', id: 'api', newId: 'gateway' });
  assert.equal(r.ok, true, r.message);
  const m = /** @type {any} */ (p.model);
  assert.equal(m.entities.get('api-writes-db').data.from, 'gateway');
  assert.deepEqual(m.entities.get('no-db-to-api').data.subjects, ['db', 'gateway']);
  assert.deepEqual(m.entities.get('no-db-to-api').data.evaluate.to, ['gateway']);
  assert.equal(p.errorCount, 0);
});

test('renaming a behavior rewrites expressions that name it', () => {
  const text = SPEC.replace('"claims": [', `"events": [ { "id": "go", "name": "Go" } ],
  "behaviors": [ { "id": "machine", "name": "M", "subject": "api", "initial": "s0",
    "variables": [ { "name": "done", "type": "boolean", "initial": false } ],
    "states": [ { "id": "s0", "name": "S0" }, { "id": "s1", "name": "S1" } ],
    "transitions": [ { "id": "t1", "from": "s0", "to": "s1", "on": "go", "guard": "machine.done == false", "effects": [ { "set": "done", "to": true } ] } ] } ],
  "scenarios": [ { "id": "sc", "name": "Sc", "behaviors": ["machine"], "steps": [ { "at": 0, "event": "go" } ] } ],
  "claims": [
    { "id": "inv", "kind": "invariant", "statement": "s", "evaluate": { "method": "state-invariant", "scenarios": ["sc"], "expr": "machine.state == 's1' => machine.done" } },`);
  const p = new Project({ specText: text });
  assert.equal(p.errorCount, 0, JSON.stringify(p.diagnostics));
  const r = p.apply({ type: 'RenameEntity', id: 'machine', newId: 'api-machine' });
  assert.equal(r.ok, true, r.message);
  const m = /** @type {any} */ (p.model);
  assert.equal(m.entities.get('t1').data.guard, 'api-machine.done == false');
  assert.equal(m.entities.get('inv').data.evaluate.expr, "api-machine.state == 's1' => api-machine.done");
});

test('deleting a referenced entity is refused with the dependents; cascade repairs them', () => {
  const p = fresh();
  const refused = p.apply({ type: 'DeleteEntity', id: 'db' });
  assert.equal(refused.ok, false);
  assert.equal(refused.code, 'delete.referenced');
  assert.deepEqual([...new Set(refused.diagnostics.map((d) => d.entityId))].sort(), ['api-writes-db', 'no-db-to-api']);
  assert.equal(p.specText, SPEC, 'a refused transaction changes nothing');

  const plan = planDelete(/** @type {any} */ (p.model), 'db');
  assert.deepEqual(plan.entities.sort(), ['api-writes-db', 'db', 'no-db-to-api']);

  const ok = p.apply({ type: 'DeleteEntity', id: 'db', cascade: true });
  assert.equal(ok.ok, true, ok.message);
  assert.equal(p.errorCount, 0);
  assert.equal(p.model?.entities.has('api-writes-db'), false);
});

test('deleting a subsystem moves its children up instead of orphaning them', () => {
  const p = fresh();
  const r = p.apply({ type: 'DeleteEntity', id: 'grp', cascade: true });
  assert.equal(r.ok, true, r.message);
  assert.equal(p.model?.entities.get('api')?.data.parent, undefined);
  assert.equal(p.errorCount, 0);
});

test('invalid operations are rejected atomically and leave the committed model untouched', () => {
  const p = fresh();
  const before = { text: p.specText, hash: p.semanticHash, revision: p.revision };
  const cases = [
    [{ type: 'SetProperty', id: 'api', property: 'category', value: 'wizard' }, 'validation.failed'],
    [{ type: 'CreateEntity', kind: 'component', data: { id: 'api', name: 'Dup', category: 'logical' } }, 'id.duplicate'],
    [{ type: 'CreateRelationship', kind: 'calls', from: 'api', to: 'ghost' }, 'validation.failed'],
    [{ type: 'SetProperty', id: 'api', property: 'parent', value: 'db' }, 'validation.failed'],
    [{ type: 'Teleport', id: 'api' }, 'op.unknown'],
    // second op fails: the first must not survive
    [[{ type: 'SetProperty', id: 'api', property: 'name', value: 'X' }, { type: 'DeleteEntity', id: 'nope' }], 'entity.unknown'],
  ];
  for (const [ops, code] of cases) {
    const r = p.apply(/** @type {any} */ (ops));
    assert.equal(r.ok, false);
    assert.equal(r.code, code);
    assert.deepEqual({ text: p.specText, hash: p.semanticHash, revision: p.revision }, before);
  }
});

test('an invalid source draft is rejected with diagnostics and does not corrupt the committed model', () => {
  const p = fresh();
  const broken = SPEC.replace('"name": "API",', '"name": "API"');
  const r = p.apply({ type: 'ReplaceSource', text: broken });
  assert.equal(r.ok, false);
  assert.ok(r.diagnostics.length > 0 && r.diagnostics[0].loc);
  assert.equal(p.specText, SPEC);
  assert.equal(p.model?.entities.size, analyzeSpec(SPEC).model?.entities.size);
  const inconsistent = SPEC.replace('"to": "cache"', '"to": "nowhere"');
  const r2 = p.apply({ type: 'ReplaceSource', text: inconsistent });
  assert.equal(r2.ok, false);
  assert.equal(r2.diagnostics[0].code, 'ref.unresolved');
  assert.equal(p.specText, SPEC);
});

test('undo and redo restore the exact text and semantic state', () => {
  const p = fresh();
  const h0 = p.semanticHash;
  p.apply({ type: 'SetProperty', id: 'api', property: 'name', value: 'Gateway' });
  const h1 = p.semanticHash;
  const t1 = p.specText;
  p.apply({ type: 'CreateRelationship', kind: 'calls', from: 'db', to: 'cache' });
  const h2 = p.semanticHash;
  assert.equal(p.undo()?.ok, true);
  assert.equal(p.semanticHash, h1);
  assert.equal(p.specText, t1);
  p.undo();
  assert.equal(p.semanticHash, h0);
  assert.equal(p.specText, SPEC);
  assert.equal(p.undo(), null);
  p.redo(); p.redo();
  assert.equal(p.semanticHash, h2);
  assert.equal(p.redo(), null);
  // a new edit after undo clears redo
  p.undo();
  p.apply({ type: 'SetProperty', id: 'db', property: 'owner', value: 'x' });
  assert.equal(p.canRedo, false);
});

test('moving a node is presentation only: the semantic hash and the spec text cannot change', () => {
  const p = fresh();
  const h = p.semanticHash;
  const r = p.apply({ type: 'MovePresentationNode', view: 'structural', id: 'api', x: 3.14159, z: -2 });
  assert.equal(r.ok, true);
  assert.equal(r.semanticChanged, false);
  assert.equal(p.semanticHash, h);
  assert.equal(p.specText, SPEC);
  assert.deepEqual(p.layout.views.structural.positions.api, [3.14, -2]);
  assert.equal(p.semanticRevision, 1);
  assert.equal(p.revision, 2);
  // positions follow renames and disappear with deletions
  p.apply({ type: 'RenameEntity', id: 'api', newId: 'gateway' });
  assert.deepEqual(p.layout.views.structural.positions, { gateway: [3.14, -2] });
  p.apply({ type: 'DeleteEntity', id: 'gateway', cascade: true });
  assert.deepEqual(p.layout.views.structural.positions, {});
  // reset
  p.apply({ type: 'MovePresentationNode', view: 'structural', id: 'db', x: 1, z: 1 });
  p.apply({ type: 'MovePresentationNode', view: 'structural', id: 'db', reset: true });
  assert.deepEqual(p.layout.views.structural.positions, {});
});

test('repeated load-edit-save-load cycles preserve semantic equivalence', () => {
  let text = SPEC;
  let layout;
  const names = ['One', 'Two', 'Three', 'Four'];
  for (const name of names) {
    const p = new Project({ specText: text, layoutText: layout });
    assert.equal(p.errorCount, 0);
    const r = p.apply({ type: 'SetProperty', id: 'cache', property: 'name', value: name });
    assert.equal(r.ok, true);
    text = p.specText;       // "save"
    layout = p.layoutText;
    const reloaded = new Project({ specText: text, layoutText: layout });   // "load"
    assert.equal(reloaded.semanticHash, p.semanticHash);
    assert.equal(semanticHash(analyzeSpec(text).model), p.semanticHash);
  }
  assert.equal(text, SPEC.replace('"name": "Cache"', '"name": "Four"'));
});

test('stale transactions are refused (optimistic concurrency)', () => {
  const p = fresh();
  const rev = p.revision;
  const hash = p.semanticHash;
  p.apply({ type: 'SetProperty', id: 'api', property: 'name', value: 'Gateway' });
  const stale = p.apply({ type: 'SetProperty', id: 'api', property: 'name', value: 'Other' }, { expectRevision: rev });
  assert.equal(stale.ok, false);
  assert.equal(stale.code, 'revision.stale');
  const staleHash = p.apply({ type: 'SetProperty', id: 'api', property: 'name', value: 'Other' }, { expectHash: hash });
  assert.equal(staleHash.code, 'revision.stale');
  assert.equal(p.model?.entities.get('api')?.data.name, 'Gateway');
});

test('external reload: valid text is adopted and ends the undo history; broken text keeps the last valid model', () => {
  const p = fresh();
  p.apply({ type: 'SetProperty', id: 'api', property: 'name', value: 'Gateway' });
  assert.equal(p.canUndo, true);
  const changed = p.specText.replace('"name": "DB"', '"name": "Database"');
  const r = p.reload({ specText: changed });
  assert.equal(r.ok, true);
  assert.deepEqual(r.affected, ['db']);
  assert.equal(p.model?.entities.get('db')?.data.name, 'Database');
  assert.equal(p.canUndo, false);
  assert.equal(p.canRedo, false);
  assert.equal(p.history.at(-1)?.origin, 'external');
  const broken = p.reload({ specText: changed.replace('"components": [', '"components": ') });
  assert.equal(broken.ok, false);
  assert.equal(broken.code, 'reload.syntax');
  assert.equal(p.model?.entities.get('db')?.data.name, 'Database');
  assert.equal(p.canUndo, false);
  const q = fresh();
  assert.equal(q.reload({ specText: SPEC.replace('"name": "DB"', '"name": "Database"') }).ok, true);
  assert.equal(q.canUndo, false);
});

test('an operation type that exists on Object.prototype is unknown, not a no-op commit', () => {
  const p = fresh();
  const before = p.revision;
  const r = p.apply({ type: 'constructor' });
  assert.equal(r.ok, false);
  assert.equal(r.code, 'op.unknown');
  assert.equal(p.revision, before);
  assert.equal(p.specText, SPEC);
});
