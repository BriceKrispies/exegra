// A transaction re-derives the model once, not after every operation (src/core/operations.js, Tx).
// These tests are the differential evidence: for seeded random operation sequences, the batched
// transaction and the per-operation reference (Tx with `eager`, Project.apply with `perOperation`)
// produce byte-identical specification and layout texts, the same failures, the same affected ids,
// and the same verdict and diagnostics; and the batched transaction's index of declarations never
// diverges from the model it describes.
//
// Corpora: a small hand-written JSONC specification with comments, one-line declarations and
// trailing commas; specs/benchmark; specs/exegra. EXEGRA_TX_DIFF_SEEDS multiplies the number of
// seeds (default 1; the routine seeds are 8, 1 and 1, one run of each shape; raise it for a longer sweep). EXEGRA_TX_DIFF_SPEC names a further specification file to run on, such as a
// frozen copy of a large linked project.
import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { Project } from '../../src/core/project.js';
import { analyzeSpec } from '../../src/core/analyze.js';
import { OPERATIONS, OpError, Tx, EMPTY_LAYOUT } from '../../src/core/operations.js';
import { declarationSite } from '../../src/core/query.js';
import { readSpecFile } from '../../tools/spec-manifest.js';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
const SCALE = Math.max(1, Number(process.env.EXEGRA_TX_DIFF_SEEDS ?? 1) || 1);

const SMALL = `{
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
      "purpose": "Serves requests.",
      "ports": [ { "id": "api-in", "name": "In", "direction": "provides" } ]
    },
    { "id": "db", "name": "DB", "category": "storage", "purpose": "Stores." },
    { "id": "cache",   "name": "Cache",   "category": "storage", "purpose": "Caches."   }, // after
    { "id": "worker", "name": "Worker", "category": "computational", "purpose": "Works.", },
  ],
  "relationships": [
    { "id": "api-writes-db", "kind": "writes", "from": "api", "to": "db", "description": "w" },
    { "id": "api-reads-cache", "kind": "reads", "from": "api", "to": "cache", "description": "r" }
  ],
  "events": [ { "id": "tick", "name": "Tick" } ],
  "behaviors": [
    {
      "id": "worker-life",
      "name": "Worker life",
      "subject": "worker",
      "initial": "idle",
      "states": [
        { "id": "idle", "name": "Idle" },
        { "id": "busy", "name": "Busy" }
      ],
      "transitions": [
        { "id": "start", "from": "idle", "to": "busy", "on": "tick" }
      ]
    }
  ],
  "claims": [
    { "id": "no-db-to-api", "kind": "structural", "statement": "s", "subjects": ["db", "api"],
      "evaluate": { "method": "no-relationship", "from": "db", "to": ["api"] } }
  ]
}
`;

/** @param {number} seed */
function rng(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

const TEXTS = ['Edited.', 'Quotes "inside" and a \\ backslash.', 'Line one.\nLine two.', 'Unicode: é ü 漢字 ✓', '', 'x'.repeat(300)];

/**
 * A random operation sequence over a model: property edits (set, remove, nested paths), creations
 * (top-level and nested, some edited later in the same transaction), relationships with derived
 * ids, renames, deletions with and without cascade, claim edits, layout moves, edits that replace
 * nested declarations, insertions before existing items, and operations that fail.
 * @param {import('../../src/core/types.js').Model} model @param {number} seed
 */
function randomOps(model, seed) {
  const r = rng(seed);
  const pick = (/** @type {any[]} */ xs) => xs[Math.floor(r() * xs.length)];
  const all = [...model.entities.values()].filter((e) => e.kind !== 'system');
  const ofKind = (/** @type {string} */ k) => model.byKind[k] ?? [];
  const props = (/** @type {string} */ k) => model.meta.entities[k]?.properties ?? {};
  const textProp = (/** @type {string} */ k) => ['description', 'name', 'statement', 'purpose'].find((p) => props(k)[p]) ?? 'description';
  const creatable = ['event', 'contract', 'capability', 'environment', 'assumption'].filter((k) => model.meta.entities[k] && declarationSite(model, k)?.section);
  /** @type {{id: string, kind: string}[]} */
  const created = [];
  let n = 0;
  const fresh = () => `tx-diff-${seed}-${n++}`;
  const newData = (/** @type {string} */ kind, /** @type {string} */ id) => (kind === 'assumption' ? { id, statement: pick(TEXTS) || 'S.' } : { id, name: `Made ${id}`, ...(props(kind).description ? { description: pick(TEXTS) } : {}) });
  const ops = [];
  const count = 1 + Math.floor(r() * 7);
  for (let i = 0; i < count; i++) {
    const roll = r();
    if (roll < 0.3 && all.length) {
      const e = pick(all);
      ops.push({ type: 'SetProperty', id: e.id, property: r() < 0.3 ? [textProp(e.kind)] : textProp(e.kind), value: pick(TEXTS) });
    } else if (roll < 0.36 && all.length) {
      const e = pick(all.filter((x) => typeof x.data.description === 'string').concat(all.slice(0, 1)));
      ops.push({ type: 'SetProperty', id: e.id, property: 'description', value: null });
    } else if (roll < 0.52 && creatable.length) {
      const kind = pick(creatable);
      const id = fresh();
      created.push({ id, kind });
      ops.push({ type: 'CreateEntity', kind, data: newData(kind, id) });
    } else if (roll < 0.62 && created.length) {
      const c = pick(created);
      ops.push({ type: 'SetProperty', id: c.id, property: textProp(c.kind), value: pick(TEXTS) || 'Again.' });
    } else if (roll < 0.67 && ofKind('component').length) {
      const id = fresh();
      created.push({ id, kind: 'port' });
      ops.push({ type: 'CreateEntity', kind: 'port', owner: pick(ofKind('component')).id, data: { id, name: `Port ${id}`, direction: pick(['provides', 'requires']) } });
    } else if (roll < 0.7 && ofKind('behavior').length) {
      const b = pick(ofKind('behavior'));
      const id = fresh();
      created.push({ id, kind: 'state' });
      ops.push({ type: 'AddState', behavior: b.id, data: { id, name: `State ${id}` } });
    } else if (roll < 0.72 && ofKind('behavior').length && ofKind('event').length) {
      const b = pick(ofKind('behavior'));
      const states = ofKind('state').filter((s) => s.owner === b.id);
      if (states.length) ops.push({ type: 'AddTransition', behavior: b.id, index: 0, data: { id: fresh(), from: pick(states).id, to: pick(states).id, on: pick(ofKind('event')).id } });
    } else if (roll < 0.77 && ofKind('component').length > 1) {
      ops.push({ type: 'CreateRelationship', kind: 'observes', from: pick(ofKind('component')).id, to: pick(ofKind('component')).id, ...(r() < 0.5 ? { description: pick(TEXTS) } : {}) });
    } else if (roll < 0.8 && ofKind('component').length) {
      // Replaces the nested declarations: the index must notice.
      const c = pick(ofKind('component'));
      const id = fresh();
      ops.push({ type: 'SetProperty', id: c.id, property: 'ports', value: [{ id, name: 'Replaced', direction: 'provides' }] });
      if (r() < 0.7) ops.push({ type: 'SetProperty', id, property: 'name', value: 'Found' });
    } else if (roll < 0.84 && (created.length || all.length)) {
      const target = created.length && r() < 0.6 ? pick(created) : pick(all);
      const newId = fresh();
      ops.push({ type: 'RenameEntity', id: target.id, newId });
      if (r() < 0.5) ops.push({ type: 'SetProperty', id: newId, property: textProp(target.kind), value: 'Renamed.' });
    } else if (roll < 0.88 && (created.length || all.length)) {
      const target = created.length && r() < 0.6 ? pick(created) : pick(all);
      ops.push({ type: 'DeleteEntity', id: target.id, cascade: r() < 0.5 });
    } else if (roll < 0.9 && ofKind('claim').length) {
      ops.push({ type: 'ModifyClaim', id: pick(ofKind('claim')).id, changes: { statement: pick(TEXTS) || 'Claimed.' } });
    } else if (roll < 0.93 && all.length) {
      ops.push({ type: 'MovePresentationNode', view: 'structural', id: pick(all).id, ...(r() < 0.2 ? { reset: true } : { x: Math.round(r() * 1000) / 10, z: -Math.round(r() * 1000) / 10 }) });
    } else if (roll < 0.95) {
      ops.push({ type: 'SetProperty', id: 'no-such-entity-anywhere', property: 'name', value: 'x' });
    } else if (roll < 0.97 && all.length) {
      const kind = creatable[0] ?? 'event';
      ops.push({ type: 'CreateEntity', kind, data: newData(kind, pick(all).id) });
    } else if (all.length) {
      const e = pick(all);
      ops.push({ type: 'SetProperty', id: e.id, property: [textProp(e.kind), 'nested', 'deep'], value: 'Not a string property.' });
    }
  }
  return ops;
}

/** @param {any} d */
const diag = (d) => ({ code: d.code, severity: d.severity, message: d.message, loc: d.loc, path: d.path, entityId: d.entityId });

/**
 * Run ops on a transaction. @param {string} spec @param {string} layout
 * @param {import('../../src/core/types.js').Model} model
 * @param {import('../../src/core/types.js').Diagnostic[]|undefined} diagnostics
 * @param {any[]} ops @param {boolean} eager
 */
function runTx(spec, layout, model, diagnostics, ops, eager) {
  const tx = new Tx(spec, layout, model, { eager, diagnostics });
  try {
    for (const op of ops) OPERATIONS[/** @type {keyof typeof OPERATIONS} */ (op.type)].apply(tx, op);
    const parsed = tx.specEdited ? tx.parsed() : null;
    return { tx, error: null, parsed };
  } catch (e) {
    if (!(e instanceof OpError)) return { tx, error: { thrown: String(e) }, parsed: null };
    tx.check();
    return { tx, error: { code: e.code, message: e.message, diagnostics: e.diagnostics.map(diag) }, parsed: null };
  }
}

/**
 * The batched transaction against the per-operation reference on one corpus.
 * @param {string} name @param {string} spec @param {string} layout @param {number} seeds
 */
function differential(name, spec, layout, seeds) {
  const a = analyzeSpec(spec);
  assert.ok(a.model, `${name} parses`);
  const model = /** @type {import('../../src/core/types.js').Model} */ (a.model);
  let accepted = 0;
  for (let seed = 1; seed <= seeds; seed++) {
    const ops = randomOps(model, seed);
    // Without the diagnostics the transaction cannot know which ids are declared twice and keeps
    // fewer facts; every other seed runs that way too.
    const diagnostics = seed % 2 ? a.diagnostics : undefined;
    const ref = runTx(spec, layout, model, diagnostics, ops, true);
    const got = runTx(spec, layout, model, diagnostics, ops, false);
    const at = `${name}, seed ${seed}: ${JSON.stringify(ops).slice(0, 400)}`;
    assert.equal(got.tx.diverged, false, `the index diverged from the model (${at})`);
    assert.deepEqual(got.error, ref.error, `same failure (${at})`);
    if (ref.error) continue;
    assert.ok(got.tx.specText === ref.tx.specText, `byte-identical specification text (${at})`);
    assert.ok(got.tx.layoutText === ref.tx.layoutText, `byte-identical layout text (${at})`);
    assert.deepEqual([...got.tx.affected], [...ref.tx.affected], `same affected ids (${at})`);
    assert.equal(got.tx.specEdited, ref.tx.specEdited);
    if (!got.tx.specEdited) continue;
    // The verdict: the analysis that reuses the transaction's parse equals a fresh full analysis.
    const reused = analyzeSpec(got.tx.specText, got.parsed);
    const full = analyzeSpec(ref.tx.specText);
    assert.equal(reused.errorCount, full.errorCount, `same verdict (${at})`);
    assert.deepEqual(reused.diagnostics.map(diag), full.diagnostics.map(diag), `same diagnostics (${at})`);
    assert.equal(reused.model?.semanticHash, full.model?.semanticHash);
    if (!full.errorCount) accepted++;
  }
  return accepted;
}

/**
 * Project.apply batched against Project.apply with perOperation: the whole result.
 * @param {string} spec @param {string} layout @param {number} seeds @param {number} offset
 */
function projectDifferential(spec, layout, seeds, offset) {
  const ref = new Project({ specText: spec, layoutText: layout });
  const got = new Project({ specText: spec, layoutText: layout });
  for (let seed = offset; seed < offset + seeds; seed++) {
    const ops = randomOps(/** @type {any} */ (ref.model), seed);
    const at = `seed ${seed}: ${JSON.stringify(ops).slice(0, 400)}`;
    // An edit jsonc-parser cannot make (a path into a string) throws from apply on both paths.
    const attempt = (/** @type {Project} */ p, /** @type {any} */ o) => { try { return { r: p.apply(ops, o), thrown: null }; } catch (e) { return { r: null, thrown: String(e) }; } };
    const ta = attempt(ref, { perOperation: true, label: 'diff' });
    const tb = attempt(got, { label: 'diff' });
    assert.equal(tb.thrown, ta.thrown, `same exception (${at})`);
    if (!ta.r || !tb.r) continue;
    const a = ta.r;
    const b = tb.r;
    assert.equal(b.ok, a.ok, `same verdict (${at})`);
    assert.equal(b.code, a.code, at);
    assert.equal(b.message, a.message, at);
    assert.deepEqual(b.diagnostics.map(diag), a.diagnostics.map(diag), at);
    assert.deepEqual(b.affected, a.affected, at);
    assert.equal(b.semanticHash, a.semanticHash, at);
    assert.ok(got.specText === ref.specText && got.layoutText === ref.layoutText, `byte-identical texts (${at})`);
    if (a.ok) { ref.undo(); got.undo(); }
  }
}

test('batched transactions equal per-operation re-derivation on a hand-written JSONC specification', () => {
  differential('small', SMALL, EMPTY_LAYOUT, 8 * SCALE);
  projectDifferential(SMALL, EMPTY_LAYOUT, 3 * SCALE, 1000);
});

test('batched transactions equal per-operation re-derivation on the benchmark specification', () => {
  const spec = fs.readFileSync(path.join(ROOT, 'specs/benchmark/spec.jsonc'), 'utf8');
  differential('benchmark', spec, EMPTY_LAYOUT, 1 * SCALE);
});

test('batched transactions equal per-operation re-derivation on the Exegra specification', () => {
  const spec = readSpecFile(path.join(ROOT, 'specs/exegra/spec.jsonc'));
  differential('exegra', spec, EMPTY_LAYOUT, 1 * SCALE);
});

test('batched transactions equal per-operation re-derivation on EXEGRA_TX_DIFF_SPEC', { skip: !process.env.EXEGRA_TX_DIFF_SPEC }, () => {
  const file = /** @type {string} */ (process.env.EXEGRA_TX_DIFF_SPEC);
  const spec = fs.readFileSync(file, 'utf8');
  differential(path.basename(file), spec, EMPTY_LAYOUT, 2 * SCALE);
});

test('a batched transaction derives the model once for property edits and creations', () => {
  const p = new Project({ specText: SMALL });
  const tx = new Tx(p.specText, p.layoutText, /** @type {any} */ (p.model), { diagnostics: p.diagnostics });
  OPERATIONS.SetProperty.apply(tx, { type: 'SetProperty', id: 'db', property: 'name', value: 'Database' });
  OPERATIONS.CreateEntity.apply(tx, { type: 'CreateEntity', kind: 'event', data: { id: 'tock', name: 'Tock' } });
  OPERATIONS.SetProperty.apply(tx, { type: 'SetProperty', id: 'tock', property: 'description', value: 'Found without a derivation.' });
  OPERATIONS.CreateEntity.apply(tx, { type: 'CreateEntity', kind: 'port', owner: 'db', data: { id: 'db-in', name: 'In', direction: 'provides' } });
  OPERATIONS.SetProperty.apply(tx, { type: 'SetProperty', id: 'db-in', property: 'description', value: 'Nested too.' });
  OPERATIONS.CreateRelationship.apply(tx, { type: 'CreateRelationship', kind: 'observes', from: 'db', to: 'cache' });
  assert.equal(tx.entity('tock').kind, 'event');
  assert.equal(tx.derivations, 0, 'no operation needed a derivation');
  assert.equal(tx.model.entities.get('db-in')?.owner, 'db');
  assert.equal(tx.derivations, 1, 'reading the model derives it once');
  assert.equal(tx.diverged, false);
  // Replacing nested declarations, renaming and deleting keep the index without a derivation.
  OPERATIONS.SetProperty.apply(tx, { type: 'SetProperty', id: 'db', property: 'ports', value: [{ id: 'db-out', name: 'Out', direction: 'requires' }] });
  assert.equal(tx.entity('db-out').owner, 'db');
  assert.throws(() => tx.entity('db-in'), /No entity has id "db-in"/);
  assert.equal(tx.derivations, 1);
  OPERATIONS.RenameEntity.apply(tx, { type: 'RenameEntity', id: 'tock', newId: 'tock-two' });
  assert.equal(tx.derivations, 2, 'a rename reads the references of the current text');
  OPERATIONS.SetProperty.apply(tx, { type: 'SetProperty', id: 'tock-two', property: 'name', value: 'Tock two' });
  OPERATIONS.DeleteEntity.apply(tx, { type: 'DeleteEntity', id: 'tock-two' });
  OPERATIONS.SetProperty.apply(tx, { type: 'SetProperty', id: 'worker', property: 'name', value: 'Worker two' });
  assert.equal(tx.derivations, 3, 'a deletion reads the references of the current text, and nothing after it derives');
  assert.equal(tx.has('tock-two'), false);
  tx.parsed();
  assert.equal(tx.diverged, false);
});
