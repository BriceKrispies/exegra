import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { analyzeSpec } from '../../src/core/analyze.js';
import { evaluateClaims } from '../../src/core/claims.js';
import { listViews, project } from '../../src/core/projections.js';

const FIXTURE = readFileSync(fileURLToPath(new URL('../fixtures/data-model/spec.jsonc', import.meta.url)), 'utf8');

/** A minimal specification with the given records, copies and claims. */
function spec({ records = [], copies = [], claims = [], relationships = [] }) {
  return JSON.stringify({
    exegra: '0.1',
    system: { id: 's', name: 'S' },
    components: [
      { id: 'owner', name: 'Owner', category: 'computational' },
      { id: 'cache', name: 'Cache', category: 'storage' },
      { id: 'island', name: 'Island', category: 'storage' },
    ],
    relationships: [{ id: 'cache-reads-owner', kind: 'reads', from: 'cache', to: 'owner' }, ...relationships],
    records, copies, claims,
  }, null, 2);
}

const PROFILE = {
  id: 'profile', name: 'Profile', owner: 'owner', key: ['who'],
  fields: [
    { name: 'who', type: 'principal-id', refersTo: 'principal', role: 'subject' },
    { name: 'name', type: 'display-name', personal: 'name' },
    { name: 'level', type: 'number' },
  ],
};

const notInfo = (ds) => ds.filter((d) => d.severity !== 'info');

// The data-model fixture validates with exactly one data-rule finding, the missing erasure point; a wrong enum and an unknown key field are errors with their positions; each rule reports its entity and field on a constructed violation; a data-model claim is violated, verified or inconclusive as the findings say; the Data projection draws records, copies and their edges.
// @evidence data-model-rules-computed #
// A record with a personal field and no erasure is a record-erasure-point finding, and a data-model claim over it is violated with the record as counterexample; a record that states an erasure point or a bounded erasure passes.
// @evidence personal-records-state-erasure #
// A classification is accepted when it is in the closed set and consistent with the personal class, rejected otherwise; the data-model fixture, which carries no classifications, validates unchanged.
// @evidence classification-validated #
test('the data slice validates and the rules find exactly the missing erasure point', () => {
  const r = analyzeSpec(FIXTURE);
  assert.equal(r.errorCount, 0);
  const found = notInfo(r.diagnostics);
  assert.equal(found.length, 1, found.map((d) => d.message).join('\n'));
  assert.equal(found[0].code, 'data.erasure-point');
  assert.equal(found[0].entityId, 'trade-name-snapshot');
  assert.deepEqual(found[0].path, ['copies', 5, 'erasure']);
  assert.match(found[0].message, /display-name\.name \(personal: name\)/);
  assert.ok(found[0].loc && found[0].loc.line > 1);

  const status = Object.fromEntries(evaluateClaims(/** @type {any} */ (r.model)).map((c) => [c.claimId, c]));
  assert.equal(status['erasure-point-on-every-copy'].status, 'violated');
  assert.deepEqual(status['erasure-point-on-every-copy'].counterexample?.entities, ['trade-name-snapshot', 'display-name']);
  for (const id of ['shared-copies-hold-no-principal', 'party-fields-by-id', 'copies-have-freshness', 'copies-held-near-owner']) assert.equal(status[id].status, 'verified', `${id}: ${status[id].explanation}`);
});

test('wrong enums, unknown fields and unresolved references are errors with positions; "principal" is not a reference', () => {
  const r = analyzeSpec(spec({
    records: [{ ...PROFILE, key: ['who', 'nobody'], fields: [...PROFILE.fields, { name: 'friend', type: 'profile-id', refersTo: 'no-such-record' }] }],
    copies: [{ id: 'c', name: 'C', of: ['profile'], fields: ['name', 'nickname'], heldBy: 'cache', scope: 'public', freshness: { bound: 5 } }],
  }));
  const codes = r.diagnostics.filter((d) => d.severity === 'error').map((d) => `${d.code}@${d.entityId}`);
  assert.ok(codes.includes('property.enum@c'), codes.join(', '));
  assert.ok(codes.includes('ref.unresolved@profile'), codes.join(', '));
  assert.ok(!r.diagnostics.some((d) => d.code.startsWith('ref.') && /principal/.test(d.message)));
  const enumErr = r.diagnostics.find((d) => d.code === 'property.enum');
  assert.deepEqual(enumErr?.path, ['copies', 0, 'scope']);
  assert.ok(enumErr?.loc?.line);

  // Consistency rules run once the structure is sound.
  const r2 = analyzeSpec(spec({
    records: [{ ...PROFILE, key: ['who', 'nobody'] }],
    copies: [{ id: 'c', name: 'C', of: ['profile'], fields: ['name', 'nickname'], heldBy: 'cache', scope: 'per-session', freshness: { bound: 5 }, erasure: { point: 'p' } }],
  }));
  const errs = r2.diagnostics.filter((d) => d.severity === 'error');
  assert.deepEqual(errs.map((d) => [d.code, d.path]).sort(), [
    ['copy.bound-unit', ['copies', 0, 'freshness', 'bound']],
    ['copy.field-unknown', ['copies', 0, 'fields', 1]],
    ['record.key-field', ['records', 0, 'key', 1]],
  ]);
});

test('each data rule reports its entity and field on a constructed violation', () => {
  const r = analyzeSpec(spec({
    records: [
      PROFILE,
      { id: 'deal', name: 'Deal', owner: 'owner', fields: [{ name: 'buyer', type: 'display-name', role: 'party' }, { name: 'seller', type: 'principal-id', refersTo: 'principal', role: 'party' }] },
    ],
    copies: [
      { id: 'cdn-profile', name: 'CDN profile', of: ['profile'], fields: ['who', 'level'], heldBy: 'cache', scope: 'shared', dependsOnAuthority: true, freshness: { bound: 60, unit: 'second' }, erasure: { point: 'purge' } },
      { id: 'stale', name: 'Stale', of: ['profile'], fields: ['level'], heldBy: 'island', scope: 'internal' },
    ],
  }));
  assert.equal(r.errorCount, 0, r.diagnostics.map((d) => d.message).join('\n'));
  const got = notInfo(r.diagnostics).map((d) => [d.code, d.entityId, d.path.slice(2).join('.')]).sort();
  assert.deepEqual(got, [
    ['data.freshness-bound', 'stale', 'freshness'],
    ['data.holder-reaches-owner', 'stale', 'heldBy'],
    ['data.no-principal-in-shared', 'cdn-profile', 'dependsOnAuthority'],
    ['data.no-principal-in-shared', 'cdn-profile', 'fields.0'],
    ['data.party-by-id', 'deal', 'fields.0'],
    ['data.record-erasure-point', 'profile', 'erasure'],
  ]);
  const party = r.diagnostics.find((d) => d.code === 'data.party-by-id');
  assert.match(party?.message ?? '', /"buyer".*does not refer to the principal and has the name type "display-name"/);
  const shared = r.diagnostics.find((d) => d.code === 'data.no-principal-in-shared' && d.path.includes('fields'));
  assert.match(shared?.message ?? '', /profile\.who \(principal id\)/);
});

test('a data-model claim is inconclusive when a listed rule has nothing to check, and unknown rules are errors', () => {
  const claims = [
    { id: 'shared-clean', kind: 'structural', statement: 'x', evaluate: { method: 'data-model', rules: ['no-principal-in-shared'] } },
    { id: 'fresh', kind: 'structural', statement: 'x', evaluate: { method: 'data-model', rules: ['freshness-bound'], records: ['profile'] } },
  ];
  const copies = [{ id: 'c', name: 'C', of: ['profile'], heldBy: 'cache', scope: 'per-session', freshness: { bound: 'the read stamp' }, erasure: { point: 'sign-out' } }];
  const r = analyzeSpec(spec({ records: [PROFILE], copies, claims }));
  assert.equal(r.errorCount, 0);
  const res = Object.fromEntries(evaluateClaims(/** @type {any} */ (r.model)).map((c) => [c.claimId, c.status]));
  assert.deepEqual(res, { 'shared-clean': 'inconclusive', fresh: 'verified' });

  const bad = analyzeSpec(spec({ records: [PROFILE], copies, claims: [{ id: 'k', kind: 'structural', statement: 'x', evaluate: { method: 'data-model', rules: ['erasure', 'freshness-bound'] } }] }));
  const e = bad.diagnostics.find((d) => d.code === 'claim.param.value');
  assert.deepEqual(e?.path, ['claims', 0, 'evaluate', 'rules', 0]);
});

test('the Data view exists only with records or copies and draws them with of, heldBy and owner edges', () => {
  assert.ok(!listViews(/** @type {any} */ (analyzeSpec(spec({})).model)).some((v) => v.id === 'data'));
  const model = /** @type {any} */ (analyzeSpec(FIXTURE).model);
  assert.ok(listViews(model).some((v) => v.id === 'data'));
  const scene = project(model, 'data');
  const node = (id) => scene.nodes.find((n) => n.id === id);
  assert.equal(node('trade')?.entityKind, 'record');
  assert.equal(node('store-page-variant')?.sublabel, 'Copy, shared');
  assert.equal(node('trade-name-snapshot')?.status, 'violated');
  assert.deepEqual(node('trade-name-snapshot')?.badges, ['erasure-point']);
  assert.equal(node('leaderboard-view')?.status, undefined);
  const edges = new Set(scene.edges.map((e) => `${e.from}>${e.to}:${e.label}`));
  for (const e of ['store-page-variant>game:copy of', 'store-page-variant>cdn:held by', 'game>platform-unit:owned by']) assert.ok(edges.has(e), e);
  for (const e of scene.edges) assert.ok(model.entities.has(e.entityId));
});

const ERASURE_CLAIM = { id: 'records-erase', kind: 'structural', statement: 'x', evaluate: { method: 'data-model', rules: ['record-erasure-point'] } };

test('a record with a personal field and no erasure is reported, and a claim using the rule is violated with the record as counterexample', () => {
  const r = analyzeSpec(spec({ records: [PROFILE], claims: [ERASURE_CLAIM] }));
  assert.equal(r.errorCount, 0, r.diagnostics.map((d) => d.message).join('\n'));
  const found = notInfo(r.diagnostics).filter((d) => d.code === 'data.record-erasure-point');
  assert.equal(found.length, 1, found.map((d) => d.message).join('\n'));
  assert.equal(found[0].entityId, 'profile');
  assert.deepEqual(found[0].path, ['records', 0, 'erasure']);
  assert.match(found[0].message, /"name" \(personal: name\)/);
  const status = Object.fromEntries(evaluateClaims(/** @type {any} */ (r.model)).map((c) => [c.claimId, c]));
  assert.equal(status['records-erase'].status, 'violated');
  assert.deepEqual(status['records-erase'].counterexample?.entities, ['profile']);
});

test('a record that states an erasure point, or a bounded retention with its unit, passes the record-erasure-point rule', () => {
  for (const erasure of [{ point: "the principal's deletion" }, { bound: 30, unit: 'day' }]) {
    const r = analyzeSpec(spec({ records: [{ ...PROFILE, erasure }], claims: [ERASURE_CLAIM] }));
    assert.equal(r.errorCount, 0, JSON.stringify(erasure));
    assert.equal(notInfo(r.diagnostics).filter((d) => d.code === 'data.record-erasure-point').length, 0, JSON.stringify(erasure));
    const status = Object.fromEntries(evaluateClaims(/** @type {any} */ (r.model)).map((c) => [c.claimId, c.status]));
    assert.equal(status['records-erase'], 'verified', JSON.stringify(erasure));
  }
});

test('a bounded erasure without a unit is an error and does not satisfy the rule', () => {
  const r = analyzeSpec(spec({ records: [{ ...PROFILE, erasure: { bound: 30 } }] }));
  assert.ok(r.diagnostics.some((d) => d.code === 'record.bound-unit' && d.severity === 'error' && d.entityId === 'profile'));
  assert.equal(notInfo(r.diagnostics).filter((d) => d.code === 'data.record-erasure-point').length, 1);
});

test('a credential field counts as personal for the record erasure rule, and a record with no personal or credential field is not checked', () => {
  const credential = { id: 'secret', name: 'Secret', owner: 'owner', key: ['id'], fields: [{ name: 'id', type: 'secret-id' }, { name: 'value', type: 'secret-value', classification: 'credential' }] };
  const plain = { id: 'plain', name: 'Plain', owner: 'owner', key: ['id'], fields: [{ name: 'id', type: 'plain-id' }, { name: 'level', type: 'number', classification: 'public' }] };
  const r = analyzeSpec(spec({ records: [credential, plain], claims: [{ ...ERASURE_CLAIM, id: 'c2' }] }));
  assert.equal(r.errorCount, 0, r.diagnostics.map((d) => d.message).join('\n'));
  const found = notInfo(r.diagnostics).filter((d) => d.code === 'data.record-erasure-point');
  assert.deepEqual(found.map((d) => d.entityId), ['secret']);
  const status = Object.fromEntries(evaluateClaims(/** @type {any} */ (r.model)).map((c) => [c.claimId, c]));
  assert.equal(status.c2.status, 'violated');
  assert.deepEqual(status.c2.counterexample?.entities, ['secret']);
});

test('classification is a closed set; personal is stated only through the personal class', () => {
  const field = (extra) => ({ name: 'level', type: 'number', ...extra });
  const cases = [
    [{ classification: 'public' }, null],
    [{ classification: 'internal' }, null],
    [{ classification: 'credential' }, null],
    [{ classification: 'personal', personal: 'activity' }, null],
    [{ classification: 'secret' }, 'property.enum'],
    [{ classification: 'personal' }, 'field.classification-personal'],
    [{ classification: 'internal', personal: 'name' }, 'field.classification-conflict'],
    [{ classification: 'personal', personal: 'name' }, null],
  ];
  for (const [extra, code] of cases) {
    const r = analyzeSpec(spec({ records: [{ id: 'rec', name: 'Rec', owner: 'owner', key: ['id'], fields: [{ name: 'id', type: 'rec-id' }, field(extra)] }] }));
    const errs = r.diagnostics.filter((d) => d.severity === 'error');
    if (code === null) assert.equal(errs.length, 0, `${JSON.stringify(extra)}: ${errs.map((d) => d.message).join('\n')}`);
    else {
      assert.ok(errs.some((d) => d.code === code), `${JSON.stringify(extra)}: expected ${code}, got ${errs.map((d) => d.code).join(', ')}`);
      assert.deepEqual(errs.find((d) => d.code === code)?.path.slice(-1), ['classification']);
    }
  }
});

test('a specification without classifications and with personal fields that state an erasure has no errors', () => {
  const r = analyzeSpec(spec({ records: [{ ...PROFILE, erasure: { point: 'deletion' } }] }));
  assert.equal(r.errorCount, 0, r.diagnostics.map((d) => d.message).join('\n'));
  assert.ok(!r.diagnostics.some((d) => /classification/.test(d.code)));
});
