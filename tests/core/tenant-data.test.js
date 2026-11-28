import { test } from 'node:test';
import assert from 'node:assert/strict';
import { analyzeSpec } from '../../src/core/analyze.js';
import { readinessGaps } from '../../src/core/readiness.js';
import { tenantDataReason } from '../../src/core/tenant-data.js';
import { spec, FIXTURES } from '../fixtures/tenant-data/fixtures.js';

// The metadata model: platform records, tenant data described only by the tenant-schema metamodel (WG-4950).

const errors = (/** @type {any} */ r) => r.diagnostics.filter((/** @type {any} */ d) => d.severity === 'error');
const codes = (/** @type {any} */ ds) => ds.map((/** @type {any} */ d) => d.code);

test('a metadata model with platform tables and tenant-meta tables described by the tenant schema validates', () => {
  for (const generation of [false, true]) {
    const r = analyzeSpec(spec(undefined, { generation }));
    assert.deepEqual(errors(r).map((/** @type {any} */ d) => `${d.code} ${d.message}`), []);
    assert.deepEqual(readinessGaps(/** @type {any} */ (r.model)), []);
  }
});

const generationChecked = new Set();
for (const [title, code, mutate] of FIXTURES) {
  // The generation switch is checked once per family of reported codes (the part before the dot); the other cases run without it.
  const modes = generationChecked.has(code.split(".")[0]) ? [false] : [false, true];
  generationChecked.add(code.split(".")[0]);
  for (const generation of modes) {
    test(`${title} is reported once as ${code}${generation ? ' (generation set)' : ''}`, () => {
      const r = analyzeSpec(spec(mutate, { generation }));
      assert.deepEqual(codes(errors(r)), [code], r.diagnostics.map((/** @type {any} */ d) => d.message).join('\n'));
      assert.ok(errors(r)[0].loc && errors(r)[0].loc.line > 1);
    });
  }
}

test('every new code has a negative fixture', () => {
  const want = ['record.tenant-data-fixed', 'record.scope-missing', 'record.described-by'];
  const have = new Set(FIXTURES.map(([, code]) => code));
  assert.deepEqual(want.filter((c) => !have.has(c)), []);
});

test('a specification without a tenant schema needs no scope and keeps its fixed records', () => {
  const r = analyzeSpec(spec((d) => {
    d.types = d.types.filter((/** @type {any} */ t) => t.metamodel === undefined);
    d.types.push({ id: 'object-type-id', name: 'Object type id', kind: 'id', repr: 'string' }, { id: 'field-id', name: 'Field id', kind: 'id', repr: 'string' }, { id: 'value-map', name: 'Value map', kind: 'scalar', repr: 'string' });
    d.records = d.records.filter((/** @type {any} */ x) => x.scope === 'platform').map((/** @type {any} */ x) => { delete x.scope; return x; });
    d.records.push({ id: 'note', name: 'Note', owner: 'store', key: ['id'], schemaVersion: 1, changes: [{ version: 1, description: 'First shape.' }], fields: [{ name: 'id', type: 'u64' }, { name: 'fields', type: 'map<field-id, string>' }] });
  }));
  assert.deepEqual(codes(errors(r)), []);
});

test('the tenant-data reason follows list, option and map values and names the field-id key', () => {
  const m = /** @type {any} */ (analyzeSpec(spec()).model);
  assert.match(String(tenantDataReason(m, 'list<option<object-type-id>>')), /tenant object type/);
  assert.match(String(tenantDataReason(m, 'map<field-id, string>')), /field id/);
  assert.match(String(tenantDataReason(m, 'map<string, value-map>')), /field values/);
  assert.equal(tenantDataReason(m, 'map<string, u64>'), undefined);
  assert.equal(tenantDataReason(m, 'tenant-schema'), undefined);
  assert.equal(tenantDataReason(m, 'field-def'), undefined);
});
