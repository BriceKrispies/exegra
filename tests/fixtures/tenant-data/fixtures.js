// Fixtures of the metadata-model rules (WG-4950): a specification in which tenants describe their own data, with
// platform tables, a generic record table of scope tenant-meta described by the tenant-schema metamodel, and for each
// rule a mutation that breaks exactly that rule.

/** @param {(d: any) => void} [mutate] @param {{generation?: boolean}} [opts] */
export function spec(mutate = () => {}, { generation = true } = {}) {
  const v1 = { schemaVersion: 1, changes: [{ version: 1, description: 'First shape.' }] };
  const d = {
    exegra: '0.1',
    system: { id: 'platform', name: 'Platform', ...(generation ? { generation: { target: 'rust' } } : {}) },
    components: [{ id: 'store', name: 'Store', category: 'storage' }],
    types: [
      { id: 'tenant-id', name: 'Tenant id', kind: 'id', repr: 'string' },
      { id: 'object-type-id', name: 'Object type id', kind: 'id', repr: 'string', metamodel: 'object-id' },
      { id: 'field-id', name: 'Field id', kind: 'id', repr: 'string', metamodel: 'field-id' },
      { id: 'value-map', name: 'Value map', kind: 'scalar', repr: 'string', metamodel: 'values' },
      { id: 'field-def', name: 'Field definition', kind: 'struct', metamodel: 'definition', fields: [{ name: 'id', type: 'field-id' }, { name: 'required', type: 'bool' }] },
      { id: 'object-def', name: 'Object definition', kind: 'struct', metamodel: 'definition', fields: [{ name: 'id', type: 'object-type-id' }, { name: 'fields', type: 'list<field-def>' }] },
      { id: 'tenant-schema', name: 'Tenant schema', kind: 'struct', metamodel: 'tenant-schema', fields: [{ name: 'version', type: 'u64' }, { name: 'objects', type: 'list<object-def>' }] },
    ],
    records: [
      { id: 'tenants', name: 'Tenants', owner: 'store', key: ['id'], scope: 'platform', ...v1, fields: [{ name: 'id', type: 'tenant-id' }, { name: 'file', type: 'string' }] },
      { id: 'jobs', name: 'Jobs', owner: 'store', key: ['id'], scope: 'platform', realisation: 'target', ...v1, fields: [{ name: 'id', type: 'u64' }] },
      { id: 'records', name: 'Records', owner: 'store', key: ['object', 'id'], scope: 'tenant-meta', describedBy: 'tenant-schema', ...v1, fields: [{ name: 'object', type: 'object-type-id' }, { name: 'id', type: 'u64' }, { name: 'data', type: 'value-map' }] },
      { id: 'record-index', name: 'Record index', owner: 'store', key: ['object', 'field', 'value', 'id'], scope: 'tenant-meta', describedBy: 'tenant-schema', ...v1, fields: [{ name: 'object', type: 'object-type-id' }, { name: 'field', type: 'field-id' }, { name: 'value', type: 'string' }, { name: 'id', type: 'u64' }] },
      { id: 'schema-history', name: 'Schema history', owner: 'store', key: ['version'], scope: 'tenant-meta', describedBy: 'tenant-schema', ...v1, fields: [{ name: 'version', type: 'u64' }, { name: 'schema', type: 'tenant-schema' }] },
    ],
  };
  mutate(d);
  return JSON.stringify(d, null, 2);
}

/** @param {any[]} list @param {string} id */
const get = (list, id) => list.find((e) => e.id === id);

/** A fixed record type standing for one tenant's articles. @param {any[]} fields */
const article = (fields) => ({ id: 'article', name: 'Article', owner: 'store', key: ['slug'], scope: 'platform', schemaVersion: 1, changes: [{ version: 1, description: 'First shape.' }], fields: [{ name: 'slug', type: 'string' }, ...fields] });

/**
 * Each rule, a mutation that breaks it exactly once, and the code it reports.
 * @type {[string, string, (d: any) => void][]}
 */
export const FIXTURES = [
  ['a platform record with a generic map of field values', 'record.tenant-data-fixed', (d) => { d.records.push(article([{ name: 'fields', type: 'map<field-id, string>' }])); }],
  ['a platform record that names a tenant object type', 'record.tenant-data-fixed', (d) => { d.records.push(article([{ name: 'object', type: 'option<object-type-id>', optional: true }])); }],
  ['a platform record holding tenant field values', 'record.tenant-data-fixed', (d) => { d.records.push(article([{ name: 'public', type: 'value-map' }])); }],
  ['a record without a scope once a tenant schema is declared', 'record.scope-missing', (d) => { delete get(d.records, 'tenants').scope; }],
  ['a tenant-meta record without describedBy', 'record.described-by', (d) => { delete get(d.records, 'records').describedBy; }],
  ['a tenant-meta record described by a type that is not the tenant schema', 'record.described-by', (d) => { get(d.records, 'records').describedBy = 'object-def'; }],
  ['a platform record with describedBy', 'record.described-by', (d) => { get(d.records, 'tenants').describedBy = 'tenant-schema'; }],
];
