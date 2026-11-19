// Fixtures of the union, map, constraint and recursion rules (WG-4925) and of sets, tuple variants and nested
// generic type texts (WG-4956): a specification that is ready to generate from and uses every new construct in
// the forms of the Strata kernel's serde types, and for each rule a mutation that breaks exactly that rule.

/** @param {(d: any) => void} [mutate] @param {{generation?: boolean}} [opts] */
export function spec(mutate = () => {}, { generation = true } = {}) {
  const d = {
    exegra: '0.1',
    system: { id: 'kernel', name: 'Kernel', ...(generation ? { generation: { target: 'rust' } } : {}) },
    components: [{ id: 'svc', name: 'Service', category: 'computational' }],
    types: [
      { id: 'field-id', name: 'Field id', kind: 'id', repr: 'string', constraints: { pattern: '^[a-z][a-z0-9_]*$', minLength: 1, maxLength: 64 } },
      { id: 'version', name: 'Version', kind: 'scalar', repr: 'u64' },
      { id: 'blob', name: 'Blob', kind: 'scalar', repr: 'bytes', constraints: { maxLength: 1024 } },
      // serde's default form: unit variants as "Null", newtype variants as {"Bool": true}, a list that holds values
      { id: 'value', name: 'Value', kind: 'union', variants: [
        { name: 'Null' },
        { name: 'Bool', newtype: true, fields: [{ name: 'value', type: 'bool' }] },
        { name: 'Int', newtype: true, fields: [{ name: 'value', type: 'i64' }] },
        { name: 'List', newtype: true, fields: [{ name: 'value', type: 'list<value>' }] },
      ] },
      // struct-like variants under the external tag: {"UpdateRecord": {"id": ..., "fields": {...}}}
      { id: 'intent', name: 'Intent', kind: 'union', variants: [
        { name: 'AssignRole', fields: [{ name: 'principal', type: 'string' }, { name: 'role', type: 'string' }] },
        { name: 'UpdateRecord', fields: [{ name: 'id', type: 'string' }, { name: 'fields', type: 'map<field-id, value>' }, { name: 'expected_version', type: 'option<version>', optional: true }] },
        { name: 'ChangeSchema', fields: [{ name: 'changes', type: 'list<intent>' }] },
      ] },
      { id: 'event-body', name: 'Event body', kind: 'union', encoding: { tag: 'internal', tagField: 'type', variantCase: 'snake_case' }, variants: [
        { name: 'TenantCreated', fields: [{ name: 'name', type: 'string' }] },
        { name: 'MemberChanged' },
      ] },
      { id: 'reply', name: 'Reply', kind: 'union', encoding: { tag: 'adjacent', tagField: 't', contentField: 'c', variantCase: 'kebab-case' }, variants: [
        { name: 'Ok', fields: [{ name: 'version', type: 'version' }] },
        { name: 'Refused', newtype: true, fields: [{ name: 'reason', type: 'string' }] },
        { name: 'Moved', tuple: true, fields: [{ name: 'from', type: 'version' }, { name: 'to', type: 'option<version>' }] },
      ] },
      // tuple variants under the external tag, as serde writes Expr::Cmp(CmpOp, Box<Expr>, Box<Expr>): {"Cmp": ["Eq", a, b]}
      { id: 'cmp-op', name: 'Cmp op', kind: 'enum', values: ['Eq', 'Lt'] },
      { id: 'cond', name: 'Cond', kind: 'union', variants: [
        { name: 'Lit', newtype: true, fields: [{ name: 'value', type: 'value' }] },
        { name: 'Var', tuple: true, fields: [{ name: 'scope', type: 'cmp-op' }, { name: 'field', type: 'field-id' }] },
        { name: 'Cmp', tuple: true, fields: [{ name: 'op', type: 'cmp-op' }, { name: 'left', type: 'cond' }, { name: 'right', type: 'cond' }] },
      ] },
      // a cycle through a list, an option, a map or a union variant is finite
      { id: 'tree', name: 'Tree', kind: 'struct', fields: [{ name: 'children', type: 'list<tree>' }, { name: 'parent', type: 'option<tree>', optional: true }, { name: 'named', type: 'map<string, tree>' }, { name: 'body', type: 'intent' }] },
      { id: 'counts', name: 'Counts', kind: 'struct', fields: [{ name: 'by-code', type: 'map<u16, u32>' }, { name: 'tags', type: 'set<field-id>' }] },
    ],
    records: [
      { id: 'rec', name: 'Rec', owner: 'svc', key: ['id'], schemaVersion: 1, changes: [{ version: 1, description: 'First shape.' }], fields: [{ name: 'id', type: 'field-id' }, { name: 'fields', type: 'map<field-id, value>' }, { name: 'tree', type: 'tree' }, { name: 'by-version', type: 'map<field-id, map<version, cond>>' }, { name: 'roles', type: 'map<string, set<string>>' }] },
    ],
    contracts: [
      { id: 'ct-apply', name: 'Apply', ref: 'CT-001', realisation: 'generated', exposure: 'local', auth: { scheme: 'in-process' }, inputs: [{ name: 'intent', type: 'intent' }], outputs: [{ name: 'reply', type: 'reply' }, { name: 'counts', type: 'map<string, list<counts>>' }], errors: [{ name: 'bad', condition: 'Refused.', type: 'event-body', status: 400 }] },
    ],
    events: [{ id: 'applied', name: 'Applied', payload: [{ name: 'body', type: 'event-body' }, { name: 'versions', type: 'map<version, blob>' }] }],
  };
  mutate(d);
  return JSON.stringify(d, null, 2);
}

/** @param {any[]} list @param {string} id */
const get = (list, id) => list.find((e) => e.id === id);

/**
 * Each rule, a mutation that breaks it exactly once, and the code it reports.
 * @type {[string, string, (d: any) => void][]}
 */
export const FIXTURES = [
  ['a union without variants', 'type.union-variants', (d) => { get(d.types, 'value').variants = []; }],
  ['a union naming a variant twice', 'type.union-variants', (d) => { get(d.types, 'intent').variants.push({ name: 'AssignRole' }); }],
  ['a variant naming a field twice', 'type.union-variants', (d) => { get(d.types, 'intent').variants[0].fields.push({ name: 'role', type: 'string' }); }],
  ['a newtype variant with two fields', 'type.union-variants', (d) => { get(d.types, 'value').variants[1].fields.push({ name: 'other', type: 'bool' }); }],
  ['two variants written alike on the wire', 'type.union-variants', (d) => { get(d.types, 'event-body').variants.push({ name: 'member_changed' }); }],
  ['a variants list on a struct', 'type.union-variants', (d) => { get(d.types, 'counts').variants = [{ name: 'A' }]; }],
  ['a variant field whose type does not resolve', 'type.union-field', (d) => { get(d.types, 'intent').variants[0].fields[0].type = 'principal-id'; }],
  ['a variant field with a map whose value does not resolve', 'type.union-field', (d) => { get(d.types, 'intent').variants[1].fields[1].type = 'map<field-id, cell>'; }],
  ['a tagField on an external tag', 'type.encoding', (d) => { get(d.types, 'value').encoding = { tag: 'external', tagField: 'type' }; }],
  ['a tagField on no tag at all', 'type.encoding', (d) => { get(d.types, 'value').encoding = { tagField: 'type' }; }],
  ['a contentField on an internal tag', 'type.encoding', (d) => { get(d.types, 'event-body').encoding.contentField = 'c'; }],
  ['an internal tag without a tagField', 'type.encoding', (d) => { delete get(d.types, 'event-body').encoding.tagField; }],
  ['an adjacent tag without a contentField', 'type.encoding', (d) => { delete get(d.types, 'reply').encoding.contentField; }],
  ['an adjacent tag with one name for both', 'type.encoding', (d) => { get(d.types, 'reply').encoding.contentField = 't'; }],
  ['an internal tag over a newtype variant', 'type.encoding', (d) => { get(d.types, 'event-body').variants.push({ name: 'Wrapped', newtype: true, fields: [{ name: 'inner', type: 'string' }] }); }],
  ['an internal tag named like a variant field', 'type.encoding', (d) => { get(d.types, 'event-body').variants[0].fields[0].name = 'type'; }],
  ['an encoding on a struct', 'type.encoding', (d) => { get(d.types, 'counts').encoding = { tag: 'external' }; }],
  ['a map keyed by f64', 'type.map-key', (d) => { get(d.records, 'rec').fields[1].type = 'map<f64, value>'; }],
  ['a map keyed by a union', 'type.map-key', (d) => { get(d.contracts, 'ct-apply').outputs[1].type = 'map<value, string>'; }],
  ['a map keyed by a list', 'type.map-key', (d) => { get(d.events, 'applied').payload[1].type = 'map<list<string>, blob>'; }],
  ['a map keyed by json inside a union field', 'type.map-key', (d) => { get(d.types, 'intent').variants[1].fields[1].type = 'map<json, value>'; }],
  ['a map keyed by an id over a uuid', 'type.map-key', (d) => { d.types.push({ id: 'row-id', name: 'Row id', kind: 'id', repr: 'uuid' }); get(d.records, 'rec').fields[1].type = 'map<row-id, value>'; }],
  ['a struct holding itself', 'type.recursion', (d) => { get(d.types, 'counts').fields.push({ name: 'inner', type: 'counts' }); }],
  ['two structs holding each other', 'type.recursion', (d) => { d.types.push({ id: 'ping', name: 'Ping', kind: 'struct', fields: [{ name: 'pong', type: 'pong' }] }, { id: 'pong', name: 'Pong', kind: 'struct', fields: [{ name: 'ping', type: 'ping' }] }); }],
  ['constraints on an enum', 'type.constraints', (d) => { d.types.push({ id: 'colour', name: 'Colour', kind: 'enum', values: ['red'], constraints: { maxLength: 3 } }); }],
  ['a pattern that is not a regular expression', 'type.constraints', (d) => { get(d.types, 'field-id').constraints.pattern = '([a-z'; }],
  ['a pattern on a number', 'type.constraints', (d) => { get(d.types, 'version').constraints = { pattern: '^[0-9]+$' }; }],
  ['a length on a number', 'type.constraints', (d) => { get(d.types, 'version').constraints = { maxLength: 3 }; }],
  ['a pattern on bytes', 'type.constraints', (d) => { get(d.types, 'blob').constraints = { pattern: '^a' }; }],
  ['a minLength above the maxLength', 'type.constraints', (d) => { get(d.types, 'field-id').constraints.minLength = 100; }],
  ['a negative maxLength', 'type.constraints', (d) => { get(d.types, 'field-id').constraints = { maxLength: -1 }; }],
  // WG-4956: sets, tuple variants and nested generic type texts
  ['a set of an unresolved type', 'type.field-unresolved', (d) => { get(d.types, 'counts').fields[1].type = 'set<tag>'; }],
  ['a set of an unresolved type in a variant field', 'type.union-field', (d) => { get(d.types, 'cond').variants[1].fields[1].type = 'set<column>'; }],
  ['a map keyed by a set', 'type.map-key', (d) => { get(d.records, 'rec').fields[4].type = 'map<set<string>, string>'; }],
  ['a map inside a set keyed by f64', 'type.map-key', (d) => { get(d.types, 'counts').fields[1].type = 'set<map<f64, u32>>'; }],
  ['a map inside a map keyed by f64', 'type.map-key', (d) => { get(d.records, 'rec').fields[3].type = 'map<field-id, map<f64, cond>>'; }],
  ['a map of maps whose inner value does not resolve', 'type.union-field', (d) => { get(d.types, 'intent').variants[1].fields[1].type = 'map<field-id, map<version, cell>>'; }],
  ['a tuple variant with one field', 'type.union-variants', (d) => { get(d.types, 'cond').variants[1].fields.pop(); }],
  ['a tuple variant that is also a newtype', 'type.union-variants', (d) => { get(d.types, 'cond').variants[2].newtype = true; get(d.types, 'cond').variants[2].fields = [{ name: 'op', type: 'cmp-op' }]; }],
  ['a tuple variant with an optional field', 'type.union-variants', (d) => { get(d.types, 'cond').variants[2].fields[2].optional = true; }],
  ['an internal tag over a tuple variant', 'type.encoding', (d) => { get(d.types, 'event-body').variants.push({ name: 'Pair', tuple: true, fields: [{ name: 'a', type: 'string' }, { name: 'b', type: 'string' }] }); }],
  // WG-4960: shared<T> is a sharing hint, read as T
  ['a shared of an unresolved type', 'type.field-unresolved', (d) => { get(d.types, 'counts').fields[1].type = 'shared<tag>'; }],
  ['a struct that holds itself through a shared field', 'type.recursion', (d) => { get(d.types, 'counts').fields.push({ name: 'self', type: 'shared<counts>' }); }],
];
