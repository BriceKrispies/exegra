// Fixtures of the format gaps the read and view functions of Strata met (WG-4968, from WG-4939): an untagged union
// wire encoding, inputs a request supplies from its route or session, the JSON null in function bodies, reference
// lookup in eval, and lexicographic ordering of lists in sortBy; and for each rule a mutation that breaks exactly
// that rule. The functions are built on the language and kernel types of the function fixtures.

import { spec as functionsSpec } from '../functions/fixtures.js';

const TYPES = [
  { id: 'plain-json', name: 'Plain JSON', kind: 'union', encoding: { tag: 'untagged' }, description: 'Raw JSON on the wire: null, a bool, a number, a string, an array or an object.', variants: [
    { name: 'Null' },
    { name: 'Bool', newtype: true, fields: [{ name: 'value', type: 'bool' }] },
    { name: 'Number', newtype: true, fields: [{ name: 'value', type: 'f64' }] },
    { name: 'Text', newtype: true, fields: [{ name: 'value', type: 'string' }] },
    { name: 'Items', newtype: true, fields: [{ name: 'value', type: 'list<plain-json>' }] },
    { name: 'Members', newtype: true, fields: [{ name: 'value', type: 'map<string, plain-json>' }] },
  ] },
  { id: 'mutation', name: 'Mutation', kind: 'union', encoding: { tag: 'internal', tagField: 'op', variantCase: 'snake_case' }, variants: [
    { name: 'Create', fields: [{ name: 'object', type: 'string' }, { name: 'fields', type: 'map<string, plain-json>' }] },
    { name: 'Update', fields: [{ name: 'object', type: 'string' }, { name: 'id', type: 'u64' }, { name: 'fields', type: 'map<string, plain-json>' }, { name: 'expected-version', type: 'u64', optional: true }] },
    { name: 'Delete', fields: [{ name: 'object', type: 'string' }, { name: 'id', type: 'u64' }] },
  ] },
  { id: 'shape', name: 'Shape', kind: 'union', variants: [
    { name: 'Empty' },
    { name: 'Radius', newtype: true, fields: [{ name: 'value', type: 'u32' }] },
    { name: 'Corners', tuple: true, fields: [{ name: 'width', type: 'u32' }, { name: 'height', type: 'u32' }] },
    { name: 'Label', fields: [{ name: 'text', type: 'string' }, { name: 'bold', type: 'bool', optional: true }] },
  ] },
  { id: 'shape-adjacent', name: 'Shape, adjacent', kind: 'union', encoding: { tag: 'adjacent', tagField: 't', contentField: 'c', variantCase: 'kebab-case' }, variants: [
    { name: 'EmptyShape' },
    { name: 'Radius', newtype: true, fields: [{ name: 'value', type: 'u32' }] },
    { name: 'Corners', tuple: true, fields: [{ name: 'width', type: 'u32' }, { name: 'height', type: 'u32' }] },
    { name: 'Label', fields: [{ name: 'text', type: 'string' }] },
  ] },
  { id: 'maybe-text', name: 'Maybe text', kind: 'union', variants: [{ name: 'null' }, { name: 'text', newtype: true, fields: [{ name: 'value', type: 'string' }] }] },
  { id: 'view-block', name: 'View block', kind: 'struct', fields: [{ name: 'kind', type: 'string' }, { name: 'params', type: 'json' }] },
];

const ENV = 'rule-env{record: record, old: null, new: null, param: {}, now: value.Null, principal: value.Null, has_role: []}';
const THROUGH = "expr.Through{scope: scope.Record, field: 'author', target: 'name'}";

const FUNCTIONS = [
  {
    id: 'blank-view',
    description: 'A projection that writes the JSON null where it has no parameters.',
    params: [{ name: 'keep', type: 'bool' }, { name: 'blob', type: 'json' }],
    returns: 'json',
    body: 'if keep then blob else null',
    examples: [{ args: { keep: true, blob: { a: 1 } }, result: { a: 1 } }, { args: { keep: false, blob: { a: 1 } }, result: null }],
  },
  {
    id: 'empty-block',
    description: 'A struct whose json field is the JSON null.',
    params: [{ name: 'kind', type: 'string' }],
    returns: 'view-block',
    body: 'view-block{kind, params: null}',
    examples: [{ args: { kind: 'divider' }, result: { kind: 'divider', params: null } }],
  },
  {
    id: 'text-or-null',
    description: 'A union with a variant named null, written plain-json.null style and matched as null.',
    params: [{ name: 'present', type: 'bool' }],
    returns: 'maybe-text',
    body: "if present then maybe-text.text('x') else maybe-text.null",
    examples: [{ args: { present: true }, result: { text: 'x' } }, { args: { present: false }, result: 'null' }],
  },
  {
    id: 'is-null-text',
    params: [{ name: 'm', type: 'maybe-text' }],
    returns: 'bool',
    body: 'match m { null => true, text(_) => false }',
    examples: [{ args: { m: 'null' }, result: true }, { args: { m: { text: 'x' } }, result: false }],
  },
  {
    id: 'author-name',
    description: 'eval of a reference followed one hop: the name of the record the author field refers to, through a lookup that covers the author field; the string uncovered when evaluation fails.',
    params: [{ name: 'record', type: 'map<string, value>' }, { name: 'lookup', type: 'map<string, map<string, map<string, value>>>' }],
    returns: 'value',
    let: [{ name: 'env', expr: ENV }, { name: 'follow', expr: THROUGH }],
    body: "match eval(rule-language, follow, env, lookup) { Ok(v) => v, Err(_) => value.Str('uncovered') }",
    examples: [
      { description: 'The target exists.', args: { record: { author: { Ref: 7 } }, lookup: { author: { 7: { name: { Str: 'Ada' } } } } }, result: { Str: 'Ada' } },
      { description: 'The lookup covers the field but holds no such record: null.', args: { record: { author: { Ref: 8 } }, lookup: { author: { 7: { name: { Str: 'Ada' } } } } }, result: 'Null' },
      { description: 'An unset reference is null.', args: { record: {}, lookup: { author: {} } }, result: 'Null' },
      { description: 'A lookup that does not cover the field is an evaluation error.', args: { record: { author: { Ref: 7 } }, lookup: {} }, result: { Str: 'uncovered' } },
    ],
  },
  {
    id: 'author-name-unfollowed',
    description: 'The same without a lookup: following a reference is an evaluation error.',
    params: [{ name: 'record', type: 'map<string, value>' }],
    returns: 'value',
    let: [{ name: 'env', expr: ENV }, { name: 'follow', expr: THROUGH }],
    body: "match eval(rule-language, follow, env) { Ok(v) => v, Err(_) => value.Str('uncovered') }",
    examples: [
      { description: 'A set reference cannot be followed without a lookup.', args: { record: { author: { Ref: 7 } } }, result: { Str: 'uncovered' } },
      { description: 'An unset reference is null, with nothing to follow.', args: { record: {} }, result: 'Null' },
    ],
  },
  {
    id: 'sort-values',
    description: 'Values as the kernel orders them (Value derives Ord): by variant in the order Null, Bool, Int, Str, Time, Ref, List, and a list item by item.',
    params: [{ name: 'values', type: 'list<value>' }],
    returns: 'list<value>',
    body: 'sortBy(v in values, v)',
    examples: [
      { description: 'Across variants.', args: { values: [{ Str: 'a' }, { Int: 5 }, 'Null', { List: [] }, { Bool: true }, { Time: 1 }, { Ref: 2 }, { Bool: false }] }, result: ['Null', { Bool: false }, { Bool: true }, { Int: 5 }, { Str: 'a' }, { Time: 1 }, { Ref: 2 }, { List: [] }] },
      { description: 'Lists item by item: a prefix before the longer list.', args: { values: [{ List: [{ Int: 1 }, { Int: 2 }] }, { List: [{ Int: 1 }] }, { List: [] }, { List: [{ Int: 0 }, { Int: 9 }] }] }, result: [{ List: [] }, { List: [{ Int: 0 }, { Int: 9 }] }, { List: [{ Int: 1 }] }, { List: [{ Int: 1 }, { Int: 2 }] }] },
    ],
  },
  {
    id: 'sort-lists',
    description: 'Lists of numbers ordered lexicographically.',
    params: [{ name: 'lists', type: 'list<list<u64>>' }],
    returns: 'list<list<u64>>',
    body: 'sortBy(l in lists, l)',
    examples: [{ args: { lists: [[1, 2], [1], [], [0, 9], [10]] }, result: [[], [0, 9], [1], [1, 2], [10]] }],
  },
];

const CONTRACTS = [
  { id: 'view-home', name: 'Home view', realisation: 'generated', exposure: 'local', auth: { scheme: 'in-process' }, outputs: [{ name: 'title', type: 'string' }] },
  {
    id: 'save-note', name: 'Save a note', realisation: 'generated', policyDefault: 'allow', exposure: 'public', tenantScope: 'request', auth: { scheme: 'session', csrf: true, origin: true, requires: ['notes-write'] },
    binding: { protocol: 'http', method: 'POST', path: '/api/notes', suppliedBy: { tenant: 'route', context: 'session' } },
    inputs: [{ name: 'tenant', type: 'string' }, { name: 'context', type: 'string' }, { name: 'title', type: 'string' }],
    outputs: [{ name: 'ok', type: 'bool' }],
  },
];

/** @param {(d: any) => void} [mutate] @param {{generation?: boolean}} [opts] */
export function spec(mutate = () => {}, { generation = true } = {}) {
  const d = JSON.parse(functionsSpec(undefined, { generation }));
  d.types.push(...structuredClone(TYPES));
  d.functions.push(...structuredClone(FUNCTIONS));
  d.contracts = [...(d.contracts ?? []), ...structuredClone(CONTRACTS)];
  d.screens = [{ id: 'home', name: 'Front page', route: '/', viewModel: 'view-home', kind: 'home', title: 'Notes', auth: 'none' }];
  d.forms = [{
    id: 'f-save', screen: 'home', contract: 'save-note', submitLabel: 'Save',
    fields: [{ name: 'title', input: 'title', label: 'Title', control: 'text' }],
    onSuccess: { toast: 'Saved.' }, onError: { show: 'inline' },
  }];
  // Saving a note is public, so it names the capability a call needs; a core capability a tenant role confers is enough.
  d.capabilities = [{ id: 'notes-write', name: 'Write notes', core: true }];
  d.roles = [{ id: 'writer', name: 'Writer', level: 'tenant', holders: ['person'], capabilities: ['notes-write'] }];
  d.errorMessages = [{ id: 'em-default', on: 'error', text: '${error.message}', fallback: 'That did not work.' }];
  d.actions = [{ id: 'a-save', screen: 'home', label: 'Save the draft', contract: 'save-note', arguments: { title: "'Draft'" }, onSuccess: { toast: 'Saved.' }, onError: { show: 'toast' } }];
  mutate(d);
  return JSON.stringify(d, null, 2);
}

/** @param {any} d @param {string} id */
const type = (d, id) => d.types.find((/** @type {any} */ t) => t.id === id);
/** @param {any} d @param {string} id */
const fn = (d, id) => d.functions.find((/** @type {any} */ f) => f.id === id);
/** @param {any} d @param {string} id */
const ct = (d, id) => d.contracts.find((/** @type {any} */ c) => c.id === id);

/**
 * Each rule, a mutation that breaks it exactly once, and the code it reports, with and without system.generation.
 * @type {[string, string, (d: any) => void][]}
 */
export const FIXTURES = [
  ['an untagged union with a tagField', 'type.encoding', (d) => { type(d, 'plain-json').encoding.tagField = 'type'; }],
  ['an untagged union with a variantCase', 'type.encoding', (d) => { type(d, 'plain-json').encoding.variantCase = 'snake_case'; }],
  ['an untagged union with two variants written as one shape', 'type.encoding', (d) => { type(d, 'plain-json').variants.push({ name: 'Flag', newtype: true, fields: [{ name: 'value', type: 'bool' }] }); }],
  ['an untagged union with two unit variants', 'type.encoding', (d) => { type(d, 'plain-json').variants.push({ name: 'Nothing' }); }],
  ['an untagged union whose json variant is not the last', 'type.encoding', (d) => { type(d, 'plain-json').variants.unshift({ name: 'Any', newtype: true, fields: [{ name: 'value', type: 'json' }] }); }],
  ['a supplied input the contract does not have', 'contract.supplied-by', (d) => { ct(d, 'save-note').binding.suppliedBy.session = 'session'; }],
  ['an input supplied by something other than the route or session', 'contract.supplied-by', (d) => { ct(d, 'save-note').inputs.push({ name: 'locale', type: 'string', optional: true }); ct(d, 'save-note').binding.suppliedBy.locale = 'cookie'; }],
  ['a form field filling an input the session supplies', 'form.supplied-input', (d) => { d.forms[0].fields.push({ name: 'context', input: 'context', label: 'Context', control: 'text' }); }],
  ['a form argument for an input the route supplies', 'form.supplied-input', (d) => { d.forms[0].arguments = { tenant: "'acme'" }; }],
  ['an action argument for an input the route supplies', 'action.supplied-input', (d) => { d.actions[0].arguments.tenant = "'acme'"; }],
  ['a null where a string is expected', 'function.expr-type', (d) => { fn(d, 'empty-block').body = 'view-block{kind: null, params: null}'; }],
  ['a null where a bool is expected', 'function.expr-type', (d) => { fn(d, 'blank-view').body = 'if null then blob else null'; }],
  ['an eval whose lookup is not a map of maps of record scopes', 'function.expr-type', (d) => { fn(d, 'author-name').params[1].type = 'map<string, value>'; }],
  ['an eval with five arguments', 'function.expr-type', (d) => { fn(d, 'author-name').body = fn(d, 'author-name').body.replace('env, lookup)', 'env, lookup, lookup)'); }],
  ['a sortBy by a map', 'function.expr-type', (d) => { d.functions.push({ id: 'sort-maps', params: [{ name: 'maps', type: 'list<map<string, u64>>' }], returns: 'list<map<string, u64>>', body: 'sortBy(m in maps, m)', examples: [{ args: { maps: [] }, result: [] }] }); }],
  ['a sortBy by a json value', 'function.expr-type', (d) => { d.functions.push({ id: 'sort-blocks', params: [{ name: 'blocks', type: 'list<view-block>' }], returns: 'list<view-block>', body: 'sortBy(b in blocks, b.params)', examples: [{ args: { blocks: [] }, result: [] }] }); }],
  ['a lexicographic order example that is wrong', 'function.example-failed', (d) => { fn(d, 'sort-lists').examples[0].result = [[], [1], [0, 9], [1, 2], [10]]; }],
  ['a reference lookup example that is wrong', 'function.example-failed', (d) => { fn(d, 'author-name').examples[0].result = { Str: 'Grace' }; }],
];
