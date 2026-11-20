// Fixtures of the language construct (WG-4929): a specification that states the Strata kernel's tenant rule
// language as it is today (crates/kernel/src/expr.rs, crates/substrate/src/syntax.rs) and is ready to generate
// from, and for each rule a mutation that breaks exactly that rule.

const ATTRS = [
  { name: '$id', shape: 'ref' },
  { name: '$version', shape: 'int' },
  { name: '$created_by', shape: 'str' },
  { name: '$created_at', shape: 'time' },
  { name: '$updated_at', shape: 'time' },
];

const expr = (/** @type {string} */ name) => ({ name, type: 'expr' });
const cmp = (/** @type {string} */ name, /** @type {string} */ value, /** @type {string} */ token, /** @type {any[]} */ operands) => (
  { name, variant: 'Cmp', case: { field: 'op', value }, syntax: { form: 'infix', token, precedence: 4, assoc: 'none' }, operands, result: 'bool', nulls: 'propagate', primitive: name });
const ORDERED = ['int', 'time', 'str'];
const call = (/** @type {string} */ name, /** @type {string} */ variant, /** @type {string} */ token, /** @type {any[]} */ operands, /** @type {string} */ result, nulls = 'propagate', primitive = name) => (
  { name, variant, syntax: { form: 'call', token }, operands, result, nulls, primitive });
const arith = (/** @type {string} */ name, /** @type {string} */ value, /** @type {string} */ token, /** @type {number} */ precedence, /** @type {any[]} */ operands, /** @type {string} */ result, /** @type {string} */ primitive) => (
  { name, variant: 'Arith', case: { field: 'op', value }, syntax: { form: 'infix', token, precedence, assoc: 'left' }, operands, result, nulls: 'propagate', primitive });
const duration = (/** @type {string} */ name, /** @type {string} */ value, /** @type {string} */ primitive) => (
  { name, variant: 'Duration', case: { field: 'unit', value }, syntax: { form: 'call', token: name }, operands: ['int'], result: 'int', nulls: 'propagate', primitive });
const lit = (/** @type {string} */ name, /** @type {string} */ value, /** @type {string} */ token, /** @type {string} */ result, primitive = 'literal') => (
  { name, variant: 'Lit', case: { field: 'value', value }, syntax: { form: 'literal', token }, operands: [], result, nulls: 'total', primitive });

/** @param {(d: any) => void} [mutate] @param {{generation?: boolean}} [opts] */
export function spec(mutate = () => {}, { generation = true } = {}) {
  const d = {
    exegra: '0.1',
    system: { id: 'kernel', name: 'Kernel', ...(generation ? { generation: { target: 'rust' } } : {}) },
    components: [{ id: 'svc', name: 'Service', category: 'computational' }],
    types: [
      // The kernel's RoleId: HasRole holds an id over string, which the evaluator reads as a string (WG-4962).
      { id: 'role-id', name: 'Role id', kind: 'id', repr: 'string' },
      { id: 'cmp-op', name: 'Comparison', kind: 'enum', values: ['Eq', 'Ne', 'Lt', 'Le', 'Gt', 'Ge'] },
      { id: 'scope', name: 'Scope', kind: 'enum', values: ['Record', 'Old', 'New'] },
      { id: 'arith-op', name: 'Arithmetic', kind: 'enum', values: ['Add', 'Sub', 'Mul'] },
      { id: 'duration-unit', name: 'Duration unit', kind: 'enum', values: ['Days', 'Hours', 'Minutes'] },
      { id: 'value', name: 'Value', kind: 'union', variants: [
        { name: 'Null' },
        { name: 'Bool', newtype: true, fields: [{ name: 'value', type: 'bool' }] },
        { name: 'Int', newtype: true, fields: [{ name: 'value', type: 'i64' }] },
        { name: 'Str', newtype: true, fields: [{ name: 'value', type: 'string' }] },
        { name: 'Time', newtype: true, fields: [{ name: 'value', type: 'i64' }] },
        { name: 'Ref', newtype: true, fields: [{ name: 'value', type: 'u64' }] },
        { name: 'List', newtype: true, fields: [{ name: 'value', type: 'list<value>' }] },
      ] },
      { id: 'expr', name: 'Expression', kind: 'union', variants: [
        { name: 'Lit', newtype: true, fields: [{ name: 'value', type: 'value' }] },
        { name: 'Var', fields: [{ name: 'scope', type: 'scope' }, { name: 'name', type: 'string' }] },
        { name: 'Through', fields: [{ name: 'scope', type: 'scope' }, { name: 'field', type: 'string' }, { name: 'target', type: 'string' }] },
        { name: 'Param', newtype: true, fields: [{ name: 'name', type: 'string' }] },
        { name: 'Now' },
        { name: 'Principal' },
        { name: 'HasRole', newtype: true, fields: [{ name: 'role', type: 'role-id' }] },
        { name: 'Not', newtype: true, fields: [expr('inner')] },
        { name: 'And', newtype: true, fields: [{ name: 'items', type: 'list<expr>' }] },
        { name: 'Or', newtype: true, fields: [{ name: 'items', type: 'list<expr>' }] },
        { name: 'Cmp', fields: [{ name: 'op', type: 'cmp-op' }, expr('left'), expr('right')] },
        { name: 'In', fields: [expr('item'), expr('list')] },
        { name: 'IsNull', newtype: true, fields: [expr('inner')] },
        { name: 'Len', newtype: true, fields: [expr('inner')] },
        { name: 'Lower', newtype: true, fields: [expr('inner')] },
        { name: 'Contains', fields: [expr('haystack'), expr('needle')] },
        { name: 'StartsWith', fields: [expr('text'), expr('prefix')] },
        { name: 'IsSlug', newtype: true, fields: [expr('inner')] },
        { name: 'If', fields: [expr('cond'), expr('then'), expr('otherwise')] },
        // Checked arithmetic, time arithmetic and text (Strata D-6540 to D-6543).
        { name: 'Arith', fields: [{ name: 'op', type: 'arith-op' }, expr('left'), expr('right')] },
        { name: 'MsBetween', fields: [expr('from'), expr('to')] },
        { name: 'Duration', fields: [{ name: 'unit', type: 'duration-unit' }, expr('amount')] },
        { name: 'Concat', fields: [expr('left'), expr('right')] },
        { name: 'Text', newtype: true, fields: [expr('inner')] },
      ] },
    ],
    languages: [{
      id: 'rule-language',
      name: 'Tenant rule language',
      ast: 'expr',
      values: 'value',
      shapes: ['bool', 'int', 'str', 'time', 'ref', 'list', 'any'],
      anyShape: 'any',
      scopes: [
        { name: 'record', kind: 'record-scope', value: 'Record', attributes: ATTRS },
        { name: 'old', kind: 'record-scope', value: 'Old', attributes: ATTRS },
        { name: 'new', kind: 'record-scope', value: 'New', attributes: ATTRS },
        { name: 'param', kind: 'param' },
        { name: 'now', kind: 'constant' },
        { name: 'principal', kind: 'constant' },
        { name: 'has_role', kind: 'role-test' },
      ],
      operators: [
        lit('lit-null', 'Null', 'null', 'any'),
        lit('lit-bool', 'Bool', 'bool', 'bool'),
        lit('lit-int', 'Int', 'int', 'int'),
        lit('lit-str', 'Str', 'string', 'str'),
        lit('lit-time', 'Time', 'time', 'time'),
        lit('lit-ref', 'Ref', 'ref', 'ref'),
        lit('lit-list', 'List', 'list', 'list', 'list-literal'),
        { name: 'var', variant: 'Var', syntax: { form: 'scope' }, operands: [], nulls: 'total', primitive: 'var' },
        { name: 'through', variant: 'Through', syntax: { form: 'scope' }, operands: [], nulls: 'total', primitive: 'through' },
        { name: 'param', variant: 'Param', syntax: { form: 'scope', token: 'param' }, operands: [], result: 'any', nulls: 'total', primitive: 'param' },
        { name: 'now', variant: 'Now', syntax: { form: 'scope', token: 'now' }, operands: [], result: 'time', nulls: 'total', primitive: 'now' },
        { name: 'principal', variant: 'Principal', syntax: { form: 'scope', token: 'principal' }, operands: [], result: 'str', nulls: 'total', primitive: 'principal' },
        { name: 'has-role', variant: 'HasRole', syntax: { form: 'scope', token: 'has_role' }, operands: [], result: 'bool', nulls: 'total', primitive: 'has-role' },
        { name: 'or', variant: 'Or', syntax: { form: 'keyword-infix', token: 'or', precedence: 1, assoc: 'n-ary' }, operands: ['bool'], result: 'bool', nulls: 'kleene-or', primitive: 'or3' },
        { name: 'and', variant: 'And', syntax: { form: 'keyword-infix', token: 'and', precedence: 2, assoc: 'n-ary' }, operands: ['bool'], result: 'bool', nulls: 'kleene-and', primitive: 'and3' },
        { name: 'not', variant: 'Not', syntax: { form: 'prefix-word', token: 'not', precedence: 3 }, operands: ['bool'], result: 'bool', nulls: 'kleene-not', primitive: 'not3' },
        cmp('eq', 'Eq', '==', ['any', 'any']),
        cmp('ne', 'Ne', '!=', ['any', 'any']),
        cmp('lt', 'Lt', '<', [ORDERED, ORDERED]),
        cmp('le', 'Le', '<=', [ORDERED, ORDERED]),
        cmp('gt', 'Gt', '>', [ORDERED, ORDERED]),
        cmp('ge', 'Ge', '>=', [ORDERED, ORDERED]),
        { name: 'in', variant: 'In', syntax: { form: 'keyword-infix', token: 'in', precedence: 4, assoc: 'none' }, operands: ['any', 'list'], result: 'bool', nulls: 'propagate', primitive: 'in-list' },
        call('is-null', 'IsNull', 'is_null', ['any'], 'bool', 'total'),
        call('len', 'Len', 'len', [['str', 'list']], 'int'),
        call('lower', 'Lower', 'lower', ['str'], 'str'),
        call('contains', 'Contains', 'contains', [['str', 'list'], 'any'], 'bool'),
        call('starts-with', 'StartsWith', 'starts_with', ['str', 'str'], 'bool'),
        call('is-slug', 'IsSlug', 'is_slug', ['str'], 'bool'),
        call('if', 'If', 'if', ['bool', 'any', 'any'], 'operand:2', 'null-is-false'),
        arith('add', 'Add', '+', 5, [['int', 'time'], 'int'], 'operand:1', 'add-checked'),
        arith('sub', 'Sub', '-', 5, [['int', 'time'], 'int'], 'operand:1', 'sub-checked'),
        arith('mul', 'Mul', '*', 6, ['int', 'int'], 'int', 'mul-checked'),
        call('ms-between', 'MsBetween', 'ms_between', ['time', 'time'], 'int', 'propagate', 'time-difference'),
        duration('days', 'Days', 'days-ms'),
        duration('hours', 'Hours', 'hours-ms'),
        duration('minutes', 'Minutes', 'minutes-ms'),
        call('concat', 'Concat', 'concat', ['str', 'str'], 'str', 'propagate', 'concat-checked'),
        call('text', 'Text', 'text', [['int', 'time', 'ref', 'bool', 'str']], 'str', 'propagate', 'to-text'),
      ],
    }],
  };
  mutate(d);
  return JSON.stringify(d, null, 2);
}

/** @param {any} d */
const lang = (d) => d.languages[0];
/** @param {any} d @param {string} name */
const op = (d, name) => lang(d).operators.find((/** @type {any} */ o) => o.name === name);
/** @param {any} d @param {string} name */
const scope = (d, name) => lang(d).scopes.find((/** @type {any} */ s) => s.name === name);
/** @param {any} d @param {string} name */
const variant = (d, name) => d.types.find((/** @type {any} */ t) => t.id === 'expr').variants.find((/** @type {any} */ v) => v.name === name);

/**
 * Each rule, a mutation that breaks it exactly once, and the code it reports. Validation errors with and without
 * system.generation.
 * @type {[string, string, (d: any) => void][]}
 */
export const FIXTURES = [
  ['two operators of one name', 'language.operator-duplicate', (d) => { op(d, 'ne').name = 'eq'; }],
  ['two operators on one symbol', 'language.token-clash', (d) => { op(d, 'ne').syntax.token = '=='; }],
  ['a function named like a scope', 'language.token-clash', (d) => { op(d, 'lower').syntax.token = 'now'; }],
  ['a function named like a literal word', 'language.token-clash', (d) => { op(d, 'lower').syntax.token = 'true'; }],
  ['an infix operator on a word', 'language.syntax', (d) => { op(d, 'eq').syntax.token = 'equals'; }],
  ['a literal of an unknown form', 'language.syntax', (d) => { op(d, 'lit-int').syntax.token = 'float'; }],
  ['a list literal on the scalar literal primitive', 'language.syntax', (d) => { op(d, 'lit-list').primitive = 'literal'; }],
  ['a call on a primitive written only as infix', 'language.syntax', (d) => { op(d, 'contains').primitive = 'in-list'; op(d, 'contains').nulls = 'propagate'; }],
  ['a binary operator without a precedence', 'language.precedence', (d) => { delete op(d, 'and').syntax.precedence; }],
  ['two associativities at one level', 'language.precedence', (d) => { op(d, 'in').syntax.assoc = 'left'; }],
  ['a precedence on a call', 'language.precedence', (d) => { op(d, 'len').syntax.precedence = 5; }],
  ['a primitive outside the catalogue', 'language.primitive-unknown', (d) => { op(d, 'lower').primitive = 'upper'; }],
  ['a call with fewer operands than its primitive', 'language.arity', (d) => { op(d, 'len').operands = []; }],
  ['an AST variant with fewer expression fields than the operator', 'language.arity', (d) => { variant(d, 'Contains').fields.pop(); }],
  ['a result naming an operand that is not there', 'language.arity', (d) => { op(d, 'if').result = 'operand:4'; }],
  ['a result of an undeclared shape', 'language.shape-unknown', (d) => { op(d, 'len').result = 'integer'; }],
  ['an operand of an undeclared shape', 'language.shape-unknown', (d) => { op(d, 'lower').operands = ['string']; }],
  ['a system attribute of an undeclared shape', 'language.shape-unknown', (d) => { scope(d, 'old').attributes = [{ name: '$id', shape: 'id' }]; }],
  ['an operator stating other null handling than its primitive', 'language.nulls', (d) => { op(d, 'in').nulls = 'total'; }],
  ['two operators for one AST variant', 'language.variant', (d) => { lang(d).operators.push({ name: 'length', variant: 'Len', syntax: { form: 'call', token: 'length' }, operands: ['str'], result: 'int', nulls: 'propagate', primitive: 'len' }); }],
  ['an operator for a variant the AST does not have', 'language.variant', (d) => { lang(d).operators.push({ name: 'upper', variant: 'Upper', syntax: { form: 'call', token: 'upper' }, operands: ['str'], result: 'str', nulls: 'propagate', primitive: 'lower' }); }],
  ['a case that is not a value of its field', 'language.variant', (d) => { lang(d).operators.push({ ...cmp('like', 'Like', '=~', ['str', 'str']), primitive: 'eq' }); }],
  ['an AST that is not a union', 'language.variant', (d) => { lang(d).ast = 'cmp-op'; }],
  ['an operator reading a scope that is not declared', 'language.scope', (d) => { lang(d).scopes = lang(d).scopes.filter((/** @type {any} */ s) => s.name !== 'param'); }],
  ['attributes on a parameter scope', 'language.scope', (d) => { scope(d, 'param').attributes = [{ name: '$id', shape: 'ref' }]; }],
  ['two record scopes for one scope value', 'language.scope', (d) => { scope(d, 'new').value = 'Old'; }],
  ['a scope no operator reads', 'language.scope', (d) => { lang(d).scopes.push({ name: 'tenant', kind: 'constant' }); }],
];

/**
 * Readiness: each mutation leaves a gap that is an error only when system.generation is set.
 * @type {[string, string, (d: any) => void][]}
 */
export const READINESS_FIXTURES = [
  ['an AST variant without an operator', 'ready.language-variant-uncovered', (d) => { lang(d).operators = lang(d).operators.filter((/** @type {any} */ o) => o.name !== 'is-slug'); }],
  ['a case of a split variant without an operator', 'ready.language-variant-uncovered', (d) => { lang(d).operators = lang(d).operators.filter((/** @type {any} */ o) => o.name !== 'ge'); }],
  ['an operator without a primitive', 'ready.language-primitive-missing', (d) => { delete op(d, 'lower').primitive; delete op(d, 'lower').nulls; }],
];
