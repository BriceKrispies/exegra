// Parsing and checking the expression text of the typed sections (src/core/layer-expr.js, WG-5060):
// the grammar of the tenant rule language, and the scope a text is written in.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { checkExpressionText, expressionScope, fieldMapOf, productContext } from '../../src/core/layer-expr.js';

const tier = { id: 'p__tier', fields: { name: { ty: 'Str' }, points: { ty: 'Int' }, owner: { ty: { Ref: { target: 'p__member', 'on-delete': 'Restrict' } } }, tags: { ty: { List: 'Str' } } } };
const member = { id: 'p__member', fields: { email: { ty: 'Str' } } };
const items = [{ section: 'objects', id: 'p__tier', value: tier }, { section: 'objects', id: 'p__member', value: member }, { section: 'roles', id: 'p__boss', value: {} }];
const ctx = productContext(/** @type {any} */ ({ entities: new Map([['member', { id: 'member', kind: 'role' }]]) }), items);
const env = (/** @type {any} */ scope) => ({ ...scope, roles: ctx.roles, objects: ctx.objects });
const own = env({ fields: fieldMapOf(tier), params: new Set(['limit']) });
const check = (/** @type {string} */ text) => checkExpressionText(text, own);

test('texts of the language are accepted', () => {
  for (const ok of [
    "record.name == 'gold' and record.points >= 10", 'not record.points < 3 or true', "record.owner.email == 'a'", 'record.$id == ref(3)',
    'param.limit > 1', 'now > time(5)', 'principal == record.$created_by', 'has_role(member) or has_role(p__boss)', "contains(record.tags, 'x')", "record.name in ['a', 'b']",
    'if(record.points > 1, 1, 2) == 1', 'is_null(record.owner)', "starts_with(lower(record.name), 'g')", 'len(record.tags) > 0', 'record.points == null', '(true)',
  ]) assert.equal(check(ok), null, ok);
});

test('a name or call the language lacks and malformed text is layer.expr-syntax with its position', () => {
  const at = (/** @type {string} */ t) => { const p = check(t); return p && [p.code, p.pos]; };
  assert.deepEqual(at('balance(record.points) > 1'), ['layer.expr-syntax', 0]);
  assert.deepEqual(at('record.points + 1'), ['layer.expr-syntax', 14]);
  assert.deepEqual(at('record.name == "gold"'), ['layer.expr-syntax', 15]);
  assert.deepEqual(at("record.name == 'gold"), ['layer.expr-syntax', 15]);
  assert.deepEqual(at('record.points >'), ['layer.expr-syntax', 15]);
  assert.deepEqual(at('(record.points > 1'), ['layer.expr-syntax', 18]);
  assert.deepEqual(at('record.points > 1 2'), ['layer.expr-syntax', 18]);
  assert.deepEqual(at('[record.points]'), ['layer.expr-syntax', 1]);
  assert.deepEqual(at('len(record.name, 1)'), ['layer.expr-syntax', 15]);
});

test('fields hops params and roles are checked against the scope', () => {
  assert.deepEqual(check('record.colour == 1'), { code: 'layer.expr-unknown-field', pos: 7, message: 'unknown field colour; the object type has the fields name, points, owner, tags' });
  assert.equal(check('record.owner.phone == null')?.code, 'layer.expr-unknown-field');
  assert.equal(check('record.nothing.email == null')?.code, 'layer.expr-unknown-field');
  assert.equal(check('record.Name == null')?.code, 'layer.expr-unknown-field', 'a name that is not a field identifier');
  assert.equal(check('param.other > 1')?.code, 'layer.expr-unknown-param');
  assert.equal(check('has_role(ghost)')?.code, 'layer.expr-unknown-role');
  assert.equal(check('record.name.email == 1')?.code, 'layer.expr-type', 'a hop through a text');
  assert.equal(check('record.tags.email == 1')?.code, 'layer.expr-type', 'a hop through a list of text');
});

test('shapes that the operator does not accept are layer.expr-type', () => {
  for (const bad of ['record.name == 1', 'record.name > 1', 'len(record.points) > 0', 'not record.points', 'record.points and true', "lower(record.points) == 'a'", 'record.points in record.points', 'if(record.points, 1, 2) == 1', "if(true, 1, 'a') == 1", 'contains(record.name, 1)', "starts_with(1, 'a')"]) {
    assert.equal(check(bad)?.code, 'layer.expr-type', bad);
  }
  assert.equal(check('record.name == record.points')?.message, 'cannot compare Str with Int');
});

test('the scope comes from the value that holds the text', () => {
  const names = (/** @type {any} */ scope) => [...(scope.fields ?? [])].map(([n]) => n);
  const objectScope = expressionScope(ctx, 'objects', tier, ['fields', 'x', 'default']);
  assert.deepEqual(names(objectScope), ['name', 'points', 'owner', 'tags']);
  assert.equal(objectScope.params?.size, 0);
  assert.deepEqual(names(expressionScope(ctx, 'policies', { resource: { Object: 'p__member' } }, ['condition'])), ['email']);
  assert.equal(expressionScope(ctx, 'policies', { resource: 'AnyObject' }, ['condition']).fields, null, 'a policy over no one object type: any field');
  assert.deepEqual(names(expressionScope(ctx, 'segments', { 'subject-type': 'p__member' }, ['predicate'])), ['email']);
  const created = expressionScope(ctx, 'triggers', { on: { RecordCreated: { object: 'p__tier' } } }, ['condition']);
  assert.equal(created.fields?.has('points'), true);
  assert.deepEqual([...(created.params ?? [])], ['seq', 'at', 'hop']);
  const posted = expressionScope(ctx, 'triggers', { on: { LedgerPosted: { unit: 'p__u' } } }, ['condition']);
  assert.equal(posted.fields?.size, 0, 'only a record event binds a record');
  assert.equal(posted.params?.has('balance_before'), true);
  const op = expressionScope(ctx, 'operations', { inputs: [{ name: 'tier' }], subject: { object: 'p__tier', input: 'tier' } }, ['conditions', 0, 'expr']);
  assert.equal(op.fields?.has('points'), true);
  assert.deepEqual([...(op.params ?? [])], ['tier']);
  assert.equal(expressionScope(ctx, 'operations', { inputs: [] }, ['steps']).fields?.size, 0, 'an operation without a subject has no record');
  assert.deepEqual(expressionScope(ctx, 'automations', {}, ['run-key']), { fields: null, params: null });
});
