// Parsing and checking the expression text of the typed sections (src/core/layer-expr.js, WG-5060):
// the grammar of the tenant rule language, and the scope a text is written in.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { checkExpressionText, typeExpressionText, expressionScope, fieldMapOf, productContext } from '../../src/core/layer-expr.js';

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

// Syntax errors and their positions.
// @evidence product-layers-expressions
test('a name or call the language lacks and malformed text is layer.expr-syntax with its position', () => {
  const at = (/** @type {string} */ t) => { const p = check(t); return p && [p.code, p.pos]; };
  assert.deepEqual(at('balance(record.points) > 1'), ['layer.expr-syntax', 0]);
  assert.deepEqual(at('record.points % 1'), ['layer.expr-syntax', 14]);
  assert.deepEqual(at('record.points +'), ['layer.expr-syntax', 15]);
  assert.deepEqual(at('- 1 > 0'), ['layer.expr-syntax', 0]);
  assert.deepEqual(at('-record.points > 0'), ['layer.expr-syntax', 0]);
  assert.deepEqual(at('ms_between(now) > 0'), ['layer.expr-syntax', 14]);
  assert.deepEqual(at('days(1, 2) > 0'), ['layer.expr-syntax', 6]);
  assert.deepEqual(at('1 < 2 < 3'), ['layer.expr-syntax', 6]);
  assert.deepEqual(at('record.name == "gold"'), ['layer.expr-syntax', 15]);
  assert.deepEqual(at("record.name == 'gold"), ['layer.expr-syntax', 15]);
  assert.deepEqual(at('record.points >'), ['layer.expr-syntax', 15]);
  assert.deepEqual(at('(record.points > 1'), ['layer.expr-syntax', 18]);
  assert.deepEqual(at('record.points > 1 2'), ['layer.expr-syntax', 18]);
  assert.deepEqual(at('[record.points]'), ['layer.expr-syntax', 1]);
  assert.deepEqual(at('len(record.name, 1)'), ['layer.expr-syntax', 15]);
});

// Unknown fields, hops, params and roles.
// @evidence product-layers-expressions
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

// Shapes an operator does not accept.
// @evidence product-layers-expressions
test('shapes that the operator does not accept are layer.expr-type', () => {
  for (const bad of ['record.name == 1', 'record.name > 1', 'len(record.points) > 0', 'not record.points', 'record.points and true', "lower(record.points) == 'a'", 'record.points in record.points', 'if(record.points, 1, 2) == 1', "if(true, 1, 'a') == 1", 'contains(record.name, 1)', "starts_with(1, 'a')"]) {
    assert.equal(check(bad)?.code, 'layer.expr-type', bad);
  }
  assert.equal(check('record.name == record.points')?.message, 'cannot compare Str with Int');
});

// The scope of a text: the object type of a policy, segment, trigger or operation, the params an event or an operation binds.
// @evidence product-layers-expressions
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

/** The shape of a text, or the code and message of its problem. @param {string} text */
const typed = (text) => { const r = typeExpressionText(text, own); return r.problem ? [r.problem.code, r.problem.message] : r.shape; };

// Each of the nine operators is accepted.
// @evidence product-layers-expressions
test('each of the nine operators is accepted and the bare result of arithmetic is an expression', () => {
  const accepted = /** @type {[string, string][]} */ ([
    ['record.points + 1', 'int'], ['record.points - 1', 'int'], ['record.points * 2', 'int'],
    ['now + 1', 'time'], ['now - 1', 'time'], ['now - days(1)', 'time'], ['time(5) + hours(2)', 'time'],
    ['ms_between(time(1), now)', 'int'], ['days(2)', 'int'], ['hours(2)', 'int'], ['minutes(record.points)', 'int'],
    ["concat(record.name, 'x')", 'str'], ['text(record.points)', 'str'], ['text(now)', 'str'], ['text(ref(1))', 'str'], ['text(true)', 'str'], ["text('a')", 'str'],
    ['ms_between(now, now + days(90)) <= days(90)', 'bool'], ["concat('n', text(record.points)) == 'n1'", 'bool'], ['param.limit + 1', 'any'],
  ]);
  for (const [text, shape] of accepted) assert.equal(typed(text), shape, text);
});

// One wrong operand per operator is layer.expr-type with the stated message.
// @evidence product-layers-expressions
test('one operand of the wrong shape per operator is layer.expr-type with the kernel message', () => {
  const refused = /** @type {[string, string][]} */ ([
    ["'a' + 1", '+ does not accept a Str operand'], ['1 + time(5)', '+ does not accept a Time operand'],
    ['true - 1', '- does not accept a Bool operand'], ["now - 'a'", '- does not accept a Str operand'],
    ['now * 2', '* does not accept a Time operand'], ['2 * now', '* does not accept a Time operand'],
    ['ms_between(1, now)', 'ms_between does not accept a Int operand'], ["ms_between(now, 'a')", 'ms_between does not accept a Str operand'],
    ["days('a')", 'days does not accept a Str operand'], ['hours(now)', 'hours does not accept a Time operand'], ['minutes(true)', 'minutes does not accept a Bool operand'],
    ['concat(1, record.name)', 'concat does not accept a Int operand'], ["concat('a', 1)", 'concat does not accept a Int operand'],
    ['text([1])', 'text does not accept a List operand'], ['text(record.tags)', 'text does not accept a List operand'],
  ]);
  for (const [text, message] of refused) assert.deepEqual(typed(text), ['layer.expr-type', message], text);
});

// Time + Time is refused.
// @evidence product-layers-expressions
test('Time plus Time and Time minus Time are refused: ms_between gives the difference', () => {
  assert.deepEqual(typed('now + now'), ['layer.expr-type', '+ does not accept a Time operand']);
  assert.deepEqual(typed('now - time(1)'), ['layer.expr-type', '- does not accept a Time operand']);
  assert.equal(typed('ms_between(time(1), now)'), 'int');
  assert.equal(check('now + now')?.pos, 6, 'the position is the right operand');
});

// The sign rule for a minus before a digit.
// @evidence product-layers-expressions
test('a minus before a digit is a sign only where no operand ends before it', () => {
  for (const literal of ['-1 < record.points', '2 * -3 > 0', 'record.points in [1, -1]', 'is_null(-1)', '1 - -1 > 0', 'record.points == -1', 'not -1 < 0', 'time(-5) < now', 'record.points > 1 and -1 < 0', 'if(true, -1, 2) == 0']) {
    assert.equal(check(literal), null, literal);
  }
  assert.equal(typed('record.points-1'), 'int', 'a name before a minus: subtraction');
  assert.equal(typed('record.points -1'), 'int');
  assert.equal(typed('1 -1'), 'int');
  assert.equal(typed('(1) -1'), 'int');
  assert.deepEqual(typed("'a' -1"), ['layer.expr-type', '- does not accept a Str operand']);
  assert.equal(check('-1 -1 > 0'), null, 'a literal, then a subtraction');
  assert.equal(typed('2*-3'), 'int');
  assert.equal(typed('1 - -1'), 'int');
  assert.equal(check('- 1 > 0')?.code, 'layer.expr-syntax', 'a symbol minus with no left operand');
  assert.equal(check('1 + - 1 > 0')?.code, 'layer.expr-syntax');
  assert.equal(check('99999999999999999999 > 1')?.code, 'layer.expr-syntax', 'out of range');
  assert.equal(check('-9223372036854775808 < record.points'), null, 'the smallest integer');
});

// Precedence and associativity.
// @evidence product-layers-expressions
test('precedence binds the product over the sum over a comparison', () => {
  assert.equal(typed('time(1) + 1 * 2'), 'time', 'a product binds tighter than the sum');
  assert.deepEqual(typed('time(1) * 1 + 2'), ['layer.expr-type', '* does not accept a Time operand']);
  assert.equal(typed('time(1) + 1 - 2'), 'time', 'left to right');
  assert.deepEqual(typed('1 + time(1) - 2'), ['layer.expr-type', '+ does not accept a Time operand']);
  assert.equal(typed('1 + 2 < 4 * 2'), 'bool', 'sums are the operands of a comparison');
  assert.equal(typed('1 + 2 in [3]'), 'bool');
  assert.equal(typed('not 1 + 1 > 1 or true'), 'bool');
  assert.equal(typed('1 + 1 == 2 and 3 - 1 == 2'), 'bool');
  assert.equal(check('1 < 2 == true')?.code, 'layer.expr-syntax', 'one comparison only');
  assert.equal(typed('(1 + 2) * 3'), 'int');
});

// A step reads the id of an earlier create step as a param.
// @evidence product-layers-expressions
test('a step reads the id of an earlier create step as a parameter', () => {
  const item = { inputs: [{ name: 'tier' }], steps: [{ CreateRecord: { id: 'made', object: 'p__tier' } }, { PostLedger: { id: 'fund', scope: 'text(param.made)' } }, { CreateRecord: { id: 'later' } }] };
  const at = (/** @type {number} */ n) => [...(expressionScope(ctx, 'operations', item, ['steps', n, 'x']).params ?? [])];
  assert.deepEqual(at(0), ['tier'], 'not its own id');
  assert.deepEqual(at(1), ['tier', 'made']);
  assert.deepEqual(at(2), ['tier', 'made'], 'a post step binds nothing');
  assert.deepEqual([...(expressionScope(ctx, 'operations', item, ['conditions', 0, 'expr']).params ?? [])], ['tier'], 'a condition runs before every step');
});
