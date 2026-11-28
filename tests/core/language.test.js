import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { analyzeSpec } from '../../src/core/analyze.js';
import { readinessGaps } from '../../src/core/readiness.js';
import { LANGUAGE_PRIMITIVES, NULL_RULES, SYNTAX_FORMS, variantOperandCount } from '../../src/core/language.js';
import { spec, FIXTURES, READINESS_FIXTURES } from '../fixtures/language/fixtures.js';
import { evalLanguage } from '../../src/core/language-eval.js';
import { decodeValue } from '../../src/core/function-value.js';
import { typeStructure } from '../../src/core/codegen-model.js';

// The language construct (WG-4929, NC-2): a tenant expression language stated as data, with operators bound to a
// fixed primitive catalogue pinned to the Strata kernel.

const errors = (/** @type {any} */ r) => r.diagnostics.filter((/** @type {any} */ d) => d.severity === 'error');
const codes = (/** @type {any} */ ds) => ds.map((/** @type {any} */ d) => d.code);

// Two operators named alike: exactly one language.operator-duplicate error.
// @evidence language-construct-rules # two operators of one name is reported once as language.operator-duplicate
// Two infix operators on ==: exactly one language.token-clash error; further fixtures name a function like a scope and like a literal word.
// @evidence language-construct-rules # two operators on one symbol is reported once as language.token-clash
// An infix token that is a word: exactly one language.syntax error; further fixtures use an unknown literal form, the list form on the scalar literal primitive, and the call form on an infix-only primitive.
// @evidence language-construct-rules # an infix operator on a word is reported once as language.syntax
// A keyword-infix operator without precedence: exactly one language.precedence error; further fixtures mix associativities at one level and put a precedence on a call.
// @evidence language-construct-rules # a binary operator without a precedence is reported once as language.precedence
// A primitive not in the catalogue: exactly one language.primitive-unknown error.
// @evidence language-construct-rules # a primitive outside the catalogue is reported once as language.primitive-unknown
// A call with no operands over a one-operand primitive: exactly one language.arity error; further fixtures shorten the AST variant and name an operand beyond the last in the result.
// @evidence language-construct-rules # a call with fewer operands than its primitive is reported once as language.arity
// An undeclared result shape: exactly one language.shape-unknown error; further fixtures use an undeclared operand shape and attribute shape.
// @evidence language-construct-rules # a result of an undeclared shape is reported once as language.shape-unknown
// An operator stating total over a propagating primitive: exactly one language.nulls error.
// @evidence language-construct-rules # an operator stating other null handling than its primitive is reported once as language.nulls
// A second operator for one AST variant: exactly one language.variant error; further fixtures name a variant the AST lacks, a case outside its field, and an AST that is not a union.
// @evidence language-construct-rules # two operators for one AST variant is reported once as language.variant
// A param operator without a param scope: exactly one language.scope error; further fixtures put attributes on a param scope, give two record scopes one value, and declare a scope no operator reads.
// @evidence language-construct-rules # an operator reading a scope that is not declared is reported once as language.scope
// An operator without a primitive: no error without system.generation, one readiness gap, one error with it.
// @evidence language-construct-rules # an operator without a primitive is reported once as ready.language-primitive-missing only when generation is set
// The Strata kernel language stated as a language entity (24 AST variants, Cmp split by comparison, Arith by operator, Duration by unit and Lit by value kind) has no error and no readiness gap, with and without system.generation.
// @evidence language-construct-rules
test('the kernel rule language as it is today validates and has no readiness gap', () => {
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
      assert.deepEqual(codes(errors(r)), [code], r.diagnostics.map((/** @type {any} */ d) => `${d.code} ${d.message}`).join('\n'));
      assert.ok(errors(r)[0].loc && errors(r)[0].loc.line > 1);
    });
  }
}

for (const [title, code, mutate] of READINESS_FIXTURES) {
  test(`${title} is reported once as ${code} only when generation is set`, () => {
    const off = analyzeSpec(spec(mutate, { generation: false }));
    assert.deepEqual(codes(errors(off)), [], off.diagnostics.map((/** @type {any} */ d) => `${d.code} ${d.message}`).join('\n'));
    assert.deepEqual(codes(readinessGaps(/** @type {any} */ (off.model))), [code]);
    const on = analyzeSpec(spec(mutate, { generation: true }));
    assert.deepEqual(codes(errors(on)), [code], on.diagnostics.map((/** @type {any} */ d) => `${d.code} ${d.message}`).join('\n'));
  });
}

test('every language code has a negative fixture', () => {
  const want = ['language.operator-duplicate', 'language.token-clash', 'language.syntax', 'language.precedence', 'language.primitive-unknown', 'language.arity', 'language.shape-unknown', 'language.nulls', 'language.variant', 'language.scope'];
  const have = new Set(FIXTURES.map(([, code]) => code));
  assert.deepEqual(want.filter((c) => !have.has(c)), []);
  const ready = new Set(READINESS_FIXTURES.map(([, code]) => code));
  assert.deepEqual(['ready.language-variant-uncovered', 'ready.language-primitive-missing'].filter((c) => !ready.has(c)), []);
});

// The catalogue is exactly the 37 primitives, each with arity, forms, null handling, the kernel function it mirrors, its semantics and its static check.
// @evidence language-construct-rules
test('the primitive catalogue is the fixed set pinned to the kernel and each entry is complete', () => {
  assert.deepEqual(Object.keys(LANGUAGE_PRIMITIVES).sort(), [
    'add-checked', 'ancestor-of', 'and3', 'concat-checked', 'contains', 'days-ms', 'eq', 'ge', 'graphemes', 'gt', 'has-role', 'hours-ms', 'if', 'in-list',
    'is-emoji', 'is-null', 'is-slug', 'le', 'len', 'list-literal', 'literal', 'lower', 'lt', 'minutes-ms', 'mul-checked', 'ne', 'not3', 'now',
    'or3', 'param', 'principal', 'starts-with', 'sub-checked', 'through', 'time-difference', 'to-text', 'var',
  ]);
  for (const [name, p] of Object.entries(LANGUAGE_PRIMITIVES)) {
    assert.ok(NULL_RULES.includes(p.nulls), name);
    assert.ok(p.forms.length && p.forms.every((f) => SYNTAX_FORMS.includes(f)), name);
    assert.match(p.kernel, /crates\/kernel\/src\/expr\.rs/, name);
    assert.ok(p.semantics && p.check, name);
    assert.ok(p.arity === 'n' || Number.isInteger(p.arity), name);
    if (p.forms.includes('scope')) assert.ok(p.scope, name);
  }
});

// docs/model-and-format.md has a row for every primitive and names every language code.
// @evidence language-construct-rules
test('the format documentation states every primitive and every code', () => {
  const doc = fs.readFileSync(new URL('../../docs/model-and-format.md', import.meta.url), 'utf8');
  for (const name of Object.keys(LANGUAGE_PRIMITIVES)) assert.ok(doc.includes(`| \`${name}\` |`), `primitive ${name} has a row`);
  for (const [, code] of [...FIXTURES, ...READINESS_FIXTURES]) assert.ok(doc.includes(`\`${code}\``), `code ${code} is documented`);
});

// Strata's table for graphemes and is_emoji (crates/kernel/tests/text_rules.rs, CASES): each text, whether it is
// exactly one emoji, and its extended grapheme count. A text-default emoji (U+00A9, U+2764) is an emoji only with
// VS16 or a skin tone after it.
const EMOJI_CASES = [
  // emoji, one grapheme
  ['\u{1F600}', true, 1],
  ['\u{1F44D}', true, 1],
  ['\u{1F44D}\u{1F3FD}', true, 1],
  ['\u{1F468}\u{200D}\u{1F469}\u{200D}\u{1F467}', true, 1],
  ['\u{1F1EC}\u{1F1E7}', true, 1],
  ['1\u{FE0F}\u{20E3}', true, 1],
  ['1\u{20E3}', true, 1],
  ['*\u{FE0F}\u{20E3}', true, 1],
  ['#\u{FE0F}\u{20E3}', true, 1],
  ['\u{2764}\u{FE0F}', true, 1],
  ['\u{A9}\u{FE0F}', true, 1],
  ['\u{2122}\u{FE0F}', true, 1],
  ['\u{1F3F3}\u{FE0F}\u{200D}\u{1F308}', true, 1],
  ['\u{1F469}\u{1F3FD}\u{200D}\u{1F4BB}', true, 1],
  ['\u{1F3F4}\u{E0067}\u{E0062}\u{E0065}\u{E006E}\u{E0067}\u{E007F}', true, 1],
  ['\u{1F9D1}\u{200D}\u{2695}\u{FE0F}', true, 1],
  ['\u{261D}\u{1F3FD}', true, 1],
  ['\u{1F3FD}', true, 1],
  // not one emoji: text, a text presentation, or a lone part
  ['\u{2764}', false, 1],
  ['\u{A9}', false, 1],
  ['\u{2122}', false, 1],
  ['\u{A9}\u{FE0E}', false, 1],
  ['\u{1F44D}\u{FE0E}', false, 1],
  ['\u{FE0F}', false, 1],
  ['\u{1F1EC}', false, 1],
  ['\u{1F1EC}\u{1F1E7}\u{1F1EB}\u{1F1F7}', false, 2],
  ['\u{1F600}\u{1F600}', false, 2],
  ['\u{1F600} ', false, 2],
  ['\u{1F600}\u{200D}', false, 1],
  ['a\u{1F44D}', false, 2],
  // letters, digits and symbols
  ['a', false, 1],
  ['A', false, 1],
  ['\u{E9}', false, 1],
  ['e\u{301}', false, 1],
  ['hello', false, 5],
  ['7', false, 1],
  ['42', false, 2],
  ['#', false, 1],
  ['*', false, 1],
  ['\u{D55C}', false, 1],
  ['\u{4E2D}', false, 1],
  [' ', false, 1],
  ['', false, 0],
];

/** Adds the two functions to the rule language the fixtures state: an AST variant and an operator each. */
const withEmoji = (/** @type {any} */ d) => {
  d.types.find((/** @type {any} */ t) => t.id === 'expr').variants.push(
    { name: 'Graphemes', newtype: true, fields: [{ name: 'inner', type: 'expr' }] },
    { name: 'IsEmoji', newtype: true, fields: [{ name: 'inner', type: 'expr' }] });
  d.languages[0].operators.push(
    { name: 'graphemes', variant: 'Graphemes', syntax: { form: 'call', token: 'graphemes' }, operands: ['str'], result: 'int', nulls: 'propagate', primitive: 'graphemes' },
    { name: 'is-emoji', variant: 'IsEmoji', syntax: { form: 'call', token: 'is_emoji' }, operands: ['str'], result: 'bool', nulls: 'propagate', primitive: 'is-emoji' });
};

/** The rule language with the two functions, and an evaluator over a literal argument. */
const emojiLanguage = () => {
  const r = analyzeSpec(spec(withEmoji));
  const model = /** @type {any} */ (r.model);
  const lang = model.entities.get('rule-language');
  const exprT = typeStructure(model, 'expr');
  const env = {}; // the literal arguments read no scope
  /** @param {string} variant @param {any} literal */
  const run = (variant, literal) => evalLanguage(model, lang, decodeValue(exprT, { [variant]: { Lit: literal } }, 'expr'), env);
  return { errors: errors(r), run };
};

// Each case of Strata's table (emoji sequences, flags, keycaps, skin tones, text-default emoji with and without VS16, digits, letters, two emoji, the empty string): the count and the is-emoji answer, both as the evaluator gives them.
// @evidence language-grapheme-emoji
test('graphemes and is_emoji validate and give Strata results for each case of its table', () => {
  const { errors: found, run } = emojiLanguage();
  assert.deepEqual(found.map((/** @type {any} */ d) => `${d.code} ${d.message}`), []);
  for (const [text, emoji, count] of EMOJI_CASES) {
    const g = run('Graphemes', { Str: text });
    assert.equal(g.variant, 'Ok', `graphemes of ${JSON.stringify(text)}`);
    assert.deepEqual([g.fields.value.variant, g.fields.value.fields.value], ['Int', count], `graphemes of ${JSON.stringify(text)}`);
    const e = run('IsEmoji', { Str: text });
    assert.equal(e.variant, 'Ok', `is_emoji of ${JSON.stringify(text)}`);
    assert.deepEqual([e.fields.value.variant, e.fields.value.fields.value], ['Bool', emoji], `is_emoji of ${JSON.stringify(text)}`);
  }
});

// A null operand gives null and an integer operand is an error, for both functions.
// @evidence language-grapheme-emoji
test('graphemes and is_emoji give null on null and an error on any other kind', () => {
  const { run } = emojiLanguage();
  assert.equal(run('Graphemes', 'Null').fields.value.variant, 'Null');
  assert.equal(run('IsEmoji', 'Null').fields.value.variant, 'Null');
  assert.equal(run('Graphemes', { Int: 1 }).variant, 'Err');
  assert.equal(run('IsEmoji', { Int: 1 }).variant, 'Err');
});

// ancestor_of (Strata WG-5510): the walk through a self-reference, bounded at 32 hops. The lookup stands for the
// records the snapshot covers: for each object type, a map from record id to the record's fields, or to null when the
// record is covered and absent. Record ids are u64 in the model, so the names below are numbers.
const ID = { root: 1, a: 100, b: 101, z: 102, zz: 103 };
const nid = (/** @type {string} */ name) => (name in ID ? ID[name] : Number(name.slice(1)) + 1);

const withAncestor = (/** @type {any} */ d) => {
  d.types.find((/** @type {any} */ t) => t.id === 'expr').variants.push(
    { name: 'AncestorOf', tuple: true, fields: [
      { name: 'x', type: 'expr' }, { name: 'y', type: 'expr' }, { name: 'object', type: 'expr' }, { name: 'via', type: 'expr' }] });
  d.languages[0].operators.push(
    { name: 'ancestor-of', variant: 'AncestorOf', syntax: { form: 'call', token: 'ancestor_of' },
      operands: ['ref', 'ref', 'str', 'str'], result: 'bool', nulls: 'propagate', primitive: 'ancestor-of' });
};

/** The rule language with ancestor_of, and a runner over its operands (JSON expressions) and a lookup. */
const ancestorLanguage = () => {
  const r = analyzeSpec(spec(withAncestor));
  const model = /** @type {any} */ (r.model);
  const lang = model.entities.get('rule-language');
  const exprT = typeStructure(model, 'expr');
  const valueT = typeStructure(model, 'value');
  /** @param {any} x @param {any} y @param {Record<string, any>|null} covered @param {any} [object] @param {any} [via] */
  const run = (x, y, covered, object = { Str: 'comment' }, via = { Str: 'parent' }) => {
    const lit = (/** @type {any} */ v) => ({ Lit: v });
    const expr = decodeValue(exprT, { AncestorOf: { x: lit(x), y: lit(y), object: lit(object), via: lit(via) } }, 'expr');
    const lookup = covered === null ? null : new Map([['comment', new Map(Object.entries(covered).map(([id, rec]) => [id,
      rec === null ? null : new Map(Object.entries(rec).map(([f, v]) => [f, decodeValue(valueT, v, 'value')]))]))]]);
    return evalLanguage(model, lang, expr, {}, lookup);
  };
  return { errors: errors(r), run };
};

/** Records root <- c1 <- c2 <- ... <- cn, keyed by their ids: each record's parent is the one before it; root has none. */
const chain = (/** @type {number} */ n) => {
  const covered = { [ID.root]: { parent: 'Null' } };
  for (let i = 1; i <= n; i += 1) covered[nid(`c${i}`)] = { parent: { Ref: i === 1 ? ID.root : nid(`c${i - 1}`) } };
  return covered;
};

const ref = (/** @type {string} */ name) => ({ Ref: nid(name) });
/** The boolean of an Ok result, or the message of an Err one. */
const answer = (/** @type {any} */ r) => (r.variant === 'Ok' ? r.fields.value.fields.value : r.fields.error);

// The rule language with ancestor_of validates; a record is its own ancestor; an ancestor reached through a chain is true; a walk that ends at a root is false.
// @evidence language-ancestor-of
test('ancestor_of validates and answers the walk through a self-reference', () => {
  const { errors: found, run } = ancestorLanguage();
  assert.deepEqual(found.map((/** @type {any} */ d) => `${d.code} ${d.message}`), []);
  const covered = chain(4);
  assert.equal(answer(run(ref('root'), ref('c4'), covered)), true);
  assert.equal(answer(run(ref('c2'), ref('c4'), covered)), true);
  assert.equal(answer(run(ref('c4'), ref('c4'), covered)), true, 'a record counts as its own ancestor');
  assert.equal(answer(run(ref('c4'), ref('c1'), covered)), false, 'a walk from c1 never meets c4');
  assert.equal(answer(run(ref('c3'), ref('root'), covered)), false, 'the root has no parent');
});

// A null reference operand gives null; an integer operand is an error.
// @evidence language-ancestor-of
test('ancestor_of is null on a null operand and an error on a non-reference operand', () => {
  const { run } = ancestorLanguage();
  const covered = chain(2);
  assert.equal(run('Null', ref('c1'), covered).fields.value.variant, 'Null');
  assert.equal(run(ref('root'), 'Null', covered).fields.value.variant, 'Null');
  assert.equal(run({ Int: 1 }, ref('c1'), covered).variant, 'Err');
});

// A walk of 32 hops answers; 33 hops is an error; a cycle is an error; a record the lookup does not cover is an error naming the lack.
// @evidence language-ancestor-of
test('ancestor_of allows 32 hops and refuses longer walks cycles and uncovered records', () => {
  const { run } = ancestorLanguage();
  assert.equal(answer(run(ref('root'), ref('c32'), chain(32))), true);
  assert.match(String(answer(run(ref('root'), ref('c33'), chain(33)))), /longer than 32 hops/);
  const cyclic = { [ID.a]: { parent: { Ref: ID.b } }, [ID.b]: { parent: { Ref: ID.a } }, [ID.z]: { parent: 'Null' } };
  assert.match(String(answer(run(ref('z'), ref('a'), cyclic))), /cycle/);
  const partial = { [nid('c1')]: { parent: { Ref: ID.root } } };
  assert.match(String(answer(run(ref('zz'), ref('c1'), partial))), /does not cover/);
});

// An object type that is not a string literal, and a field that is not a field identifier, are errors.
// @evidence language-ancestor-of
test('ancestor_of reads its object type and field only from string literals', () => {
  const { run } = ancestorLanguage();
  assert.match(String(answer(run(ref('c1'), ref('c1'), chain(1), { Int: 1 }))), /string literal/);
  assert.match(String(answer(run(ref('c1'), ref('c1'), chain(1), { Str: 'comment' }, { Str: 'Bad Field' }))), /invalid field/);
});

// A variant without an operator, and a comparison case without one: no error without system.generation, the gap listed by readiness, and exactly one error with it.
// @evidence language-construct-rules # an AST variant without an operator is reported once as ready.language-variant-uncovered only when generation is set
test('an AST variant holds as many expression operands as its fields of the AST type, or a list', () => {
  assert.equal(variantOperandCount({ fields: [{ name: 'op', type: 'cmp-op' }, { name: 'l', type: 'expr' }, { name: 'r', type: 'expr' }] }, 'expr'), 2);
  assert.equal(variantOperandCount({ fields: [{ name: 'items', type: 'list<expr>' }] }, 'expr'), 'n');
  assert.equal(variantOperandCount({ fields: [{ name: 'x', type: 'option<expr>' }] }, 'expr'), 1);
  assert.equal(variantOperandCount({}, 'expr'), 0);
});
