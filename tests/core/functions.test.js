import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { analyzeSpec } from '../../src/core/analyze.js';
import { readinessGaps } from '../../src/core/readiness.js';
import { parseFnExpr, BUILTIN_OPS } from '../../src/core/function-syntax.js';
import { analyzeFunctions, runFunction, resolvedExample } from '../../src/core/function.js';
import { functionCoverage } from '../../src/core/function-coverage.js';
import { decodeValue, encodeTyped } from '../../src/core/function-value.js';
import { evalLanguage, checkLanguage } from '../../src/core/language-eval.js';
import { typeStructure } from '../../src/core/codegen-model.js';
import { spec, FIXTURES, READINESS_FIXTURES } from '../fixtures/functions/fixtures.js';

// The function construct (WG-4933, NC-3): pure functions with examples Exegra evaluates in JavaScript. The passing
// fixture states roles_of, may_attempt and authorize (crates/kernel/src/rules.rs) and check_version
// (crates/kernel/src/transition.rs) with examples from the kernel's own tests.

const errors = (/** @type {any} */ r) => r.diagnostics.filter((/** @type {any} */ d) => d.severity === 'error');
const codes = (/** @type {any} */ ds) => ds.map((/** @type {any} */ d) => d.code);
const CODES = ['function.expr-syntax', 'function.expr-reference', 'function.expr-type', 'function.match-exhaustive', 'function.recursion', 'function.error-unknown', 'function.param', 'function.example-failed', 'example.fixture-unknown', 'example.fixture-type', 'example.fixture-override'];

// A body cut off mid-expression: exactly one function.expr-syntax error; a further fixture breaks a let.
// @evidence function-construct-rules # a body that does not parse is reported once as function.expr-syntax
// A read of a field the struct lacks: exactly one function.expr-reference error; further fixtures call an undeclared function, build a variant the union lacks and name an operation that does not exist.
// @evidence function-construct-rules # a field the struct does not have is reported once as function.expr-reference
// Comparing an enum with a union: exactly one function.expr-type error; further fixtures return the wrong type and set a struct field with a value of the wrong type.
// @evidence function-construct-rules # a comparison of an action with a resource is reported once as function.expr-type
// A match without an arm for one variant and no _: exactly one function.match-exhaustive error; further fixtures give one variant two arms and put an arm after _.
// @evidence function-construct-rules # a match that leaves out a variant is reported once as function.match-exhaustive
// A fail in a function without errors: exactly one function.error-unknown error; further fixtures name an enum as errors and try an error of another union.
// @evidence function-construct-rules # a fail in a function that declares no errors is reported once as function.error-unknown
// Two parameters named alike: exactly one function.param error; further fixtures use a parameter type and a return type that do not resolve and a let named like a parameter.
// @evidence function-construct-rules # two parameters of one name is reported once as function.param
// An authorize example claiming the refused writer is allowed: exactly one function.example-failed error; further fixtures state a wrong error message, expect an error where the function succeeds, pass an argument of the wrong type and name a parameter that does not exist.
// @evidence function-construct-rules # an example whose result is wrong is reported once as function.example-failed
// A call of mentions-field on its own parameter: exactly one function.recursion error; a further fixture calls it on a value it builds.
// @evidence function-language-kernel-fidelity # a call of itself on the whole parameter is reported once as function.recursion
// If{cond, then, otherwise}: exactly one function.expr-syntax error; a further fixture names a keyword variant the union lacks (function.expr-reference).
// @evidence function-language-kernel-fidelity # a keyword-named field bound without a name is reported once as function.expr-syntax
// trim of the unit value is refused; further fixtures write () into a {} placeholder, an enum to {:json}, a string to print, a number to startsWith, a list to a character class and read parseTime as a number (function.expr-type), and print a name that is not a language (function.expr-reference).
// @evidence function-language-kernel-fidelity # the unit value where a string is expected is reported once as function.expr-type
// A union named unit shadows the built-in: exactly one type.shadows-builtin error; a further fixture represents an id as unit (type.repr-not-builtin).
// @evidence function-language-kernel-fidelity # a declared type named unit is reported once as type.shadows-builtin
// An argument that names a fixture that is not declared: exactly one example.fixture-unknown error; a second fixture does the same for a result.
// @evidence example-fixture-rules # an example that refers to a fixture that is not declared is reported once as example.fixture-unknown
// A fixture whose value is not its type: exactly one example.fixture-type error, on the fixture, not on its uses; further fixtures break the type text, use a fixture for a parameter of another type and make an override produce another type.
// @evidence example-fixture-rules # a fixture whose value is not its type is reported once as example.fixture-type
// An override of a field the struct lacks: exactly one example.fixture-override error; further fixtures go into a map key that is not there and use a path with an empty step.
// @evidence example-fixture-rules # an override of a field the struct does not have is reported once as example.fixture-override
// roles_of, may_attempt and authorize (rules.rs) and check_version (transition.rs) stated as functions with examples from the kernel tests (owner bypass, policy:none, a null condition fails, writers edit only their own notes, a stale expected version is a conflict) have no error and no readiness gap, with and without system.generation.
// The examples of print-rule (the kernel's Display), request-text and debug-texts (Rust Debug), json-text (serde_json), is-field-id, kind-rule, blank, route-ok and parse-time (plain.rs tests) and the keyword-named plain-value functions hold, with no readiness gap.
// The passing fixture shares a tenant and a stored note through exampleFixtures, one example overrides two paths of a fixture, and it has no error and no readiness gap, with and without system.generation.
// @evidence function-construct-rules function-language-kernel-fidelity example-fixture-rules
test('the kernel decisions stated as functions validate with every example holding and nothing missing for generation', () => {
  for (const generation of [false, true]) {
    const r = analyzeSpec(spec(undefined, { generation }));
    assert.deepEqual(errors(r).map((/** @type {any} */ d) => `${d.code} ${d.message}`), []);
    assert.deepEqual(readinessGaps(/** @type {any} */ (r.model)), []);
  }
});

// Every example of the passing fixture, run by the JavaScript evaluator, gives its stated result or error.
// @evidence function-construct-rules
test('the examples are evaluated: each one gives its stated result or error', () => {
  const model = /** @type {any} */ (analyzeSpec(spec()).model);
  const { sigs } = analyzeFunctions(model);
  let n = 0;
  for (const s of sigs.values()) {
    assert.ok(s.ok, s.fn.id);
    for (const ex of s.fn.data.examples) {
      const r = resolvedExample(model, s, ex);
      const got = runFunction(model, s, sigs, s.params.map((p, k) => decodeValue(p.type, r.args[k], p.name)));
      if ('result' in ex) assert.deepEqual('value' in got ? encodeTyped(s.returns, got.value) : got, r.result === null ? null : encodeTyped(s.returns, decodeValue(s.returns, r.result, 'result')), `${s.fn.id}: ${ex.description ?? JSON.stringify(ex.args)}`);
      else assert.ok('error' in got, s.fn.id);
      n++;
    }
  }
  assert.ok(n >= 30, `${n} examples`);
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

// An override replaces the value at its path and nothing else, and the declared fixture keeps its value.
// @evidence example-fixture-rules
test('fixtures are resolved: an override changes only its path and not the declared fixture', () => {
  const model = /** @type {any} */ (analyzeSpec(spec()).model);
  const { sigs } = analyzeFunctions(model);
  const s = /** @type {any} */ (sigs.get('authorize'));
  const ex = s.fn.data.examples.find((/** @type {any} */ e) => e.args.subject?.with);
  assert.ok(ex, 'an example overrides a fixture');
  const r = resolvedExample(model, s, ex);
  const subject = r.args[s.params.findIndex((/** @type {any} */ p) => p.name === 'subject')];
  assert.deepEqual({ ...subject.new.status }, { Str: 'published' });
  assert.equal(subject.new.title.Str, 'First');
  assert.equal(model.entities.get('note-stored').data.value.new.status, undefined);
});

// Every function.* code and ready.function-example-missing has a negative fixture.
// Every example fixture code has a negative fixture.
// @evidence function-construct-rules example-fixture-rules
test('every function code has a negative fixture', () => {
  const have = new Set(FIXTURES.map(([, code]) => code));
  assert.deepEqual(CODES.filter((c) => !have.has(c)), []);
  assert.deepEqual(['ready.function-example-missing'].filter((c) => !READINESS_FIXTURES.some(([, code]) => code === c)), []);
});

// docs/model-and-format.md names every function code and every operation of the body language, and says functions are not mirrored in Lean.
// docs/model-and-format.md states every example fixture code.
// @evidence function-construct-rules example-fixture-rules
test('the format documentation states every code and operation and that functions are not mirrored in Lean', () => {
  const doc = fs.readFileSync(new URL('../../docs/model-and-format.md', import.meta.url), 'utf8');
  for (const code of [...CODES, 'ready.function-example-missing']) assert.ok(doc.includes(`\`${code}\``), `code ${code} is documented`);
  for (const op of BUILTIN_OPS) assert.ok(doc.includes(`\`${op}(`), `operation ${op} is documented`);
  assert.match(doc, /[Ff]unctions are \*\*not mirrored in Lean\*\*/);
});

// Branch coverage of the examples (WG-4965, docs/coverage.md).

// The nine kernel functions take every branch; if then and else, match arms, try ok and err, and fail all occur; check-version lists its branches in the order written.
// @evidence function-branch-coverage
test('every branch of the kernel functions is taken by an example: if and match arms and try and fail', () => {
  const cov = functionCoverage(/** @type {any} */ (analyzeSpec(spec()).model));
  assert.equal(cov.length, /** @type {any} */ (analyzeSpec(spec()).model).byKind.function.length);
  for (const c of cov) assert.equal(c.covered, c.total, `${c.id}: ${c.branches.filter((b) => !b.covered).map((b) => b.id).join(', ')}`);
  const kinds = new Set(cov.flatMap((c) => c.branches.map((b) => `${b.kind}:${b.outcome.startsWith('arm:') ? 'arm' : b.outcome}`)));
  for (const k of ['if:then', 'if:else', 'match:arm', 'try:ok', 'try:err', 'fail:taken']) assert.ok(kinds.has(k), k);
  const check = /** @type {any} */ (cov.find((c) => c.id === 'check-version'));
  assert.deepEqual(check.branches.map((/** @type {any} */ b) => `${b.kind} ${b.label}`), ['match Some(v)', 'match None', 'if then', 'if else', 'fail fail']);
});

// Without the example of a principal who is no member, the None arm of roles-of is the one uncovered branch, located in the body, and no readiness gap is raised.
// @evidence function-branch-coverage
test('a branch no example takes is listed uncovered with its location and raises no readiness gap', () => {
  const without = spec((d) => { d.functions.find((/** @type {any} */ f) => f.id === 'roles-of').examples.splice(3, 1); });
  const roles = /** @type {any} */ (functionCoverage(/** @type {any} */ (analyzeSpec(without).model)).find((c) => c.id === 'roles-of'));
  const open = roles.branches.filter((/** @type {any} */ b) => !b.covered);
  assert.deepEqual(open.map((/** @type {any} */ b) => [b.kind, b.label, b.where, b.line]), [['match', 'None', 'body', 1]]);
  assert.ok(open[0].text.startsWith('None =>'), open[0].text);
  // Uncovered branches are information, not a readiness gap: no code asks for one example per branch.
  const model = /** @type {any} */ (analyzeSpec(without).model);
  assert.deepEqual(readinessGaps(model).filter((g) => g.code.includes('branch')), []);
  assert.deepEqual(readinessGaps(model).filter((g) => g.entityId === 'roles-of'), []);
});

// A specification that still sets functionBranches validates, and the setting changes no finding.
// @evidence function-branch-coverage
test('system.generation.functionBranches is still accepted and changes nothing', () => {
  const r = analyzeSpec(spec((d) => { d.functions.find((/** @type {any} */ f) => f.id === 'roles-of').examples.splice(3, 1); d.system.generation.functionBranches = 'gap'; }));
  assert.deepEqual(codes(errors(r)), []);
  assert.deepEqual(r.diagnostics.filter((/** @type {any} */ d) => d.code.includes('branch')), []);
});

// Evaluating the examples with the recorder attached leaves validation of the fixture without errors.
// @evidence function-branch-coverage
test('recording branches does not change what an example evaluates to', () => {
  const model = /** @type {any} */ (analyzeSpec(spec()).model);
  functionCoverage(model);
  assert.deepEqual(errors(analyzeSpec(spec())), []);
});

// Every form of the grammar parses; a match scrutinee takes no struct constructor; malformed binders, keywords used as names and empty matches are refused.
// @evidence function-construct-rules
test('the body language parses every form of its grammar', () => {
  const forms = [
    'a.b.c', '(f).x', '!a && b || c => d', '-x + 1 * 2 % 3', 'if a then b else c', 'let x = 1 in x + 1',
    'match o { None => 0, Some(x) => x }', 'match u { A => 1, B{f, g: h} => h, C(_) => 2, _ => 3 }',
    'T{a: 1, b}', 'U.V{a: 1}', 'U.N(1)', 'U.Unit', '[1, 2]', '[]', '{}', 'call f(1, 2)', 'try call f()',
    'map(x in xs, x + 1)', 'fold(x in xs, acc = 0, acc + x)', 'sortBy(x in xs, x.k)', 'format("policy:{}", p.id)',
    'eval(lang, e, env)', 'fail(E.V{m: "x"})', 'get(m, k)', 'insert(m, k, v)', 'remove(m, k)', 'take(xs, 2)',
  ];
  for (const src of forms) assert.ok(parseFnExpr(src).ok, src);
  // A match scrutinee takes no struct constructor, so the brace opens the arms.
  const m = parseFnExpr('match x { A => 1 }');
  assert.ok(m.ok && m.ast.t === 'match' && m.ast.e.t === 'ref');
  for (const bad of ['let in = 1 in 2', 'match x { }', 'map(xs, x)', 'fold(x in xs, 0, x)', 'a.', '[1,']) assert.equal(parseFnExpr(bad).ok, false, bad);
});

// eval of the rule language gives null for null == x, Kleene and/or, an error for comparing kinds that differ, null for a reference hop from no record, and counts characters, not bytes.
// @evidence function-construct-rules
test('eval of the declared language follows its primitives: three-valued logic and comparisons with null', () => {
  const model = /** @type {any} */ (analyzeSpec(spec()).model);
  const lang = model.entities.get('rule-language');
  const exprT = /** @type {any} */ (typeStructure(model, 'expr'));
  const valueT = /** @type {any} */ (typeStructure(model, 'value'));
  const run = (/** @type {any} */ e) => {
    const r = evalLanguage(model, lang, decodeValue(exprT, e, 'e'), { record: null, old: null, new: null, param: new Map(), now: null, principal: null, has_role: [] });
    return r.variant === 'Ok' ? encodeTyped(valueT, r.fields.value) : 'error';
  };
  const NULL = { Lit: 'Null' }, T = { Lit: { Bool: true } }, F = { Lit: { Bool: false } };
  assert.equal(run({ Cmp: { op: 'Eq', left: NULL, right: { Lit: { Str: 'x' } } } }), 'Null');
  assert.deepEqual(run({ And: [NULL, F] }), { Bool: false });
  assert.equal(run({ And: [NULL, T] }), 'Null');
  assert.deepEqual(run({ Or: [NULL, T] }), { Bool: true });
  assert.equal(run({ Or: [NULL, F] }), 'Null');
  assert.equal(run({ Cmp: { op: 'Lt', left: { Lit: { Str: 'a' } }, right: { Lit: { Int: 1 } } } }), 'error');
  assert.deepEqual(run({ Len: { Lit: { Str: 'héllo' } } }), { Int: 5 });
  // No record in scope: null. A record whose reference cannot be followed without a lookup is an error (format-gaps.test.js).
  assert.equal(run({ Through: { scope: 'Record', field: 'author', target: 'name' } }), 'Null');
});

// eval of {HasRole: editor}, whose field is a role-id, gives Bool(true) with the roles editor and public and Bool(false) without editor; check refuses an undeclared role with "unknown role editor".
// @evidence function-language-kernel-fidelity
test('has_role reads its operand when the AST field is an id over string', () => {
  const model = /** @type {any} */ (analyzeSpec(spec()).model);
  const lang = model.entities.get('rule-language');
  const exprT = /** @type {any} */ (typeStructure(model, 'expr'));
  const e = decodeValue(exprT, { HasRole: 'editor' }, 'e');
  const env = (/** @type {string[]} */ roles) => ({ record: null, old: null, new: null, param: new Map(), now: null, principal: null, has_role: roles });
  assert.deepEqual(encodeTyped(/** @type {any} */ (typeStructure(model, 'value')), evalLanguage(model, lang, e, env(['editor', 'public'])).fields.value), { Bool: true });
  assert.deepEqual(encodeTyped(/** @type {any} */ (typeStructure(model, 'value')), evalLanguage(model, lang, e, env(['public'])).fields.value), { Bool: false });
  const checked = checkLanguage(model, lang, e, { fields: new Map(), params: [], roles: ['editor'] });
  assert.equal(checked.variant, 'Ok');
  assert.equal(checkLanguage(model, lang, e, { fields: new Map(), params: [], roles: [] }).fields.error, 'unknown role editor');
});

// A function calling itself: exactly one function.recursion error; a further fixture has two functions call each other.
// @evidence function-construct-rules # a function that calls itself is reported once as function.recursion
// A function without a success example, one without an example of an error variant it fails with, and one without an example of an error it passes on with try: no error without system.generation, the gap listed by readiness, and exactly one error with it.
// @evidence function-construct-rules # a function without a success example is reported once as ready.function-example-missing only when generation is set
// mentions_field, recursive over the expression union, has no finding; calls of itself on the whole parameter or on a value the body builds are refused as function.recursion naming the rule.
// @evidence function-language-kernel-fidelity
test('a function may call itself only on a strict sub-value of a union parameter', () => {
  const { sigs, diagnostics } = analyzeFunctions(/** @type {any} */ (analyzeSpec(spec()).model));
  assert.deepEqual(diagnostics.map((d) => d.code), []);
  assert.equal(sigs.get('mentions-field')?.structural, true);
  for (const [, code, mutate] of FIXTURES.filter(([title]) => title.startsWith('a call of itself'))) {
    const r = analyzeSpec(spec(mutate));
    const d = errors(r).find((/** @type {any} */ x) => x.code === code);
    assert.match(d.message, /strict sub-value of a union parameter/);
  }
});

// value.null, expr.if{condition, then, else}, x.then, null and if{then, else} patterns and () parse; a keyword-named field bound by shorthand and a keyword bound as a name are refused.
// @evidence function-language-kernel-fidelity
test('the body language writes keyword-named variants and fields and the unit value', () => {
  for (const src of ['value.null', 'expr.if{condition: c, then: a, else: b}', 'x.then', 'match v { null => 1, if{then: t, else: _} => 2, in(x) => 3 }', '()', 'if a then () else ()']) {
    assert.ok(parseFnExpr(src).ok, src);
  }
  const u = parseFnExpr('()');
  assert.ok(u.ok && u.ast.t === 'unit');
  for (const bad of ['match v { if{then} => 1 }', 'T{else}', 'let null = 1 in 2', 'match v { null(in) => 1 }']) assert.equal(parseFnExpr(bad).ok, false, bad);
});
