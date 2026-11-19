import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { analyzeSpec } from '../../src/core/analyze.js';
import { readinessGaps } from '../../src/core/readiness.js';
import { LANGUAGE_PRIMITIVES, NULL_RULES, SYNTAX_FORMS, variantOperandCount } from '../../src/core/language.js';
import { spec, FIXTURES, READINESS_FIXTURES } from '../fixtures/language/fixtures.js';

// The language construct (WG-4929, NC-2): a tenant expression language stated as data, with operators bound to a
// fixed primitive catalogue pinned to the Strata kernel.

const errors = (/** @type {any} */ r) => r.diagnostics.filter((/** @type {any} */ d) => d.severity === 'error');
const codes = (/** @type {any} */ ds) => ds.map((/** @type {any} */ d) => d.code);

test('the kernel rule language as it is today validates and has no readiness gap', () => {
  for (const generation of [false, true]) {
    const r = analyzeSpec(spec(undefined, { generation }));
    assert.deepEqual(errors(r).map((/** @type {any} */ d) => `${d.code} ${d.message}`), []);
    assert.deepEqual(readinessGaps(/** @type {any} */ (r.model)), []);
  }
});

for (const [title, code, mutate] of FIXTURES) {
  for (const generation of [false, true]) {
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

test('the primitive catalogue is the fixed set pinned to the kernel and each entry is complete', () => {
  assert.deepEqual(Object.keys(LANGUAGE_PRIMITIVES).sort(), [
    'and3', 'contains', 'eq', 'ge', 'gt', 'has-role', 'if', 'in-list', 'is-null', 'is-slug', 'le', 'len', 'list-literal', 'literal', 'lower', 'lt',
    'ne', 'not3', 'now', 'or3', 'param', 'principal', 'starts-with', 'through', 'var',
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

test('the format documentation states every primitive and every code', () => {
  const doc = fs.readFileSync(new URL('../../docs/model-and-format.md', import.meta.url), 'utf8');
  for (const name of Object.keys(LANGUAGE_PRIMITIVES)) assert.ok(doc.includes(`| \`${name}\` |`), `primitive ${name} has a row`);
  for (const [, code] of [...FIXTURES, ...READINESS_FIXTURES]) assert.ok(doc.includes(`\`${code}\``), `code ${code} is documented`);
});

test('an AST variant holds as many expression operands as its fields of the AST type, or a list', () => {
  assert.equal(variantOperandCount({ fields: [{ name: 'op', type: 'cmp-op' }, { name: 'l', type: 'expr' }, { name: 'r', type: 'expr' }] }, 'expr'), 2);
  assert.equal(variantOperandCount({ fields: [{ name: 'items', type: 'list<expr>' }] }, 'expr'), 'n');
  assert.equal(variantOperandCount({ fields: [{ name: 'x', type: 'option<expr>' }] }, 'expr'), 1);
  assert.equal(variantOperandCount({}, 'expr'), 0);
});
