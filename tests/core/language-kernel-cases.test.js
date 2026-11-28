import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { analyzeSpec } from '../../src/core/analyze.js';
import { evalLanguage, checkLanguage, printLanguage } from '../../src/core/language-eval.js';
import { decodeValue, encodeTyped } from '../../src/core/function-value.js';
import { typeStructure } from '../../src/core/codegen-model.js';
import { spec } from '../fixtures/functions/fixtures.js';

// The shared case table of the kernel's expression language (WG-4957): Exegra's evaluator and checker give the
// kernel's result and its exact error text (crates/kernel/src/expr.rs eval and check), and Exegra's printer gives
// the kernel's Display of each expression, which is the source the kernel's own tests parse from the same table.

const TABLE = JSON.parse(fs.readFileSync(new URL('../fixtures/language/kernel-cases.json', import.meta.url), 'utf8'));
const model = /** @type {any} */ (analyzeSpec(spec()).model);
const lang = model.entities.get('rule-language');
const T = (/** @type {string} */ id) => /** @type {any} */ (typeStructure(model, id));
const exprT = T('expr'), valueT = T('value'), ruleEnvT = T('rule-env'), checkEnvT = T('check-env');

/** @param {any} r the result<V, string> a language operation gave, as examples write it */
const written = (/** @type {any} */ r, /** @type {any} */ okType) => (r.variant === 'Ok' ? { Ok: encodeTyped(okType, r.fields.value) } : { Err: r.fields.error });

// The shared case table holds at least 20 eval and 15 check cases, each named once.
// @evidence function-language-kernel-fidelity
test('the case table names each case once and has eval and check cases', () => {
  assert.ok(TABLE.eval.length >= 20 && TABLE.check.length >= 15);
  for (const part of ['eval', 'check']) {
    const names = TABLE[part].map((/** @type {any} */ c) => c.name);
    assert.equal(new Set(names).size, names.length, part);
  }
});

for (const c of TABLE.eval) {
  // Each eval case gives the kernel's value or exact error text ("cannot compare a string with a int", "len does not apply to a bool", "author cannot be followed here", ...), and print gives the case's source.
  // @evidence function-language-kernel-fidelity # eval gives the kernel result: comparing a string with an int
  // 2^53-1 plus 1 is integer-overflow; the eval cases cover +, - and * at both ends of the range, a product beyond 64 bits, a timestamp plus and minus milliseconds, ms_between, days, hours and minutes at the range, nulls and operands of the wrong kind.
  // @evidence language-checked-arithmetic # eval gives the kernel result: add past the safe maximum
  // A concatenation of 4097 bytes of UTF-8 is string-too-long and one of 4096 bytes is not; text writes ints, timestamps and references as decimal digits, bools as true or false, and refuses a list.
  // @evidence language-checked-arithmetic # eval gives the kernel result: concat of two-byte characters past 4096 bytes
  test(`eval gives the kernel result: ${c.name}`, () => {
    const e = decodeValue(exprT, c.expr, 'expr');
    const env = decodeValue(ruleEnvT, { record: null, old: null, new: null, param: {}, now: 'Null', principal: 'Null', has_role: [], ...c.env }, 'env');
    assert.deepEqual(written(evalLanguage(model, lang, e, env), valueT), c.result);
    assert.equal(printLanguage(model, lang, e), c.source);
  });
}

for (const c of TABLE.check) {
  // Each check case gives the kernel's shape or exact error text ("len does not accept a Bool operand", "cannot compare Str with Int", "invalid field identifier: "Bad"", ...) in the kernel's order of operands.
  // @evidence function-language-kernel-fidelity # check gives the kernel result: len of a bool
  // The checker refuses int + timestamp, timestamp - timestamp, timestamp * int, ms_between of an int, days of a string, concat of an int and text of a list, and gives a timestamp plus days the time shape.
  // @evidence language-checked-arithmetic # check gives the kernel result: adding a timestamp on the right
  test(`check gives the kernel result: ${c.name}`, () => {
    const e = decodeValue(exprT, c.expr, 'expr');
    const env = decodeValue(checkEnvT, { fields: {}, params: [], roles: [], ...c.env }, 'env');
    assert.deepEqual(written(checkLanguage(model, lang, e, env), { k: 'prim', name: 'string' }), c.result);
    assert.equal(printLanguage(model, lang, e), c.source);
  });
}
