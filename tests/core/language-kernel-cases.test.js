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

test('the case table names each case once and has eval and check cases', () => {
  assert.ok(TABLE.eval.length >= 20 && TABLE.check.length >= 15);
  for (const part of ['eval', 'check']) {
    const names = TABLE[part].map((/** @type {any} */ c) => c.name);
    assert.equal(new Set(names).size, names.length, part);
  }
});

for (const c of TABLE.eval) {
  test(`eval gives the kernel result: ${c.name}`, () => {
    const e = decodeValue(exprT, c.expr, 'expr');
    const env = decodeValue(ruleEnvT, { record: null, old: null, new: null, param: {}, now: 'Null', principal: 'Null', has_role: [], ...c.env }, 'env');
    assert.deepEqual(written(evalLanguage(model, lang, e, env), valueT), c.result);
    assert.equal(printLanguage(model, lang, e), c.source);
  });
}

for (const c of TABLE.check) {
  test(`check gives the kernel result: ${c.name}`, () => {
    const e = decodeValue(exprT, c.expr, 'expr');
    const env = decodeValue(checkEnvT, { fields: {}, params: [], roles: [], ...c.env }, 'env');
    assert.deepEqual(written(checkLanguage(model, lang, e, env), { k: 'prim', name: 'string' }), c.result);
    assert.equal(printLanguage(model, lang, e), c.source);
  });
}
