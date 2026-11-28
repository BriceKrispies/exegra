// The shared case table of expression and value semantics (tests/fixtures/expr-cases.json, WG-4902):
// integer bounds and checked arithmetic, integer division and remainder, structural equality, absent
// values and time differences. The JavaScript evaluator (src/core/expr.js) and the Lean core (`expr.eval`
// in formal/Exegra/Api/Engine.lean, `Exegra.eval`) must both give every expected outcome. Strata runs a
// byte-identical copy of the table on the generated Rust and JavaScript (crates/spec-expr-cases). Needs
// `npm run build:formal-wasm` for the Lean half.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { parseExpr, evalExpr } from '../../src/core/expr.js';
import { call, initLean } from '../../src/core/lean.js';

const TABLE = JSON.parse(readFileSync(fileURLToPath(new URL('../fixtures/expr-cases.json', import.meta.url)), 'utf8'));

/** The engine type of a specification type name in the table (time-units.js, evalTypeOf). @param {string} t */
function engineType(t) {
  if (t === 'timestamp') return 'i64';
  if (t === 'duration') return 'u64';
  if (t.startsWith('option<')) return 'option';
  return t;
}

/** @param {Record<string, string>} types */
const engineTypes = (types) => Object.fromEntries(Object.entries(types).map(([k, v]) => [k, engineType(v)]));

/** The kind of an evaluation error message. @param {string} message */
function errorKind(message) {
  if (/^Integer overflow/.test(message)) return 'overflow';
  if (/^Division by zero/.test(message)) return 'division-by-zero';
  if (/^Unknown reference/.test(message)) return 'absent';
  if (/operand .* is not a (u|i)\d+$/.test(message)) return 'refused';
  return `unexpected: ${message}`;
}

/** @param {any} c @returns {{value: any} | {error: string}} */
function viaJs(c) {
  const p = parseExpr(c.expr);
  if (!p.ok) return { error: `parse: ${p.error.message}` };
  const types = engineTypes(c.types);
  try {
    const value = evalExpr(p.ast, (path) => {
      const k = path.join('.');
      return Object.hasOwn(c.env, k) ? c.env[k] : undefined;
    }, (path) => types[path.join('.')]);
    return { value };
  } catch (e) {
    return { error: errorKind(/** @type {Error} */ (e).message) };
  }
}

/** @param {any} c @returns {{value: any} | {error: string}} */
function viaLean(c) {
  const r = call('expr.eval', { expr: c.expr, env: c.env, types: engineTypes(c.types) });
  if (!r.ok) return { error: `call: ${r.error}` };
  return 'error' in r.value ? { error: errorKind(r.value.error) } : { value: r.value.value };
}

test('the case table is well formed', () => {
  assert.equal(TABLE.format, 'exegra-expr-cases');
  assert.ok(TABLE.cases.length >= 40);
  for (const c of TABLE.cases) {
    assert.equal(typeof c.expr, 'string', c.name);
    assert.ok(parseExpr(c.expr).ok, c.name);
    assert.ok('value' in c.expect || ['overflow', 'division-by-zero', 'absent', 'refused'].includes(c.expect.error), c.name);
  }
});

for (const c of TABLE.cases) {
  // One test per case of the shared table on the JavaScript evaluator.
  // @evidence expression-semantics-shared # expression case on the JavaScript evaluator
  test(`expression case on the JavaScript evaluator: ${c.name}`, () => {
    assert.deepEqual(viaJs(c), c.expect, `${c.expr} with ${JSON.stringify(c.env)}`);
  });
}

// Every case of the shared table on the Lean core through expr.eval.
// @evidence expression-semantics-shared
test('expression cases on the Lean core: every case gives the expected outcome', () => {
  initLean();
  for (const c of TABLE.cases) assert.deepEqual(viaLean(c), c.expect, `${c.name}: ${c.expr} with ${JSON.stringify(c.env)}`);
});

test('without declared types numbers stay IEEE doubles, as a model-level machine computes them', () => {
  const p = parseExpr('n - 1');
  assert.ok(p.ok);
  assert.equal(evalExpr(p.ast, () => 0), -1);
  const q = parseExpr('7 / 2');
  assert.ok(q.ok);
  assert.equal(evalExpr(q.ast, () => undefined), 3.5);
});
