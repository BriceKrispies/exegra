// The function construct (WG-4933, NC-3): pure functions stated in a specification, so that a kernel's decision
// logic (intent decision, policy evaluation, validation, workflow steps, view assembly) can be stated and compiled
// by a generator into a pure crate. docs/model-and-format.md, "Functions".
//
// A function is {id, description?, params: [{name, type}], returns, errors?, let?: [{name, expr}], body,
// examples?: [{args, result} | {args, error}]}. Its body is written in the language of src/core/function-syntax.js.
// The call graph is acyclic but for structural recursion (a function calling itself on a strict sub-value of a
// union parameter, WG-4957), and every list operation runs over a finite list, so every function is total.
//
// Exegra gives functions a checked meaning by evaluating their examples here, in JavaScript. Functions are not
// mirrored in Lean: claims about them are checked by examples and tests, never proved.
//
// Consistency rules (errors, always on):
//   function.expr-syntax       the body and every let parse
//   function.expr-reference    every name, field, variant, type, function, language and operation exists
//   function.expr-type         every expression is well typed, and the body has the declared return type
//   function.match-exhaustive  a match covers every variant (or has _), with no arm twice and none after _
//   function.recursion         the call graph is acyclic, but for structural self-recursion
//   function.error-unknown     errors names a union; fail and try are used only with it
//   function.param             params, returns and lets are well formed: names, no duplicates, types that resolve
//   function.example-failed    every example is well formed and evaluates to its result or error
//   example.fixture-unknown    an example refers to a fixture (exampleFixtures) that is not declared
//   example.fixture-type       a fixture's value is not its declared type, or a fixture (with its overrides) is not the
//                              type of the argument, result or error it stands for
//   example.fixture-override   an override path of "with" does not lead into the fixture's value
// Readiness (errors when system.generation is set, listed by the readiness command otherwise):
//   ready.function-example-missing  a success example, and an example per error variant the function can fail with
// The branches the examples take are reported by cover-functions (src/core/function-coverage.js, which records
// them through withBranchRecorder), not as a readiness rule.

import { typeStructure } from './codegen-model.js';
import { splitTop } from './type-expr.js';
import { INT_RANGES } from './expr.js';
import { parseFnExpr, calledFunctions, isBindableName, BUILTIN_OPS } from './function-syntax.js';
import {
  UnionValue, FnEvalError, RESULT_TYPE, UNIT, ok, errOf, valueEq, compareKeys, compareOrdered, isOrderable, primName, isIntType, isNumberType, typeText,
  decodeValue, encodeTyped, displayValue, debugValue, debuggable, jsonText, jsonWritable, rustDebugStr,
} from './function-value.js';
import { evalLanguage, checkLanguage, printLanguage } from './language-eval.js';
import { isFixtureRef, setAtPath, OverrideError } from './function-fixtures.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */
/** @typedef {import('./function-value.js').FnType} FnType */
/** @typedef {import('./function-syntax.js').FnAst} FnAst */
/** @typedef {{code: string, severity: 'error', message: string, entityId: string}} Gap */

/** @param {any} v */
const isObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);
/** @param {any} v @returns {any[]} */
const list = (v) => (Array.isArray(v) ? v : []);

/** @type {FnType} */ const BOOL = { k: 'prim', name: 'bool' };
/** @type {FnType} */ const STRING = { k: 'prim', name: 'string' };
/** @type {FnType} */ const NUMBER = { k: 'prim', name: 'number' };
/** @type {FnType} */ const U64 = { k: 'prim', name: 'u64' };
/** @type {FnType} */ const I64 = { k: 'prim', name: 'i64' };
/** @type {FnType} */ const UNIT_T = { k: 'prim', name: 'unit' };
/** @type {FnType} */ const NEVER = { k: 'never' };
/** @type {FnType} */ const UNKNOWN = { k: 'unknown' };

class CheckError extends Error {
  /** @param {string} code @param {string} message */
  constructor(code, message) {
    super(message);
    this.code = code;
  }
}
/** A fail reached during evaluation, carrying the error value. */
class Failure {
  /** @param {any} value */
  constructor(value) { this.value = value; }
}

/**
 * A type text of a parameter or return: a type of the format, or result<T, E>.
 * @param {Model} model @param {any} text @returns {FnType|undefined}
 */
export function fnTypeOf(model, text) {
  if (typeof text !== 'string') return undefined;
  const m = /^result<(.+)>$/.exec(text.trim());
  if (m) {
    const args = splitTop(m[1], ',');
    if (args.length !== 2) return undefined;
    const okT = fnTypeOf(model, args[0]), errT = fnTypeOf(model, args[1]);
    return okT && errT ? { k: 'result', ok: okT, err: errT } : undefined;
  }
  return typeStructure(model, text);
}

/** The class two scalar types share, for compatibility: number, string, bool, bytes, json. @param {FnType} t */
function scalarClass(t) {
  const n = primName(t);
  if (n === undefined) return undefined;
  if (isNumberType(t)) return 'number';
  if (n === 'string' || n === 'uuid') return 'string';
  return n;
}

/** The type of the literal null: an option of unknown. @param {FnType} t */
const isNullLiteral = (t) => t.k === 'option' && t.of.k === 'unknown';

/**
 * Whether a value of type `from` may stand where `to` is expected. A T stands for option<T>; never and unknown
 * fit everything; ids and scalars fit their representation's class.
 * @param {FnType} from @param {FnType} to @returns {boolean}
 */
export function assignable(from, to) {
  if (from.k === 'never' || from.k === 'unknown' || to.k === 'never' || to.k === 'unknown') return true;
  if (to.k === 'option') return from.k === 'option' ? assignable(from.of, to.of) : assignable(from, to.of);
  // The literal null is also the JSON null, where a json value is expected.
  if (isNullLiteral(from) && scalarClass(to) === 'json') return true;
  if (from.k === 'option') return false;
  const fc = scalarClass(from), tc = scalarClass(to);
  if (fc !== undefined || tc !== undefined) return fc === tc;
  if (from.k !== to.k) return false;
  switch (from.k) {
    case 'list': return assignable(from.of, /** @type {any} */ (to).of);
    case 'map': return assignable(from.key, /** @type {any} */ (to).key) && assignable(from.value, /** @type {any} */ (to).value);
    case 'result': return assignable(from.ok, /** @type {any} */ (to).ok) && assignable(from.err, /** @type {any} */ (to).err);
    case 'enum': case 'struct': case 'union': return from.id === /** @type {any} */ (to).id;
    default: return false;
  }
}

/** A type with its article, for messages. @param {FnType} t */
function aText(t) {
  const s = typeText(t);
  if (s.startsWith('a ')) return s;
  // u is a vowel sound only in un- (an unknown), not in unit, u64 or uuid.
  return `${/^(?:[aeio]|un(?!it))/.test(s) ? 'an' : 'a'} ${s}`;
}

/** Whether two values may be compared with == and !=. @param {FnType} a @param {FnType} b */
const comparable = (a, b) => assignable(a, b) || assignable(b, a);

/**
 * The type of two branches together (if, match arms, list items), or undefined when they do not fit.
 * @param {FnType} a @param {FnType} b @returns {FnType|undefined}
 */
export function join(a, b) {
  if (a.k === 'never' || a.k === 'unknown') return b.k === 'never' && a.k === 'unknown' ? a : b;
  if (b.k === 'never' || b.k === 'unknown') return a;
  if (isNullLiteral(a) && scalarClass(b) === 'json') return b;
  if (isNullLiteral(b) && scalarClass(a) === 'json') return a;
  if (a.k === 'option' || b.k === 'option') {
    const inner = join(a.k === 'option' ? a.of : a, b.k === 'option' ? b.of : b);
    return inner && { k: 'option', of: inner };
  }
  if (a.k === 'list' && b.k === 'list') { const of = join(a.of, b.of); return of && { k: 'list', of }; }
  if (a.k === 'map' && b.k === 'map') { const key = join(a.key, b.key), value = join(a.value, b.value); return key && value && { k: 'map', key, value }; }
  if (a.k === 'result' && b.k === 'result') { const o = join(a.ok, b.ok), e = join(a.err, b.err); return o && e && { k: 'result', ok: o, err: e }; }
  if (!assignable(a, b) || !assignable(b, a)) return undefined;
  return primName(a) === 'number' ? b : a;
}

/**
 * The variants a type can be matched on: union variants, None/Some, Ok/Err, or enum values.
 * @param {FnType} t
 * @returns {{name: string, newtype: boolean, fields: {name: string, type: FnType, optional: boolean}[]}[]|undefined}
 */
function matchVariants(t) {
  if (t.k === 'union') return t.variants;
  if (t.k === 'option') return [{ name: 'None', newtype: false, fields: [] }, { name: 'Some', newtype: true, fields: [{ name: 'value', type: t.of, optional: false }] }];
  if (t.k === 'result') return [{ name: 'Ok', newtype: true, fields: [{ name: 'value', type: t.ok, optional: false }] }, { name: 'Err', newtype: true, fields: [{ name: 'error', type: t.err, optional: false }] }];
  if (t.k === 'enum') return t.values.map((v) => ({ name: v, newtype: false, fields: [] }));
  return undefined;
}

/** A field's type as read: an optional field reads as option<T>. @param {{type: FnType, optional: boolean}} f @returns {FnType} */
const fieldType = (f) => (f.optional && f.type.k !== 'option' ? { k: 'option', of: f.type } : f.type);

/**
 * @typedef {Object} Signature
 * @property {Entity} fn
 * @property {{name: string, type: FnType}[]} params
 * @property {FnType} returns
 * @property {Extract<FnType, {k: 'union'}>|undefined} errors
 * @property {FnAst[]} lets the parsed lets, in order
 * @property {FnAst|undefined} body
 * @property {boolean} ok    true when the function has no finding of its own
 * @property {Set<string>|'all'} fails the error variants its own fail expressions name ('all' when one is not a constructor)
 * @property {boolean} [structural] true when it calls itself and every such call is structural (selfRecursion)
 * @property {string} [recursionProblem] why its calls of itself are not structural
 */

/**
 * Type one function. Annotates the AST nodes (ty, res) for the evaluator. Throws CheckError at the first finding.
 * @param {Model} model @param {Signature} sig @param {Map<string, Signature>} sigs
 */
function typeFunction(model, sig, sigs) {
  const fnId = sig.fn.id;
  /** @param {string} message */
  const refErr = (message) => new CheckError('function.expr-reference', message);
  /** @param {string} message */
  const tyErr = (message) => new CheckError('function.expr-type', message);
  /** @param {FnType} t @param {FnType} want @param {string} what */
  const need = (t, want, what) => { if (!assignable(t, want)) throw tyErr(`${what} is ${aText(t)}, not ${aText(want)}`); };
  /** @param {FnType} t @param {string} what */
  const needList = (t, what) => {
    if (t.k === 'unknown' || t.k === 'never') return UNKNOWN;
    if (t.k !== 'list') throw tyErr(`${what} is ${aText(t)}, not a list`);
    return t.of;
  };
  /** @param {FnType} t @param {string} what */
  const needMap = (t, what) => {
    if (t.k === 'unknown' || t.k === 'never') return { key: UNKNOWN, value: UNKNOWN };
    if (t.k !== 'map') throw tyErr(`${what} is ${aText(t)}, not a map`);
    return t;
  };
  /** @param {FnType} t @param {string} name @param {string} what @returns {FnType} */
  const fieldOf = (t, name, what) => {
    if (t.k === 'unknown' || t.k === 'never') return UNKNOWN;
    if (t.k !== 'struct') throw tyErr(`${what} is ${aText(t)}, which has no fields; it cannot be read as .${name}`);
    const f = t.fields.find((x) => x.name === name);
    if (!f) throw refErr(`${what} is a ${t.id}, which has no field "${name}" (${t.fields.map((x) => x.name).join(', ')})`);
    return fieldType(f);
  };
  /** @param {string} id */
  const typeEntity = (id) => {
    const t = model.entities.get(id);
    return t?.kind === 'type' ? typeStructure(model, id) : undefined;
  };
  /**
   * The fields a constructor sets, checked against the declared fields.
   * @param {{name: string, type: FnType, optional: boolean}[]} declared @param {{name: string, e: FnAst}[]} given
   * @param {Map<string, FnType>} scope @param {string} what
   */
  const ctorFields = (declared, given, scope, what) => {
    const seen = new Set();
    for (const g of given) {
      const f = declared.find((x) => x.name === g.name);
      if (!f) throw refErr(`${what} has no field "${g.name}" (${declared.map((x) => x.name).join(', ') || 'none'})`);
      if (seen.has(g.name)) throw tyErr(`${what} sets the field "${g.name}" twice`);
      seen.add(g.name);
      need(walk(g.e, scope), fieldType(f), `Field "${g.name}" of ${what}`);
    }
    const missing = declared.filter((f) => !seen.has(f.name) && !f.optional && f.type.k !== 'option');
    if (missing.length) throw tyErr(`${what} does not set ${missing.map((f) => `"${f.name}"`).join(', ')}`);
  };
  /** The union and variant a path T.V names. @param {string[]} path */
  const variantOf = (path) => {
    const t = typeEntity(path[0]);
    if (!t) throw refErr(`"${path[0]}" is not a declared type`);
    if (t.k !== 'union') throw tyErr(`"${path[0]}" is a ${t.k === 'enum' ? 'an enum' : t.k}, not a union, so it has no variant ${path[1]}`);
    const v = t.variants.find((x) => x.name === path[1]);
    if (!v) throw refErr(`union "${t.id}" has no variant "${path[1]}" (${t.variants.map((x) => x.name).join(', ')})`);
    return { t, v };
  };
  /** @param {FnAst} n @param {Map<string, FnType>} scope @param {string} name @param {FnType} t */
  const bindIn = (n, scope, name, t) => {
    const s = new Map(scope);
    s.set(name, t);
    return s;
  };
  /** @param {any} e @param {string} what */
  const languageOf = (e, what) => {
    if (e?.t !== 'ref' || e.path.length !== 1) throw refErr(`the first argument of ${what} is the id of a language`);
    const lang = model.entities.get(e.path[0]);
    if (lang?.kind !== 'language') throw refErr(`"${e.path[0]}" is not a declared language`);
    return lang;
  };

  /** @param {FnAst} n @param {Map<string, FnType>} scope @returns {FnType} */
  const walk = (n, scope) => {
    const t = type(n, scope);
    n.ty = t;
    return t;
  };
  /** @param {FnAst} n @param {Map<string, FnType>} scope @returns {FnType} */
  const type = (n, scope) => {
    switch (n.t) {
      case 'lit':
        if (n.v === null) return { k: 'option', of: UNKNOWN };
        return typeof n.v === 'boolean' ? BOOL : typeof n.v === 'number' ? NUMBER : STRING;
      case 'unit': return UNIT_T;
      case 'ref': {
        const [head, ...rest] = n.path;
        if (scope.has(head)) {
          n.res = 'var';
          let t = /** @type {FnType} */ (scope.get(head));
          rest.forEach((f, i) => { t = fieldOf(t, f, [head, ...rest.slice(0, i)].join('.')); });
          return t;
        }
        const te = typeEntity(head);
        if (te && rest.length === 1 && te.k === 'enum') {
          if (!te.values.includes(rest[0])) throw refErr(`enum "${te.id}" has no value "${rest[0]}" (${te.values.join(', ')})`);
          n.res = 'enum';
          return te;
        }
        if (te && rest.length === 1 && te.k === 'union') {
          const { t, v } = variantOf(n.path);
          if (v.fields.length) throw tyErr(`variant ${v.name} of "${t.id}" has fields; write ${t.id}.${v.name}${v.newtype ? '(...)' : '{...}'}`);
          n.res = 'unit';
          return t;
        }
        throw refErr(`"${n.path.join('.')}" names nothing: not a parameter, let or bound name${te ? `, and type "${head}" is read as ${head}.<variant or value>` : ''}`);
      }
      case 'field': return fieldOf(walk(n.a, scope), n.name, 'The value');
      case 'un': {
        const a = walk(n.a, scope);
        if (n.op === '!') { need(a, BOOL, 'The operand of "!"'); return BOOL; }
        if (!isNumberType(a) && a.k !== 'unknown' && a.k !== 'never') throw tyErr(`The operand of "-" is ${aText(a)}, not a number`);
        return a;
      }
      case 'bin': {
        const a = walk(n.a, scope), b = walk(n.b, scope);
        if (['&&', '||', '=>'].includes(n.op)) { need(a, BOOL, `The left of "${n.op}"`); need(b, BOOL, `The right of "${n.op}"`); return BOOL; }
        if (n.op === '==' || n.op === '!=') {
          if (!comparable(a, b)) throw tyErr(`"${n.op}" compares ${aText(a)} with ${aText(b)}`);
          return BOOL;
        }
        if (n.op === '+' && (scalarClass(a) === 'string' || scalarClass(b) === 'string')) {
          need(a, STRING, 'The left of "+"'); need(b, STRING, 'The right of "+"');
          return STRING;
        }
        for (const [x, side] of [[a, 'left'], [b, 'right']]) {
          const xt = /** @type {FnType} */ (x);
          if (!isNumberType(xt) && xt.k !== 'unknown' && xt.k !== 'never') throw tyErr(`The ${side} of "${n.op}" is ${aText(xt)}, not a number`);
        }
        if (['<', '<=', '>', '>='].includes(n.op)) return BOOL;
        return primName(a) !== 'number' && isNumberType(a) ? a : b;
      }
      case 'if': {
        need(walk(n.c, scope), BOOL, 'The condition of if');
        const a = walk(n.a, scope), b = walk(n.b, scope);
        const j = join(a, b);
        if (!j) throw tyErr(`The branches of if are ${aText(a)} and ${aText(b)}`);
        return j;
      }
      case 'let': return walk(n.body, bindIn(n, scope, n.name, walk(n.value, scope)));
      case 'match': {
        const st = walk(n.e, scope);
        const variants = matchVariants(st);
        if (!variants) throw tyErr(`match needs a union, an option, a result or an enum; this is ${aText(st)}`);
        const seen = new Set();
        let wild = false;
        /** @type {FnType} */
        let out = NEVER;
        for (const arm of n.arms) {
          if (wild) throw new CheckError('function.match-exhaustive', `An arm of match follows "_", so it is never reached`);
          let s = scope;
          if (arm.pat.k === 'wild') wild = true;
          else {
            const pat = arm.pat;
            const v = variants.find((x) => x.name === pat.name);
            if (!v) throw refErr(`match on ${aText(st)} has no case "${pat.name}" (${variants.map((x) => x.name).join(', ')})`);
            if (seen.has(v.name)) throw new CheckError('function.match-exhaustive', `match has two arms for "${v.name}"`);
            seen.add(v.name);
            if (pat.bind !== undefined) {
              if (v.fields.length !== 1) throw tyErr(`"${v.name}" has ${v.fields.length} fields; ${v.name}(x) binds the one field of a newtype variant, so write ${v.name}{...}`);
              if (pat.bind !== '_') s = bindIn(n, s, pat.bind, fieldType(v.fields[0]));
            }
            for (const f of pat.fields ?? []) {
              const vf = v.fields.find((x) => x.name === f.field);
              if (!vf) throw refErr(`"${v.name}" has no field "${f.field}" (${v.fields.map((x) => x.name).join(', ') || 'none'})`);
              if (f.bind !== '_') s = bindIn(n, s, f.bind, fieldType(vf));
            }
          }
          const bt = walk(arm.body, s);
          const j = join(out, bt);
          if (!j) throw tyErr(`The arms of match are ${aText(out)} and ${aText(bt)}`);
          out = j;
        }
        const missing = variants.filter((v) => !seen.has(v.name));
        if (!wild && missing.length) throw new CheckError('function.match-exhaustive', `match on ${aText(st)} does not cover ${missing.map((v) => v.name).join(', ')}; add arms or "_"`);
        return out;
      }
      case 'list': {
        /** @type {FnType} */
        let of = UNKNOWN;
        n.items.forEach((item, i) => {
          const it = walk(item, scope);
          const j = join(of, it);
          if (!j) throw tyErr(`Item ${i + 1} of the list is ${aText(it)}, the items before it ${aText(of)}`);
          of = j;
        });
        return { k: 'list', of };
      }
      case 'emptymap': return { k: 'map', key: UNKNOWN, value: UNKNOWN };
      case 'ctor': {
        if (n.path.length === 1) {
          const t = typeEntity(n.path[0]);
          if (!t) throw refErr(`"${n.path[0]}" is not a declared type`);
          if (t.k !== 'struct') throw tyErr(`"${n.path[0]}" is ${t.k === 'union' ? 'a union; write a variant, ' + n.path[0] + '.<Variant>{...}' : `a ${t.k}, not a struct`}`);
          ctorFields(t.fields, n.fields, scope, `struct "${t.id}"`);
          return t;
        }
        if (n.path.length !== 2) throw refErr(`"${n.path.join('.')}" is not a type or a union variant`);
        const { t, v } = variantOf(n.path);
        if (v.newtype) throw tyErr(`variant ${v.name} of "${t.id}" is a newtype; write ${t.id}.${v.name}(value)`);
        ctorFields(v.fields, n.fields, scope, `variant ${v.name} of "${t.id}"`);
        return t;
      }
      case 'newtype': {
        if (n.path.length !== 2) throw refErr(`"${n.path.join('.')}" is not a union variant; a call of a function is written call f(...)`);
        const { t, v } = variantOf(n.path);
        if (v.fields.length !== 1) throw tyErr(`variant ${v.name} of "${t.id}" has ${v.fields.length} fields; ${t.id}.${v.name}(value) builds a variant with one`);
        need(walk(n.arg, scope), fieldType(v.fields[0]), `The value of ${t.id}.${v.name}`);
        return t;
      }
      case 'call': {
        const callee = sigs.get(n.fn);
        if (!callee) throw refErr(`call names "${n.fn}", which is not a declared function`);
        if (n.args.length !== callee.params.length) throw tyErr(`"${n.fn}" takes ${callee.params.length} argument${callee.params.length === 1 ? '' : 's'}; the call gives ${n.args.length}`);
        n.args.forEach((a, i) => need(walk(a, scope), callee.params[i].type, `Argument "${callee.params[i].name}" of call ${n.fn}`));
        return callee.errors ? { k: 'result', ok: callee.returns, err: callee.errors } : callee.returns;
      }
      case 'try': {
        const t = walk(n.e, scope);
        if (t.k !== 'result') throw tyErr(`try needs a result (a call of a function that declares errors); this is ${aText(t)}`);
        if (!sig.errors) throw new CheckError('function.error-unknown', `try passes on an error, but function "${fnId}" declares no errors`);
        if (t.err.k !== 'union' || t.err.id !== sig.errors.id) throw new CheckError('function.error-unknown', `try passes on ${aText(t.err)} error, but function "${fnId}" fails with ${sig.errors.id}`);
        return t.ok;
      }
      case 'builtin': return builtin(n, scope);
    }
    throw tyErr('Malformed expression');
  };

  /** @param {Extract<FnAst, {t: 'builtin'}>} n @param {Map<string, FnType>} scope @returns {FnType} */
  const builtin = (n, scope) => {
    const op = n.name;
    if (!BUILTIN_OPS.includes(op)) throw refErr(`"${op}" is not an operation (${BUILTIN_OPS.join(', ')}); a function is called as call ${op}(...)`);
    const arity = (/** @type {number} */ k) => { if (n.args.length !== k) throw tyErr(`${op} takes ${k} argument${k === 1 ? '' : 's'}${n.binder ? ' after its binder' : ''}; it is given ${n.args.length}`); };
    if (n.binder) {
      const of = needList(walk(n.binder.src, scope), `The list of ${op}`);
      let s = bindIn(n, scope, n.binder.name, of);
      if (op === 'fold') {
        const acc = walk(/** @type {any} */ (n.acc).init, scope);
        s = bindIn(n, s, /** @type {any} */ (n.acc).name, acc);
        arity(1);
        const body = walk(n.args[0], s);
        const j = join(acc, body);
        if (!j || !assignable(body, acc)) throw tyErr(`The step of fold is ${aText(body)}, its accumulator ${aText(acc)}`);
        return j;
      }
      arity(1);
      const body = walk(n.args[0], s);
      switch (op) {
        case 'map': return { k: 'list', of: body };
        case 'filter': need(body, BOOL, 'The condition of filter'); return { k: 'list', of };
        case 'find': need(body, BOOL, 'The condition of find'); return { k: 'option', of };
        case 'any': case 'all': need(body, BOOL, `The condition of ${op}`); return BOOL;
        case 'sortBy': {
          if (!isOrderable(body)) throw tyErr(`The key of sortBy is ${aText(body)}; it is a number, a string, a bool, an enum value, or a list, option, struct or union of those`);
          return { k: 'list', of };
        }
      }
    }
    if (['map', 'filter', 'find', 'any', 'all', 'fold', 'sortBy'].includes(op)) throw tyErr(`${op} binds a name: ${op}(x in list, ...)`);
    switch (op) {
      case 'take': {
        arity(2);
        const of = needList(walk(n.args[0], scope), 'The list of take');
        const k = walk(n.args[1], scope);
        if (!isNumberType(k)) throw tyErr(`The count of take is ${aText(k)}, not a number`);
        return { k: 'list', of };
      }
      case 'concat': {
        arity(2);
        const a = walk(n.args[0], scope), b = walk(n.args[1], scope);
        needList(a, 'The first list of concat'); needList(b, 'The second list of concat');
        const j = join(a, b);
        if (!j) throw tyErr(`concat joins ${aText(a)} and ${aText(b)}`);
        return j;
      }
      case 'keys': { arity(1); return { k: 'list', of: needMap(walk(n.args[0], scope), 'The argument of keys').key }; }
      case 'values': { arity(1); return { k: 'list', of: needMap(walk(n.args[0], scope), 'The argument of values').value }; }
      case 'get': {
        arity(2);
        const c = walk(n.args[0], scope), k = walk(n.args[1], scope);
        if (c.k === 'list') { if (!isNumberType(k)) throw tyErr(`The index of get is ${aText(k)}, not a number`); return { k: 'option', of: c.of }; }
        const m = needMap(c, 'The first argument of get');
        need(k, m.key, 'The key of get');
        return { k: 'option', of: m.value };
      }
      case 'insert': {
        arity(3);
        const m = walk(n.args[0], scope);
        const mm = needMap(m, 'The first argument of insert');
        const k = walk(n.args[1], scope), v = walk(n.args[2], scope);
        const key = join(mm.key, k), value = join(mm.value, v);
        if (!key) throw tyErr(`The key of insert is ${aText(k)}, the map's keys ${typeText(mm.key)}`);
        if (!value) throw tyErr(`The value of insert is ${aText(v)}, the map's values ${typeText(mm.value)}`);
        return { k: 'map', key, value };
      }
      case 'remove': {
        arity(2);
        const m = walk(n.args[0], scope);
        const mm = needMap(m, 'The first argument of remove');
        need(walk(n.args[1], scope), mm.key, 'The key of remove');
        return m;
      }
      case 'format': {
        const [first, ...rest] = n.args;
        if (first?.t !== 'lit' || typeof first.v !== 'string') throw tyErr('The first argument of format is a string literal, such as "policy:{}"');
        const holes = formatHoles(first.v);
        if (holes.length !== rest.length) throw tyErr(`format "${first.v}" has ${holes.length} placeholder${holes.length === 1 ? '' : 's'} and ${rest.length} value${rest.length === 1 ? '' : 's'}`);
        walk(first, scope);
        rest.forEach((a, i) => {
          const t = walk(a, scope);
          if (holes[i] === 'debug') {
            if (!debuggable(t)) throw tyErr(`Value ${i + 1} of format is ${aText(t)}; {:?} writes any value but json and bytes`);
            return;
          }
          if (holes[i] === 'json') {
            if (!jsonWritable(t)) throw tyErr(`Value ${i + 1} of format is ${aText(t)}; {:json} writes strings, numbers, bools, json, and options and lists of them`);
            return;
          }
          const c = scalarClass(t);
          if ((c === undefined && t.k !== 'enum' && t.k !== 'unknown') || c === 'json' || c === 'bytes' || c === 'unit') {
            throw tyErr(`Value ${i + 1} of format is ${aText(t)}; {} writes numbers, strings, bools and enum values ({:?} writes Rust's debug text of any value)`);
          }
        });
        return STRING;
      }
      case 'print': {
        arity(2);
        const lang = languageOf(n.args[0], op);
        n.args[0].res = 'language';
        n.args[0].ty = UNKNOWN;
        const ast = typeStructure(model, lang.data.ast);
        if (!ast) throw refErr(`language "${lang.id}" has no AST type`);
        need(walk(n.args[1], scope), ast, 'The expression of print');
        return STRING;
      }
      case 'startsWith': case 'endsWith': {
        arity(2);
        need(walk(n.args[0], scope), STRING, `The text of ${op}`);
        need(walk(n.args[1], scope), STRING, `The ${op === 'startsWith' ? 'prefix' : 'suffix'} of ${op}`);
        return BOOL;
      }
      case 'length': {
        arity(1);
        const t = walk(n.args[0], scope);
        if (t.k !== 'list') need(t, STRING, 'The argument of length');
        return U64;
      }
      case 'trim': case 'snakeCase': { arity(1); need(walk(n.args[0], scope), STRING, `The argument of ${op}`); return STRING; }
      case 'chars': { arity(1); need(walk(n.args[0], scope), STRING, 'The argument of chars'); return { k: 'list', of: STRING }; }
      case 'isAsciiLowercase': case 'isAsciiUppercase': case 'isAsciiAlphabetic': case 'isAsciiDigit': case 'isAsciiAlphanumeric':
        arity(1);
        need(walk(n.args[0], scope), STRING, `The argument of ${op}`);
        return BOOL;
      case 'parseTime': { arity(1); need(walk(n.args[0], scope), STRING, 'The argument of parseTime'); return { k: 'result', ok: I64, err: STRING }; }
      case 'eval': case 'check': {
        if (op === 'eval' && n.args.length === 4) arity(4);
        else arity(3);
        const lang = languageOf(n.args[0], op);
        n.args[0].res = 'language';
        n.args[0].ty = UNKNOWN;
        const ast = typeStructure(model, lang.data.ast);
        if (!ast) throw refErr(`language "${lang.id}" has no AST type`);
        need(walk(n.args[1], scope), ast, `The expression of ${op}`);
        const env = walk(n.args[2], scope);
        if (env.k !== 'struct') throw tyErr(`The environment of ${op} is ${aText(env)}, not a struct`);
        if (op === 'eval') {
          const values = /** @type {FnType} */ (typeStructure(model, lang.data.values) ?? UNKNOWN);
          for (const s of list(lang.data.scopes).filter(isObj)) {
            /** @type {FnType} */
            const want = s.kind === 'record-scope' ? { k: 'option', of: { k: 'map', key: STRING, value: values } }
              : s.kind === 'param' ? { k: 'map', key: STRING, value: values }
                : s.kind === 'role-test' ? { k: 'list', of: STRING } : values;
            const f = env.fields.find((x) => x.name === s.name);
            if (!f) throw tyErr(`The environment of eval, ${env.id}, has no field "${s.name}" for scope "${s.name}" of language "${lang.id}"`);
            if (!assignable(fieldType(f), want) || !assignable(want, fieldType(f))) throw tyErr(`Field "${s.name}" of ${env.id} is a ${typeText(fieldType(f))}; scope "${s.name}" (${s.kind}) of language "${lang.id}" reads ${aText(want)}`);
          }
          // The optional fourth argument: the lookup that following a reference (through) reads. For each reference
          // field it covers, the records that exist, by the decimal text of their id, as record scopes are.
          if (n.args.length === 4) {
            /** @type {FnType} */
            const lookup = { k: 'map', key: STRING, value: { k: 'map', key: STRING, value: { k: 'map', key: STRING, value: values } } };
            need(walk(n.args[3], scope), lookup, 'The lookup of eval');
          }
          return { k: 'result', ok: values, err: STRING };
        }
        /** @type {[string, FnType][]} */
        const wants = [['fields', { k: 'map', key: STRING, value: STRING }], ['params', { k: 'list', of: STRING }], ['roles', { k: 'list', of: STRING }]];
        for (const [name, want] of wants) {
          const f = env.fields.find((x) => x.name === name);
          if (!f || !assignable(fieldType(f), want)) throw tyErr(`The environment of check, ${env.id}, needs a field "${name}" of type ${typeText(want)}`);
        }
        return { k: 'result', ok: STRING, err: STRING };
      }
      case 'fail': {
        arity(1);
        if (!sig.errors) throw new CheckError('function.error-unknown', `fail is used, but function "${fnId}" declares no errors`);
        const t = walk(n.args[0], scope);
        if (t.k !== 'union' || t.id !== sig.errors.id) throw new CheckError('function.error-unknown', `fail is given ${aText(t)}, but function "${fnId}" fails with ${sig.errors.id}`);
        const a = n.args[0];
        const variant = a.t === 'ctor' || a.t === 'newtype' ? a.path[1] : a.t === 'ref' && a.res === 'unit' ? a.path[1] : undefined;
        if (variant === undefined) sig.fails = 'all';
        else if (sig.fails !== 'all') sig.fails.add(variant);
        return NEVER;
      }
    }
    throw refErr(`"${op}" is not an operation`);
  };

  /** @type {Map<string, FnType>} */
  let scope = new Map(sig.params.map((p) => [p.name, p.type]));
  list(sig.fn.data.let).forEach((l, i) => {
    const t = walk(sig.lets[i], scope);
    scope = new Map(scope);
    scope.set(l.name, t);
  });
  const body = walk(/** @type {FnAst} */ (sig.body), scope);
  if (!assignable(body, sig.returns)) throw tyErr(`The body of "${fnId}" is ${aText(body)}, but the function returns ${typeText(sig.returns)}`);
}

/** The operations whose result holds only items or values of their container (structural recursion). */
const SUB_VALUE_OPS = Object.freeze(['values', 'get', 'find', 'filter', 'take', 'sortBy']);

/**
 * Structural recursion (WG-4957): whether every call a typed function makes of itself passes, at one parameter
 * position shared by all of them, a strict sub-value of that parameter, which is a union. A strict sub-value is a
 * name bound by a match on the parameter (or on a sub-value of it) to a field of one of its union variants, an item
 * of a list held in such a field (x in items), an item or value such a container gives (values, get, find, filter,
 * take, sortBy), or a field read from any of these; Some(x) and Ok(x) of a sub-value bind a
 * sub-value as strict as the matched one, and a let passes a sub-value on. Each call then works on a strictly smaller
 * value than its caller, so the recursion ends.
 * @param {Signature} sig
 * @returns {{calls: number, position?: number, problem?: string}} calls is the number of self-calls; position the
 *   parameter they all decrease, or problem why there is none
 */
function selfRecursion(sig) {
  /** @typedef {{i: number, strict: boolean}|null} Origin */
  /** @type {Set<number>[]} */
  const found = [];
  /** @param {any} n @param {Map<string, Origin>} env @returns {Origin} */
  const origin = (n, env) => {
    if (n?.t === 'ref') {
      const o = env.get(n.path[0]);
      if (!o) return null;
      return n.path.length > 1 ? { i: o.i, strict: true } : o;
    }
    if (n?.t === 'field') {
      const o = origin(n.a, env);
      return o && { i: o.i, strict: true };
    }
    // The items and values of a container a sub-value holds are sub-values: values(m), get(m, k), get(xs, i),
    // find, filter, take and sortBy of it.
    if (n?.t === 'builtin' && SUB_VALUE_OPS.includes(n.name)) {
      const o = origin(n.binder ? n.binder.src : n.args[0], env);
      return o && { i: o.i, strict: true };
    }
    return null;
  };
  /** @param {Map<string, Origin>} env @param {string} name @param {Origin} o */
  const bind = (env, name, o) => { const e = new Map(env); e.set(name, o); return e; };
  /** @param {any} n @param {Map<string, Origin>} env */
  const walk = (n, env) => {
    if (!n || typeof n !== 'object') return;
    switch (n.t) {
      case 'let': walk(n.value, env); walk(n.body, bind(env, n.name, origin(n.value, env))); return;
      case 'match': {
        walk(n.e, env);
        const o = origin(n.e, env);
        const st = n.e.ty;
        for (const arm of n.arms) {
          let e = env;
          if (arm.pat.k === 'variant') {
            /** @type {Origin} */
            const sub = !o ? null : st?.k === 'union' ? { i: o.i, strict: true } : st?.k === 'option' || st?.k === 'result' ? o : null;
            if (arm.pat.bind !== undefined && arm.pat.bind !== '_') e = bind(e, arm.pat.bind, sub);
            for (const f of arm.pat.fields ?? []) if (f.bind !== '_') e = bind(e, f.bind, sub);
          }
          walk(arm.body, e);
        }
        return;
      }
      case 'builtin': {
        if (n.binder) {
          walk(n.binder.src, env);
          const o = origin(n.binder.src, env);
          let e = bind(env, n.binder.name, o && { i: o.i, strict: true });
          if (n.acc) { walk(n.acc.init, env); e = bind(e, n.acc.name, null); }
          n.args.forEach((/** @type {any} */ a) => walk(a, e));
          return;
        }
        n.args.forEach((/** @type {any} */ a) => walk(a, env));
        return;
      }
      case 'call': {
        n.args.forEach((/** @type {any} */ a) => walk(a, env));
        if (n.fn !== sig.fn.id) return;
        const ok = new Set();
        n.args.forEach((/** @type {any} */ a, /** @type {number} */ j) => { const o = origin(a, env); if (o && o.i === j && o.strict) ok.add(j); });
        found.push(ok);
        return;
      }
      default:
        for (const [k, v] of Object.entries(n)) {
          if (k === 'ty' || k === 'res' || !v || typeof v !== 'object') continue;
          if (Array.isArray(v)) v.forEach((x) => walk(x, env));
          else walk(v, env);
        }
    }
  };
  /** @type {Map<string, Origin>} */
  let env = new Map(sig.params.map((p, i) => [p.name, { i, strict: false }]));
  list(sig.fn.data.let).forEach((l, i) => {
    walk(sig.lets[i], env);
    env = bind(env, l.name, origin(sig.lets[i], env));
  });
  walk(sig.body, env);
  if (!found.length) return { calls: 0 };
  const unions = sig.params.map((p, i) => (p.type.k === 'union' ? i : -1)).filter((i) => i >= 0);
  const shared = unions.filter((i) => found.every((s) => s.has(i)));
  if (shared.length) return { calls: found.length, position: shared[0] };
  const problem = !unions.length
    ? 'no parameter is a union, so no call can be on a strict sub-value of one'
    : `no union parameter (${unions.map((i) => sig.params[i].name).join(', ')}) is given a strict sub-value of itself in every self-call: a field of a variant matched from it, or an item of a list in such a field`;
  return { calls: found.length, problem };
}

/**
 * Evaluate a typed function on decoded arguments. Returns {value} or {error}; throws FnEvalError.
 * @param {Model} model @param {Signature} sig @param {Map<string, Signature>} sigs @param {any[]} args
 * @returns {{value: any} | {error: any}}
 */
export function runFunction(model, sig, sigs, args) {
  try {
    return { value: call(model, sig, sigs, args) };
  } catch (e) {
    if (e instanceof Failure) return { error: e.value };
    throw e;
  }
}

/** @param {Model} model @param {Signature} sig @param {Map<string, Signature>} sigs @param {any[]} args */
function call(model, sig, sigs, args) {
  /** @type {Map<string, any>} */
  let env = new Map(sig.params.map((p, i) => [p.name, args[i]]));
  list(sig.fn.data.let).forEach((l, i) => {
    const v = ev(model, sig.lets[i], env, sigs);
    env = new Map(env);
    env.set(l.name, v);
  });
  return ev(model, /** @type {FnAst} */ (sig.body), env, sigs);
}

/** @param {Map<string, any>} env @param {string} name @param {any} v */
const bound = (env, name, v) => { const e = new Map(env); e.set(name, v); return e; };

/**
 * The branch recorder of src/core/function-coverage.js while it evaluates examples, null otherwise. Each branch
 * the evaluator takes is reported as (node, outcome): an if as "then" or "else", a match as "arm:<index>", a try
 * as "ok" or "err", a fail as "taken". Recording never changes what is evaluated.
 * @type {((node: FnAst, outcome: string) => void) | null}
 */
let branchHit = null;

/**
 * Run `run` with `recorder` receiving every branch the evaluator takes (see branchHit), then remove it.
 * @template T @param {(node: FnAst, outcome: string) => void} recorder @param {() => T} run @returns {T}
 */
export function withBranchRecorder(recorder, run) {
  const prior = branchHit;
  branchHit = recorder;
  try {
    return run();
  } finally {
    branchHit = prior;
  }
}

/**
 * @param {Model} model @param {FnAst} n @param {Map<string, any>} env @param {Map<string, Signature>} sigs
 * @returns {any}
 */
function ev(model, n, env, sigs) {
  const go = (/** @type {FnAst} */ x, e = env) => ev(model, x, e, sigs);
  switch (n.t) {
    case 'lit': return n.v;
    case 'unit': return UNIT;
    case 'ref': {
      if (n.res === 'enum') return n.path[1];
      if (n.res === 'unit') return new UnionValue(n.path[0], n.path[1], {});
      let v = env.get(n.path[0]);
      for (const f of n.path.slice(1)) v = v?.[f] ?? null;
      return v;
    }
    case 'field': return go(n.a)?.[n.name] ?? null;
    case 'un': {
      const a = go(n.a);
      if (n.op === '!') return !a;
      return intCheck(n.ty, '-', -a + 0);
    }
    case 'bin': {
      const op = n.op;
      if (op === '&&') return go(n.a) && go(n.b);
      if (op === '||') return go(n.a) || go(n.b);
      if (op === '=>') return !go(n.a) || go(n.b);
      const a = go(n.a), b = go(n.b);
      switch (op) {
        case '==': return valueEq(a, b);
        case '!=': return !valueEq(a, b);
        case '<': return a < b;
        case '<=': return a <= b;
        case '>': return a > b;
        case '>=': return a >= b;
        case '+': return typeof a === 'string' ? a + b : intCheck(n.ty, op, a + b);
        case '-': return intCheck(n.ty, op, a - b);
        case '*': return intCheck(n.ty, op, a * b);
        case '/': if (b === 0) throw new FnEvalError('Division by zero'); return intCheck(n.ty, op, isIntType(n.ty) ? Math.trunc(a / b) : a / b);
        case '%': if (b === 0) throw new FnEvalError('Division by zero'); return intCheck(n.ty, op, a % b);
      }
      break;
    }
    case 'if': {
      const c = go(n.c);
      branchHit?.(n, c ? 'then' : 'else');
      return c ? go(n.a) : go(n.b);
    }
    case 'let': return go(n.body, bound(env, n.name, go(n.value)));
    case 'match': {
      const v = go(n.e);
      const st = /** @type {FnType} */ (n.e.ty);
      /** @type {string} */
      let tag;
      /** @type {Record<string, any>} */
      let fields = {};
      if (st.k === 'option') { tag = v === null ? 'None' : 'Some'; fields = { value: v }; }
      else if (st.k === 'enum') tag = v;
      else { tag = v.variant; fields = v.fields; }
      for (const [i, arm] of n.arms.entries()) {
        if (arm.pat.k === 'wild') { branchHit?.(n, `arm:${i}`); return go(arm.body); }
        if (arm.pat.name !== tag) continue;
        branchHit?.(n, `arm:${i}`);
        let e = env;
        if (arm.pat.bind !== undefined && arm.pat.bind !== '_') e = bound(e, arm.pat.bind, Object.values(fields)[0]);
        for (const f of arm.pat.fields ?? []) if (f.bind !== '_') e = bound(e, f.bind, fields[f.field] ?? null);
        return go(arm.body, e);
      }
      throw new FnEvalError(`No arm of match takes ${tag}`);
    }
    case 'list': return Object.freeze(n.items.map((x) => go(x)));
    case 'emptymap': return new Map();
    case 'ctor': {
      /** @type {Record<string, any>} */
      const fields = {};
      const t = /** @type {any} */ (n.ty);
      const declared = n.path.length === 1 ? t.fields : t.variants.find((/** @type {any} */ v) => v.name === n.path[1]).fields;
      for (const f of declared) fields[f.name] = null;
      for (const g of n.fields) fields[g.name] = go(g.e);
      return n.path.length === 1 ? Object.freeze(fields) : new UnionValue(n.path[0], n.path[1], fields);
    }
    case 'newtype': {
      const t = /** @type {any} */ (n.ty);
      const v = t.variants.find((/** @type {any} */ x) => x.name === n.path[1]);
      return new UnionValue(n.path[0], n.path[1], { [v.fields[0].name]: go(n.arg) });
    }
    case 'call': {
      const callee = /** @type {Signature} */ (sigs.get(n.fn));
      const args = n.args.map((a) => go(a));
      if (!callee.errors) return call(model, callee, sigs, args);
      const r = runFunction(model, callee, sigs, args);
      return 'value' in r ? ok(r.value) : errOf(r.error);
    }
    case 'try': {
      const r = go(n.e);
      if (r.variant === 'Err') { branchHit?.(n, 'err'); throw new Failure(r.fields.error); }
      branchHit?.(n, 'ok');
      return r.fields.value;
    }
    case 'builtin': return builtin(model, n, env, sigs);
  }
  throw new FnEvalError('Malformed expression');
}

/** Integer arithmetic is checked in the static type of the expression. @param {any} ty @param {string} op @param {number} r */
function intCheck(ty, op, r) {
  if (!ty || !isIntType(ty)) return r;
  const name = /** @type {string} */ (primName(ty));
  const [lo, hi] = INT_RANGES[name];
  if (!Number.isInteger(r) || r < lo || r > hi) throw new FnEvalError(`Integer overflow: "${op}" on ${name} gives ${String(r)}, outside ${lo}..${hi}`);
  return r + 0;
}

/** @param {Model} model @param {Extract<FnAst, {t: 'builtin'}>} n @param {Map<string, any>} env @param {Map<string, Signature>} sigs */
function builtin(model, n, env, sigs) {
  const go = (/** @type {FnAst} */ x, e = env) => ev(model, x, e, sigs);
  if (n.binder) {
    const xs = /** @type {any[]} */ (go(n.binder.src));
    const name = n.binder.name;
    const body = n.args[0];
    const at = (/** @type {any} */ x) => go(body, bound(env, name, x));
    switch (n.name) {
      case 'map': return Object.freeze(xs.map(at));
      case 'filter': return Object.freeze(xs.filter(at));
      case 'find': return xs.find(at) ?? null;
      case 'any': return xs.some(at);
      case 'all': return xs.every(at);
      case 'sortBy': return Object.freeze(xs.map((x) => ({ x, k: at(x) })).sort((a, b) => compareOrdered(/** @type {FnType} */ (body.ty), a.k, b.k)).map((p) => p.x));
      case 'fold': {
        const acc = /** @type {any} */ (n.acc);
        let a = go(acc.init);
        for (const x of xs) a = go(body, bound(bound(env, acc.name, a), name, x));
        return a;
      }
    }
  }
  const args = n.name === 'eval' || n.name === 'check' || n.name === 'print' ? [null, ...n.args.slice(1).map((a) => go(a))] : n.name === 'fail' ? [] : n.args.map((a) => go(a));
  switch (n.name) {
    case 'take': return Object.freeze(args[0].slice(0, Math.max(0, args[1])));
    case 'concat': return Object.freeze([...args[0], ...args[1]]);
    case 'keys': return Object.freeze([...args[0].keys()].sort(compareKeys));
    case 'values': return Object.freeze([...args[0].keys()].sort(compareKeys).map((k) => args[0].get(k)));
    case 'get': {
      if (Array.isArray(args[0])) return Number.isInteger(args[1]) && args[1] >= 0 && args[1] < args[0].length ? args[0][args[1]] : null;
      return args[0].has(args[1]) ? args[0].get(args[1]) : null;
    }
    case 'insert': { const m = new Map(args[0]); m.set(args[1], args[2]); return m; }
    case 'remove': { const m = new Map(args[0]); m.delete(args[1]); return m; }
    case 'format': {
      const [text, ...rest] = args;
      let i = 0;
      return String(text).replace(FORMAT_HOLE, (hole) => {
        const k = i++;
        const t = /** @type {FnType} */ (n.args[k + 1].ty ?? UNKNOWN);
        if (hole === '{:?}') return debugValue(t, rest[k]);
        if (hole === '{:json}') return jsonText(t, rest[k]);
        return displayValue(rest[k], t);
      });
    }
    case 'eval': case 'check': case 'print': {
      const first = /** @type {any} */ (n.args[0]);
      const lang = /** @type {Entity} */ (model.entities.get(first.path[0]));
      if (n.name === 'print') return printLanguage(model, lang, args[1]);
      return n.name === 'eval' ? evalLanguage(model, lang, args[1], args[2], args[3]) : checkLanguage(model, lang, args[1], args[2]);
    }
    case 'startsWith': return String(args[0]).startsWith(args[1]);
    case 'endsWith': return String(args[0]).endsWith(args[1]);
    case 'length': return Array.isArray(args[0]) ? args[0].length : [...String(args[0])].length;
    case 'trim': return String(args[0]).replace(RUST_TRIM, '');
    case 'chars': return Object.freeze([...String(args[0])]);
    case 'snakeCase': return snakeCase(String(args[0]));
    case 'isAsciiLowercase': return charsAll(args[0], /^[a-z]$/);
    case 'isAsciiUppercase': return charsAll(args[0], /^[A-Z]$/);
    case 'isAsciiAlphabetic': return charsAll(args[0], /^[A-Za-z]$/);
    case 'isAsciiDigit': return charsAll(args[0], /^[0-9]$/);
    case 'isAsciiAlphanumeric': return charsAll(args[0], /^[A-Za-z0-9]$/);
    case 'parseTime': return parseTime(String(args[0]));
    case 'fail': {
      const value = go(n.args[0]);
      branchHit?.(n, 'taken');
      throw new Failure(value);
    }
  }
  throw new FnEvalError(`Unknown operation ${n.name}`);
}

/** The placeholders of format: {} (Display), {:?} (Rust's derived Debug) and {:json} (JSON text). */
const FORMAT_HOLE = /\{(?::\?|:json)?\}/g;

/** The kind of each placeholder of a format text, in order. @param {string} text @returns {('display'|'debug'|'json')[]} */
function formatHoles(text) {
  return [...text.matchAll(FORMAT_HOLE)].map((m) => (m[0] === '{:?}' ? 'debug' : m[0] === '{:json}' ? 'json' : 'display'));
}

/** Rust's White_Space characters, which str::trim removes from both ends (U+0085 is one; U+FEFF is not). */
const WS = '\\t\\n\\v\\f\\r \\u0085\\u00a0\\u1680\\u2000-\\u200a\\u2028\\u2029\\u202f\\u205f\\u3000';
const RUST_TRIM = new RegExp(`^[${WS}]+|[${WS}]+$`, 'g');

/** Whether a string is non-empty and every character is in the class (Rust char::is_ascii_*, for one character). @param {any} s @param {RegExp} cls */
function charsAll(s, cls) {
  const cs = [...String(s)];
  return cs.length > 0 && cs.every((c) => cls.test(c));
}

/**
 * The kernel's snake_case of a PascalCase name (crates/kernel/src/transition.rs snake_case): every ASCII capital
 * becomes its lower case, preceded by _ unless it is the first character; every other character is kept.
 * @param {string} name
 */
function snakeCase(name) {
  let out = '';
  [...name].forEach((c, i) => {
    if (c >= 'A' && c <= 'Z') out += (i > 0 ? '_' : '') + c.toLowerCase();
    else out += c;
  });
  return out;
}

/** Rust's i64::from_str: an optional + or -, then one or more ASCII digits, within the i64 range. @param {string} s @returns {number|undefined} */
function parseI64(s) {
  if (!/^[+-]?[0-9]+$/.test(s)) return undefined;
  const b = BigInt(s);
  if (b < -(2n ** 63n) || b > 2n ** 63n - 1n) return undefined;
  return Number(b);
}

/** Days since the Unix epoch of a proleptic Gregorian date (crates/substrate/src/plain.rs days_from_civil). @param {number} year @param {number} month @param {number} day */
function daysFromCivil(year, month, day) {
  const div = (/** @type {number} */ a, /** @type {number} */ b) => Math.trunc(a / b);
  const y = month <= 2 ? year - 1 : year;
  const era = div(y >= 0 ? y : y - 399, 400);
  const yoe = y - era * 400;
  const doy = div(153 * (month + (month > 2 ? -3 : 9)) + 2, 5) + day - 1;
  const doe = yoe * 365 + div(yoe, 4) - div(yoe, 100) + doy;
  return era * 146097 + doe - 719468;
}

/**
 * crates/substrate/src/plain.rs parse_time: YYYY-MM-DD or YYYY-MM-DDTHH:MM[:SS]Z (UTC) as milliseconds since the
 * epoch, Ok, or Err "not a UTC timestamp: <the text as Rust's {:?} writes it>". The date and time split at the first
 * T; the year is four characters; each number is read as Rust's i64::from_str reads it (a sign is allowed); month
 * 1..12, day 1..31 (any month), hour 0..23, minute and second 0..59.
 * @param {string} text
 */
function parseTime(text) {
  const bad = () => errOf(`not a UTC timestamp: ${rustDebugStr(text)}`);
  const at = text.indexOf('T');
  let date = text;
  /** @type {string|undefined} */
  let time;
  if (at >= 0) {
    date = text.slice(0, at);
    const rest = text.slice(at + 1);
    if (!rest.endsWith('Z')) return bad();
    time = rest.slice(0, -1);
  }
  const parts = date.split('-');
  if (parts.length !== 3 || new TextEncoder().encode(parts[0]).length !== 4) return bad();
  const [year, month, day] = parts.map(parseI64);
  if (year === undefined || month === undefined || day === undefined) return bad();
  if (month < 1 || month > 12 || day < 1 || day > 31) return bad();
  let seconds = daysFromCivil(year, month, day) * 86400;
  if (time !== undefined) {
    const tp = time.split(':');
    if (tp.length < 2 || tp.length > 3) return bad();
    const hour = parseI64(tp[0]), minute = parseI64(tp[1]);
    const second = tp.length === 3 ? parseI64(tp[2]) : 0;
    if (hour === undefined || minute === undefined || second === undefined) return bad();
    if (hour < 0 || hour >= 24 || minute < 0 || minute >= 60 || second < 0 || second >= 60) return bad();
    seconds += hour * 3600 + minute * 60 + second;
  }
  return ok(seconds * 1000);
}

/**
 * The signatures of every function: parsed params, return, errors, lets and body. Findings of function.param,
 * function.error-unknown and function.expr-syntax are reported here.
 * @param {Model} model
 * @param {(code: string, e: Entity, message: string, sub?: (string|number)[]) => void} err
 * @returns {Map<string, Signature>}
 */
function signatures(model, err) {
  /** @type {Map<string, Signature>} */
  const sigs = new Map();
  for (const fn of model.byKind.function ?? []) {
    const d = fn.data;
    let okSig = true;
    /** @param {string} code @param {string} message @param {(string|number)[]} [sub] */
    const report = (code, message, sub) => { if (okSig) err(code, fn, message, sub); okSig = false; };
    const names = new Set();
    /** @type {{name: string, type: FnType}[]} */
    const params = [];
    list(d.params).forEach((p, i) => {
      if (!isObj(p) || !isBindableName(p.name)) { report('function.param', `Parameter ${i + 1} of function "${fn.id}" needs a "name" that is a plain name and not a keyword (found ${JSON.stringify(p?.name)}).`, ['params', i, 'name']); return; }
      if (names.has(p.name)) report('function.param', `Function "${fn.id}" has the parameter "${p.name}" twice.`, ['params', i, 'name']);
      names.add(p.name);
      const t = fnTypeOf(model, p.type);
      if (!t) report('function.param', `Parameter "${p.name}" of function "${fn.id}" has ${p.type === undefined ? 'no type' : `type "${p.type}", which does not resolve`}.`, ['params', i, 'type']);
      params.push({ name: p.name, type: t ?? UNKNOWN });
    });
    if (d.params !== undefined && !Array.isArray(d.params)) report('function.param', `The "params" of function "${fn.id}" is a list of {name, type}.`, ['params']);
    const returns = fnTypeOf(model, d.returns);
    if (!returns) report('function.param', `Function "${fn.id}" returns ${d.returns === undefined ? 'nothing stated' : `"${d.returns}", which does not resolve`}; "returns" is a type.`, ['returns']);
    /** @type {any} */
    let errors;
    if (d.errors !== undefined) {
      const t = typeof d.errors === 'string' ? typeStructure(model, d.errors) : undefined;
      if (t?.k !== 'union') report('function.error-unknown', `The errors of function "${fn.id}", ${JSON.stringify(d.errors)}, ${t ? 'is not a union type' : 'is not a declared type'}; errors names the union of the ways it can fail.`, ['errors']);
      else errors = t;
    }
    /** @type {FnAst[]} */
    const lets = [];
    list(d.let).forEach((l, i) => {
      if (!isObj(l) || !isBindableName(l.name)) { report('function.param', `Let ${i + 1} of function "${fn.id}" needs a "name" that is a plain name and not a keyword.`, ['let', i, 'name']); lets.push({ t: 'lit', v: null }); return; }
      if (names.has(l.name)) report('function.param', `Let "${l.name}" of function "${fn.id}" has the name of a parameter or an earlier let.`, ['let', i, 'name']);
      names.add(l.name);
      const r = parseFnExpr(l.expr);
      if (!r.ok) { report('function.expr-syntax', `Let "${l.name}" of function "${fn.id}" does not parse: ${r.error.message} (at ${r.error.pos}).`, ['let', i, 'expr']); lets.push({ t: 'lit', v: null }); }
      else lets.push(r.ast);
    });
    const r = parseFnExpr(d.body);
    /** @type {FnAst|undefined} */
    let body;
    if (!r.ok) report('function.expr-syntax', `The body of function "${fn.id}" does not parse: ${r.error.message} (at ${r.error.pos}).`, ['body']);
    else body = r.ast;
    sigs.set(fn.id, { fn, params, returns: returns ?? UNKNOWN, errors, lets, body, ok: okSig, fails: new Set() });
  }
  return sigs;
}

/**
 * The functions on a cycle of the call graph, each cycle once, in declaration order.
 * @param {Map<string, Signature>} sigs @returns {string[][]}
 */
function cycles(sigs) {
  /** @type {Map<string, string[]>} */
  const edges = new Map();
  for (const [id, s] of sigs) {
    // A structural call of itself ends (selfRecursion); it is no edge of the graph that must be acyclic.
    const calls = [...s.lets, ...(s.body ? [s.body] : [])].flatMap(calledFunctions).filter((c) => sigs.has(c) && !(c === id && s.structural));
    edges.set(id, [...new Set(calls)]);
  }
  /** @param {string} from */
  const reach = (from) => {
    const seen = new Set();
    const stack = [...(edges.get(from) ?? [])];
    while (stack.length) {
      const n = /** @type {string} */ (stack.pop());
      if (seen.has(n)) continue;
      seen.add(n);
      stack.push(...(edges.get(n) ?? []));
    }
    return seen;
  };
  const reached = new Map([...sigs.keys()].map((id) => [id, reach(id)]));
  /** @type {string[][]} */
  const out = [];
  const done = new Set();
  for (const id of sigs.keys()) {
    if (done.has(id) || !reached.get(id)?.has(id)) continue;
    const cycle = [...sigs.keys()].filter((o) => reached.get(id)?.has(o) && reached.get(o)?.has(id));
    cycle.forEach((c) => done.add(c));
    out.push(cycle);
  }
  return out;
}

/**
 * The functions a function calls, directly or not, itself excluded unless on a cycle.
 * @param {Map<string, Signature>} sigs @param {string} id
 */
export function callees(sigs, id) {
  const seen = new Set();
  const s0 = sigs.get(id);
  const stack = s0 ? [...s0.lets, ...(s0.body ? [s0.body] : [])].flatMap(calledFunctions) : [];
  while (stack.length) {
    const n = /** @type {string} */ (stack.pop());
    if (seen.has(n) || !sigs.has(n)) continue;
    seen.add(n);
    const s = /** @type {Signature} */ (sigs.get(n));
    stack.push(...[...s.lets, ...(s.body ? [s.body] : [])].flatMap(calledFunctions));
  }
  return seen;
}

/**
 * Parse, type and order every function: the signatures with each one's ok flag, and the findings.
 * @param {Model} model
 */
export function analyzeFunctions(model) {
  /** @type {Diagnostic[]} */
  const out = [];
  /** @param {string} code @param {Entity} e @param {string} message @param {(string|number)[]} [sub] */
  const err = (code, e, message, sub = []) => out.push({ code, severity: 'error', message, entityId: e.id, loc: e.loc, path: [...e.path, ...sub] });
  const sigs = signatures(model, err);
  for (const s of sigs.values()) {
    if (!s.ok || !s.body) continue;
    try {
      typeFunction(model, s, sigs);
    } catch (e) {
      if (!(e instanceof CheckError)) throw e;
      err(e.code, s.fn, `Function "${s.fn.id}": ${e.message}.`, ['body']);
      s.ok = false;
    }
  }
  for (const s of sigs.values()) {
    // Only a typed body tells a union match from another; an untyped one already has its finding.
    if (!s.body) continue;
    if (!s.ok) { s.structural = true; continue; }
    const r = selfRecursion(s);
    s.structural = r.calls > 0 && r.position !== undefined;
    if (r.problem) s.recursionProblem = r.problem;
  }
  for (const cycle of cycles(sigs)) {
    const first = /** @type {Signature} */ (sigs.get(cycle[0]));
    const why = cycle.length === 1 && first.recursionProblem
      ? `; a function may call itself only on a strict sub-value of a union parameter (structural recursion), but ${first.recursionProblem}`
      : '; the call graph must be acyclic, but for a function that calls itself on a strict sub-value of a union parameter, so that every function is total';
    err('function.recursion', first.fn, `Function "${first.fn.id}" calls itself${cycle.length > 1 ? ` through ${cycle.slice(1).join(', ')}` : ''}${why}.`, ['body']);
    for (const c of cycle) /** @type {Signature} */ (sigs.get(c)).ok = false;
  }
  return { sigs, diagnostics: out };
}

/**
 * The error variants a function can fail with: the ones its own fail expressions name, and those of the
 * functions it calls with try (all of a union when a fail is not given a constructor).
 * @param {Map<string, Signature>} sigs @param {string} id @returns {string[]}
 */
export function failVariants(sigs, id) {
  const s = sigs.get(id);
  if (!s?.errors) return [];
  const all = s.errors.variants.map((v) => v.name);
  /** @type {Set<string>} */
  const out = new Set();
  /** @param {Signature} x */
  const add = (x) => { if (x.fails === 'all') all.forEach((v) => out.add(v)); else x.fails.forEach((v) => out.add(v)); };
  add(s);
  // A callee's failures pass on only through try, and only within one error union.
  /** @param {Signature} x @param {Set<string>} seen */
  const through = (x, seen) => {
    /** @param {any} n */
    const walk = (n) => {
      if (!n || typeof n !== 'object') return;
      if (Array.isArray(n)) { n.forEach(walk); return; }
      if (n.t === 'try' && n.e?.t === 'call') {
        const c = sigs.get(n.e.fn);
        if (c && !seen.has(c.fn.id)) { seen.add(c.fn.id); add(c); through(c, seen); }
      }
      for (const [k, v] of Object.entries(n)) if (k !== 'ty' && k !== 'res' && typeof v === 'object') walk(v);
    };
    [...x.lets, x.body].forEach(walk);
  };
  through(s, new Set([id]));
  return all.filter((v) => out.has(v));
}

/**
 * The fixture table of each model. A model does not change once derived, and every function example that names a
 * fixture asks for the table: decoding every fixture again for each example made validating a specification with
 * many examples and fixtures take minutes.
 * @type {WeakMap<Model, Map<string, {e: Entity, type?: FnType, problem?: string}>>}
 */
const FIXTURE_TABLES = new WeakMap();

/**
 * The fixtures of the model by id, each with its type and, when its value is not that type, why not. Memoized per
 * model; callers only read it.
 * @param {Model} model
 * @returns {Map<string, {e: Entity, type?: FnType, problem?: string}>}
 */
function fixtureTable(model) {
  const hit = FIXTURE_TABLES.get(model);
  if (hit) return hit;
  /** @type {Map<string, {e: Entity, type?: FnType, problem?: string}>} */
  const table = new Map();
  FIXTURE_TABLES.set(model, table);
  for (const e of model.byKind.exampleFixture ?? []) {
    const type = fnTypeOf(model, e.data.type);
    /** @type {string|undefined} */
    let problem;
    if (!type) problem = `Example fixture "${e.id}" has ${e.data.type === undefined ? 'no type' : `type "${e.data.type}", which does not resolve`}.`;
    else {
      try {
        decodeValue(type, 'value' in e.data ? e.data.value : null, 'value');
      } catch (x) {
        if (!(x instanceof FnEvalError)) throw x;
        problem = `The value of example fixture "${e.id}" is not a ${typeText(type)}: ${x.message}.`;
      }
    }
    table.set(e.id, { e, type, problem });
  }
  return table;
}

/** Whether a value of the fixture's type stands where `to` is expected: the same type, or an option of it. @param {FnType} from @param {FnType} to */
function fixtureFits(from, to) {
  return typeText(from) === typeText(to) || (to.k === 'option' && typeText(to.of) === typeText(from));
}

/**
 * An example value with a fixture reference replaced by the fixture's value (and its overrides). `expected` is the
 * type the value stands for (none: no type check). A problem is {code, message}; skip is a reference to a fixture
 * whose own value is wrong, already reported.
 * @param {Map<string, {e: Entity, type?: FnType, problem?: string}>} table @param {any} v @param {FnType|undefined} expected
 * @returns {{json: any} | {skip: true} | {code: string, message: string}}
 */
function resolveExampleValue(table, v, expected) {
  if (!isFixtureRef(v)) return { json: v };
  const f = table.get(v.fixture);
  if (!f) return { code: 'example.fixture-unknown', message: `it refers to the fixture "${v.fixture}", which is not declared in exampleFixtures` };
  if (f.problem || !f.type) return { skip: true };
  if (expected && !fixtureFits(f.type, expected)) return { code: 'example.fixture-type', message: `the fixture "${v.fixture}" is a ${typeText(f.type)}, but a ${typeText(expected)} stands here` };
  let json = structuredClone(f.e.data.value ?? null);
  if (v.with !== undefined) {
    if (!isObj(v.with)) return { code: 'example.fixture-override', message: `"with" of the fixture "${v.fixture}" is an object of dotted path to value` };
    for (const [path, value] of Object.entries(v.with)) {
      try {
        const segs = path.split('.');
        if (segs.some((x) => x === '')) throw new OverrideError('a path is names and indexes joined by dots');
        json = setAtPath(json, f.type, segs, value);
      } catch (x) {
        if (!(x instanceof OverrideError)) throw x;
        return { code: 'example.fixture-override', message: `the override "${path}" of the fixture "${v.fixture}" does not lead into its value: ${x.message}` };
      }
    }
    if (expected) {
      try {
        decodeValue(expected, json, 'value');
      } catch (x) {
        if (!(x instanceof FnEvalError)) throw x;
        return { code: 'example.fixture-type', message: `the fixture "${v.fixture}" with its overrides is not a ${typeText(expected)}: ${x.message}` };
      }
    }
  }
  return { json };
}

/**
 * The arguments, result and error of an example with the fixtures resolved (for code that reads examples, such as
 * tests); a reference that cannot be resolved throws.
 * @param {Model} model @param {Signature} s @param {any} ex
 * @returns {{args: any[], result?: any, error?: any}}
 */
export function resolvedExample(model, s, ex) {
  const table = fixtureTable(model);
  /** @param {any} v @param {FnType|undefined} t */
  const one = (v, t) => {
    const r = resolveExampleValue(table, v, t);
    if ('json' in r) return r.json;
    throw new Error('code' in r ? `${r.code}: ${r.message}` : 'a fixture with a wrong value');
  };
  const out = /** @type {{args: any[], result?: any, error?: any}} */ ({ args: s.params.map((p) => one(ex.args[p.name] ?? null, p.type)) });
  if ('result' in ex) out.result = one(ex.result, s.returns);
  if ('error' in ex) out.error = one(ex.error, s.errors);
  return out;
}

/**
 * The consistency rules of functions, including the evaluation of every example.
 * @param {Model} model @returns {Diagnostic[]}
 */
export function checkFunctions(model) {
  const { sigs, diagnostics: out } = analyzeFunctions(model);
  const fixtures = fixtureTable(model);
  for (const f of fixtures.values()) {
    if (f.problem) out.push({ code: 'example.fixture-type', severity: 'error', message: f.problem, entityId: f.e.id, loc: f.e.loc, path: [...f.e.path, ...(f.type ? ['value'] : ['type'])] });
  }
  for (const s of sigs.values()) {
    const fn = s.fn;
    const usable = s.ok && [...callees(sigs, fn.id)].every((c) => sigs.get(c)?.ok);
    if (!usable) continue;
    list(fn.data.examples).forEach((ex, i) => {
      const at = ['examples', i];
      /** @param {string} message */
      const fail = (message) => out.push({ code: 'function.example-failed', severity: 'error', message: `Example ${i + 1} of function "${fn.id}": ${message}`, entityId: fn.id, loc: fn.loc, path: [...fn.path, ...at] });
      if (!isObj(ex) || !isObj(ex.args) || ('result' in ex) === ('error' in ex)) { fail('an example is {args, result} or {args, error}, with args an object of the parameters.'); return; }
      const extra = Object.keys(ex.args).filter((k) => !s.params.some((p) => p.name === k));
      if (extra.length) { fail(`args names ${extra.map((k) => `"${k}"`).join(', ')}, which ${extra.length === 1 ? 'is not a parameter' : 'are not parameters'}.`); return; }
      if ('error' in ex && !s.errors) { fail('it expects an error, but the function declares no errors.'); return; }
      // Fixture references become the fixture's value; a reference that cannot is reported once, here.
      let unresolved = false;
      /** @param {any} v @param {FnType|undefined} expected @param {(string|number)[]} sub */
      const resolve = (v, expected, sub) => {
        const r = resolveExampleValue(fixtures, v, expected);
        if ('json' in r) return r.json;
        unresolved = true;
        if ('code' in r) out.push({ code: r.code, severity: 'error', message: `Example ${i + 1} of function "${fn.id}", ${sub.join('.')}: ${r.message}.`, entityId: fn.id, loc: fn.loc, path: [...fn.path, ...at, ...sub] });
        return undefined;
      };
      const argJson = s.params.map((p) => resolve(ex.args[p.name] ?? null, p.type, ['args', p.name]));
      const resultJson = 'result' in ex ? resolve(ex.result, s.returns, ['result']) : undefined;
      const errorJson = 'error' in ex ? resolve(ex.error, s.errors, ['error']) : undefined;
      if (unresolved) return;
      try {
        const args = s.params.map((p, k) => decodeValue(p.type, argJson[k], `args.${p.name}`));
        const got = runFunction(model, s, sigs, args);
        if ('result' in ex) {
          const want = decodeValue(s.returns, resultJson, 'result');
          if ('error' in got) fail(`expected ${JSON.stringify(resultJson)}, but it failed with ${JSON.stringify(encodeTyped(/** @type {FnType} */ (s.errors), got.error))}.`);
          else if (!valueEq(got.value, want)) fail(`expected ${JSON.stringify(resultJson)}, but it gave ${JSON.stringify(encodeTyped(s.returns, got.value))}.`);
        } else {
          const want = decodeValue(/** @type {FnType} */ (s.errors), errorJson, 'error');
          if ('value' in got) fail(`expected the error ${JSON.stringify(errorJson)}, but it gave ${JSON.stringify(encodeTyped(s.returns, got.value))}.`);
          else if (!valueEq(got.error, want)) fail(`expected the error ${JSON.stringify(errorJson)}, but it failed with ${JSON.stringify(encodeTyped(/** @type {FnType} */ (s.errors), got.error))}.`);
        }
      } catch (e) {
        if (!(e instanceof FnEvalError)) throw e;
        fail(e.message);
      }
    });
  }
  return out;
}

/**
 * Readiness of functions: a success example, and an example for every error variant the function can fail with.
 * @param {Model} model @returns {Gap[]}
 */
export function functionReadiness(model) {
  /** @type {Gap[]} */
  const out = [];
  const { sigs } = analyzeFunctions(model);
  const fixtures = fixtureTable(model);
  for (const s of sigs.values()) {
    const fn = s.fn;
    const examples = list(fn.data.examples).filter(isObj);
    /** @param {string} message */
    const gap = (message) => out.push({ code: 'ready.function-example-missing', severity: 'error', message, entityId: fn.id });
    if (!examples.some((ex) => 'result' in ex)) gap(`Function "${fn.id}" has no example that succeeds ({args, result}).`);
    if (!s.ok) continue;
    const covered = new Set(examples.filter((ex) => 'error' in ex).map((ex) => {
      const r = resolveExampleValue(fixtures, ex.error, undefined);
      const e = 'json' in r ? r.json : undefined;
      return typeof e === 'string' ? e : isObj(e) ? Object.keys(e)[0] : undefined;
    }));
    for (const v of failVariants(sigs, fn.id)) {
      if (!covered.has(v)) gap(`Function "${fn.id}" can fail with ${/** @type {any} */ (s.errors).id}.${v} but no example shows it ({args, error: {"${v}": ...}}).`);
    }
  }
  return out;
}

export { RESULT_TYPE };
