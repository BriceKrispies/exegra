// Evaluating, checking and printing an expression of a declared language (WG-4929) in JavaScript, for the eval,
// check and print operations of function bodies (WG-4933, WG-4957). Exegra runs this only to evaluate the examples
// of functions; the meaning of each operator is the one its primitive has in the catalogue of src/core/language.js,
// and the code a generator produces follows the kernel (crates/kernel/src/expr.rs), not this file. Not mirrored in
// Lean.
//
// An expression is a value of the language's AST union, never source text: the kernel stores parsed expressions.
// eval reads names from an environment struct with one field per scope, named as the scope:
//   record-scope  option<map<string, V>>   the record's fields and system attributes ($id, ...), null for no record
//   param         map<string, V>           the parameters supplied
//   constant      V                        the constant's value (now, principal)
//   role-test     list<string>             the roles the acting principal holds
// where V is the language's value union. Which variant of V is which kind of value (null, bool, int, string,
// time, ref, list) is read from the language's literal operators: the operator for literal form `int` names the
// variant of V that an int literal is. Following a reference (`through`) reads an optional lookup (WG-4968), a
// map<string, map<string, map<string, V>>>: for each reference field it covers, the records that exist, by the
// decimal text of the id the reference holds, each as a record scope is (its fields and system attributes). Without
// a lookup, or for a field it does not cover, following a reference is an evaluation error, as it is in the kernel
// without one or for a record the snapshot does not cover; a target the lookup covers but does not hold is null.
//
// check takes an environment struct {fields: map<string, string>, params: list<string>, roles: list<string>}: the
// shape of each field of the record at the definition site, the parameters and the roles declared there.
//
// The text of an error is the kernel's (expr.rs eval and check, as specc's generated evaluator writes it): the
// shared case table tests/fixtures/language/kernel-cases.json pins it.
//
// print writes an expression in the language's authoring syntax, as the kernel's Display for Expr does and as
// specc's generated printer does (crates/spec-compiler/src/language.rs, printer): the rules of the "Parsing and
// printing" table of docs/model-and-format.md.

import { LANGUAGE_PRIMITIVES, LITERAL_KINDS, SAFE_INT, MAX_TEXT_BYTES, INTEGER_OVERFLOW, STRING_TOO_LONG } from './language.js';
import { typeStructure } from './codegen-model.js';
import { UnionValue, FnEvalError, errOf, ok, valueEq, compareKeys, primName, rustDebugStr, rustPascal } from './function-value.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */

class LangError extends Error {}

/** @param {any} v */
const isObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);
/** @param {any} v @returns {any[]} */
const list = (v) => (Array.isArray(v) ? v : []);

/**
 * The kernel's FieldId rule (crates/kernel/src/ids.rs is_name): an ASCII lower-case letter, then lower-case
 * letters, digits and _, at most 64 bytes. A record name that is not one is an error of var, through and check.
 * @param {string} s
 */
export const isFieldName = (s) => typeof s === 'string' && s.length <= 64 && /^[a-z][a-z0-9_]*$/.test(s);

/**
 * What an evaluator needs to know about a language, read once.
 * @param {Model} model @param {Entity} lang
 */
function languageInfo(model, lang) {
  const d = lang.data;
  const astType = model.entities.get(d.ast);
  const variants = new Map(list(astType?.data.variants).filter(isObj).map((v) => [v.name, v]));
  const operators = list(d.operators).filter(isObj);
  /** @type {Map<string, string>} literal form -> variant of the value union */
  const kindVariant = new Map();
  /** @type {Map<string, string>} variant of the value union -> literal form */
  const variantKind = new Map();
  /** @type {Map<string, string>} literal form -> the shape its literal operator gives */
  const kindShape = new Map();
  for (const op of operators) {
    if (op.syntax?.form !== 'literal' || !isObj(op.case)) continue;
    kindVariant.set(op.syntax.token, op.case.value);
    variantKind.set(op.case.value, op.syntax.token);
    if (typeof op.result === 'string') kindShape.set(op.syntax.token, op.result);
  }
  const valuesType = model.entities.get(d.values);
  const valueVariants = new Map(list(valuesType?.data.variants).filter(isObj).map((v) => [v.name, v]));
  const scopes = list(d.scopes).filter(isObj);
  /** @type {Map<string, boolean>} a field type text -> whether it is a string (string, or an id or scalar over one) */
  const stringTypes = new Map();
  /** @param {any} text */
  const isString = (text) => {
    if (typeof text !== 'string') return false;
    if (!stringTypes.has(text)) {
      const t = typeStructure(model, text);
      stringTypes.set(text, t !== undefined && primName(t) === 'string');
    }
    return /** @type {boolean} */ (stringTypes.get(text));
  };
  return { d, astId: d.ast, valuesId: d.values, variants, operators, kindVariant, variantKind, kindShape, valueVariants, scopes, isString };
}

/** @typedef {ReturnType<typeof languageInfo>} Info */

/**
 * The operator that reads an AST value: the variant's operator, or the one for the value of its case field.
 * @param {Info} info @param {UnionValue} e
 */
function operatorFor(info, e) {
  const mine = info.operators.filter((op) => op.variant === e.variant);
  if (mine.length === 1 && !isObj(mine[0].case)) return mine[0];
  for (const op of mine) {
    if (!isObj(op.case)) continue;
    const v = e.fields[op.case.field];
    const value = v instanceof UnionValue ? v.variant : v;
    if (value === op.case.value) return op;
  }
  throw new LangError(`no operator of language reads ${e.variant}`);
}

/**
 * The expression operands of an AST value, in field order; an n-ary variant gives its list.
 * @param {Info} info @param {UnionValue} e @returns {any[]}
 */
function operandsOf(info, e) {
  const v = info.variants.get(e.variant);
  const out = [];
  for (const f of list(v?.fields)) {
    const t = typeof f.type === 'string' ? f.type.replace(/\s+/g, '') : '';
    if (t === `list<${info.astId}>`) return list(e.fields[f.name]);
    if (t === info.astId || t === `option<${info.astId}>`) out.push(e.fields[f.name]);
  }
  return out;
}

/**
 * The string fields of an AST value (a name, a field, a target, a role), in field order, and the record scope its
 * scope field names. A field is a string field when its type is string or an id or scalar over string (has-role's
 * role-id, WG-4962), resolved through the model.
 * @param {Info} info @param {UnionValue} e
 */
function namesOf(info, e) {
  const v = info.variants.get(e.variant);
  /** @type {string[]} */
  const strings = [];
  let scope;
  const records = info.scopes.filter((s) => s.kind === 'record-scope');
  for (const f of list(v?.fields)) {
    const x = e.fields[f.name];
    if (info.isString(f.type)) strings.push(x);
    else {
      const value = x instanceof UnionValue ? x.variant : x;
      const s = records.find((r) => r.value === value);
      if (s) scope = s;
    }
  }
  if (!scope && records.length === 1) scope = records[0];
  return { strings, scope };
}

/** The label a primitive's errors name: its operator's token (and, or, not, in, len, ...). @param {any} op */
const label = (op) => (typeof op.syntax?.token === 'string' ? op.syntax.token : op.name);

/**
 * An operand of checked arithmetic: an integer within ±(2^53-1), or the error integer-overflow. Example values are
 * decoded within that range already; the test keeps the evaluator correct for any number it is handed.
 * @param {any} n @returns {number}
 */
const safe = (n) => {
  if (typeof n !== 'number' || !Number.isSafeInteger(n)) throw new LangError(INTEGER_OVERFLOW);
  return n;
};

/**
 * The result of checked arithmetic on safe operands. The exact sum, difference or product of two safe integers is
 * outside ±(2^53-1) exactly when the double JavaScript computes is (rounding to nearest is monotonic and 2^53 is a
 * double), and inside that range the double is exact, so the test below decides on the exact value. -0 becomes 0.
 * @param {number} n @returns {number}
 */
const checked = (n) => {
  if (!(Math.abs(n) <= SAFE_INT)) throw new LangError(INTEGER_OVERFLOW);
  return n === 0 ? 0 : n;
};

/** Decimal digits of an integer, as Rust's Display of i64 and u64 writes them. @param {any} n */
const decimal = (n) => (n === 0 ? '0' : BigInt(n).toString());

/** The length of a string in bytes of UTF-8 (Rust's str::len). @param {string} s */
const utf8Length = (s) => {
  let n = 0;
  for (const c of s) {
    const cp = /** @type {number} */ (c.codePointAt(0));
    n += cp < 0x80 ? 1 : cp < 0x800 ? 2 : cp < 0x10000 ? 3 : 4;
  }
  return n;
};

/**
 * Evaluate an expression value. Returns result<V, string>: Ok of a value of the language's value union, or Err of
 * the kernel's message (crates/kernel/src/expr.rs eval).
 * @param {Model} model @param {Entity} lang @param {any} expr @param {Record<string, any>} env
 * @param {Map<string, Map<string, Map<string, any>>>|null} [lookup] where references may be followed; none when null
 * @returns {UnionValue}
 */
export function evalLanguage(model, lang, expr, env, lookup = null) {
  const info = languageInfo(model, lang);
  /** @param {string} kind @param {any} [payload] */
  const mk = (kind, payload) => {
    const variant = info.kindVariant.get(kind);
    if (variant === undefined) throw new LangError(`the language has no ${kind} literal`);
    const vv = info.valueVariants.get(variant);
    const f = list(vv?.fields)[0];
    return new UnionValue(info.valuesId, variant, f ? { [f.name]: payload } : {});
  };
  const NULL = () => mk('null');
  /** @param {any} v */
  const kind = (v) => (v instanceof UnionValue ? info.variantKind.get(v.variant) : undefined);
  /** The kernel's Value::kind name of a value, as messages write it. @param {any} v */
  const kindName = (v) => LITERAL_KINDS[/** @type {string} */ (kind(v))] ?? String(kind(v));
  /** @param {any} v */
  const payload = (v) => (v instanceof UnionValue ? Object.values(v.fields)[0] : undefined);
  /** @param {any} v */
  const isNull = (v) => kind(v) === 'null';
  /** @param {string} what @param {any} v */
  const typeError = (what, v) => new LangError(`${what} does not apply to a ${kindName(v)}`);
  /** A record scope's record: null, or a map of its fields and attributes. @param {any} scope */
  const recordOf = (scope) => {
    const r = scope ? env[scope.name] : undefined;
    return r instanceof Map ? r : null;
  };
  /** The kernel's attribute: a declared system attribute, or a field; null when unset. @param {Map<string, any>} record @param {any} scope @param {string} name */
  const attribute = (record, scope, name) => {
    if (list(scope?.attributes).some((a) => a.name === name)) return record.get(name) ?? NULL();
    if (!isFieldName(name)) throw new LangError(`unknown attribute ${name}`);
    return record.get(name) ?? NULL();
  };

  /** @param {any} e @returns {UnionValue} */
  const ev = (e) => {
    if (!(e instanceof UnionValue)) throw new LangError('not an expression');
    const op = operatorFor(info, e);
    const prim = op.primitive;
    const args = operandsOf(info, e);
    switch (prim) {
      case 'literal': case 'list-literal': return /** @type {any} */ (Object.values(e.fields).find((x) => x instanceof UnionValue && x.type === info.valuesId) ?? NULL());
      case 'and3': case 'or3': {
        const decisive = prim === 'or3';
        let sawNull = false;
        for (const item of args) {
          const v = ev(item);
          if (kind(v) === 'bool') { if (payload(v) === decisive) return mk('bool', decisive); }
          else if (isNull(v)) sawNull = true;
          else throw typeError(label(op), v);
        }
        return sawNull ? NULL() : mk('bool', !decisive);
      }
      case 'not3': {
        const v = ev(args[0]);
        if (kind(v) === 'bool') return mk('bool', !payload(v));
        if (isNull(v)) return v;
        throw typeError(label(op), v);
      }
      case 'eq': case 'ne': case 'lt': case 'le': case 'gt': case 'ge': {
        const a = ev(args[0]), b = ev(args[1]);
        if (isNull(a) || isNull(b)) return NULL();
        if (kindName(a) !== kindName(b)) throw new LangError(`cannot compare a ${kindName(a)} with a ${kindName(b)}`);
        if (prim === 'eq') return mk('bool', valueEq(a, b));
        if (prim === 'ne') return mk('bool', !valueEq(a, b));
        if (!['int', 'time', 'string'].includes(/** @type {string} */ (kind(a)))) throw typeError('ordering', a);
        const c = compareKeys(payload(a), payload(b));
        return mk('bool', prim === 'lt' ? c < 0 : prim === 'le' ? c <= 0 : prim === 'gt' ? c > 0 : c >= 0);
      }
      case 'in-list': {
        const a = ev(args[0]), b = ev(args[1]);
        if (isNull(a) || isNull(b)) return NULL();
        if (kind(b) !== 'list') throw typeError(label(op), b);
        return mk('bool', list(payload(b)).some((x) => valueEq(x, a)));
      }
      case 'is-null': return mk('bool', isNull(ev(args[0])));
      case 'len': {
        const a = ev(args[0]);
        if (isNull(a)) return a;
        if (kind(a) === 'string') return mk('int', [...payload(a)].length);
        if (kind(a) === 'list') return mk('int', list(payload(a)).length);
        throw typeError(label(op), a);
      }
      case 'lower': {
        const a = ev(args[0]);
        if (isNull(a)) return a;
        if (kind(a) !== 'string') throw typeError(label(op), a);
        return mk('string', String(payload(a)).toLowerCase());
      }
      case 'contains': {
        const a = ev(args[0]), b = ev(args[1]);
        if (isNull(a) || isNull(b)) return NULL();
        if (kind(a) === 'string' && kind(b) === 'string') return mk('bool', String(payload(a)).includes(payload(b)));
        if (kind(a) === 'list') return mk('bool', list(payload(a)).some((x) => valueEq(x, b)));
        throw typeError(label(op), a);
      }
      case 'starts-with': {
        const a = ev(args[0]), b = ev(args[1]);
        if (isNull(a) || isNull(b)) return NULL();
        if (kind(a) === 'string' && kind(b) === 'string') return mk('bool', String(payload(a)).startsWith(payload(b)));
        throw typeError(label(op), a);
      }
      case 'is-slug': {
        const a = ev(args[0]);
        if (isNull(a)) return a;
        if (kind(a) !== 'string') throw typeError(label(op), a);
        return mk('bool', /^[a-z0-9]+(-[a-z0-9]+)*$/.test(payload(a)));
      }
      case 'add-checked': case 'sub-checked': case 'mul-checked': {
        // Both operands first, left to right; then nulls; then the left's kind, then the right's.
        const a = ev(args[0]), b = ev(args[1]);
        if (isNull(a) || isNull(b)) return NULL();
        const left = prim === 'mul-checked' ? ['int'] : ['int', 'time'];
        if (!left.includes(/** @type {string} */ (kind(a)))) throw typeError(label(op), a);
        if (kind(b) !== 'int') throw typeError(label(op), b);
        const x = safe(payload(a)), y = safe(payload(b));
        return mk(/** @type {string} */ (kind(a)), checked(prim === 'add-checked' ? x + y : prim === 'sub-checked' ? x - y : x * y));
      }
      case 'time-difference': {
        const a = ev(args[0]), b = ev(args[1]);
        if (isNull(a) || isNull(b)) return NULL();
        if (kind(a) !== 'time') throw typeError(label(op), a);
        if (kind(b) !== 'time') throw typeError(label(op), b);
        return mk('int', checked(safe(payload(b)) - safe(payload(a))));
      }
      case 'days-ms': case 'hours-ms': case 'minutes-ms': {
        const a = ev(args[0]);
        if (isNull(a)) return a;
        if (kind(a) !== 'int') throw typeError(label(op), a);
        const unit = prim === 'days-ms' ? 86400000 : prim === 'hours-ms' ? 3600000 : 60000;
        return mk('int', checked(safe(payload(a)) * unit));
      }
      case 'concat-checked': {
        const a = ev(args[0]), b = ev(args[1]);
        if (isNull(a) || isNull(b)) return NULL();
        if (kind(a) !== 'string') throw typeError(label(op), a);
        if (kind(b) !== 'string') throw typeError(label(op), b);
        const s = String(payload(a)) + String(payload(b));
        if (utf8Length(s) > MAX_TEXT_BYTES) throw new LangError(STRING_TOO_LONG);
        return mk('string', s);
      }
      case 'to-text': {
        const a = ev(args[0]);
        if (isNull(a)) return a;
        const k = kind(a);
        if (k === 'string') return a;
        if (k === 'bool') return mk('string', payload(a) ? 'true' : 'false');
        if (k === 'int' || k === 'time' || k === 'ref') return mk('string', decimal(payload(a)));
        throw typeError(label(op), a);
      }
      case 'if': {
        const c = ev(args[0]);
        if (kind(c) === 'bool' && payload(c) === true) return ev(args[1]);
        if ((kind(c) === 'bool' && payload(c) === false) || isNull(c)) return ev(args[2]);
        throw typeError(label(op), c);
      }
      case 'has-role': {
        const roles = env[op.syntax.token];
        return mk('bool', list(roles).includes(namesOf(info, e).strings[0]));
      }
      case 'now': case 'principal': return env[op.syntax.token] ?? NULL();
      case 'param': {
        const m = env[op.syntax.token];
        const v = m instanceof Map ? m.get(namesOf(info, e).strings[0]) : undefined;
        return v ?? NULL();
      }
      case 'var': {
        const { strings, scope } = namesOf(info, e);
        if (!scope) throw new LangError('no record scope');
        const record = recordOf(scope);
        if (!record) return NULL();
        return attribute(record, scope, strings[0]);
      }
      case 'through': {
        // expr.rs Expr::Through: the reference field is read and followed through the lookup (WG-4968). Without a
        // lookup, or for a field the lookup does not cover, a reference cannot be followed.
        const { strings, scope } = namesOf(info, e);
        if (!scope) throw new LangError('no record scope');
        const record = recordOf(scope);
        if (!record) return NULL();
        const [field, target] = strings;
        if (!isFieldName(field)) throw new LangError(`invalid field identifier: ${rustDebugStr(field)}`);
        const v = record.get(field) ?? NULL();
        if (isNull(v)) return v;
        if (kind(v) !== 'ref') throw typeError('following a reference', v);
        if (!(lookup instanceof Map)) throw new LangError(`${field} cannot be followed here`);
        const covered = lookup.get(field);
        if (!(covered instanceof Map)) throw new LangError(`the lookup does not cover ${field}`);
        const found = covered.get(String(payload(v)));
        if (!(found instanceof Map)) return NULL();
        return found.get(target) ?? NULL();
      }
      default: throw new LangError(`operator ${op.name} has no primitive`);
    }
  };
  try {
    return ok(ev(expr));
  } catch (e) {
    if (e instanceof LangError) return errOf(e.message);
    throw e;
  }
}

/**
 * Check an expression value statically: result<string, string>, Ok of its shape or Err of the kernel's message
 * (crates/kernel/src/expr.rs check: "len does not accept a Int operand", "cannot compare Str with Int", ...).
 * Operands are checked in the kernel's order: for comparisons, in and contains both operands first, then their
 * shapes; for every other operator one operand after another.
 * @param {Model} model @param {Entity} lang @param {any} expr @param {Record<string, any>} env
 * @returns {UnionValue}
 */
export function checkLanguage(model, lang, expr, env) {
  const info = languageInfo(model, lang);
  const any = info.d.anyShape;
  const shapes = list(info.d.shapes);
  const fields = env.fields instanceof Map ? env.fields : new Map();
  const params = list(env.params);
  const roles = list(env.roles);
  const strShape = info.kindShape.get('string');
  const refShape = info.kindShape.get('ref');
  /** A shape as the kernel's {:?} of Shape writes it: Str, Int, Any. @param {string} s */
  const D = (s) => rustPascal(String(s));
  /** @param {string} shape @param {any} allowed @param {string} what */
  const expect = (shape, allowed, what) => {
    const a = allowed === undefined ? [any] : Array.isArray(allowed) ? allowed : [allowed];
    if (a.includes(any) || shape === any || a.includes(shape)) return;
    throw new LangError(`${what} does not accept a ${D(shape)} operand`);
  };
  /** A field's shape at the definition site (attribute_shape for a field). @param {string} name */
  const fieldShape = (name) => {
    if (!isFieldName(name)) throw new LangError(`invalid field identifier: ${rustDebugStr(name)}`);
    if (!fields.has(name)) throw new LangError(`unknown field ${name}`);
    const s = fields.get(name);
    if (!shapes.includes(s)) throw new LangError(`the field ${name} has the unknown shape ${s}`);
    return s;
  };
  /** @param {any} op */
  const result = (op) => (typeof op.result === 'string' ? op.result : any);
  /** @param {any} e @returns {string} */
  const sh = (e) => {
    if (!(e instanceof UnionValue)) throw new LangError('not an expression');
    const op = operatorFor(info, e);
    if (!LANGUAGE_PRIMITIVES[op.primitive]) throw new LangError(`operator ${op.name} has no primitive`);
    const ops = list(op.operands);
    const args = operandsOf(info, e);
    const what = label(op);
    switch (op.primitive) {
      case 'literal': case 'list-literal': return result(op);
      case 'var': {
        const { strings, scope } = namesOf(info, e);
        const a = list(scope?.attributes).find((x) => x.name === strings[0]);
        return a ? a.shape : fieldShape(strings[0]);
      }
      case 'through': {
        const { strings, scope } = namesOf(info, e);
        const [field, target] = strings;
        if (fieldShape(field) !== refShape) throw new LangError(`${field} is not a single reference`);
        const a = list(scope?.attributes).find((x) => x.name === target);
        if (a) return a.shape;
        if (!isFieldName(target)) throw new LangError(`invalid field identifier: ${rustDebugStr(target)}`);
        return any;
      }
      case 'param': {
        const name = namesOf(info, e).strings[0];
        if (!params.includes(name)) throw new LangError(`undeclared parameter ${name}`);
        return result(op);
      }
      case 'has-role': {
        const role = namesOf(info, e).strings[0];
        if (!roles.includes(role)) throw new LangError(`unknown role ${role}`);
        return result(op);
      }
      case 'now': case 'principal': return result(op);
      case 'and3': case 'or3':
        for (const item of args) expect(sh(item), ops[0], 'and/or');
        return result(op);
      case 'eq': case 'ne': case 'lt': case 'le': case 'gt': case 'ge': {
        const l = sh(args[0]), r = sh(args[1]);
        if (l !== any && r !== any && l !== r) throw new LangError(`cannot compare ${D(l)} with ${D(r)}`);
        expect(l, ops[0], 'ordering');
        expect(r, ops[1], 'ordering');
        return result(op);
      }
      case 'in-list': case 'contains': {
        const first = sh(args[0]), second = sh(args[1]);
        expect(first, ops[0], what);
        expect(second, ops[1], what);
        if (op.primitive === 'contains' && first === strShape) expect(second, [strShape], what);
        return result(op);
      }
      case 'if': {
        expect(sh(args[0]), ops[0], what);
        const t = sh(args[1]), o = sh(args[2]);
        if (t !== any && o !== any && t !== o) throw new LangError(`${what} branches differ: ${D(t)} and ${D(o)}`);
        return t === any ? o : t;
      }
      default: {
        // One operand after another: not, is_null, len, lower, starts_with, is_slug.
        const got = args.map((a, k) => { const s = sh(a); expect(s, ops[k], what); return s; });
        const m = typeof op.result === 'string' ? /^operand:([1-9][0-9]*)$/.exec(op.result) : null;
        if (m) return got[Number(m[1]) - 1] ?? any;
        return result(op);
      }
    }
  };
  try {
    return ok(sh(expr));
  } catch (e) {
    if (e instanceof LangError) return errOf(e.message);
    throw e;
  }
}

/**
 * Print an expression value in the language's authoring syntax: what the kernel's Display for Expr writes, byte for
 * byte, and what specc's generated printer writes (crates/spec-compiler/src/language.rs, printer). Per form:
 * binary `(a tok b)`; n-ary `(a tok b tok c)`, an empty list the primitive's identity (true for and3, false for
 * or3), one item `(a)`; prefix `tok(a)`; call `tok(a, b)`; literal null, true/false, an integer, a single-quoted
 * string with \' \\ and \n escaped, time(n), ref(n), [a, b]; scope `<record scope>.<name>`,
 * `<record scope>.<field>.<name>`, `<token>.<name>` for a parameter, `<token>(<role>)` for a role test, the token
 * for a constant.
 * @param {Model} model @param {Entity} lang @param {any} expr @returns {string}
 */
export function printLanguage(model, lang, expr) {
  const info = languageInfo(model, lang);
  /** @param {any} v @returns {string} */
  const value = (v) => {
    if (!(v instanceof UnionValue)) throw new FnEvalError('print: a literal holds something other than a value');
    const k = info.variantKind.get(v.variant);
    const x = Object.values(v.fields)[0];
    switch (k) {
      case 'null': return 'null';
      case 'bool': case 'int': return String(x);
      case 'time': return `time(${x})`;
      case 'ref': return `ref(${x})`;
      case 'string': {
        let out = "'";
        for (const c of String(x)) out += c === "'" ? "\\'" : c === '\\' ? '\\\\' : c === '\n' ? '\\n' : c;
        return `${out}'`;
      }
      case 'list': return `[${list(x).map(value).join(', ')}]`;
      default: throw new FnEvalError(`print: the value variant ${v.variant} has no literal form`);
    }
  };
  /** @param {any} e @returns {string} */
  const pr = (e) => {
    if (!(e instanceof UnionValue)) throw new FnEvalError('print: not an expression');
    let op;
    try { op = operatorFor(info, e); } catch (err) { throw new FnEvalError(`print: ${/** @type {Error} */ (err).message}`); }
    const syntax = op.syntax ?? {};
    const tok = syntax.token;
    switch (syntax.form) {
      case 'literal': return value(Object.values(e.fields).find((x) => x instanceof UnionValue && x.type === info.valuesId));
      case 'infix': case 'keyword-infix': {
        const args = operandsOf(info, e);
        if (syntax.assoc === 'n-ary') {
          if (!args.length) return op.primitive === 'and3' ? 'true' : 'false';
          return `(${args.map(pr).join(` ${tok} `)})`;
        }
        return `(${pr(args[0])} ${tok} ${pr(args[1])})`;
      }
      case 'prefix-word': return `${tok}(${pr(operandsOf(info, e)[0])})`;
      case 'call': return `${tok}(${operandsOf(info, e).map(pr).join(', ')})`;
      case 'scope': {
        const { strings, scope } = namesOf(info, e);
        switch (op.primitive) {
          case 'var': return `${scope?.name}.${strings[0]}`;
          case 'through': return `${scope?.name}.${strings[0]}.${strings[1]}`;
          case 'param': return `${tok}.${strings[0]}`;
          case 'has-role': return `${tok}(${strings[0]})`;
          default: return String(tok);
        }
      }
      default: throw new FnEvalError(`print: operator ${op.name} has no syntax form`);
    }
  };
  return pr(expr);
}
