// Exegra expression language: a small, side-effect-free language for guards,
// effect values and invariants. No host-language evaluation is ever involved.
//
// Grammar (lowest to highest precedence):
//   implies :  a => b            (right associative)
//   or      :  a || b
//   and     :  a && b
//   equality:  a == b, a != b
//   compare :  a < b, a <= b, a > b, a >= b
//   additive:  a + b, a - b      (binary minus needs surrounding spaces next to identifiers)
//   multiply:  a * b, a / b, a % b
//   unary   :  !a, -a
//   primary :  number | 'string' | "string" | true | false | null | reference | ( expr )
//   reference: ident ( '.' ident )*   where ident may contain inner hyphens (entity ids)

/** @typedef {{t:'lit', v:any} | {t:'ref', path:string[], pos:number} | {t:'un', op:string, a:Ast} | {t:'bin', op:string, a:Ast, b:Ast}} Ast */

export class ExprError extends Error {
  /** @param {string} message @param {number} [pos] */
  constructor(message, pos) {
    super(message);
    this.name = 'ExprError';
    this.pos = pos ?? -1;
  }
}

const IDENT = /[A-Za-z_][A-Za-z0-9_]*(?:-[A-Za-z_][A-Za-z0-9_]*)*/y;
const NUMBER = /\d+(?:\.\d+)?/y;
const OPS = ['=>', '||', '&&', '==', '!=', '<=', '>=', '<', '>', '+', '-', '*', '/', '%', '!', '(', ')', '.'];

/** @param {string} src */
function tokenize(src) {
  /** @type {{k:string, v:any, pos:number}[]} */
  const out = [];
  let i = 0;
  while (i < src.length) {
    const c = src[i];
    if (c === ' ' || c === '\t' || c === '\n' || c === '\r') { i++; continue; }
    if (c === '"' || c === "'") {
      const end = src.indexOf(c, i + 1);
      if (end < 0) throw new ExprError('Unterminated string literal', i);
      out.push({ k: 'str', v: src.slice(i + 1, end), pos: i });
      i = end + 1;
      continue;
    }
    NUMBER.lastIndex = i;
    let m = NUMBER.exec(src);
    if (m) { out.push({ k: 'num', v: Number(m[0]), pos: i }); i += m[0].length; continue; }
    IDENT.lastIndex = i;
    m = IDENT.exec(src);
    if (m) { out.push({ k: 'id', v: m[0], pos: i }); i += m[0].length; continue; }
    const op = OPS.find((o) => src.startsWith(o, i));
    if (!op) throw new ExprError(`Unexpected character '${c}'`, i);
    out.push({ k: 'op', v: op, pos: i });
    i += op.length;
  }
  out.push({ k: 'end', v: null, pos: src.length });
  return out;
}

const BINARY = [['=>'], ['||'], ['&&'], ['==', '!='], ['<', '<=', '>', '>='], ['+', '-'], ['*', '/', '%']];

/**
 * Parse an expression. Never throws.
 * @param {string} src
 * @returns {{ok:true, ast:Ast} | {ok:false, error:{message:string, pos:number}}}
 */
export function parseExpr(src) {
  try {
    if (typeof src !== 'string') throw new ExprError('Expression must be a string', 0);
    const toks = tokenize(src);
    let p = 0;
    const peek = () => toks[p];
    const isOp = (/** @type {string} */ v) => toks[p].k === 'op' && toks[p].v === v;

    /** @param {number} level @returns {Ast} */
    const binary = (level) => {
      if (level >= BINARY.length) return unary();
      let left = binary(level + 1);
      while (peek().k === 'op' && BINARY[level].includes(peek().v)) {
        const op = toks[p++].v;
        if (op === '=>') return { t: 'bin', op, a: left, b: binary(level) };
        left = { t: 'bin', op, a: left, b: binary(level + 1) };
      }
      return left;
    };
    /** @returns {Ast} */
    const unary = () => {
      if (isOp('!') || isOp('-')) { const op = toks[p++].v; return { t: 'un', op, a: unary() }; }
      return primary();
    };
    /** @returns {Ast} */
    const primary = () => {
      const tk = toks[p++];
      if (tk.k === 'num' || tk.k === 'str') return { t: 'lit', v: tk.v };
      if (tk.k === 'id') {
        if (tk.v === 'true') return { t: 'lit', v: true };
        if (tk.v === 'false') return { t: 'lit', v: false };
        if (tk.v === 'null') return { t: 'lit', v: null };
        const path = [tk.v];
        while (isOp('.')) {
          p++;
          const next = toks[p++];
          if (next.k !== 'id') throw new ExprError('Expected a name after "."', next.pos);
          path.push(next.v);
        }
        return { t: 'ref', path, pos: tk.pos };
      }
      if (tk.k === 'op' && tk.v === '(') {
        const inner = binary(0);
        if (!isOp(')')) throw new ExprError('Expected ")"', peek().pos);
        p++;
        return inner;
      }
      throw new ExprError(tk.k === 'end' ? 'Unexpected end of expression' : `Unexpected "${tk.v}"`, tk.pos);
    };

    const ast = binary(0);
    if (peek().k !== 'end') throw new ExprError(`Unexpected "${peek().v}"`, peek().pos);
    return { ok: true, ast };
  } catch (e) {
    const err = /** @type {any} */ (e);
    return { ok: false, error: { message: err.message, pos: err.pos ?? 0 } };
  }
}

/**
 * The integer representation types and their ranges (WG-4902, docs/semantics.md, "Numbers"). `u64`
 * and `i64` are limited to the integers a double holds exactly. Mirrors `IntKind` in
 * formal/Exegra/Value.lean.
 * @type {Readonly<Record<string, readonly [number, number]>>}
 */
export const INT_RANGES = Object.freeze({
  u8: [0, 255], u16: [0, 65535], u32: [0, 4294967295], u64: [0, 9007199254740991],
  i32: [-2147483648, 2147483647], i64: [-9007199254740991, 9007199254740991],
});

/** @typedef {(path: string[]) => string|undefined} TypeOf the declared type of a reference: an integer type name, `option`, or anything else (untyped) */

/** @param {string|undefined} ty */
const isInt = (ty) => ty !== undefined && Object.hasOwn(INT_RANGES, ty);

/** The declared type an arithmetic expression is computed in (`staticTy`). @param {Ast} ast @param {TypeOf} types @returns {string|undefined} */
function staticType(ast, types) {
  if (ast.t === 'ref') {
    // As STy.ofName: an integer type, `option`, or no type.
    const t = types(ast.path);
    return t === 'option' || isInt(t) ? t : undefined;
  }
  if (ast.t === 'un' && ast.op === '-') return staticType(ast.a, types);
  if (ast.t === 'bin' && ['+', '-', '*', '/', '%'].includes(ast.op)) {
    const a = staticType(ast.a, types);
    return a !== undefined ? a : staticType(ast.b, types);
  }
  return undefined;
}

/** @param {string} k @param {number} x */
function holds(k, x) {
  const [lo, hi] = INT_RANGES[k];
  return Math.floor(x) === x && lo <= x && x <= hi;
}

/**
 * The result of an arithmetic operator in declared type `ty` (`intResult` in formal/Exegra/Expr.lean):
 * untyped arithmetic is IEEE; integer arithmetic checks both operands and the exact result.
 * @param {string|undefined} ty @param {string} op @param {number} x @param {number} y @param {number} r
 */
function intResult(ty, op, x, y, r) {
  if (ty === undefined || !Object.hasOwn(INT_RANGES, ty)) return r;
  const [lo, hi] = INT_RANGES[ty];
  if (!holds(ty, x)) throw new ExprError(`Operator "${op}" on ${ty}: operand ${String(x)} is not a ${ty}`);
  if (!holds(ty, y)) throw new ExprError(`Operator "${op}" on ${ty}: operand ${String(y)} is not a ${ty}`);
  if (!holds(ty, r)) throw new ExprError(`Integer overflow: "${op}" on ${ty} gives ${String(r)}, outside ${lo}..${hi}`);
  // An integer has no negative zero.
  return r + 0;
}

/**
 * Equality of values (`==`), structural (`Value.eqv` in formal/Exegra/Value.lean): numbers by
 * value, arrays element by element, objects by their keys and members in any order.
 * @param {any} a @param {any} b @returns {boolean}
 */
export function valueEquals(a, b) {
  if (a === b) return true;
  if (typeof a !== 'object' || typeof b !== 'object' || a === null || b === null) return false;
  if (Array.isArray(a) !== Array.isArray(b)) return false;
  if (Array.isArray(a)) return a.length === b.length && a.every((x, i) => valueEquals(x, b[i]));
  const ka = Object.keys(a);
  return ka.length === Object.keys(b).length && ka.every((k) => Object.hasOwn(b, k) && valueEquals(a[k], b[k]));
}

/** @type {TypeOf} */
const UNTYPED = () => undefined;

/**
 * Evaluate a parsed expression. `resolve` maps a reference path to a value and
 * must return undefined for an unknown reference (which is an error). `types`, when given, maps a
 * reference path to its declared type (WG-4902): integer types make arithmetic checked integer
 * arithmetic, and an absent value of type `option` reads as null. Mirrors `eval` in
 * formal/Exegra/Expr.lean.
 * @param {Ast} ast
 * @param {(path:string[]) => any} resolve
 * @param {TypeOf} [types]
 * @returns {any}
 */
export function evalExpr(ast, resolve, types = UNTYPED) {
  switch (ast.t) {
    case 'lit': return ast.v;
    case 'ref': {
      const v = resolve(ast.path);
      if (v === undefined) {
        if (types(ast.path) === 'option') return null;
        throw new ExprError(`Unknown reference "${ast.path.join('.')}"`, ast.pos);
      }
      return v;
    }
    case 'un': {
      const a = evalExpr(ast.a, resolve, types);
      if (ast.op === '!') { requireType(a, 'boolean', '!'); return !a; }
      requireType(a, 'number', '-');
      return intResult(staticType(ast.a, types), '-', a, 0, -a);
    }
    case 'bin': {
      const op = ast.op;
      if (op === '&&' || op === '||' || op === '=>') {
        const a = evalExpr(ast.a, resolve, types);
        requireType(a, 'boolean', op);
        if (op === '&&' && !a) return false;
        if (op === '||' && a) return true;
        if (op === '=>' && !a) return true;
        const b = evalExpr(ast.b, resolve, types);
        requireType(b, 'boolean', op);
        return b;
      }
      const a = evalExpr(ast.a, resolve, types);
      const b = evalExpr(ast.b, resolve, types);
      if (op === '==') return valueEquals(a, b);
      if (op === '!=') return !valueEquals(a, b);
      if (op === '+' && typeof a === 'string' && typeof b === 'string') return a + b;
      requireType(a, 'number', op);
      requireType(b, 'number', op);
      const ty = staticType(ast, types);
      switch (op) {
        case '<': return a < b;
        case '<=': return a <= b;
        case '>': return a > b;
        case '>=': return a >= b;
        case '+': return intResult(ty, op, a, b, a + b);
        case '-': return intResult(ty, op, a, b, a - b);
        case '*': return intResult(ty, op, a, b, a * b);
        case '/': if (b === 0) throw new ExprError('Division by zero'); return intResult(ty, op, a, b, isInt(ty) ? (a - (a % b)) / b : a / b);
        case '%': if (b === 0) throw new ExprError('Division by zero'); return intResult(ty, op, a, b, a % b);
      }
    }
  }
  throw new ExprError('Malformed expression');
}

/** @param {any} v @param {string} type @param {string} op */
function requireType(v, type, op) {
  if (typeof v !== type) throw new ExprError(`Operator "${op}" needs a ${type}, got ${v === null ? 'null' : typeof v}`);
}

/**
 * All reference paths used by an expression.
 * @param {Ast} ast
 * @returns {string[][]}
 */
export function exprRefs(ast) {
  /** @type {string[][]} */
  const out = [];
  /** @param {Ast} n */
  const walk = (n) => {
    if (n.t === 'ref') out.push(n.path);
    else if (n.t === 'un') walk(n.a);
    else if (n.t === 'bin') { walk(n.a); walk(n.b); }
  };
  walk(ast);
  return out;
}

/**
 * Parse and evaluate in one call; throws ExprError on a parse failure.
 * @param {string} src
 * @param {(path:string[]) => any} resolve
 * @param {TypeOf} [types]
 */
export function evaluate(src, resolve, types) {
  const r = parseExpr(src);
  if (!r.ok) throw new ExprError(r.error.message, r.error.pos);
  return evalExpr(r.ast, resolve, types);
}
