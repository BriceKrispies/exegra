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
 * Evaluate a parsed expression. `resolve` maps a reference path to a value and
 * must return undefined for an unknown reference (which is an error).
 * @param {Ast} ast
 * @param {(path:string[]) => any} resolve
 * @returns {any}
 */
export function evalExpr(ast, resolve) {
  switch (ast.t) {
    case 'lit': return ast.v;
    case 'ref': {
      const v = resolve(ast.path);
      if (v === undefined) throw new ExprError(`Unknown reference "${ast.path.join('.')}"`, ast.pos);
      return v;
    }
    case 'un': {
      const a = evalExpr(ast.a, resolve);
      if (ast.op === '!') { requireType(a, 'boolean', '!'); return !a; }
      requireType(a, 'number', '-');
      return -a;
    }
    case 'bin': {
      const op = ast.op;
      if (op === '&&' || op === '||' || op === '=>') {
        const a = evalExpr(ast.a, resolve);
        requireType(a, 'boolean', op);
        if (op === '&&' && !a) return false;
        if (op === '||' && a) return true;
        if (op === '=>' && !a) return true;
        const b = evalExpr(ast.b, resolve);
        requireType(b, 'boolean', op);
        return b;
      }
      const a = evalExpr(ast.a, resolve);
      const b = evalExpr(ast.b, resolve);
      if (op === '==') return a === b;
      if (op === '!=') return a !== b;
      if (op === '+' && typeof a === 'string' && typeof b === 'string') return a + b;
      requireType(a, 'number', op);
      requireType(b, 'number', op);
      switch (op) {
        case '<': return a < b;
        case '<=': return a <= b;
        case '>': return a > b;
        case '>=': return a >= b;
        case '+': return a + b;
        case '-': return a - b;
        case '*': return a * b;
        case '/': if (b === 0) throw new ExprError('Division by zero'); return a / b;
        case '%': if (b === 0) throw new ExprError('Division by zero'); return a % b;
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
 */
export function evaluate(src, resolve) {
  const r = parseExpr(src);
  if (!r.ok) throw new ExprError(r.error.message, r.error.pos);
  return evalExpr(r.ast, resolve);
}
