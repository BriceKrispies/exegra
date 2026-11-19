// The body language of function entities (WG-4933, NC-3): Exegra's guard language (src/core/expr.js) extended
// with field access, if, let, match, constructors, list literals, built-in operations, calls to other functions,
// fail and try. This module only parses; src/core/function.js types and evaluates. docs/model-and-format.md,
// "Functions", states the grammar in full.
//
// Grammar (lowest to highest precedence; the binary levels are the guard language's):
//   expr     : implies
//   implies  : or ( '=>' implies )?                    right associative
//   or       : and ( '||' and )*
//   and      : equality ( '&&' equality )*
//   equality : compare ( ( '==' | '!=' ) compare )*
//   compare  : additive ( ( '<' | '<=' | '>' | '>=' ) additive )*
//   additive : multiply ( ( '+' | '-' ) multiply )*
//   multiply : unary ( ( '*' | '/' | '%' ) unary )*
//   unary    : '!' unary | '-' unary | 'try' unary | postfix
//   postfix  : primary ( '.' word )*
//   primary  : number | string | 'true' | 'false' | 'null' | '(' ')' | '(' expr ')'   () is the unit value
//            | '[' ( expr ( ',' expr )* )? ']'                       list literal
//            | '{' '}'                                               the empty map
//            | 'if' expr 'then' expr 'else' expr
//            | 'let' name '=' expr 'in' expr
//            | 'match' expr '{' arm ( ',' arm )* ','? '}'            the scrutinee takes no struct constructor
//            | 'call' name '(' ( expr ( ',' expr )* )? ')'           a call of another function
//            | name '(' args ')'                                     a built-in operation
//            | path '{' ( init ( ',' init )* ','? )? '}'             struct T{..} or union variant T.V{..}
//            | path '(' expr ')'                                     newtype union variant T.V(e)
//            | path                                                  a name, its fields, a unit variant T.V or an enum value T.V
//   path     : name ( '.' word )*
//   init     : word ':' expr | name                                  name alone is name: name
//   arm      : pattern '=>' expr
//   pattern  : '_' | word | word '(' bind ')' | word '{' field ( ',' field )* '}'
//   field    : word ':' bind | name
//   bind     : name | '_'
//   args     : binder ',' expr                                       map, filter, find, any, all, sortBy
//            | binder ',' name '=' expr ',' expr                     fold
//            | ( expr ( ',' expr )* )?                               every other operation
//   binder   : name 'in' expr
//   name     : as in the guard language: letters, digits and _, with inner hyphens (may-attempt); not a keyword
//   word     : a name or a keyword. A variant, enum value or field whose name is a keyword (value.null, expr.if,
//              a null => arm, then: e) is written as it is wherever the grammar reads a word: after a '.', as the
//              name of a pattern, and before the ':' of a constructor field or pattern field. It is never bound.

/**
 * @typedef {{k: 'wild', pos: number} | {k: 'variant', name: string, pos: number, bind?: string, fields?: {field: string, bind: string}[]}} Pattern
 * @typedef {{pat: Pattern, body: FnAst, pos: number}} Arm
 * @typedef {{name: string, e: FnAst, pos: number}} Init
 * @typedef {(
 *   {t: 'lit', v: any, pos?: number} |
 *   {t: 'unit', pos: number} |
 *   {t: 'ref', path: string[], pos: number} |
 *   {t: 'un', op: string, a: FnAst, pos?: number} |
 *   {t: 'bin', op: string, a: FnAst, b: FnAst, pos?: number} |
 *   {t: 'field', a: FnAst, name: string, pos: number} |
 *   {t: 'if', c: FnAst, a: FnAst, b: FnAst, pos: number} |
 *   {t: 'let', name: string, value: FnAst, body: FnAst, pos: number} |
 *   {t: 'match', e: FnAst, arms: Arm[], pos: number} |
 *   {t: 'list', items: FnAst[], pos: number} |
 *   {t: 'emptymap', pos: number} |
 *   {t: 'ctor', path: string[], fields: Init[], pos: number} |
 *   {t: 'newtype', path: string[], arg: FnAst, pos: number} |
 *   {t: 'builtin', name: string, args: FnAst[], binder?: {name: string, src: FnAst}, acc?: {name: string, init: FnAst}, pos: number} |
 *   {t: 'call', fn: string, args: FnAst[], pos: number} |
 *   {t: 'try', e: FnAst, pos: number}
 * ) & {ty?: any, res?: any}} FnAst
 */

export class FnSyntaxError extends Error {
  /** @param {string} message @param {number} pos */
  constructor(message, pos) {
    super(message);
    this.name = 'FnSyntaxError';
    this.pos = pos;
  }
}

/** Words the body language keeps for itself; none of them can name a parameter, a let or a binder. */
export const KEYWORDS = Object.freeze(['let', 'in', 'if', 'then', 'else', 'match', 'call', 'try', 'true', 'false', 'null']);
/** The built-in operations whose first argument binds a name over a list. */
export const BINDER_OPS = Object.freeze(['map', 'filter', 'find', 'any', 'all', 'sortBy', 'fold']);
/** Every built-in operation. */
export const BUILTIN_OPS = Object.freeze([
  'map', 'filter', 'find', 'any', 'all', 'fold', 'sortBy', 'take', 'concat', 'keys', 'values', 'get', 'insert', 'remove',
  'format', 'eval', 'check', 'print', 'fail',
  'startsWith', 'endsWith', 'length', 'trim', 'chars', 'snakeCase', 'parseTime',
  'isAsciiLowercase', 'isAsciiUppercase', 'isAsciiAlphabetic', 'isAsciiDigit', 'isAsciiAlphanumeric',
]);

const IDENT = /[A-Za-z_][A-Za-z0-9_]*(?:-[A-Za-z_][A-Za-z0-9_]*)*/y;
const NUMBER = /\d+(?:\.\d+)?/y;
const OPS = ['=>', '||', '&&', '==', '!=', '<=', '>=', '<', '>', '+', '-', '*', '/', '%', '!', '(', ')', '.', '{', '}', '[', ']', ',', ':', '='];
const BINARY = [['=>'], ['||'], ['&&'], ['==', '!='], ['<', '<=', '>', '>='], ['+', '-'], ['*', '/', '%']];

/** A name a parameter, let or binder may take. @param {any} s */
export function isBindableName(s) {
  if (typeof s !== 'string') return false;
  IDENT.lastIndex = 0;
  const m = IDENT.exec(s);
  return m !== null && m[0] === s && !KEYWORDS.includes(s) && s !== '_';
}

/** @param {string} src */
function tokenize(src) {
  /** @type {{k: string, v: any, pos: number}[]} */
  const out = [];
  let i = 0;
  while (i < src.length) {
    const c = src[i];
    if (c === ' ' || c === '\t' || c === '\n' || c === '\r') { i++; continue; }
    if (c === '"' || c === "'") {
      const end = src.indexOf(c, i + 1);
      if (end < 0) throw new FnSyntaxError('Unterminated string literal', i);
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
    if (!op) throw new FnSyntaxError(`Unexpected character '${c}'`, i);
    out.push({ k: 'op', v: op, pos: i });
    i += op.length;
  }
  out.push({ k: 'end', v: null, pos: src.length });
  return out;
}

/**
 * Parse a function body or let expression. Never throws.
 * @param {string} src
 * @returns {{ok: true, ast: FnAst} | {ok: false, error: {message: string, pos: number}}}
 */
export function parseFnExpr(src) {
  try {
    if (typeof src !== 'string') throw new FnSyntaxError('An expression must be a string', 0);
    const toks = tokenize(src);
    let p = 0;
    let noStruct = false;
    const peek = () => toks[p];
    const isOp = (/** @type {string} */ v) => toks[p].k === 'op' && toks[p].v === v;
    const isWord = (/** @type {string} */ v) => toks[p].k === 'id' && toks[p].v === v;
    const show = (/** @type {{k: string, v: any}} */ t) => (t.k === 'end' ? 'the end of the expression' : `"${t.v}"`);
    /** @param {string} v */
    const expectOp = (v) => {
      if (!isOp(v)) throw new FnSyntaxError(`Expected "${v}", found ${show(peek())}`, peek().pos);
      p++;
    };
    /** @param {string} v */
    const expectWord = (v) => {
      if (!isWord(v)) throw new FnSyntaxError(`Expected "${v}", found ${show(peek())}`, peek().pos);
      p++;
    };
    /** @param {string} what */
    const name = (what) => {
      const t = toks[p];
      if (t.k !== 'id' || KEYWORDS.includes(t.v)) throw new FnSyntaxError(`Expected ${what}, found ${show(t)}`, t.pos);
      p++;
      return /** @type {string} */ (t.v);
    };
    /** A word: a name or a keyword, where no expression can begin (after '.', a pattern, a field before ':'). @param {string} what */
    const word = (what) => {
      const t = toks[p];
      if (t.k !== 'id') throw new FnSyntaxError(`Expected ${what}, found ${show(t)}`, t.pos);
      p++;
      return /** @type {string} */ (t.v);
    };
    /** @param {string} what */
    const bindName = (what) => {
      const pos = peek().pos;
      const n = name(what);
      if (n === '_') throw new FnSyntaxError(`${what} cannot be "_"`, pos);
      return n;
    };
    /** A sub-expression in which a struct constructor is allowed again. @param {() => FnAst} f */
    const nested = (f) => {
      const saved = noStruct;
      noStruct = false;
      try { return f(); } finally { noStruct = saved; }
    };

    /** @returns {FnAst} */
    const expr = () => binary(0);
    /** @param {number} level @returns {FnAst} */
    const binary = (level) => {
      if (level >= BINARY.length) return unary();
      let left = binary(level + 1);
      while (peek().k === 'op' && BINARY[level].includes(peek().v)) {
        const pos = peek().pos;
        const op = toks[p++].v;
        if (op === '=>') return { t: 'bin', op, a: left, b: binary(level), pos };
        left = { t: 'bin', op, a: left, b: binary(level + 1), pos };
      }
      return left;
    };
    /** @returns {FnAst} */
    const unary = () => {
      const pos = peek().pos;
      if (isOp('!') || isOp('-')) { const op = toks[p++].v; return { t: 'un', op, a: unary(), pos }; }
      if (isWord('try')) { p++; return { t: 'try', e: unary(), pos }; }
      return postfix();
    };
    /** @returns {FnAst} */
    const postfix = () => {
      let e = primary();
      while (isOp('.')) {
        p++;
        const pos = peek().pos;
        e = { t: 'field', a: e, name: word('a field name after "."'), pos };
      }
      return e;
    };
    /** @returns {Pattern} */
    const pattern = () => {
      const pos = peek().pos;
      const n = word('a pattern');
      if (n === '_') return { k: 'wild', pos };
      if (isOp('(')) {
        p++;
        const bind = name('a name or _');
        expectOp(')');
        return { k: 'variant', name: n, pos, bind };
      }
      if (isOp('{')) {
        p++;
        /** @type {{field: string, bind: string}[]} */
        const fields = [];
        while (!isOp('}')) {
          const fpos = peek().pos;
          const field = word('a field name');
          let bind = field;
          if (isOp(':')) { p++; bind = name('a name or _'); }
          else if (KEYWORDS.includes(field)) throw new FnSyntaxError(`The field "${field}" has the name of a keyword, which cannot be bound; write ${field}: <name>`, fpos);
          fields.push({ field, bind });
          if (!isOp(',')) break;
          p++;
        }
        expectOp('}');
        return { k: 'variant', name: n, pos, fields };
      }
      return { k: 'variant', name: n, pos };
    };
    /** @param {string} op @param {number} pos @returns {FnAst} */
    const builtin = (op, pos) => {
      expectOp('(');
      return nested(() => {
        /** @type {FnAst} */
        const node = { t: 'builtin', name: op, args: [], pos };
        if (BINDER_OPS.includes(op)) {
          const bname = bindName('the name a list operation binds');
          expectWord('in');
          node.binder = { name: bname, src: expr() };
          expectOp(',');
          if (op === 'fold') {
            const acc = bindName('the accumulator name of fold');
            expectOp('=');
            node.acc = { name: acc, init: expr() };
            expectOp(',');
          }
          node.args.push(expr());
        } else if (!isOp(')')) {
          node.args.push(expr());
          while (isOp(',')) { p++; node.args.push(expr()); }
        }
        expectOp(')');
        return node;
      });
    };
    /** @returns {FnAst} */
    const primary = () => {
      const tk = toks[p];
      const pos = tk.pos;
      if (tk.k === 'num' || tk.k === 'str') { p++; return { t: 'lit', v: tk.v, pos }; }
      if (tk.k === 'op' && tk.v === '(') {
        p++;
        if (isOp(')')) { p++; return { t: 'unit', pos }; }
        const inner = nested(expr);
        expectOp(')');
        return inner;
      }
      if (tk.k === 'op' && tk.v === '[') {
        p++;
        return nested(() => {
          /** @type {FnAst[]} */
          const items = [];
          if (!isOp(']')) {
            items.push(expr());
            while (isOp(',')) { p++; items.push(expr()); }
          }
          expectOp(']');
          return { t: 'list', items, pos };
        });
      }
      if (tk.k === 'op' && tk.v === '{') { p++; expectOp('}'); return { t: 'emptymap', pos }; }
      if (tk.k !== 'id') throw new FnSyntaxError(tk.k === 'end' ? 'Unexpected end of expression' : `Unexpected "${tk.v}"`, pos);
      const w = tk.v;
      if (w === 'true' || w === 'false' || w === 'null') { p++; return { t: 'lit', v: w === 'null' ? null : w === 'true', pos }; }
      if (w === 'if') {
        p++;
        const c = nested(expr);
        expectWord('then');
        const a = nested(expr);
        expectWord('else');
        return { t: 'if', c, a, b: expr(), pos };
      }
      if (w === 'let') {
        p++;
        const n = bindName('the name a let binds');
        expectOp('=');
        const value = nested(expr);
        expectWord('in');
        return { t: 'let', name: n, value, body: expr(), pos };
      }
      if (w === 'match') {
        p++;
        const saved = noStruct;
        noStruct = true;
        const e = expr();
        noStruct = saved;
        expectOp('{');
        return nested(() => {
          /** @type {Arm[]} */
          const arms = [];
          while (!isOp('}')) {
            const apos = peek().pos;
            const pat = pattern();
            expectOp('=>');
            arms.push({ pat, body: expr(), pos: apos });
            if (!isOp(',')) break;
            p++;
          }
          expectOp('}');
          if (!arms.length) throw new FnSyntaxError('A match needs at least one arm', pos);
          return { t: 'match', e, arms, pos };
        });
      }
      if (w === 'call') {
        p++;
        const fn = name('the id of the function to call');
        expectOp('(');
        return nested(() => {
          /** @type {FnAst[]} */
          const args = [];
          if (!isOp(')')) {
            args.push(expr());
            while (isOp(',')) { p++; args.push(expr()); }
          }
          expectOp(')');
          return { t: 'call', fn, args, pos };
        });
      }
      if (KEYWORDS.includes(w)) throw new FnSyntaxError(`Unexpected "${w}"`, pos);
      p++;
      const path = [w];
      if (isOp('(')) return builtin(w, pos);
      while (isOp('.')) {
        p++;
        path.push(word('a name after "."'));
      }
      if (isOp('(')) {
        p++;
        const arg = nested(expr);
        expectOp(')');
        return { t: 'newtype', path, arg, pos };
      }
      if (isOp('{') && !noStruct) {
        p++;
        return nested(() => {
          /** @type {Init[]} */
          const fields = [];
          while (!isOp('}')) {
            const fpos = peek().pos;
            const f = word('a field name');
            if (isOp(':')) { p++; fields.push({ name: f, e: expr(), pos: fpos }); }
            else if (KEYWORDS.includes(f)) throw new FnSyntaxError(`The field "${f}" has the name of a keyword; write ${f}: <value>`, fpos);
            else fields.push({ name: f, e: { t: 'ref', path: [f], pos: fpos }, pos: fpos });
            if (!isOp(',')) break;
            p++;
          }
          expectOp('}');
          return { t: 'ctor', path, fields, pos };
        });
      }
      return { t: 'ref', path, pos };
    };

    const ast = expr();
    if (peek().k !== 'end') throw new FnSyntaxError(`Unexpected ${show(peek())}`, peek().pos);
    return { ok: true, ast };
  } catch (e) {
    const err = /** @type {any} */ (e);
    return { ok: false, error: { message: err.message, pos: err.pos ?? 0 } };
  }
}

/**
 * The ids of the functions an expression calls, in order of appearance.
 * @param {FnAst} ast @returns {string[]}
 */
export function calledFunctions(ast) {
  /** @type {string[]} */
  const out = [];
  /** @param {any} n */
  const walk = (n) => {
    if (!n || typeof n !== 'object') return;
    if (Array.isArray(n)) { n.forEach(walk); return; }
    if (n.t === 'call') out.push(n.fn);
    for (const [k, v] of Object.entries(n)) if (k !== 'ty' && k !== 'res' && typeof v === 'object') walk(v);
  };
  walk(ast);
  return out;
}
