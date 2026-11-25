// The expressions of the typed sections of a product file (WG-5060).
//
// A value of the platform type `expr` or `expression` (a policy condition, a trigger condition, an
// operation's check, a field default or read rule, a segment predicate, an automation's expression) is text in
// the authoring syntax of the tenant rule language (D-6546). layer-values.js collects each such text with its
// path; this module parses it and checks it statically against the scope it is written in, and layers.js reports
// what it finds. specc does the same (crates/spec-compiler/src/layer_expr.rs), with the same rule codes:
//
//   layer.expr-syntax         the text does not parse: a character, a name or an operator the language does not
//                             have (a call such as balance(x) is an unknown name), a missing bracket
//   layer.expr-unknown-field  a record field that the object type of the scope does not have, or a field a
//                             reference hop cannot follow to
//   layer.expr-unknown-role   has_role names a role that neither the platform nor the product declares
//   layer.expr-unknown-param  param.<name> names a parameter the scope does not bind
//   layer.expr-type           an operand of a shape the operator does not accept, two shapes that cannot be
//                             compared, branches of different shapes, a hop through a field that is not a single reference
//
// Every message names the product entity, the place of the text in it, the text and the position in the text
// (a count of characters from 0).
//
// The nine operators added to the language (checked + - *, a timestamp plus or minus milliseconds, ms_between,
// days, hours, minutes, concat, text) are parsed and typed here as the generated parser and checker do: a '-'
// before a digit is the sign of an integer literal only where no operand ends before it, + and - bind looser
// than *, both tighter than a comparison. tests/core/layer-expr-drift.test.js probes every operator a language
// entity declares against this module, so a new operator fails a test here until it is handled.
//
// The grammar and the static check are those the specification's `tenant-rule-language` entity states, which
// specc generates into the kernel (crates/model-core/src/tenant_rule_language.rs: tokenize, Parser, check). The
// operator table is not read from the entity here: Exegra's evaluator and checker of a declared language
// (language-eval.js) work on an AST value, never on text, and cannot follow a hop to another object type, so this
// module keeps the grammar and the messages of the kernel's generated parser and checker, which the same entity pins.
//
// The scope of a text comes from the value that holds it (expressionScope): the fields of an object type, the
// params an operation or an event binds, and the roles of the platform and of the product.

/** The shapes of the language, as the kernel names them in messages. */
const SHAPE = Object.freeze({ bool: 'Bool', int: 'Int', str: 'Str', time: 'Time', ref: 'Ref', list: 'List', any: 'Any' });

/** The parameters every event binds, and those each event adds (D-6523). */
const EVENT_PARAMS = Object.freeze({
  RecordCreated: [],
  RecordUpdated: ['transition'],
  RecordDeleted: [],
  SegmentEntered: ['person', 'segment', 'reason'],
  SegmentExited: ['person', 'segment', 'reason'],
  LedgerPosted: ['owner', 'unit', 'amount', 'balance', 'balance_before', 'entry_sequence', 'reason'],
  SettingChanged: ['setting', 'level', 'subject'],
  ScheduleDue: ['schedule', 'due_at'],
  InboundWebhook: ['endpoint', 'event_id', 'body'],
});
const EVENT_BASE_PARAMS = Object.freeze(['seq', 'at', 'hop']);
const RECORD_EVENTS = Object.freeze(['RecordCreated', 'RecordUpdated', 'RecordDeleted']);

const FIELD_ID = /^[a-z][a-z0-9_]*$/;
/** @param {any} s */
const isFieldId = (s) => typeof s === 'string' && s.length <= 64 && FIELD_ID.test(s);
/** @param {any} v */
const isObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);

/**
 * @typedef {{shape: string, target: string|null}} FieldInfo   a field's shape; `target`: the object type of a single reference
 * @typedef {Map<string, FieldInfo>} FieldMap
 * @typedef {{fields: FieldMap|null, params: Set<string>|null}} Scope   null: not known here, so any name is accepted
 * @typedef {{objects: Map<string, FieldMap>, roles: Set<string>}} ProductContext
 * @typedef {{code: string, pos: number, message: string}} ExprProblem
 */

/**
 * The fields of an object type value, with the shape of each (shape_of_type in crates/kernel/src/expr.rs).
 * @param {any} objectType @returns {FieldMap}
 */
export function fieldMapOf(objectType) {
  /** @type {FieldMap} */
  const out = new Map();
  const fields = isObj(objectType?.fields) ? objectType.fields : {};
  for (const [name, def] of Object.entries(fields)) {
    const ty = isObj(def) ? def.ty : undefined;
    const tag = typeof ty === 'string' ? ty : isObj(ty) ? Object.keys(ty)[0] : '';
    /** @type {Record<string, string>} */
    const shapes = { Str: 'str', Int: 'int', Bool: 'bool', Time: 'time', Ref: 'ref', List: 'list', File: 'str', Language: 'str' };
    const target = tag === 'Ref' && isObj(ty) && typeof ty.Ref?.target === 'string' ? ty.Ref.target : null;
    out.set(name, { shape: shapes[tag] ?? 'any', target });
  }
  return out;
}

/**
 * What a product file declares that its expressions may name: its object types and its roles, and the roles of
 * the platform.
 * @param {{entities: Map<string, {kind: string}>}|null} baseModel the platform's model
 * @param {{section: string, id: string|null, value: any}[]} items the typed and entity items of the file
 * @returns {ProductContext}
 */
export function productContext(baseModel, items) {
  /** @type {ProductContext} */
  const ctx = { objects: new Map(), roles: new Set() };
  for (const e of baseModel?.entities.values() ?? []) if (e.kind === 'role') ctx.roles.add(/** @type {any} */ (e).id);
  for (const it of items) {
    if (it.id === null) continue;
    if (it.section === 'objects') ctx.objects.set(it.id, fieldMapOf(it.value));
    if (it.section === 'roles') ctx.roles.add(it.id);
  }
  return ctx;
}

/**
 * The scope a text is written in, found from the item that holds it and the path of the text in the item.
 * Objects: the fields of the object type itself. Policies: the object type of the resource. Segments: the
 * subject type. Triggers: the object of a record event (none for the others) and the params the event binds.
 * Operations: the subject's object type and the inputs as params, and in a step the ids of the create steps before it. Anything else (an automation, a token): the
 * run's params are not known here, so any field and param is accepted.
 * @param {ProductContext} ctx @param {string} section @param {any} item @param {(string|number)[]} path
 * @returns {Scope}
 */
export function expressionScope(ctx, section, item, path) {
  /** @param {any} id @returns {FieldMap|null} */
  const fieldsOf = (id) => (typeof id === 'string' ? ctx.objects.get(id) ?? null : null);
  switch (section) {
    case 'objects': return { fields: fieldsOf(item?.id) ?? new Map(), params: new Set() };
    case 'policies': return { fields: fieldsOf(item?.resource?.Object), params: new Set() };
    case 'segments': return { fields: fieldsOf(item?.['subject-type']), params: new Set() };
    case 'triggers': {
      const on = item?.on;
      const event = typeof on === 'string' ? on : isObj(on) ? Object.keys(on)[0] : undefined;
      if (event === undefined || !Object.hasOwn(EVENT_PARAMS, event)) return { fields: null, params: null };
      const params = new Set([...EVENT_BASE_PARAMS, ...EVENT_PARAMS[/** @type {keyof typeof EVENT_PARAMS} */ (event)]]);
      return { fields: RECORD_EVENTS.includes(event) ? fieldsOf(on[event]?.object) : new Map(), params };
    }
    case 'operations': {
      const params = new Set((Array.isArray(item?.inputs) ? item.inputs : []).map((/** @type {any} */ i) => i?.name).filter((/** @type {any} */ n) => typeof n === 'string'));
      // A step reads the identifier of the record an earlier create step made as the parameter named by that step's id (D-6548).
      if (path[0] === 'steps' && typeof path[1] === 'number' && Array.isArray(item?.steps)) {
        for (const earlier of item.steps.slice(0, path[1])) {
          const id = isObj(earlier) ? earlier.CreateRecord?.id : undefined;
          if (typeof id === 'string') params.add(id);
        }
      }
      const subject = item?.subject?.object;
      return { fields: typeof subject === 'string' ? fieldsOf(subject) : new Map(), params };
    }
    default: return { fields: null, params: null };
  }
}

class Problem extends Error {
  /** @param {string} code @param {number} pos @param {string} message */
  constructor(code, pos, message) { super(message); this.code = code; this.pos = pos; }
}

/** @typedef {{t: 'id'|'int'|'str'|'sym', v: any, pos: number}} Token */

/** Whether a token ends an operand, so that a '-' after it subtracts instead of signing a literal. @param {Token|undefined} tok */
function endsOperand(tok) {
  if (tok === undefined) return false;
  if (tok.t === 'int' || tok.t === 'str') return true;
  if (tok.t === 'sym') return tok.v === ')' || tok.v === ']';
  return !['or', 'and', 'not', 'in'].includes(tok.v);
}

/** @param {string} source @returns {Token[]} */
function tokenize(source) {
  const SYMBOLS = ['==', '!=', '<=', '>=', '<', '>', '+', '-', '*', '(', ')', '[', ']', ',', '.'];
  const chars = [...source];
  /** @type {Token[]} */
  const out = [];
  let i = 0;
  while (i < chars.length) {
    const c = chars[i];
    if (/\s/.test(c)) { i++; continue; }
    if (/[A-Za-z_$]/.test(c)) {
      const start = i;
      while (i < chars.length && /[A-Za-z0-9_$]/.test(chars[i])) i++;
      out.push({ t: 'id', v: chars.slice(start, i).join(''), pos: start });
    } else if (/[0-9]/.test(c) || (c === '-' && /[0-9]/.test(chars[i + 1] ?? '') && !endsOperand(out[out.length - 1]))) {
      const start = i++;
      while (i < chars.length && /[0-9]/.test(chars[i])) i++;
      const text = chars.slice(start, i).join('');
      if (BigInt(text) > 9223372036854775807n || BigInt(text) < -9223372036854775808n) throw new Problem('layer.expr-syntax', start, `number out of range: ${text}`);
      out.push({ t: 'int', v: text, pos: start });
    } else if (c === "'") {
      const start = i++;
      let text = '';
      for (;;) {
        const d = chars[i];
        if (d === undefined) throw new Problem('layer.expr-syntax', start, 'unterminated string');
        if (d === "'") break;
        if (d === '\\') {
          i++;
          const e = chars[i];
          if (e === 'n') text += '\n';
          else if (e === "'" || e === '\\') text += e;
          else throw new Problem('layer.expr-syntax', i - 1, `bad escape: ${e === undefined ? 'none' : JSON.stringify(e)}`);
        } else text += d;
        i++;
      }
      i++;
      out.push({ t: 'str', v: text, pos: start });
    } else {
      const rest = chars.slice(i, i + 2).join('');
      const sym = SYMBOLS.find((s) => rest.startsWith(s));
      if (!sym) throw new Problem('layer.expr-syntax', i, `unexpected character ${JSON.stringify(c)}`);
      out.push({ t: 'sym', v: sym, pos: i });
      i += sym.length;
    }
  }
  return out;
}

/** The call forms: the token, the number of arguments. */
const CALLS = Object.freeze({ is_null: 1, len: 1, lower: 1, contains: 2, starts_with: 2, is_slug: 1, if: 3, ms_between: 2, days: 1, hours: 1, minutes: 1, concat: 2, text: 1, ancestor_of: 4 });

/**
 * @typedef {{k: string, pos: number, [key: string]: any}} Node
 */

/** @param {string} source @returns {Node} */
function parse(source) {
  const tokens = tokenize(source);
  let at = 0;
  const end = [...source].length;
  const peek = () => tokens[at];
  const here = () => peek()?.pos ?? end;
  const show = (/** @type {Token|undefined} */ tok) => (tok === undefined ? 'the end of the text' : tok.t === 'str' ? `the string '${tok.v}'` : `"${tok.v}"`);
  const word = (/** @type {string} */ w) => { if (peek()?.t === 'id' && peek().v === w) { at++; return true; } return false; };
  const sym = (/** @type {string} */ s) => { if (peek()?.t === 'sym' && peek().v === s) { at++; return true; } return false; };
  const expect = (/** @type {string} */ s) => { if (!sym(s)) throw new Problem('layer.expr-syntax', here(), `expected "${s}", found ${show(peek())}`); };
  const ident = () => {
    const tok = tokens[at];
    if (tok?.t !== 'id') throw new Problem('layer.expr-syntax', here(), `expected a name, found ${show(tok)}`);
    at++;
    return /** @type {string} */ (tok.v);
  };
  const intArg = () => {
    expect('(');
    const tok = tokens[at];
    if (tok?.t !== 'int') throw new Problem('layer.expr-syntax', here(), `expected a number, found ${show(tok)}`);
    at++;
    expect(')');
    return tok.v;
  };
  /** @param {number} n @returns {Node[]} */
  const args = (n) => {
    expect('(');
    /** @type {Node[]} */
    const out = [];
    for (let i = 0; i < n; i++) {
      if (i > 0) expect(',');
      out.push(level0());
    }
    expect(')');
    return out;
  };
  /** @returns {Node} */
  const level0 = () => {
    const pos = here();
    const items = [level1()];
    while (word('or')) items.push(level1());
    return items.length === 1 ? items[0] : { k: 'or', pos, items };
  };
  /** @returns {Node} */
  const level1 = () => {
    const pos = here();
    const items = [level2()];
    while (word('and')) items.push(level2());
    return items.length === 1 ? items[0] : { k: 'and', pos, items };
  };
  /** @returns {Node} */
  const level2 = () => {
    const pos = here();
    if (word('not')) return { k: 'not', pos, of: level2() };
    return level3();
  };
  /** @returns {Node} */
  const level3 = () => {
    const pos = here();
    const left = level4();
    for (const op of ['==', '!=', '<', '<=', '>', '>=']) if (sym(op)) return { k: 'cmp', pos, op, left, right: level4() };
    if (word('in')) return { k: 'in', pos, left, right: level4() };
    return left;
  };
  /** + and -, left associative. @returns {Node} */
  const level4 = () => {
    const pos = here();
    let left = level5();
    for (;;) {
      const op = sym('+') ? '+' : sym('-') ? '-' : null;
      if (op === null) return left;
      left = { k: 'arith', pos, op, left, right: level5() };
    }
  };
  /** The product, left associative. @returns {Node} */
  const level5 = () => {
    const pos = here();
    let left = primary();
    while (sym('*')) left = { k: 'arith', pos, op: '*', left, right: primary() };
    return left;
  };
  /** @returns {Node} */
  const primary = () => {
    const tok = tokens[at];
    const pos = here();
    at++;
    if (tok === undefined) throw new Problem('layer.expr-syntax', pos, 'unexpected end of the text');
    if (tok.t === 'int') return { k: 'lit', pos, shape: 'int' };
    if (tok.t === 'str') return { k: 'lit', pos, shape: 'str', text: tok.v };
    if (tok.t === 'sym' && tok.v === '(') { const inner = level0(); expect(')'); return inner; }
    if (tok.t === 'sym' && tok.v === '[') {
      let n = 0;
      while (!sym(']')) {
        if (n > 0) expect(',');
        const item = primary();
        if (item.k !== 'lit') throw new Problem('layer.expr-syntax', item.pos, 'a list holds literals only');
        n++;
      }
      return { k: 'lit', pos, shape: 'list' };
    }
    if (tok.t !== 'id') throw new Problem('layer.expr-syntax', pos, `unexpected ${show(tok)}`);
    const name = /** @type {string} */ (tok.v);
    switch (name) {
      case 'true': case 'false': return { k: 'lit', pos, shape: 'bool' };
      case 'null': return { k: 'lit', pos, shape: 'any' };
      case 'param': expect('.'); return { k: 'param', pos, name: ident(), namePos: tokens[at - 1].pos };
      case 'now': return { k: 'now', pos };
      case 'principal': return { k: 'principal', pos };
      case 'has_role': { expect('('); const role = ident(); const rolePos = tokens[at - 1].pos; expect(')'); return { k: 'has_role', pos, role, rolePos }; }
      case 'record': case 'old': case 'new': {
        expect('.');
        const field = ident();
        const fieldPos = tokens[at - 1].pos;
        if (sym('.')) return { k: 'through', pos, field, fieldPos, name: ident(), namePos: tokens[at - 1].pos };
        return { k: 'var', pos, name: field, namePos: fieldPos };
      }
      case 'time': intArg(); return { k: 'lit', pos, shape: 'time' };
      case 'ref': { const v = intArg(); if (v.startsWith('-')) throw new Problem('layer.expr-syntax', pos, 'a record id is not negative'); return { k: 'lit', pos, shape: 'ref' }; }
      default:
        if (Object.hasOwn(CALLS, name)) return { k: 'call', pos, name, args: args(CALLS[/** @type {keyof typeof CALLS} */ (name)]) };
        throw new Problem('layer.expr-syntax', pos, `unknown name "${name}": the tenant rule language has no such name or call (its calls are ${Object.keys(CALLS).join(', ')}, and has_role, param, now, principal)`);
    }
  };
  const tree = level0();
  if (at < tokens.length) throw new Problem('layer.expr-syntax', tokens[at].pos, `unexpected ${show(tokens[at])} after the expression`);
  return tree;
}

const SYSTEM_ATTRIBUTES = Object.freeze({ $id: 'ref', $version: 'int', $created_by: 'str', $created_at: 'time', $updated_at: 'time' });

/**
 * Check a parsed expression: its shape, or a Problem (crates/model-core/src/tenant_rule_language.rs check).
 * @param {Node} tree @param {Scope & {roles: Set<string>, objects: Map<string, FieldMap>}} env @returns {string}
 */
function check(tree, env) {
  /** @param {string} shape @param {string[]} allowed @param {string} what @param {number} pos */
  const expect = (shape, allowed, what, pos) => {
    if (shape !== 'any' && !allowed.includes(shape)) throw new Problem('layer.expr-type', pos, `${what} does not accept a ${SHAPE[/** @type {keyof typeof SHAPE} */ (shape)]} operand`);
  };
  /** @param {string} name @param {number} pos */
  const fieldId = (name, pos) => { if (!isFieldId(name)) throw new Problem('layer.expr-unknown-field', pos, `invalid field identifier: ${JSON.stringify(name)}`); };
  /** The shape of a name read from `fields` (null: any). @param {FieldMap|null} fields @param {string} name @param {number} pos @returns {string} */
  const attribute = (fields, name, pos) => {
    if (Object.hasOwn(SYSTEM_ATTRIBUTES, name)) return SYSTEM_ATTRIBUTES[/** @type {keyof typeof SYSTEM_ATTRIBUTES} */ (name)];
    fieldId(name, pos);
    if (fields === null) return 'any';
    const f = fields.get(name);
    if (!f) throw new Problem('layer.expr-unknown-field', pos, `unknown field ${name}; the object type has ${fields.size === 0 ? 'no fields in this scope' : `the fields ${[...fields.keys()].join(', ')}`}`);
    return f.shape;
  };
  /** @param {Node} n @returns {string} */
  const sh = (n) => {
    switch (n.k) {
      case 'lit': return n.shape;
      case 'var': return attribute(env.fields, n.name, n.namePos);
      case 'through': {
        fieldId(n.field, n.fieldPos);
        /** @type {FieldMap|null} */
        let target = null;
        if (env.fields !== null) {
          const f = env.fields.get(n.field);
          if (!f) throw new Problem('layer.expr-unknown-field', n.fieldPos, `unknown field ${n.field}; the object type has ${env.fields.size === 0 ? 'no fields in this scope' : `the fields ${[...env.fields.keys()].join(', ')}`}`);
          if (f.shape !== 'ref' || f.target === null) throw new Problem('layer.expr-type', n.fieldPos, `${n.field} is not a single reference`);
          target = env.objects.get(f.target) ?? null;
        }
        return attribute(target, n.name, n.namePos);
      }
      case 'param':
        if (env.params !== null && !env.params.has(n.name)) throw new Problem('layer.expr-unknown-param', n.namePos, `undeclared parameter ${n.name}; the scope binds ${env.params.size === 0 ? 'no parameters' : [...env.params].join(', ')}`);
        return 'any';
      case 'now': return 'time';
      case 'principal': return 'str';
      case 'has_role':
        if (!env.roles.has(n.role)) throw new Problem('layer.expr-unknown-role', n.rolePos, `unknown role ${n.role}; neither the platform nor the product declares it`);
        return 'bool';
      case 'not': expect(sh(n.of), ['bool'], 'not', n.of.pos); return 'bool';
      case 'and': case 'or':
        for (const item of n.items) expect(sh(item), ['bool'], 'and/or', item.pos);
        return 'bool';
      case 'cmp': {
        const l = sh(n.left), r = sh(n.right);
        if (l !== 'any' && r !== 'any' && l !== r) throw new Problem('layer.expr-type', n.pos, `cannot compare ${SHAPE[/** @type {keyof typeof SHAPE} */ (l)]} with ${SHAPE[/** @type {keyof typeof SHAPE} */ (r)]}`);
        if (n.op !== '==' && n.op !== '!=') {
          expect(l, ['int', 'time', 'str'], 'ordering', n.left.pos);
          expect(r, ['int', 'time', 'str'], 'ordering', n.right.pos);
        }
        return 'bool';
      }
      case 'arith': {
        const first = sh(n.left);
        if (n.op === '*') { expect(first, ['int'], n.op, n.left.pos); expect(sh(n.right), ['int'], n.op, n.right.pos); return 'int'; }
        expect(first, ['int', 'time'], n.op, n.left.pos);
        expect(sh(n.right), ['int'], n.op, n.right.pos);
        return first;
      }
      case 'in': sh(n.left); expect(sh(n.right), ['list'], 'in', n.right.pos); return 'bool';
      case 'call': {
        const a = n.args;
        switch (n.name) {
          case 'is_null': sh(a[0]); return 'bool';
          case 'len': expect(sh(a[0]), ['str', 'list'], 'len', a[0].pos); return 'int';
          case 'lower': expect(sh(a[0]), ['str'], 'lower', a[0].pos); return 'str';
          case 'contains': {
            const first = sh(a[0]), second = sh(a[1]);
            expect(first, ['str', 'list'], 'contains', a[0].pos);
            if (first === 'str') expect(second, ['str'], 'contains', a[1].pos);
            return 'bool';
          }
          case 'starts_with': expect(sh(a[0]), ['str'], 'starts_with', a[0].pos); expect(sh(a[1]), ['str'], 'starts_with', a[1].pos); return 'bool';
          case 'is_slug': expect(sh(a[0]), ['str'], 'is_slug', a[0].pos); return 'bool';
          case 'ancestor_of': {
            // expr.rs check, Expr::AncestorOf (WG-5510): the object type and field are string literals, read at check time.
            // Refusals follow language-eval.js: a non-literal is a syntax refusal, a bad field or an empty object type too.
            expect(sh(a[0]), ['ref'], 'ancestor_of', a[0].pos);
            expect(sh(a[1]), ['ref'], 'ancestor_of', a[1].pos);
            const literal = (/** @type {Node} */ arg) => {
              if (arg.k !== 'lit' || arg.shape !== 'str') throw new Problem('layer.expr-syntax', arg.pos, 'ancestor_of takes a string literal here');
              return String(arg.text);
            };
            const object = literal(a[2]), via = literal(a[3]);
            if (!isFieldId(via)) throw new Problem('layer.expr-unknown-field', a[3].pos, `invalid field identifier: ${JSON.stringify(via)}`);
            if (object === '') throw new Problem('layer.expr-syntax', n.pos, 'ancestor_of names an empty object type');
            return 'bool';
          }
          case 'ms_between': for (const arg of a) expect(sh(arg), ['time'], 'ms_between', arg.pos); return 'int';
          case 'days': case 'hours': case 'minutes': expect(sh(a[0]), ['int'], n.name, a[0].pos); return 'int';
          case 'concat': for (const arg of a) expect(sh(arg), ['str'], 'concat', arg.pos); return 'str';
          case 'text': expect(sh(a[0]), ['int', 'time', 'ref', 'bool', 'str'], 'text', a[0].pos); return 'str';
          default: {
            expect(sh(a[0]), ['bool'], 'if', a[0].pos);
            const then = sh(a[1]), otherwise = sh(a[2]);
            if (then !== 'any' && otherwise !== 'any' && then !== otherwise) throw new Problem('layer.expr-type', n.pos, `if branches differ: ${SHAPE[/** @type {keyof typeof SHAPE} */ (then)]} and ${SHAPE[/** @type {keyof typeof SHAPE} */ (otherwise)]}`);
            return then === 'any' ? otherwise : then;
          }
        }
      }
      default: throw new Problem('layer.expr-syntax', n.pos, `unknown expression ${n.k}`);
    }
  };
  return sh(tree);
}

/**
 * Parse and check one text. Returns the first problem, or null when the text parses and checks.
 * @param {string} text
 * @param {Scope & {roles: Set<string>, objects: Map<string, FieldMap>}} env
 * @returns {ExprProblem|null}
 */
export function checkExpressionText(text, env) {
  return typeExpressionText(text, env).problem ?? null;
}

/**
 * Parse and check one text, giving the shape of its value (bool, int, str, time, ref, list or any) or the first problem.
 * @param {string} text
 * @param {Scope & {roles: Set<string>, objects: Map<string, FieldMap>}} env
 * @returns {{shape: string, problem?: undefined}|{shape?: undefined, problem: ExprProblem}}
 */
export function typeExpressionText(text, env) {
  try {
    return { shape: check(parse(text), env) };
  } catch (e) {
    if (e instanceof Problem) return { problem: { code: e.code, pos: e.pos, message: e.message } };
    throw e;
  }
}
