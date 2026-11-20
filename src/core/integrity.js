// Integrity rules: declarative consistency rules over a whole specification.
//
// A rule is an `integrityRule` entity whose `rule` is a formula of a small first-order language over
// the finite model: quantifiers over entities (of some kinds, or all) or over the values of a term,
// property access that follows references through lists, equality, membership, `nonempty`, `kindof`
// and the boolean connectives, and atoms `rel(t1, ..., tn)` of derived relations (`integrityRelation`
// entities: the least relation over finite parameter domains closed under its clauses, stratified
// so that recursion is through positive atoms only). No arithmetic, and relations are computed by
// iteration over finite candidate sets, so evaluation is total. The same formula is exported to
// Lean (integrity-export.js, formal/Exegra/Integrity.lean), where `Sat` under `Least` is its meaning
// and `eval` over `solve` the checker this file mirrors.

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */

/**
 * @typedef {{t: 'var', name: string} | {t: 'lit', vs: string[]} | {t: 'prop', of: Term, p: string} | {t: 'kindOf', of: Term}} Term
 * @typedef {{t: 'any'} | {t: 'kinds', ks: string[]} | {t: 'term', of: Term}} Dom
 * @typedef {{t: 'tt'} | {t: 'ff'} | {t: 'eq', a: Term, b: Term} | {t: 'mem', a: Term, b: Term} | {t: 'nonempty', a: Term}
 *   | {t: 'not', f: Formula} | {t: 'and'|'or'|'imp', f: Formula, g: Formula}
 *   | {t: 'all'|'ex', v: string, d: Dom, f: Formula, b: Formula} | {t: 'atom', r: string, args: Term[]}} Formula
 */

export class RuleSyntaxError extends Error {
  /** @param {string} message @param {number} pos */
  constructor(message, pos) { super(message); this.pos = pos; }
}

// --- values ---------------------------------------------------------------

/** A JSON value as a typed key, so that "1", 1 and true stay distinct. @param {any} v */
export function valueKey(v) {
  if (typeof v === 'string') return 's:' + v;
  if (typeof v === 'number') return 'n:' + String(v);
  if (typeof v === 'boolean') return 'b:' + String(v);
  return 'j:' + canonical(v);
}

/** @param {any} v @returns {string} */
function canonical(v) {
  if (Array.isArray(v)) return '[' + v.map(canonical).join(',') + ']';
  if (v && typeof v === 'object') return '{' + Object.keys(v).sort().map((k) => JSON.stringify(k) + ':' + canonical(v[k])).join(',') + '}';
  return JSON.stringify(v);
}

/** The values of one property: absent and null are none, a list is its items. @param {any} raw */
export function propertyKeys(raw) {
  if (raw === undefined || raw === null) return [];
  if (Array.isArray(raw)) return raw.filter((x) => x !== null && x !== undefined).map(valueKey);
  return [valueKey(raw)];
}

/** "s:dec-01" -> dec-01; other keys as JSON text. @param {string} key */
export function keyText(key) {
  return key.slice(2);
}

// --- syntax ---------------------------------------------------------------

const KEYWORDS = new Set(['forall', 'exists', 'in', 'where', 'not', 'nonempty', 'kindof', 'true', 'false']);

const NUM = /-?[0-9]+(\.[0-9]+)?([eE][+-]?[0-9]+)?/y;

/** @param {string} src */
function tokenize(src) {
  /** @type {{k: string, v: string, pos: number}[]} */
  const out = [];
  let i = 0;
  while (i < src.length) {
    const c = src[i];
    if (/\s/.test(c)) { i++; continue; }
    const start = i;
    if (c === '"' || c === "'") {
      let s = '';
      i++;
      while (i < src.length && src[i] !== c) {
        if (src[i] === '\\' && i + 1 < src.length) { s += src[i + 1]; i += 2; } else s += src[i++];
      }
      if (i >= src.length) throw new RuleSyntaxError('Unterminated string.', start);
      i++;
      out.push({ k: 'str', v: s, pos: start });
      continue;
    }
    NUM.lastIndex = i;
    const num = NUM.exec(src);
    if (num) {
      i += num[0].length;
      out.push({ k: 'num', v: num[0], pos: start });
      continue;
    }
    // Ids are lower-case words joined by hyphens, so an identifier may contain "-" between word characters.
    if (/[A-Za-z_]/.test(c)) {
      i++;
      while (i < src.length && (/[A-Za-z0-9_]/.test(src[i]) || (src[i] === '-' && /[A-Za-z0-9_]/.test(src[i + 1] ?? '')))) i++;
      const v = src.slice(start, i);
      out.push({ k: KEYWORDS.has(v) ? v : 'ident', v, pos: start });
      continue;
    }
    const two = src.slice(i, i + 2);
    if (['==', '!=', '&&', '||', '=>'].includes(two)) { out.push({ k: two, v: two, pos: start }); i += 2; continue; }
    if ('!().,:[]|*'.includes(c)) { out.push({ k: c, v: c, pos: start }); i++; continue; }
    throw new RuleSyntaxError(`Unexpected character "${c}".`, start);
  }
  out.push({ k: 'eof', v: '', pos: src.length });
  return out;
}

/**
 * Parse a rule. Grammar (lowest precedence first):
 *   formula := quant | or ('=>' formula)?
 *   quant   := ('forall'|'exists') x (':' kinds | 'in' term) ('where' formula)? ',' formula
 *   or := and ('||' and)*      and := unary ('&&' unary)*
 *   unary   := '!' unary | quant | '(' formula ')' | 'true' | 'false' | 'nonempty' term
 *            | rel '(' (term (',' term)*)? ')' | term ('==' | '!=' | 'in' | 'not' 'in') term
 *   kinds   := '*' | kind ('|' kind)*
 *   term    := 'kindof' term | atom ('.' prop)*      atom := x | literal | '[' literal, ... ']'
 * @param {string} src
 * @returns {{ok: true, ast: Formula} | {ok: false, error: {message: string, pos: number}}}
 */
export function parseRule(src) {
  try {
    const toks = tokenize(src);
    let i = 0;
    const peek = (o = 0) => toks[Math.min(i + o, toks.length - 1)];
    const next = () => toks[i++];
    /** @param {string} k @param {string} what */
    const expect = (k, what) => {
      const t = next();
      if (t.k !== k) throw new RuleSyntaxError(`Expected ${what}, found ${t.k === 'eof' ? 'the end' : `"${t.v}"`}.`, t.pos);
      return t;
    };
    /** @returns {Formula} */
    const formula = () => {
      if (peek().k === 'forall' || peek().k === 'exists') return quant();
      const left = or();
      if (peek().k === '=>') { next(); return { t: 'imp', f: left, g: formula() }; }
      return left;
    };
    /** @returns {Formula} */
    const quant = () => {
      const q = next();
      const v = expect('ident', 'a variable name').v;
      /** @type {Dom} */
      let d;
      if (peek().k === ':') {
        next();
        if (peek().k === '*') { next(); d = { t: 'any' }; } else {
          const ks = [expect('ident', 'an entity kind').v];
          while (peek().k === '|') { next(); ks.push(expect('ident', 'an entity kind').v); }
          d = { t: 'kinds', ks };
        }
      } else if (peek().k === 'in') { next(); d = { t: 'term', of: term() }; } else throw new RuleSyntaxError(`Expected ":" and a kind, or "in" and a term, after "${q.v} ${v}".`, peek().pos);
      /** @type {Formula} */
      let f = { t: 'tt' };
      if (peek().k === 'where') { next(); f = formula(); }
      expect(',', '","');
      return { t: q.k === 'forall' ? 'all' : 'ex', v, d, f, b: formula() };
    };
    /** @returns {Formula} */
    const or = () => {
      let f = and();
      while (peek().k === '||') { next(); f = { t: 'or', f, g: and() }; }
      return f;
    };
    /** @returns {Formula} */
    const and = () => {
      let f = unary();
      while (peek().k === '&&') { next(); f = { t: 'and', f, g: unary() }; }
      return f;
    };
    const isCmp = (/** @type {string} */ k) => ['==', '!=', 'in', 'not'].includes(k);
    /** @returns {Formula} */
    const unary = () => {
      const t = peek();
      if (t.k === '!') { next(); return { t: 'not', f: unary() }; }
      if (t.k === 'forall' || t.k === 'exists') return quant();
      if (t.k === '(') { next(); const f = formula(); expect(')', '")"'); return f; }
      if ((t.k === 'true' || t.k === 'false') && !isCmp(peek(1).k)) { next(); return { t: t.k === 'true' ? 'tt' : 'ff' }; }
      if (t.k === 'nonempty') { next(); return { t: 'nonempty', a: term() }; }
      if (t.k === 'ident' && peek(1).k === '(') {
        next(); next();
        /** @type {Term[]} */
        const args = [];
        if (peek().k !== ')') { args.push(term()); while (peek().k === ',') { next(); args.push(term()); } }
        expect(')', '")" after the arguments of a relation');
        return { t: 'atom', r: t.v, args };
      }
      const a = term();
      const op = next();
      if (op.k === '==') return { t: 'eq', a, b: term() };
      if (op.k === '!=') return { t: 'not', f: { t: 'eq', a, b: term() } };
      if (op.k === 'in') return { t: 'mem', a, b: term() };
      if (op.k === 'not') { expect('in', '"in" after "not"'); return { t: 'not', f: { t: 'mem', a, b: term() } }; }
      throw new RuleSyntaxError(`Expected a comparison (==, !=, in, not in) after a term, found ${op.k === 'eof' ? 'the end' : `"${op.v}"`}.`, op.pos);
    };
    /** @returns {string} */
    const literal = () => {
      const t = next();
      if (t.k === 'str') return valueKey(t.v);
      if (t.k === 'num') return valueKey(Number(t.v));
      if (t.k === 'true' || t.k === 'false') return valueKey(t.k === 'true');
      throw new RuleSyntaxError(`Expected a literal, found ${t.k === 'eof' ? 'the end' : `"${t.v}"`}.`, t.pos);
    };
    /** @returns {Term} */
    const term = () => {
      if (peek().k === 'kindof') { next(); return { t: 'kindOf', of: term() }; }
      /** @type {Term} */
      let x;
      const t = peek();
      if (t.k === 'ident') { next(); x = { t: 'var', name: t.v }; } else if (t.k === '[') {
        next();
        const vs = [];
        if (peek().k !== ']') { vs.push(literal()); while (peek().k === ',') { next(); vs.push(literal()); } }
        expect(']', '"]"');
        return { t: 'lit', vs };
      } else return { t: 'lit', vs: [literal()] };
      while (peek().k === '.') { next(); x = { t: 'prop', of: x, p: expect('ident', 'a property name').v }; }
      return x;
    };
    const ast = formula();
    if (peek().k !== 'eof') throw new RuleSyntaxError(`Unexpected "${peek().v}" after the end of the rule.`, peek().pos);
    return { ok: true, ast };
  } catch (e) {
    if (e instanceof RuleSyntaxError) return { ok: false, error: { message: e.message, pos: e.pos } };
    throw e;
  }
}

/**
 * Static checks: every variable is bound, every kind exists, every property is declared on some kind,
 * every atom names a relation with its arity.
 * @param {Formula} ast @param {any} meta the effective meta-model
 * @param {{arity?: Map<string, number>, scope?: string[], unboundCode?: string}} [opts] the relations
 *   by id with their arity (none: every atom is unknown), the free variables allowed (a relation's
 *   parameters), and the code of an unbound variable
 * @returns {{code: string, message: string}[]}
 */
export function checkRule(ast, meta, opts = {}) {
  /** @type {{code: string, message: string}[]} */
  const out = [];
  const arity = opts.arity ?? new Map();
  const props = new Set(['id']);
  for (const def of Object.values(meta.entities)) for (const p of Object.keys(/** @type {any} */ (def).properties)) props.add(p);
  /** @param {Term} t @param {string[]} scope */
  const term = (t, scope) => {
    if (t.t === 'var') {
      if (!scope.includes(t.name)) {
        out.push(opts.unboundCode
          ? { code: opts.unboundCode, message: `"${t.name}" is free in a clause but is not a parameter (bind it with forall or exists, or declare it in params).` }
          : { code: 'integrity.unbound', message: `"${t.name}" is not a bound variable (bind it with forall or exists; quote a string literal).` });
      }
    } else if (t.t === 'prop') { term(t.of, scope); if (!props.has(t.p)) out.push({ code: 'integrity.property', message: `No entity kind declares a property "${t.p}".` }); }
    else if (t.t === 'kindOf') term(t.of, scope);
  };
  /** @param {Formula} f @param {string[]} scope */
  const walk = (f, scope) => {
    switch (f.t) {
      case 'eq': case 'mem': term(f.a, scope); term(f.b, scope); return;
      case 'nonempty': term(f.a, scope); return;
      case 'not': walk(f.f, scope); return;
      case 'and': case 'or': case 'imp': walk(f.f, scope); walk(f.g, scope); return;
      case 'atom': {
        for (const a of f.args) term(a, scope);
        const n = arity.get(f.r);
        if (n === undefined) out.push({ code: 'integrity.relation-unknown', message: `"${f.r}" is not an integrity relation.` });
        else if (n !== f.args.length) out.push({ code: 'integrity.relation-arity', message: `Relation "${f.r}" has ${n} parameter(s) but is given ${f.args.length} argument(s).` });
        return;
      }
      case 'all': case 'ex':
        if (f.d.t === 'kinds') for (const k of f.d.ks) if (!Object.hasOwn(meta.entities, k)) out.push({ code: 'integrity.kind', message: `"${k}" is not an entity kind.` });
        if (f.d.t === 'term') term(f.d.of, scope);
        walk(f.f, [f.v, ...scope]);
        walk(f.b, [f.v, ...scope]);
    }
  };
  walk(ast, opts.scope ?? []);
  return out;
}

/** The relations a formula names in its atoms. @param {Formula} f @param {Set<string>} [into] */
export function atomsOf(f, into = new Set()) {
  switch (f.t) {
    case 'atom': into.add(f.r); break;
    case 'not': atomsOf(f.f, into); break;
    case 'and': case 'or': case 'imp': atomsOf(f.f, into); atomsOf(f.g, into); break;
    case 'all': case 'ex': atomsOf(f.f, into); atomsOf(f.b, into); break;
  }
  return into;
}

/**
 * Every atom with its polarity, as `posF` of formal/Exegra/Integrity.lean counts it: `!` flips, the
 * left side of `=>` flips, a `forall` filter flips, an `exists` filter does not. (Quantifier domains
 * are terms, which contain no atoms.)
 * @param {Formula} f @param {boolean} [positive]
 * @returns {{r: string, positive: boolean}[]}
 */
export function atomPolarities(f, positive = true) {
  switch (f.t) {
    case 'atom': return [{ r: f.r, positive }];
    case 'not': return atomPolarities(f.f, !positive);
    case 'and': case 'or': return [...atomPolarities(f.f, positive), ...atomPolarities(f.g, positive)];
    case 'imp': return [...atomPolarities(f.f, !positive), ...atomPolarities(f.g, positive)];
    case 'all': return [...atomPolarities(f.f, !positive), ...atomPolarities(f.b, positive)];
    case 'ex': return [...atomPolarities(f.f, positive), ...atomPolarities(f.b, positive)];
    default: return [];
  }
}

// --- derived relations --------------------------------------------------------

/** A relation whose candidate tuples (the product of its parameter domains) exceed this is refused. */
export const RELATION_CANDIDATE_LIMIT = 100000;

/**
 * @typedef {Object} RelationInfo
 * @property {string} id
 * @property {import('./types.js').Entity} entity
 * @property {{name: string, kinds: string[] | '*'}[]} params
 * @property {Formula[]} clauses the clauses that parse
 * @property {Set<string>} uses relations named by the clauses
 * @property {{code: string, message: string} | null} problem why the relation is invalid: a problem of
 *   its own, a relation it uses that is invalid, or a relation of its cycle that is invalid
 * @property {number} stratum index into `strata`
 */

/**
 * @typedef {Object} RelationAnalysis
 * @property {Map<string, RelationInfo>} rels
 * @property {string[][]} strata the strongly connected components of the dependency graph, lowest
 *   first: every relation a stratum uses is in it or in an earlier one
 * @property {Map<string, number>} arity relation id to its number of parameters
 */

/** @type {WeakMap<Model, RelationAnalysis>} */
const RELATIONS = new WeakMap();

/** A parameter name or relation id must be an identifier of the rule language. @param {any} s */
const isIdent = (s) => typeof s === 'string' && /^[A-Za-z_][A-Za-z0-9_]*(-[A-Za-z0-9_]+)*$/.test(s) && !KEYWORDS.has(s);

/**
 * The relations of a model: parsed, checked, stratified. Memoized per model.
 *
 * Stratification: the dependency graph has an edge from each relation to every relation its clauses
 * name. Its strongly connected components, in topological order (Tarjan), are the strata. Within a
 * component every atom of a relation of that component must occur positively; an atom of a lower
 * stratum may occur with any polarity. A relation is invalid when it has a problem of its own, uses
 * an invalid relation, or is in a cycle with one.
 * @param {Model} model
 * @returns {RelationAnalysis}
 */
export function analyzeRelations(model) {
  const hit = RELATIONS.get(model);
  if (hit) return hit;
  const meta = model.meta;
  /** @type {Map<string, RelationInfo>} */
  const rels = new Map();
  /** @type {Map<string, number>} */
  const arity = new Map();
  const get = (/** @type {string} */ id) => /** @type {RelationInfo} */ (rels.get(id));
  for (const e of model.byKind.integrityRelation ?? []) {
    /** @type {RelationInfo} */
    const info = { id: e.id, entity: e, params: [], clauses: [], uses: new Set(), problem: null, stratum: -1 };
    rels.set(e.id, info);
    const fail = (/** @type {string} */ code, /** @type {string} */ message) => { if (!info.problem) info.problem = { code, message }; };
    if (!isIdent(e.id)) fail('integrity.relation-params', `"${e.id}" cannot name a relation in a formula: it is a keyword of the rule language.`);
    const params = Array.isArray(e.data.params) ? e.data.params : null;
    if (!params) { fail('integrity.relation-params', 'params must be a list of {name, kinds}.'); continue; }
    const names = new Set();
    for (const p of params) {
      if (!p || typeof p !== 'object' || !isIdent(p.name)) { fail('integrity.relation-params', `A parameter needs a name that is an identifier and not a keyword (${JSON.stringify(p?.name ?? p)}).`); continue; }
      if (names.has(p.name)) fail('integrity.relation-params', `The parameter "${p.name}" is declared twice.`);
      names.add(p.name);
      if (p.kinds === '*') { info.params.push({ name: p.name, kinds: '*' }); continue; }
      if (!Array.isArray(p.kinds) || p.kinds.length === 0 || !p.kinds.every((/** @type {any} */ k) => typeof k === 'string')) {
        fail('integrity.relation-kind', `The kinds of parameter "${p.name}" must be "*" or a non-empty list of entity kinds.`);
        continue;
      }
      for (const k of p.kinds) if (!Object.hasOwn(meta.entities, k)) fail('integrity.relation-kind', `Parameter "${p.name}": "${k}" is not an entity kind.`);
      info.params.push({ name: p.name, kinds: [...p.kinds] });
    }
    arity.set(e.id, params.length);
  }
  for (const info of rels.values()) {
    const fail = (/** @type {string} */ code, /** @type {string} */ message) => { if (!info.problem) info.problem = { code, message }; };
    const texts = Array.isArray(info.entity.data.clauses) ? info.entity.data.clauses : null;
    if (!texts) { fail('integrity.relation-syntax', 'clauses must be a list of formulas.'); continue; }
    const scope = info.params.map((p) => p.name);
    texts.forEach((/** @type {any} */ text, /** @type {number} */ i) => {
      const parsed = parseRule(String(text ?? ''));
      if (!parsed.ok) { fail('integrity.relation-syntax', `Clause ${i + 1}: ${parsed.error.message} (at character ${parsed.error.pos + 1})`); return; }
      for (const p of checkRule(parsed.ast, meta, { arity, scope, unboundCode: 'integrity.relation-unbound' })) fail(p.code, `Clause ${i + 1}: ${p.message}`);
      atomsOf(parsed.ast, info.uses);
      info.clauses.push(parsed.ast);
    });
  }

  // Tarjan's strongly connected components: a component is emitted after every component it uses.
  const order = [...rels.keys()];
  /** @type {string[][]} */
  const strata = [];
  /** @type {Map<string, number>} */
  const index = new Map();
  /** @type {Map<string, number>} */
  const low = new Map();
  /** @type {string[]} */
  const stack = [];
  const onStack = new Set();
  let counter = 0;
  /** @param {string} v */
  const connect = (v) => {
    index.set(v, counter); low.set(v, counter); counter++;
    stack.push(v); onStack.add(v);
    for (const w of [...get(v).uses].sort()) {
      if (!rels.has(w)) continue;
      if (!index.has(w)) { connect(w); low.set(v, Math.min(/** @type {number} */ (low.get(v)), /** @type {number} */ (low.get(w)))); }
      else if (onStack.has(w)) low.set(v, Math.min(/** @type {number} */ (low.get(v)), /** @type {number} */ (index.get(w))));
    }
    if (low.get(v) === index.get(v)) {
      /** @type {string[]} */
      const comp = [];
      let w;
      do { w = /** @type {string} */ (stack.pop()); onStack.delete(w); comp.push(w); } while (w !== v);
      comp.sort((a, b) => order.indexOf(a) - order.indexOf(b));
      strata.push(comp);
    }
  };
  for (const id of [...order].sort()) if (!index.has(id)) connect(id);

  strata.forEach((comp, i) => {
    const members = new Set(comp);
    for (const id of comp) get(id).stratum = i;
    /** @type {string[]} */
    const negative = [];
    for (const id of comp) {
      get(id).clauses.forEach((c, ci) => {
        for (const a of atomPolarities(c)) if (!a.positive && members.has(a.r)) negative.push(`"${a.r}" occurs negatively in clause ${ci + 1} of "${id}"`);
      });
    }
    if (negative.length) {
      const message = `Recursion through negation: ${negative.join('; ')}. Within a cycle of relations (${comp.join(', ')}) every atom of the cycle must occur positively.`;
      for (const id of comp) if (!get(id).problem) get(id).problem = { code: 'integrity.relation-unstratified', message };
    }
    // Invalid through a relation it uses: lower strata are settled; within the cycle, see below.
    for (const id of comp) {
      const info = get(id);
      if (info.problem) continue;
      for (const u of [...info.uses].sort()) {
        const dep = rels.get(u);
        if (dep && !members.has(u) && dep.problem) { info.problem = { code: dep.problem.code, message: `It uses relation "${u}", which is invalid: ${dep.problem.message}` }; break; }
      }
    }
    const bad = comp.find((id) => get(id).problem);
    if (bad) {
      const code = /** @type {{code: string}} */ (get(bad).problem).code;
      for (const id of comp) if (!get(id).problem) get(id).problem = { code, message: `It is in a cycle with relation "${bad}", which is invalid.` };
      return;
    }
    for (const id of comp) {
      const info = get(id);
      const n = info.params.reduce((acc, p) => acc * domainOf(model, p.kinds).length, 1);
      if (n > RELATION_CANDIDATE_LIMIT) info.problem = { code: 'integrity.relation-size', message: `Its parameter domains give ${n} candidate tuples, more than ${RELATION_CANDIDATE_LIMIT}; narrow the parameter kinds.` };
    }
    const big = comp.find((id) => get(id).problem);
    if (big) for (const id of comp) if (!get(id).problem) get(id).problem = { code: 'integrity.relation-size', message: `It is in a cycle with relation "${big}", which is invalid.` };
  });
  const out = { rels, strata, arity };
  RELATIONS.set(model, out);
  return out;
}

/** The entity ids (typed keys) a parameter ranges over, in model order. @param {Model} model @param {string[] | '*'} kinds */
export function domainOf(model, kinds) {
  /** @type {string[]} */
  const out = [];
  for (const e of model.entities.values()) if (kinds === '*' || kinds.includes(e.kind)) out.push('s:' + e.id);
  return out;
}

/** The candidate tuples of a relation: the product of its parameter domains. @param {Model} model @param {{kinds: string[] | '*'}[]} params */
export function candidates(model, params) {
  /** @type {string[][]} */
  let out = [[]];
  for (const p of params) {
    const dom = domainOf(model, p.kinds);
    out = out.flatMap((vs) => dom.map((v) => [...vs, v]));
  }
  return out;
}

/**
 * A tuple of typed keys as one string: its JSON text, which is unambiguous whatever characters the
 * values hold (an id may contain any character; validation reports it, evaluation still runs).
 * @param {string[]} vs
 */
export const tupleKey = (vs) => JSON.stringify(vs);

/** The tuple a `tupleKey` stands for. @param {string} key @returns {string[]} */
export const tupleOf = (key) => JSON.parse(key);

/** @type {WeakMap<Model, {tables: Map<string, Set<string>>, done: Set<number>, ev: any}>} */
const TABLES = new WeakMap();

/**
 * The tables of the valid relations of a model: per relation, the keys (`tupleKey`) of its tuples.
 * Computed stratum by stratum, lowest first; within a stratum by iteration from the empty table:
 * every candidate tuple not yet in its relation is added when one of its clauses holds, until a
 * pass adds nothing. The clauses are monotone in the stratum's own atoms (they occur only
 * positively), so every added tuple is in the least model, and the final table is closed under the
 * clauses: it is the least model, as `Least` and `solve` in formal/Exegra/Integrity.lean define and
 * compute it. Every pass but the last adds a tuple, so there are at most as many passes as candidate
 * tuples plus one.
 *
 * Only the strata of `ids` and of the relations they use, directly or not, are computed (every
 * stratum when `ids` is absent). Each stratum is computed at most once per model: the tables are
 * memoized and grow as later calls need more relations.
 * @param {Model} model @param {Iterable<string>} [ids] the relations needed
 * @returns {Map<string, Set<string>>}
 */
export function relationTables(model, ids) {
  /** @type {{tables: Map<string, Set<string>>, done: Set<number>, ev: ReturnType<typeof makeEvaluator>} | undefined} */
  let st = TABLES.get(model);
  if (!st) {
    /** @type {Map<string, Set<string>>} */
    const tables = new Map();
    st = { tables, done: new Set(), ev: makeEvaluator(model, tables) };
    TABLES.set(model, st);
  }
  const { tables, done, ev } = st;
  const { rels, strata } = analyzeRelations(model);
  /** @type {Set<number>} */
  const need = new Set();
  if (ids === undefined) strata.forEach((_, i) => need.add(i));
  else {
    const seen = new Set();
    const work = [...ids];
    while (work.length) {
      const id = /** @type {string} */ (work.pop());
      const info = rels.get(id);
      if (!info || seen.has(id)) continue;
      seen.add(id);
      need.add(info.stratum);
      for (const u of info.uses) work.push(u);
    }
  }
  // Ascending index is topological order: every stratum a needed stratum uses is needed and lower.
  for (const si of [...need].sort((x, y) => x - y)) {
    if (done.has(si)) continue;
    done.add(si);
    const members = strata[si].map((id) => /** @type {RelationInfo} */ (rels.get(id)));
    if (members.some((r) => r.problem)) continue;
    for (const r of members) tables.set(r.id, new Set());
    const cands = members.map((r) => candidates(model, r.params));
    let changed = true;
    while (changed) {
      changed = false;
      members.forEach((r, i) => {
        const table = /** @type {Set<string>} */ (tables.get(r.id));
        for (const vs of cands[i]) {
          const key = tupleKey(vs);
          if (table.has(key)) continue;
          /** @type {Map<string, string>} */
          const env = new Map();
          r.params.forEach((p, j) => env.set(p.name, vs[j]));
          if (r.clauses.some((c) => ev.sat(c, env))) { table.add(key); changed = true; }
        }
      });
    }
  }
  return tables;
}

/**
 * The relations a rule depends on, directly or through other relations, and the first problem that
 * makes it invalid: an atom of an invalid relation.
 * @param {Model} model @param {Formula} ast
 * @returns {{used: Set<string>, problem: {code: string, message: string} | null}}
 */
export function relationsOfRule(model, ast) {
  const { rels } = analyzeRelations(model);
  const used = new Set();
  /** @type {{code: string, message: string} | null} */
  let problem = null;
  const work = [...atomsOf(ast)];
  for (const r of [...work].sort()) {
    const info = rels.get(r);
    if (info?.problem && !problem) problem = { code: info.problem.code, message: `Relation "${r}" is invalid: ${info.problem.message}` };
  }
  while (work.length) {
    const r = /** @type {string} */ (work.pop());
    if (used.has(r) || !rels.has(r)) continue;
    used.add(r);
    for (const u of /** @type {RelationInfo} */ (rels.get(r)).uses) work.push(u);
  }
  return { used, problem };
}

// --- evaluation -------------------------------------------------------------

/**
 * The evaluator of formulas over a model, with atoms looked up in `tables` (relation id to the keys
 * of its tuples; a relation without a table holds nothing).
 * @param {Model} model @param {Map<string, Set<string>>} tables
 */
function makeEvaluator(model, tables) {
  const entityOf = (/** @type {string} */ key) => (key.startsWith('s:') ? model.entities.get(key.slice(2)) : undefined);
  /** @type {Map<string, any[]>} */
  const kindCache = new Map();
  /** @param {Term} t @param {Map<string, string>} env @returns {string[]} */
  const termVals = (t, env) => {
    switch (t.t) {
      case 'var': { const v = env.get(t.name); return v === undefined ? [] : [v]; }
      case 'lit': return t.vs;
      case 'prop': {
        const out = [];
        for (const v of termVals(t.of, env)) {
          const e = entityOf(v);
          if (e) for (const k of propertyKeys(e.data[t.p])) out.push(k);
        }
        return out;
      }
      case 'kindOf': {
        const out = [];
        for (const v of termVals(t.of, env)) { const e = entityOf(v); if (e) out.push(valueKey(e.kind)); }
        return out;
      }
    }
  };
  /** @param {Dom} d @param {Map<string, string>} env @returns {string[]} */
  const domVals = (d, env) => {
    if (d.t === 'any') return [...model.entities.keys()].map((id) => 's:' + id);
    if (d.t === 'kinds') {
      const key = d.ks.join('|');
      if (!kindCache.has(key)) kindCache.set(key, [...model.entities.values()].filter((e) => d.ks.includes(e.kind)).map((e) => 's:' + e.id));
      return /** @type {string[]} */ (kindCache.get(key));
    }
    return termVals(d.of, env);
  };
  /**
   * Some choice of one value from each list is a tuple of the table.
   * @param {Set<string>} table @param {string[][]} lists @param {number} i @param {string[]} acc
   * @returns {boolean}
   */
  const pick = (table, lists, i, acc) => {
    if (i === lists.length) return table.has(tupleKey(acc));
    return lists[i].some((v) => pick(table, lists, i + 1, [...acc, v]));
  };
  /** @param {Formula} f @param {Map<string, string>} env @returns {boolean} */
  const sat = (f, env) => {
    switch (f.t) {
      case 'tt': return true;
      case 'ff': return false;
      case 'eq': { const a = termVals(f.a, env), b = termVals(f.b, env); return a.every((x) => b.includes(x)) && b.every((x) => a.includes(x)); }
      case 'mem': { const a = termVals(f.a, env), b = termVals(f.b, env); return a.length > 0 && a.every((x) => b.includes(x)); }
      case 'nonempty': return termVals(f.a, env).length > 0;
      case 'not': return !sat(f.f, env);
      case 'and': return sat(f.f, env) && sat(f.g, env);
      case 'or': return sat(f.f, env) || sat(f.g, env);
      case 'imp': return !sat(f.f, env) || sat(f.g, env);
      case 'all': return domVals(f.d, env).every((v) => { const e2 = new Map(env).set(f.v, v); return !sat(f.f, e2) || sat(f.b, e2); });
      case 'ex': return domVals(f.d, env).some((v) => { const e2 = new Map(env).set(f.v, v); return sat(f.f, e2) && sat(f.b, e2); });
      case 'atom': {
        const table = tables.get(f.r);
        return table !== undefined && pick(table, f.args.map((a) => termVals(a, env)), 0, []);
      }
    }
  };
  return { termVals, domVals, sat };
}

/**
 * Evaluate one parsed rule over a model, as `eval` and `cex` of formal/Exegra/Integrity.lean do.
 * Counterexamples are assignments of the leading universal quantifiers that pass their filters and
 * falsify the body. `instances` counts the bodies evaluated under that prefix. Atoms are looked up
 * in the model's relation tables (`relationTables`).
 * @param {Model} model @param {Formula} ast @param {Map<string, Set<string>>} [tables]
 */
export function evaluateFormula(model, ast, tables) {
  const { domVals, sat } = makeEvaluator(model, tables ?? (atomsOf(ast).size ? relationTables(model, atomsOf(ast)) : new Map()));
  let instances = 0;
  /** @type {{vars: string[], values: string[]}[]} */
  const counterexamples = [];
  /** @param {Formula} f @param {Map<string, string>} env @param {string[]} vars @param {string[]} vals */
  const prefix = (f, env, vars, vals) => {
    if (f.t !== 'all') {
      instances++;
      if (!sat(f, env)) counterexamples.push({ vars, values: vals });
      return;
    }
    for (const v of domVals(f.d, env)) {
      const e2 = new Map(env).set(f.v, v);
      if (sat(f.f, e2)) prefix(f.b, e2, [...vars, f.v], [...vals, v]);
    }
  };
  prefix(ast, new Map(), [], []);
  return { holds: counterexamples.length === 0, instances, vacuous: ast.t === 'all' && instances === 0, counterexamples };
}

/**
 * @typedef {Object} RuleResult
 * @property {string} ruleId
 * @property {'error'|'warning'} severity
 * @property {string} statement
 * @property {'holds'|'violated'|'invalid'} status
 * @property {number} instances
 * @property {boolean} vacuous
 * @property {{vars: string[], values: string[]}[]} counterexamples
 * @property {string} [problem] why the rule is invalid
 * @property {string} [problemCode] the diagnostic code of the problem (integrity.invalid, or the
 *   integrity.relation-* code of a relation the rule names that is unknown, misused or invalid)
 * @property {number} ms evaluation time
 */

/** @type {WeakMap<Model, RuleResult[]>} */
const CACHE = new WeakMap();

/**
 * Every integrity rule of the model, evaluated. Memoized per model: validation and the ratchet of
 * Project.apply share one evaluation of each model.
 * @param {Model} model
 * @returns {RuleResult[]}
 */
export function evaluateIntegrity(model) {
  const hit = CACHE.get(model);
  if (hit) return hit;
  const out = (model.byKind.integrityRule ?? []).map((r) => evaluateRuleEntity(model, r));
  CACHE.set(model, out);
  return out;
}

/** @param {Model} model @param {import('./types.js').Entity} r @returns {RuleResult} */
export function evaluateRuleEntity(model, r) {
  const severity = /** @type {'error'|'warning'} */ (r.data.severity === 'warning' ? 'warning' : 'error');
  const base = { ruleId: r.id, severity, statement: String(r.data.statement ?? ''), instances: 0, vacuous: false, counterexamples: [], ms: 0 };
  const parsed = parseRule(String(r.data.rule ?? ''));
  if (!parsed.ok) return { ...base, status: 'invalid', problem: `${parsed.error.message} (at character ${parsed.error.pos + 1})` };
  const { arity } = analyzeRelations(model);
  const problems = checkRule(parsed.ast, model.meta, { arity });
  const relationProblem = problems.find((p) => p.code.startsWith('integrity.relation-'));
  if (problems.length) return { ...base, status: 'invalid', problem: problems.map((p) => p.message).join(' '), problemCode: relationProblem?.code ?? 'integrity.invalid' };
  const used = relationsOfRule(model, parsed.ast);
  if (used.problem) return { ...base, status: 'invalid', problem: used.problem.message, problemCode: used.problem.code };
  const t0 = performance.now();
  const res = evaluateFormula(model, parsed.ast, used.used.size ? relationTables(model, used.used) : new Map());
  return { ...base, status: res.holds ? 'holds' : 'violated', instances: res.instances, vacuous: res.vacuous, counterexamples: res.counterexamples, ms: performance.now() - t0 };
}

/** One counterexample as "e = area-rev (line 12), b = g-own-01 (line 40)". @param {Model} model @param {{vars: string[], values: string[]}} c */
export function describeCounterexample(model, c) {
  if (!c.vars.length) return 'the rule is false (it has no leading universal quantifier to name an instance)';
  return c.vars.map((v, i) => {
    const key = c.values[i];
    const e = key.startsWith('s:') ? model.entities.get(key.slice(2)) : undefined;
    return e ? `${v} = ${e.id} (${e.kind}, line ${e.loc.line})` : `${v} = ${keyText(key)}`;
  }).join(', ');
}

/** Bindings of a counterexample with entity ids and lines. @param {Model} model @param {{vars: string[], values: string[]}} c */
export function counterexampleJson(model, c) {
  return c.vars.map((v, i) => {
    const key = c.values[i];
    const e = key.startsWith('s:') ? model.entities.get(key.slice(2)) : undefined;
    return e ? { variable: v, entity: e.id, kind: e.kind, line: e.loc.line } : { variable: v, value: keyText(key) };
  });
}

/** Stable identity of a violation, for the ratchet. @param {string} ruleId @param {{values: string[]}} c */
export function violationKey(ruleId, c) {
  return JSON.stringify([ruleId, ...c.values]);
}

/**
 * Diagnostics for validation: an invalid relation is an error with its integrity.relation-* code; an
 * invalid rule is an error (integrity.invalid, or the code of the relation problem that makes it
 * invalid); each counterexample is a diagnostic of the rule's severity, code `integrity.violated`,
 * placed at the first entity it names; a rule whose quantifier ranges over nothing is a warning.
 * @param {Model} model
 * @returns {Diagnostic[]}
 */
export function integrityDiagnostics(model) {
  /** @type {Diagnostic[]} */
  const out = [];
  for (const rel of analyzeRelations(model).rels.values()) {
    if (!rel.problem) continue;
    const e = rel.entity;
    out.push({ code: rel.problem.code, severity: 'error', message: `Integrity relation "${rel.id}": ${rel.problem.message}`, entityId: e.id, loc: e.loc, path: [...e.path, 'clauses'] });
  }
  for (const r of evaluateIntegrity(model)) {
    const rule = /** @type {import('./types.js').Entity} */ (model.entities.get(r.ruleId));
    if (r.status === 'invalid') {
      out.push({ code: r.problemCode ?? 'integrity.invalid', severity: 'error', message: `Integrity rule "${r.ruleId}": ${r.problem}`, entityId: rule.id, loc: rule.loc, path: [...rule.path, 'rule'] });
      continue;
    }
    if (r.vacuous) out.push({ code: 'integrity.vacuous', severity: 'warning', message: `Integrity rule "${r.ruleId}" is vacuous: its quantifier ranges over nothing, so it checks nothing.`, entityId: rule.id, loc: rule.loc, path: [...rule.path, 'rule'] });
    for (const c of r.counterexamples) {
      const firstKey = c.values.find((k) => k.startsWith('s:') && model.entities.has(k.slice(2)));
      const at = firstKey ? /** @type {import('./types.js').Entity} */ (model.entities.get(firstKey.slice(2))) : rule;
      out.push({ code: 'integrity.violated', severity: r.severity, message: `Integrity rule "${r.ruleId}" is violated: ${describeCounterexample(model, c)}. ${r.statement}`, entityId: at.id, loc: at.loc, path: at.path });
    }
  }
  return out;
}

/**
 * The ratchet: violations of `error` rules in `after` that `before` did not have. Existing
 * violations do not block unrelated edits; a transaction may not add one.
 * @param {Model|null} before @param {Model} after
 */
export function newErrorViolations(before, after) {
  const old = new Set();
  if (before) for (const r of evaluateIntegrity(before)) for (const c of r.counterexamples) old.add(violationKey(r.ruleId, c));
  /** @type {{ruleId: string, statement: string, counterexample: {vars: string[], values: string[]}}[]} */
  const added = [];
  for (const r of evaluateIntegrity(after)) {
    if (r.severity !== 'error') continue;
    for (const c of r.counterexamples) if (!old.has(violationKey(r.ruleId, c))) added.push({ ruleId: r.ruleId, statement: r.statement, counterexample: c });
  }
  return added;
}
