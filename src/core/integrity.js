// Integrity rules: declarative consistency rules over a whole specification.
//
// A rule is an `integrityRule` entity whose `rule` is a formula of a small first-order language over
// the finite model: quantifiers over entities (of some kinds, or all) or over the values of a term,
// property access that follows references through lists, equality, membership, `nonempty`, `kindof`
// and the boolean connectives. No recursion and no arithmetic, so evaluation is total. The same
// formula is exported to Lean (integrity-export.js, formal/Exegra/Integrity.lean), where `Sat` is
// its meaning and `eval` the checker this file mirrors.

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */

/**
 * @typedef {{t: 'var', name: string} | {t: 'lit', vs: string[]} | {t: 'prop', of: Term, p: string} | {t: 'kindOf', of: Term}} Term
 * @typedef {{t: 'any'} | {t: 'kinds', ks: string[]} | {t: 'term', of: Term}} Dom
 * @typedef {{t: 'tt'} | {t: 'ff'} | {t: 'eq', a: Term, b: Term} | {t: 'mem', a: Term, b: Term} | {t: 'nonempty', a: Term}
 *   | {t: 'not', f: Formula} | {t: 'and'|'or'|'imp', f: Formula, g: Formula}
 *   | {t: 'all'|'ex', v: string, d: Dom, f: Formula, b: Formula}} Formula
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

const NUM = /-?[0-9]+(.[0-9]+)?([eE][+-]?[0-9]+)?/y;

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
 *            | term ('==' | '!=' | 'in' | 'not' 'in') term
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
 * Static checks: every variable is bound, every kind exists, every property is declared on some kind.
 * @param {Formula} ast @param {any} meta the effective meta-model
 * @returns {{code: string, message: string}[]}
 */
export function checkRule(ast, meta) {
  /** @type {{code: string, message: string}[]} */
  const out = [];
  const props = new Set(['id']);
  for (const def of Object.values(meta.entities)) for (const p of Object.keys(/** @type {any} */ (def).properties)) props.add(p);
  /** @param {Term} t @param {string[]} scope */
  const term = (t, scope) => {
    if (t.t === 'var') { if (!scope.includes(t.name)) out.push({ code: 'integrity.unbound', message: `"${t.name}" is not a bound variable (bind it with forall or exists; quote a string literal).` }); }
    else if (t.t === 'prop') { term(t.of, scope); if (!props.has(t.p)) out.push({ code: 'integrity.property', message: `No entity kind declares a property "${t.p}".` }); }
    else if (t.t === 'kindOf') term(t.of, scope);
  };
  /** @param {Formula} f @param {string[]} scope */
  const walk = (f, scope) => {
    switch (f.t) {
      case 'eq': case 'mem': term(f.a, scope); term(f.b, scope); return;
      case 'nonempty': term(f.a, scope); return;
      case 'not': walk(f.f, scope); return;
      case 'and': case 'or': case 'imp': walk(f.f, scope); walk(f.g, scope); return;
      case 'all': case 'ex':
        if (f.d.t === 'kinds') for (const k of f.d.ks) if (!Object.hasOwn(meta.entities, k)) out.push({ code: 'integrity.kind', message: `"${k}" is not an entity kind.` });
        if (f.d.t === 'term') term(f.d.of, scope);
        walk(f.f, [f.v, ...scope]);
        walk(f.b, [f.v, ...scope]);
    }
  };
  walk(ast, []);
  return out;
}

// --- evaluation -------------------------------------------------------------

/**
 * Evaluate one parsed rule over a model, as `eval` and `cex` of formal/Exegra/Integrity.lean do.
 * Counterexamples are assignments of the leading universal quantifiers that pass their filters and
 * falsify the body. `instances` counts the bodies evaluated under that prefix.
 * @param {Model} model @param {Formula} ast
 */
export function evaluateFormula(model, ast) {
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
    }
  };
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
  const problems = checkRule(parsed.ast, model.meta);
  if (problems.length) return { ...base, status: 'invalid', problem: problems.map((p) => p.message).join(' ') };
  const t0 = performance.now();
  const res = evaluateFormula(model, parsed.ast);
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
  return ruleId + '\u0000' + c.values.join('\u0000');
}

/**
 * Diagnostics for validation: an invalid rule is an error; each counterexample is a diagnostic of
 * the rule's severity, code `integrity.violated`, placed at the first entity it names; a rule whose
 * quantifier ranges over nothing is a warning.
 * @param {Model} model
 * @returns {Diagnostic[]}
 */
export function integrityDiagnostics(model) {
  /** @type {Diagnostic[]} */
  const out = [];
  for (const r of evaluateIntegrity(model)) {
    const rule = /** @type {import('./types.js').Entity} */ (model.entities.get(r.ruleId));
    if (r.status === 'invalid') {
      out.push({ code: 'integrity.invalid', severity: 'error', message: `Integrity rule "${r.ruleId}": ${r.problem}`, entityId: rule.id, loc: rule.loc, path: [...rule.path, 'rule'] });
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
