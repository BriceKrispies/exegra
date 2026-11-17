// Integrity rules to Lean: the facts a rule reads and the rule itself, as terms of
// formal/Exegra/Integrity.lean. Pure and deterministic; tools/prove-integrity.js runs Lean.
//
// Only what the rule touches is exported: the entities it can reach (every entity when it quantifies
// over `*`, otherwise the entities of the kinds it quantifies over, closed under the references of
// the properties it reads) and, per entity, its kind and those properties. Every value is interned
// to a natural number, so the Lean kernel compares numbers, not strings.

import { parseRule, checkRule, propertyKeys, valueKey } from './integrity.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./integrity.js').Formula} Formula */
/** @typedef {import('./integrity.js').Term} Term */

/** Axioms a kernel-checked integrity proof may depend on: Lean's standard ones. */
export const STANDARD_AXIOMS = ['propext', 'Classical.choice', 'Quot.sound'];

/** Properties read and literals named by a formula. @param {Formula} ast */
function touched(ast) {
  const props = new Set(), lits = new Set(), kinds = new Set();
  let any = false;
  /** @param {Term} t */
  const term = (t) => {
    if (t.t === 'prop') { props.add(t.p); term(t.of); } else if (t.t === 'kindOf') term(t.of);
    else if (t.t === 'lit') for (const v of t.vs) lits.add(v);
  };
  /** @param {Formula} f */
  const walk = (f) => {
    switch (f.t) {
      case 'eq': case 'mem': term(f.a); term(f.b); return;
      case 'nonempty': term(f.a); return;
      case 'not': walk(f.f); return;
      case 'and': case 'or': case 'imp': walk(f.f); walk(f.g); return;
      case 'all': case 'ex':
        if (f.d.t === 'any') any = true;
        else if (f.d.t === 'kinds') for (const k of f.d.ks) kinds.add(k);
        else term(f.d.of);
        walk(f.f); walk(f.b);
    }
  };
  walk(ast);
  return { props: [...props].sort(), lits, kinds, any };
}

/**
 * The export of one rule: interned values, entities, and the formula with de Bruijn variables.
 * @param {Model} model @param {string} ruleId
 */
export function exportRule(model, ruleId) {
  const rule = model.entities.get(ruleId);
  if (!rule || rule.kind !== 'integrityRule') throw new Error(`"${ruleId}" is not an integrity rule.`);
  const parsed = parseRule(String(rule.data.rule ?? ''));
  if (!parsed.ok) throw new Error(`Integrity rule "${ruleId}" does not parse: ${parsed.error.message}`);
  const problems = checkRule(parsed.ast, model.meta);
  if (problems.length) throw new Error(`Integrity rule "${ruleId}": ${problems.map((p) => p.message).join(' ')}`);
  const ast = parsed.ast;
  const t = touched(ast);

  // Entities: the quantified kinds (or all), plus every entity reachable through a read property.
  /** @type {Set<string>} */
  const ids = new Set();
  /** @type {string[]} */
  const work = [];
  const add = (/** @type {string} */ id) => { if (!ids.has(id) && model.entities.has(id)) { ids.add(id); work.push(id); } };
  for (const e of model.entities.values()) if (t.any || t.kinds.has(e.kind)) add(e.id);
  for (const v of t.lits) if (v.startsWith('s:')) add(v.slice(2));
  while (work.length) {
    const e = /** @type {any} */ (model.entities.get(/** @type {string} */ (work.pop())));
    for (const p of t.props) for (const k of propertyKeys(e.data[p])) if (k.startsWith('s:')) add(k.slice(2));
  }
  const entityIds = [...ids].sort();

  /** @type {Map<string, number>} */
  const intern = new Map();
  const num = (/** @type {string} */ key) => {
    let n = intern.get(key);
    if (n === undefined) { n = intern.size; intern.set(key, n); }
    return n;
  };
  for (const id of entityIds) num('s:' + id);
  const entities = entityIds.map((id) => {
    const e = /** @type {any} */ (model.entities.get(id));
    const props = [];
    for (const p of t.props) {
      const vs = propertyKeys(e.data[p]);
      if (vs.length) props.push({ p: num('p:' + p), vs: vs.map(num) });
    }
    return { id: num('s:' + id), kind: num(valueKey(e.kind)), props };
  });

  /** @param {Term} x @param {string[]} scope @returns {any} */
  const term = (x, scope) => {
    switch (x.t) {
      case 'var': return { t: 'var', i: scope.indexOf(x.name) };
      case 'lit': return { t: 'lit', vs: x.vs.map(num) };
      case 'prop': return { t: 'prop', of: term(x.of, scope), p: num('p:' + x.p) };
      case 'kindOf': return { t: 'kindOf', of: term(x.of, scope) };
    }
  };
  /** @param {Formula} f @param {string[]} scope @returns {any} */
  const formula = (f, scope) => {
    switch (f.t) {
      case 'tt': case 'ff': return { t: f.t };
      case 'eq': case 'mem': return { t: f.t, a: term(f.a, scope), b: term(f.b, scope) };
      case 'nonempty': return { t: 'nonempty', a: term(f.a, scope) };
      case 'not': return { t: 'not', f: formula(f.f, scope) };
      case 'and': case 'or': case 'imp': return { t: f.t, f: formula(f.f, scope), g: formula(f.g, scope) };
      case 'all': case 'ex': {
        const d = f.d.t === 'any' ? { t: 'any' } : f.d.t === 'kinds' ? { t: 'kinds', ks: f.d.ks.map((k) => num(valueKey(k))) } : { t: 'term', of: term(f.d.of, scope) };
        const inner = [f.v, ...scope];
        return { t: f.t, d, f: formula(f.f, inner), b: formula(f.b, inner) };
      }
    }
  };
  const lean = formula(ast, []);
  return { ruleId, statement: String(rule.data.statement ?? ''), text: String(rule.data.rule), ast, formula: lean, entities, intern, props: t.props, quantifiesOverAll: t.any };
}

/** Witness values (typed keys) as interned numbers. @param {ReturnType<typeof exportRule>} ex @param {string[]} values */
export function witnessNumbers(ex, values) {
  return values.map((k) => {
    const n = ex.intern.get(k);
    if (n === undefined) throw new Error(`The witness value ${k} is not among the exported facts.`);
    return n;
  });
}

/** The request `exegra-lean integrity` reads. @param {ReturnType<typeof exportRule>} ex */
export function integrityRequest(ex) {
  return JSON.stringify({ entities: ex.entities, rules: [{ id: ex.ruleId, formula: ex.formula }] });
}

/** @param {any} x @returns {string} */
function leanTerm(x) {
  switch (x.t) {
    case 'var': return `(.var ${x.i})`;
    case 'lit': return `(.lit [${x.vs.join(', ')}])`;
    case 'prop': return `(.prop ${leanTerm(x.of)} ${x.p})`;
    case 'kindOf': return `(.kindOf ${leanTerm(x.of)})`;
  }
  throw new Error('unknown term');
}

/** @param {any} f @returns {string} */
export function leanFormula(f) {
  switch (f.t) {
    case 'tt': case 'ff': return `.${f.t}`;
    case 'eq': case 'mem': return `(.${f.t} ${leanTerm(f.a)} ${leanTerm(f.b)})`;
    case 'nonempty': return `(.nonempty ${leanTerm(f.a)})`;
    case 'not': return `(.not ${leanFormula(f.f)})`;
    case 'and': case 'or': case 'imp': return `(.${f.t} ${leanFormula(f.f)} ${leanFormula(f.g)})`;
    case 'all': case 'ex': {
      const d = f.d.t === 'any' ? '.any' : f.d.t === 'kinds' ? `(.kinds [${f.d.ks.join(', ')}])` : `(.term ${leanTerm(f.d.of)})`;
      return `(.${f.t} ${d} ${leanFormula(f.f)} ${leanFormula(f.b)})`;
    }
  }
  throw new Error('unknown formula');
}

/** Balanced search tree over entities sorted by interned id. @param {any[]} ents */
function leanFacts(ents) {
  const sorted = [...ents].sort((a, b) => a.id - b.id);
  /** @param {number} lo @param {number} hi @returns {string} */
  const tree = (lo, hi) => {
    if (lo >= hi) return '.leaf';
    const m = (lo + hi) >> 1, e = sorted[m];
    const props = e.props.map((/** @type {any} */ p) => `(${p.p}, [${p.vs.join(', ')}])`).join(', ');
    return `(.node ${tree(lo, m)} (E ${e.id} ${e.kind} [${props}]) ${tree(m + 1, hi)})`;
  };
  return tree(0, sorted.length);
}

/** A Lean namespace component for a rule id. @param {string} ruleId */
export function proofNamespace(ruleId) {
  return 'Exegra.IntegrityProof.R_' + ruleId.replace(/[^A-Za-z0-9]/g, '_');
}

/** @param {string} ruleId */
export function proofFileName(ruleId) {
  return `generated/integrity/${ruleId}.lean`;
}

/**
 * The Lean proof file of one rule: the facts, the rule, `facts_search_tree`, and either `holds`
 * (proof by reflection) or one `violated_<n>` per witness (refutation from the witness alone).
 * Every theorem is discharged by `decide +kernel`: the kernel evaluates the checker; no compiled
 * code is trusted.
 * @param {ReturnType<typeof exportRule>} ex
 * @param {{holds: true} | {holds: false, witnesses: number[][]}} claim what the file states
 */
export function leanProofFile(ex, claim) {
  const theorems = claim.holds ? ['holds'] : claim.witnesses.map((_, i) => `violated_${i}`);
  const lines = [
    'import Exegra.Integrity',
    '',
    `-- Integrity rule "${ex.ruleId}", generated by exegra prove-integrity. Do not edit.`,
    `-- Statement: ${ex.statement.replace(/\n/g, ' ')}`,
    `-- Rule: ${ex.text.replace(/\n/g, ' ')}`,
    `-- Facts: ${ex.entities.length} entities, properties ${ex.props.join(', ') || '(none)'}; values are interned (${ex.ruleId}.values.json).`,
    '',
    'set_option maxRecDepth 100000',
    '',
    `namespace ${proofNamespace(ex.ruleId)}`,
    'open Exegra.Integrity',
    '',
    'abbrev E (i k : Nat) (ps : List (Nat × List Nat)) : Ent := ⟨i, k, ps⟩',
    '',
    `noncomputable def facts : Facts := ${leanFacts(ex.entities)}`,
    '',
    `def rule : Formula := ${leanFormula(ex.formula)}`,
    '',
    '-- Ids are unique and ordered, so following a reference finds exactly that entity (Facts.find_complete).',
    'theorem facts_search_tree : facts.bst none none = true := by decide +kernel',
    '',
  ];
  if (claim.holds) lines.push('theorem holds : Sat facts [] rule := holds_of_eval (by decide +kernel)');
  else claim.witnesses.forEach((w, i) => lines.push(`theorem violated_${i} : ¬ Sat facts [] rule := violated_of_refutes [${w.join(', ')}] (by decide +kernel)`));
  lines.push('');
  for (const t of ['facts_search_tree', ...theorems]) lines.push(`#print axioms ${t}`);
  lines.push('', `end ${proofNamespace(ex.ruleId)}`, '');
  return lines.join('\n');
}

/** The intern table, for reading a proof file. @param {ReturnType<typeof exportRule>} ex */
export function valuesTable(ex) {
  /** @type {Record<string, string>} */
  const out = {};
  for (const [k, n] of ex.intern) out[n] = k;
  return JSON.stringify(out, null, 0) + '\n';
}

/**
 * Axioms per theorem from `#print axioms` output.
 * @param {string} output
 * @returns {Map<string, string[]>}
 */
export function parseAxioms(output) {
  /** @type {Map<string, string[]>} */
  const out = new Map();
  const re = /'([^']+)' depends on axioms: \[([^\]]*)\]/g;
  let m;
  while ((m = re.exec(output))) out.set(/** @type {string} */ (m[1].split('.').pop()), m[2].split(',').map((s) => s.trim()).filter(Boolean));
  const none = /'([^']+)' does not depend on any axioms/g;
  while ((m = none.exec(output))) out.set(/** @type {string} */ (m[1].split('.').pop()), []);
  return out;
}

/** Only Lean's standard axioms: no `Lean.ofReduceBool` (native_decide), no `sorryAx`. @param {string[]} axioms */
export function kernelChecked(axioms) {
  return axioms.every((a) => STANDARD_AXIOMS.includes(a));
}
