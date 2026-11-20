// Integrity rules to Lean: the facts a rule reads and the rule itself, as terms of
// formal/Exegra/Integrity.lean. Pure and deterministic; tools/prove-integrity.js runs Lean.
//
// Only what the rule touches is exported: the entities it can reach (every entity when it quantifies
// over `*`, otherwise the entities of the kinds it quantifies over, closed under the references of
// the properties it reads) and, per entity, its kind and those properties. Every value is interned
// to a natural number, so the Lean kernel compares numbers, not strings.
//
// A rule that names derived relations brings its program: the relations it uses, directly or
// through other relations, in stratum order (lowest first), with their parameter domains and their
// clauses; the facts then also cover what the clauses read and the parameter domains. The JavaScript
// tables of those relations are exported too, in the layout `solve` of Integrity.lean produces, so
// the proof file can state `solve facts prog [] = some table`.

import { parseRule, checkRule, propertyKeys, valueKey, analyzeRelations, relationsOfRule, relationTables, tupleOf } from './integrity.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./integrity.js').Formula} Formula */
/** @typedef {import('./integrity.js').Term} Term */

/** Axioms a kernel-checked integrity proof may depend on: Lean's standard ones. */
export const STANDARD_AXIOMS = ['propext', 'Classical.choice', 'Quot.sound'];

/** Properties read and literals named by formulas. @param {Formula[]} asts */
function touched(asts) {
  const props = new Set(), lits = new Set(), kinds = new Set();
  let any = false, kindOf = false;
  /** @param {Term} t */
  const term = (t) => {
    if (t.t === 'prop') { props.add(t.p); term(t.of); } else if (t.t === 'kindOf') { kindOf = true; term(t.of); }
    else if (t.t === 'lit') for (const v of t.vs) lits.add(v);
  };
  /** @param {Formula} f */
  const walk = (f) => {
    switch (f.t) {
      case 'eq': case 'mem': term(f.a); term(f.b); return;
      case 'nonempty': term(f.a); return;
      case 'not': walk(f.f); return;
      case 'and': case 'or': case 'imp': walk(f.f); walk(f.g); return;
      case 'atom': for (const a of f.args) term(a); return;
      case 'all': case 'ex':
        if (f.d.t === 'any') any = true;
        else if (f.d.t === 'kinds') for (const k of f.d.ks) kinds.add(k);
        else term(f.d.of);
        walk(f.f); walk(f.b);
    }
  };
  for (const ast of asts) walk(ast);
  return { props: [...props].sort(), lits, kinds, any, kindOf };
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
  const analysis = analyzeRelations(model);
  const problems = checkRule(parsed.ast, model.meta, { arity: analysis.arity });
  if (problems.length) throw new Error(`Integrity rule "${ruleId}": ${problems.map((p) => p.message).join(' ')}`);
  const ast = parsed.ast;
  const used = relationsOfRule(model, ast);
  if (used.problem) throw new Error(`Integrity rule "${ruleId}": ${used.problem.message}`);
  // The program: the strata that hold a used relation, lowest first.
  const strata = analysis.strata.map((comp) => comp.filter((id) => used.used.has(id))).filter((comp) => comp.length);
  const rels = strata.flat().map((id) => /** @type {import('./integrity.js').RelationInfo} */ (analysis.rels.get(id)));
  const t = touched([ast, ...rels.flatMap((r) => r.clauses)]);
  for (const r of rels) for (const p of r.params) { if (p.kinds === '*') t.any = true; else for (const k of p.kinds) t.kinds.add(k); }

  // Entities: the quantified kinds (or all), plus every entity reachable through a read property,
  // and, when a formula takes `kindof`, the entity (if any) whose id is an exported entity's kind:
  // a kind is a value like any other, and a term may read its properties.
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
    if (t.kindOf && typeof e.kind === 'string') add(e.kind);
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
      case 'atom': return { t: 'atom', r: num('r:' + f.r), ts: f.args.map((a) => term(a, scope)) };
      case 'all': case 'ex': {
        const d = f.d.t === 'any' ? { t: 'any' } : f.d.t === 'kinds' ? { t: 'kinds', ks: f.d.ks.map((k) => num(valueKey(k))) } : { t: 'term', of: term(f.d.of, scope) };
        const inner = [f.v, ...scope];
        return { t: f.t, d, f: formula(f.f, inner), b: formula(f.b, inner) };
      }
    }
  };
  const lean = formula(ast, []);
  // A clause's variables 0 .. n-1 are its relation's parameters, in order: the tuple is the env.
  const program = strata.map((comp) => comp.map((id) => {
    const r = /** @type {import('./integrity.js').RelationInfo} */ (analysis.rels.get(id));
    const scope = r.params.map((p) => p.name);
    return {
      id: num('r:' + id),
      doms: r.params.map((p) => (p.kinds === '*' ? { t: 'any' } : { t: 'kinds', ks: p.kinds.map((k) => num(valueKey(k))) })),
      clauses: r.clauses.map((c) => formula(c, scope)),
    };
  }));
  // The tables, as `solve` lists them: higher strata first, each stratum in its order, each
  // relation's tuples in lexicographic order of the interned values (the order of its candidates).
  const tables = used.used.size ? relationTables(model, used.used) : new Map();
  const table = [...strata].reverse().flatMap((comp) => comp.map((id) => {
    const keys = /** @type {Set<string>} */ (tables.get(id));
    const tuples = [...keys].map((k) => tupleOf(k).map((v) => {
      const n = intern.get(v);
      if (n === undefined) throw new Error(`The tuple value ${v} of relation "${id}" is not among the exported facts.`);
      return n;
    }));
    tuples.sort(lexCompare);
    return { id: num('r:' + id), relation: id, tuples };
  }));
  // The candidate tuples over the exported facts: what the kernel's fixpoint iteration ranges over.
  const domainSize = (/** @type {any} */ d) => (d.t === 'any' ? entities.length : entities.filter((e) => d.ks.includes(e.kind)).length);
  const candidates = program.flat().reduce((acc, r) => acc + r.doms.reduce((m, d) => m * domainSize(d), 1), 0);
  return { ruleId, statement: String(rule.data.statement ?? ''), text: String(rule.data.rule), ast, formula: lean, entities, intern, props: t.props, quantifiesOverAll: t.any, relations: strata.flat(), program, table, candidates };
}

/** Lexicographic order of number tuples. @param {number[]} a @param {number[]} b */
function lexCompare(a, b) {
  for (let i = 0; i < Math.min(a.length, b.length); i++) if (a[i] !== b[i]) return a[i] - b[i];
  return a.length - b.length;
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
  return JSON.stringify({ entities: ex.entities, program: ex.program, rules: [{ id: ex.ruleId, formula: ex.formula }] });
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
    case 'all': case 'ex': return `(.${f.t} ${leanDom(f.d)} ${leanFormula(f.f)} ${leanFormula(f.b)})`;
    case 'atom': return `(.atom ${f.r} [${f.ts.map(leanTerm).join(', ')}])`;
  }
  throw new Error('unknown formula');
}

/** @param {any} d */
function leanDom(d) {
  return d.t === 'any' ? '.any' : d.t === 'kinds' ? `(.kinds [${d.ks.join(', ')}])` : `(.term ${leanTerm(d.of)})`;
}

/** The program as a Lean `Program`. @param {any[][]} program */
export function leanProgram(program) {
  return `[${program.map((s) => `[${s.map((r) => `⟨${r.id}, [${r.doms.map(leanDom).join(', ')}], [${r.clauses.map(leanFormula).join(', ')}]⟩`).join(', ')}]`).join(', ')}]`;
}

/** The solved table as a Lean `Table`. @param {{id: number, tuples: number[][]}[]} table */
export function leanTable(table) {
  return `[${table.map((e) => `(${e.id}, [${e.tuples.map((w) => `[${w.join(', ')}]`).join(', ')}])`).join(', ')}]`;
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

/** The theorems every proof file states before `holds` or `violated_<n>`. */
export const PROOF_PRELUDE_THEOREMS = ['facts_search_tree', 'prog_wf', 'prog_solved'];

/** A Lean namespace component for a rule id. @param {string} ruleId */
export function proofNamespace(ruleId) {
  return 'Exegra.IntegrityProof.R_' + ruleId.replace(/[^A-Za-z0-9]/g, '_');
}

/** @param {string} ruleId */
export function proofFileName(ruleId) {
  return `generated/integrity/${ruleId}.lean`;
}

/**
 * The Lean proof file of one rule: the facts, the program of the relations it uses (empty without
 * any), their table, the rule, `facts_search_tree`, `prog_wf` (the program is stratified),
 * `prog_solved` (the checker's fixpoint is the table), and either `holds` (proof by reflection) or
 * one `violated_<n>` per witness (refutation from the witness alone). `holds` and `violated_<n>` are
 * statements about `Sat facts (Least facts prog) [] rule`: the least-model meaning, not the checker.
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
    `-- Relations: ${ex.relations.join(', ') || '(none)'}.`,
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
    `def prog : Program := ${leanProgram(ex.program)}`,
    '',
    `def table : Table := ${leanTable(ex.table)}`,
    '',
    `def rule : Formula := ${leanFormula(ex.formula)}`,
    '',
    '-- Ids are unique and ordered, so following a reference finds exactly that entity (Facts.find_complete).',
    'theorem facts_search_tree : facts.bst none none = true := by decide +kernel',
    '',
    '-- The program is stratified: within a stratum its own atoms occur positively (wf, posF).',
    'theorem prog_wf : wf prog = true := by decide +kernel',
    '',
    '-- The checker reaches its fixpoint, and it is this table; by least_eq_table it is the least model.',
    'theorem prog_solved : solve facts prog [] = some table := by decide +kernel',
    '',
  ];
  if (claim.holds) lines.push('theorem holds : Sat facts (Least facts prog) [] rule := holds_of_eval prog_wf prog_solved (by decide +kernel)');
  else claim.witnesses.forEach((w, i) => lines.push(`theorem violated_${i} : ¬ Sat facts (Least facts prog) [] rule := violated_of_refutes [${w.join(', ')}] prog_wf prog_solved (by decide +kernel)`));
  lines.push('');
  for (const t of PROOF_PRELUDE_THEOREMS.concat(theorems)) lines.push(`#print axioms ${t}`);
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
