// Derived relations against Nemo (https://github.com/knowsys/nemo), an independent Datalog engine:
// the relations of tests/fixtures/integrity/relations.jsonc and of seeded random programs over
// random module graphs (random uses and feeds edges, recursive reachability in several forms,
// mutual recursion, and stratified negation) are translated to Nemo's rule language, and the
// relation contents nmo derives must equal the tables of the JavaScript evaluator
// (relationTables). Both compute the least model of a stratified program, so they must agree.
//
// The translation covers the fragment Nemo expresses directly: a clause becomes one rule per
// disjunct of its disjunctive normal form, with atoms and `~` negated atoms of relations, `x in
// y.p` (a fact of the property), `x.p == literal` on a single-valued property, `exists v in x.p`
// and `exists v : kind` (fresh variables bound by facts), and each parameter bound by the facts of
// its kinds. A relation outside the fragment, or one that uses such a relation, is not translated:
// the test compares every translated relation, prints which were skipped, and requires that the
// fixture's relations and most random relations were compared.
//
// nmo is EXEGRA_NEMO, else %LOCALAPPDATA%\exegra\tools\nemo-0.10.1\nmo.exe. Without it the test
// is skipped with the reason: a skip is not a pass.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { Project } from '../../src/core/project.js';
import { analyzeRelations, relationTables, domainOf, propertyKeys } from '../../src/core/integrity.js';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const FIXTURE = fs.readFileSync(path.join(HERE, '..', 'fixtures', 'integrity', 'relations.jsonc'), 'utf8');

const NMO = process.env.EXEGRA_NEMO || path.join(process.env.LOCALAPPDATA ?? path.join(os.homedir(), 'AppData', 'Local'), 'exegra', 'tools', 'nemo-0.10.1', 'nmo.exe');
const NO_NEMO = `nmo was not found at ${NMO} (set EXEGRA_NEMO to the Nemo command-line binary); derived relations were not compared with Nemo`;

class Unsupported extends Error {}

/**
 * Nemo rules for the relations of a model, in the fragment described above.
 * @param {any} model
 * @returns {{program: string, files: Map<string, string>, translated: string[], skipped: Map<string, string>, predicate: Map<string, string>}}
 */
function translate(model) {
  const { rels, strata } = analyzeRelations(model);
  /** @type {Map<string, string>} relation id to predicate */
  const predicate = new Map();
  /** @type {Map<string, string>} file name to CSV text */
  const files = new Map();
  /** @type {Map<string, string>} */
  const imports = new Map();
  const q = (/** @type {string} */ s) => JSON.stringify(s);
  /** The predicate of the entities of a kind ('*': every entity). @param {string} kind */
  const kindPred = (kind) => {
    const name = kind === '*' ? 'entity' : `kind_${kind.replace(/[^A-Za-z0-9]/g, '_')}`;
    if (!imports.has(name)) {
      const ids = domainOf(model, kind === '*' ? '*' : [kind]);
      files.set(`${name}.csv`, ids.map((v) => `${q(v)}\n`).join(''));
      imports.set(name, `@import ${name} :- csv{resource = "${name}.csv", format = (string)}.`);
    }
    return name;
  };
  /** The predicate of a property's (entity, value) facts. @param {string} p */
  const propPred = (p) => {
    const name = `prop_${p.replace(/[^A-Za-z0-9]/g, '_')}`;
    if (!imports.has(name)) {
      let text = '';
      for (const e of model.entities.values()) for (const v of propertyKeys(e.data[p])) text += `${q('s:' + e.id)},${q(v)}\n`;
      files.set(`${name}.csv`, text);
      imports.set(name, `@import ${name} :- csv{resource = "${name}.csv", format = (string, string)}.`);
    }
    return name;
  };
  /** Is a property single-valued for every kind that declares it? @param {string} p */
  const single = (p) => Object.values(model.meta.entities).every((def) => {
    const t = /** @type {any} */ (def).properties[p];
    return !t || t.type !== 'list';
  });
  let fresh = 0;
  /**
   * A term as a Nemo term: a variable or a one-value literal.
   * @param {any} t @param {Map<string, string>} env
   */
  const simple = (t, env) => {
    if (t.t === 'var' && env.has(t.name)) return /** @type {string} */ (env.get(t.name));
    if (t.t === 'lit' && t.vs.length === 1) return q(t.vs[0]);
    throw new Unsupported(`term ${JSON.stringify(t)}`);
  };
  /**
   * A positive literal: `x in y.p`, `y.p == lit` (single-valued p), or an atom.
   * @param {any} f @param {Map<string, string>} env @returns {string}
   */
  const literal = (f, env) => {
    if (f.t === 'atom') {
      const pr = predicate.get(f.r);
      if (!pr) throw new Unsupported(`relation ${f.r} is not translated`);
      return `${pr}(${f.args.map((/** @type {any} */ a) => simple(a, env)).join(', ')})`;
    }
    if (f.t === 'mem' && f.b.t === 'prop' && f.b.of.t === 'var') return `${propPred(f.b.p)}(${simple(f.b.of, env)}, ${simple(f.a, env)})`;
    if (f.t === 'eq' && f.a.t === 'prop' && f.a.of.t === 'var' && f.b.t === 'lit' && f.b.vs.length === 1 && single(f.a.p)) return `${propPred(f.a.p)}(${simple(f.a.of, env)}, ${q(f.b.vs[0])})`;
    throw new Unsupported(`literal ${f.t}`);
  };
  /**
   * Disjunctive normal form: a list of conjunctions of body literals.
   * @param {any} f @param {Map<string, string>} env @returns {string[][]}
   */
  const dnf = (f, env) => {
    switch (f.t) {
      case 'tt': return [[]];
      case 'ff': return [];
      case 'and': { const a = dnf(f.f, env), b = dnf(f.g, env); return a.flatMap((x) => b.map((y) => [...x, ...y])); }
      case 'or': return [...dnf(f.f, env), ...dnf(f.g, env)];
      case 'not': return [[`~${literal(f.f, env)}`]];
      case 'ex': {
        const v = `?V${fresh++}`;
        const inner = new Map(env).set(f.v, v);
        /** @type {string[][]} */
        let bind;
        if (f.d.t === 'term' && f.d.of.t === 'prop' && f.d.of.of.t === 'var') bind = [[`${propPred(f.d.of.p)}(${simple(f.d.of.of, env)}, ${v})`]];
        else if (f.d.t === 'kinds') bind = f.d.ks.map((/** @type {string} */ k) => [`${kindPred(k)}(${v})`]);
        else if (f.d.t === 'any') bind = [[`${kindPred('*')}(${v})`]];
        else throw new Unsupported('exists domain');
        const body = dnf({ t: 'and', f: f.f, g: f.b }, inner);
        return bind.flatMap((x) => body.map((y) => [...x, ...y]));
      }
      default: return [[literal(f, env)]];
    }
  };
  /** @type {string[]} */
  const rules = [];
  const translated = [];
  /** @type {Map<string, string>} */
  const skipped = new Map();
  let n = 0;
  for (const comp of strata) {
    const members = comp.map((id) => /** @type {any} */ (rels.get(id)));
    if (members.some((r) => r.problem)) { for (const r of members) skipped.set(r.id, 'invalid'); continue; }
    for (const r of members) predicate.set(r.id, `rel${n++}`);
    /** @type {string[]} */
    const out = [];
    try {
      for (const r of members) {
        if (r.params.length === 0) throw new Unsupported('a relation without parameters');
        const env = new Map(r.params.map((/** @type {any} */ p, /** @type {number} */ i) => [p.name, `?P${i}`]));
        // Each parameter is bound by the facts of one of its kinds.
        /** @type {string[][]} */
        let heads = [[]];
        r.params.forEach((/** @type {any} */ p, /** @type {number} */ i) => {
          const ks = p.kinds === '*' ? ['*'] : p.kinds;
          heads = heads.flatMap((h) => ks.map((/** @type {string} */ k) => [...h, `${kindPred(k)}(?P${i})`]));
        });
        const head = `${predicate.get(r.id)}(${r.params.map((/** @type {any} */ _, /** @type {number} */ i) => `?P${i}`).join(', ')})`;
        for (const c of r.clauses) for (const conj of dnf(c, env)) for (const h of heads) out.push(`${head} :- ${[...h, ...conj].join(', ')}.`);
      }
      rules.push(...out);
      for (const r of members) translated.push(r.id);
    } catch (e) {
      if (!(e instanceof Unsupported)) throw e;
      for (const r of members) { predicate.delete(r.id); skipped.set(r.id, e.message); }
    }
  }
  const exports = translated.map((id) => `@export ${predicate.get(id)} :- csv{resource = "${predicate.get(id)}.csv"}.`);
  return { program: [...imports.values(), ...rules, ...exports].join('\n') + '\n', files, translated, skipped, predicate };
}

/** Strip the quotes nmo wraps exported strings in ("""x""" for x). @param {string} s */
const unquote = (s) => s.trim().replace(/^"+/, '').replace(/"+$/, '');

/**
 * Run nmo on the translation and compare every translated relation with the JavaScript table.
 * @param {any} model @param {string} what
 */
function compareWithNemo(model, what) {
  const tr = translate(model);
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-nemo-'));
  try {
    for (const [name, text] of tr.files) fs.writeFileSync(path.join(dir, name), text);
    fs.writeFileSync(path.join(dir, 'prog.rls'), tr.program);
    const run = spawnSync(NMO, ['-o', '-D', 'out', 'prog.rls'], { cwd: dir, encoding: 'utf8', windowsHide: true });
    assert.equal(run.status, 0, `${what}: nmo failed:\n${run.stderr}${run.stdout}\n${tr.program}`);
    const tables = relationTables(model);
    for (const id of tr.translated) {
      const file = path.join(dir, 'out', `${tr.predicate.get(id)}.csv`);
      const text = fs.existsSync(file) ? fs.readFileSync(file, 'utf8') : '';
      const nemo = text.split(/\r?\n/).filter((l) => l.trim()).map((l) => JSON.stringify(l.split(',').map(unquote))).sort();
      const js = [...(/** @type {Set<string>} */ (tables.get(id)))].sort();
      assert.deepEqual(nemo, js, `${what}: relation "${id}"\n${tr.program}`);
    }
    return tr;
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
}

/** A small deterministic generator (mulberry32). @param {number} seed */
function rng(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let x = a;
    x = Math.imul(x ^ (x >>> 15), x | 1);
    x ^= x + Math.imul(x ^ (x >>> 7), x | 61);
    return ((x ^ (x >>> 14)) >>> 0) / 4294967296;
  };
}

// Every relation of the fixture translated to Nemo rules; nmo derives the JavaScript tables.
// @evidence integrity-relations-agree-with-lean-and-nemo
test('Nemo derives the same relations as the JavaScript evaluator on the relations fixture', (t) => {
  if (!fs.existsSync(NMO)) { t.skip(NO_NEMO); return; }
  const project = new Project({ specText: FIXTURE });
  assert.equal(project.errorCount, 0);
  const tr = compareWithNemo(project.model, 'relations.jsonc');
  assert.deepEqual([...tr.skipped.keys()], [], `every fixture relation is in the fragment: ${JSON.stringify([...tr.skipped])}`);
  assert.deepEqual([...tr.translated].sort(), ['even-path', 'live', 'odd-path', 'reaches', 'stale-dep']);
});

/** Clause templates over parameters a, b (two parameters) or a (one), by relation shape. */
const BINARY = [
  // Closure of an edge property, right- and left-recursive, and through a lower relation.
  (/** @type {string} */ self, /** @type {string} */ e) => [`b in a.${e}`, `exists m in a.${e}, ${self}(m, b)`],
  (/** @type {string} */ self, /** @type {string} */ e) => [`b in a.${e}`, `exists m : node, ${self}(a, m) && b in m.${e}`],
  (/** @type {string} */ self, /** @type {string} */ e) => [`b in a.${e} || exists m : node, ${self}(a, m) && ${self}(m, b)`],
];

/**
 * A random stratified program over node graphs: closures of random edge properties, a mutually
 * recursive pair, binary relations combining lower ones with negation, and unary filters.
 * @param {() => number} rand
 */
function randomProgram(rand) {
  /** @template T @param {T[]} xs @returns {T} */
  const pick = (xs) => xs[Math.floor(rand() * xs.length)];
  const edges = ['next', 'link'];
  const two = [{ name: 'a', kinds: ['node'] }, { name: 'b', kinds: ['node'] }];
  const one = [{ name: 'a', kinds: ['node'] }];
  /** @type {any[]} */
  const rels = [];
  /** @type {string[]} */
  const binary = [];
  /** @type {string[]} */
  const unary = [];
  const nClosures = 1 + Math.floor(rand() * 3);
  for (let i = 0; i < nClosures; i++) {
    const id = `close-${i}`;
    rels.push({ id, statement: 'x', params: two, clauses: pick(BINARY)(id, pick(edges)) });
    binary.push(id);
  }
  if (rand() < 0.6) {
    const e = pick(edges);
    rels.push({ id: 'odd', statement: 'x', params: two, clauses: [`b in a.${e}`, `exists m in a.${e}, even(m, b)`] });
    rels.push({ id: 'even', statement: 'x', params: two, clauses: [`exists m in a.${e}, odd(m, b)`] });
    binary.push('odd', 'even');
  }
  rels.push({ id: 'marked', statement: 'x', params: one, clauses: [rand() < 0.5 ? 'a.flag == true' : 'a.flag == true || exists m in a.link, m.flag == true'] });
  unary.push('marked');
  const nDerived = 1 + Math.floor(rand() * 4);
  for (let i = 0; i < nDerived; i++) {
    const id = `derived-${i}`;
    const r1 = pick(binary), r2 = pick(binary), u = pick(unary);
    const shape = Math.floor(rand() * 5);
    if (shape === 0) rels.push({ id, statement: 'x', params: two, clauses: [`${r1}(a, b) && !${r2}(b, a)`] });
    else if (shape === 1) rels.push({ id, statement: 'x', params: two, clauses: [`${r1}(a, b) && !${u}(b)`, `${r2}(b, a) && ${u}(a)`] });
    else if (shape === 2) { rels.push({ id, statement: 'x', params: one, clauses: [`exists b : node, ${r1}(a, b) && !${u}(b)`] }); unary.push(id); continue; }
    else if (shape === 3) { rels.push({ id, statement: 'x', params: one, clauses: [`!${r1}(a, a) && !${u}(a)`] }); unary.push(id); continue; }
    // Recursion through a lower relation, with negation of a lower one inside the recursion.
    else rels.push({ id, statement: 'x', params: two, clauses: [`${r1}(a, b) && !${u}(b)`, `exists m : node, ${id}(a, m) && ${id}(m, b)`] });
    binary.push(id);
  }
  return rels;
}

/** @param {() => number} rand */
function randomSpec(rand) {
  const n = 2 + Math.floor(rand() * 6);
  const ids = Array.from({ length: n }, (_, i) => `n-${i}`);
  const nodes = ids.map((id) => {
    /** @type {Record<string, any>} */
    const e = { id };
    const next = ids.filter(() => rand() < 0.3);
    const link = ids.filter(() => rand() < 0.2);
    if (next.length) e.next = next;
    if (link.length) e.link = link;
    if (rand() < 0.3) e.flag = true;
    return e;
  });
  return {
    exegra: '0.1',
    system: { id: 'nemo-random', name: 'Random relations', illustrative: true },
    vocabulary: { entityKinds: { node: { label: 'Node', section: 'nodes', properties: {
      next: { type: 'list', items: { type: 'ref', ref: 'node' } },
      link: { type: 'list', items: { type: 'ref', ref: 'node' } },
      flag: { type: 'boolean' },
    } } } },
    nodes,
    integrityRelations: randomProgram(rand),
  };
}

// On 40 seeded random graphs with random stratified programs (closures, mutual recursion, negation of lower strata) nmo derives the JavaScript tables.
// @evidence integrity-relations-agree-with-lean-and-nemo
test('Nemo derives the same relations as the JavaScript evaluator on seeded random graphs and stratified programs', (t) => {
  if (!fs.existsSync(NMO)) { t.skip(NO_NEMO); return; }
  const rand = rng(52630);
  let compared = 0, tuples = 0;
  /** @type {Map<string, string>} */
  const skipped = new Map();
  for (let i = 0; i < 40; i++) {
    const spec = randomSpec(rand);
    const project = new Project({ specText: JSON.stringify(spec, null, 2) });
    const what = `random case ${i}`;
    assert.equal(project.errorCount, 0, `${what}: ${project.diagnostics.filter((d) => d.severity === 'error').map((d) => d.message).join('; ')}`);
    const model = /** @type {any} */ (project.model);
    const tr = compareWithNemo(model, what);
    compared += tr.translated.length;
    for (const id of tr.translated) tuples += /** @type {Set<string>} */ (relationTables(model).get(id)).size;
    for (const [id, why] of tr.skipped) skipped.set(`${what}: ${id}`, why);
  }
  if (skipped.size) t.diagnostic(`not compared with Nemo (outside the translated fragment): ${[...skipped].map(([k, v]) => `${k} (${v})`).join('; ')}`);
  // Every case has at least one closure, marked and one derived relation.
  assert.ok(compared >= 40 * 3, `compared ${compared} relations`);
  assert.ok(skipped.size === 0, 'every generated relation is in the translated fragment');
  assert.ok(tuples > 0, 'the random programs derived some tuples');
});
