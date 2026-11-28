// Derived relations of integrity rules (integrityRelation, src/core/integrity.js): atoms in the rule
// language, the least-model tables of recursive and mutually recursive relations, stratified
// negation, the stratification check and the other relation diagnostics, and the ratchet on rules
// that use relations. Fixture: tests/fixtures/integrity/relations.jsonc, where every rule holds, and
// relations-mutations.json, which gives every rule an edit after which it must fail.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { Project } from '../../src/core/project.js';
import { analyzeSpec } from '../../src/core/analyze.js';
import { OPERATIONS, Tx } from '../../src/core/operations.js';
import { parseRule, evaluateIntegrity, relationTables, analyzeRelations, atomPolarities, tupleOf, tupleKey } from '../../src/core/integrity.js';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const DIR = path.join(HERE, '..', 'fixtures', 'integrity');
const SPEC = fs.readFileSync(path.join(DIR, 'relations.jsonc'), 'utf8');
const MUTATIONS = JSON.parse(fs.readFileSync(path.join(DIR, 'relations-mutations.json'), 'utf8')).mutations;

/** The model after operations, without the transaction gate. @param {any[]} ops */
function mutated(ops) {
  const p = new Project({ specText: SPEC });
  const tx = new Tx(p.specText, p.layoutText, /** @type {any} */ (p.model));
  for (const op of ops) OPERATIONS[/** @type {keyof typeof OPERATIONS} */ (op.type)].apply(tx, op);
  const a = analyzeSpec(tx.specText);
  assert.ok(a.model, 'the mutated specification parses');
  return { model: /** @type {any} */ (a.model), analysis: a };
}

/** A relation's tuples as sorted "a b" strings. @param {any} model @param {string} id */
const tuples = (model, id) => [...(/** @type {Set<string>} */ (relationTables(model).get(id)))].map((k) => tupleOf(k).map((v) => v.slice(2)).join(' ')).sort();

/** @param {any} model @param {string} ruleId */
const resultOf = (model, ruleId) => /** @type {any} */ (evaluateIntegrity(model).find((r) => r.ruleId === ruleId));

/** Counterexamples as {var: id} objects. @param {any} r */
const bindings = (r) => r.counterexamples.map((/** @type {any} */ c) => Object.fromEntries(c.vars.map((/** @type {string} */ v, /** @type {number} */ i) => [v, c.values[i].slice(2)])));

// Atoms parse with term arguments; their polarity flips under !, the left side of => and a forall filter, not an exists filter.
// @evidence integrity-relations-evaluated
test('relation atoms parse with term arguments and their polarity follows negation and implication and filters', () => {
  const p = parseRule('forall a : module where live(a), exists b in a.uses, !reaches(b, a) && reaches(a.uses, [\'m-store\'])');
  assert.ok(p.ok);
  if (!p.ok) return;
  assert.deepEqual(atomPolarities(p.ast), [
    { r: 'live', positive: false },
    { r: 'reaches', positive: false },
    { r: 'reaches', positive: true },
  ]);
  const q = parseRule('(r(x) => s(x)) || exists y : module where t(y), u()');
  assert.ok(q.ok);
  if (q.ok) assert.deepEqual(atomPolarities(q.ast).map((a) => `${a.r}${a.positive ? '+' : '-'}`), ['r-', 's+', 't+', 'u+']);
  const bad = parseRule('reaches(a, b');
  assert.equal(bad.ok, false);
  if (!bad.ok) assert.match(bad.error.message, /Expected "\)" after the arguments of a relation/);
});

// The fixture tables equal the least models written out by hand; strata are ordered; a cycle and a deprecation give exactly the expected tuples.
// @evidence integrity-relations-evaluated
test('the relations of the fixture are their least models: reachability and mutual recursion and stratified negation', () => {
  const project = new Project({ specText: SPEC });
  assert.equal(project.errorCount, 0);
  assert.deepEqual(project.diagnostics.filter((d) => d.code.startsWith('integrity.')), []);
  const model = /** @type {any} */ (project.model);
  // Strata: every relation a stratum uses is in it or lower; odd-path and even-path are one stratum.
  const strata = analyzeRelations(model).strata;
  const at = (/** @type {string} */ id) => strata.findIndex((s) => s.includes(id));
  assert.deepEqual(strata.find((s) => s.includes('odd-path')), ['odd-path', 'even-path']);
  assert.ok(at('reaches') < at('stale-dep') && at('live') < at('stale-dep'));
  assert.deepEqual(tuples(model, 'reaches'), [
    'm-model m-store', 'm-rules m-model', 'm-rules m-store', 'm-shell m-model', 'm-shell m-rules',
    'm-shell m-store', 'm-shell m-view', 'm-view m-model', 'm-view m-rules', 'm-view m-store',
  ]);
  assert.deepEqual(tuples(model, 'odd-path'), [
    'm-model m-store', 'm-rules m-model', 'm-rules m-store', 'm-shell m-model', 'm-shell m-store',
    'm-shell m-view', 'm-view m-rules', 'm-view m-store',
  ]);
  assert.deepEqual(tuples(model, 'even-path'), ['m-rules m-store', 'm-shell m-rules', 'm-shell m-store', 'm-view m-model', 'm-view m-store']);
  assert.deepEqual(tuples(model, 'live'), ['m-model', 'm-rules', 'm-shell', 'm-store', 'm-view']);
  assert.deepEqual(tuples(model, 'stale-dep'), []);
  const results = Object.fromEntries(evaluateIntegrity(model).map((r) => [r.ruleId, [r.status, r.instances]]));
  assert.deepEqual(results, {
    'uses-acyclic': ['holds', 6],
    'core-below-ui': ['holds', 9],
    'live-modules-stay-live': ['holds', 5],
    'no-odd-cycles': ['holds', 6],
    'live-kinds-described': ['holds', 5],
  });
  // A cycle gives every module on it a path to itself; the least model adds nothing else.
  const { model: cyc } = mutated([{ type: 'SetProperty', id: 'm-store', property: 'uses', value: ['m-rules'] }]);
  assert.ok(tuples(cyc, 'reaches').includes('m-store m-store'));
  assert.ok(!tuples(cyc, 'reaches').some((x) => x.startsWith('m-store m-view') || x.startsWith('m-legacy')), 'nothing reaches upward or from m-legacy');
  // Stratified negation: deprecating a module that others reach makes them stale.
  const { model: dep } = mutated([{ type: 'SetProperty', id: 'm-store', property: 'deprecated', value: true }]);
  assert.deepEqual(tuples(dep, 'stale-dep'), ['m-model', 'm-rules', 'm-shell', 'm-view']);
});

// Each relation rule fails after its mutation with the stated counterexample, and Project.apply refuses the mutation.
// @evidence integrity-relations-evaluated
test('every relation rule can be made to fail: each mutation gives its stated counterexample and apply refuses it', () => {
  const model = /** @type {any} */ (new Project({ specText: SPEC }).model);
  for (const r of model.byKind.integrityRule) assert.ok(MUTATIONS.some((/** @type {any} */ m) => m.rule === r.id), `rule "${r.id}" has a mutation`);
  for (const m of MUTATIONS) {
    const { model: after } = mutated(m.ops);
    const r = resultOf(after, m.rule);
    assert.equal(r.status, 'violated', `${m.rule}: ${m.note}`);
    assert.ok(bindings(r).some((/** @type {any} */ b) => JSON.stringify(b) === JSON.stringify(m.expect)), `${m.rule}: expected ${JSON.stringify(m.expect)}, got ${JSON.stringify(bindings(r))}`);
    const project = new Project({ specText: SPEC });
    const tx = project.apply(m.ops);
    assert.equal(tx.ok, false, `${m.rule}: the transaction must be refused`);
    assert.equal(tx.code, 'integrity.violated');
    assert.ok(tx.diagnostics.some((d) => d.message.includes(`"${m.rule}"`)), `${m.rule}: the refusal names the rule`);
  }
});

// Each integrity.relation-* problem is an error on the relation and on the rule using it; invalidity propagates to relations that use it; negation of a lower stratum is accepted.
// @evidence integrity-relations-evaluated
test('invalid relations: each problem is a named diagnostic that makes the relation and every rule using it invalid', () => {
  /** @param {any} data @param {string} [rule] */
  const withRelation = (data, rule) => {
    const ops = [{ type: 'CreateEntity', kind: 'integrityRelation', data: { statement: 'x', ...data } }];
    if (rule) ops.push({ type: 'CreateEntity', kind: 'integrityRule', data: { id: 'uses-bad', severity: 'error', statement: 'x', rule } });
    return mutated(ops).analysis;
  };
  const two = [{ name: 'a', kinds: ['module'] }, { name: 'b', kinds: ['module'] }];
  const cases = [
    ['integrity.relation-unstratified', { id: 'bad', params: two, clauses: ['b in a.uses && !bad(b, a)'] }, /Recursion through negation: "bad" occurs negatively in clause 1 of "bad"/],
    ['integrity.relation-unstratified', { id: 'bad', params: two, clauses: ['forall m in a.uses where reaches(m, b) && bad(m, b), true'] }, /occurs negatively/],
    ['integrity.relation-arity', { id: 'bad', params: two, clauses: ['reaches(a)'] }, /Relation "reaches" has 2 parameter\(s\) but is given 1/],
    ['integrity.relation-unknown', { id: 'bad', params: two, clauses: ['reachez(a, b)'] }, /"reachez" is not an integrity relation/],
    ['integrity.relation-unbound', { id: 'bad', params: two, clauses: ['c in a.uses'] }, /"c" is free in a clause but is not a parameter/],
    ['integrity.relation-kind', { id: 'bad', params: [{ name: 'a', kinds: ['modul'] }], clauses: ['true'] }, /"modul" is not an entity kind/],
    ['integrity.relation-syntax', { id: 'bad', params: two, clauses: ['b in'] }, /Clause 1: Expected a literal/],
    ['integrity.relation-params', { id: 'bad', params: [{ name: 'a', kinds: ['module'] }, { name: 'a', kinds: '*' }], clauses: ['true'] }, /declared twice/],
  ];
  for (const [code, data, re] of cases) {
    const a = withRelation(data, 'forall m : module, !bad(m' + (data.params.length === 2 ? ', m)' : ')'));
    const d = a.diagnostics.find((x) => x.code === code && x.entityId === 'bad');
    assert.ok(d, `${code}: ${JSON.stringify(a.diagnostics.map((x) => [x.code, x.message]))}`);
    assert.equal(d.severity, 'error');
    assert.match(d.message, /** @type {RegExp} */ (re));
    const r = a.diagnostics.find((x) => x.entityId === 'uses-bad');
    assert.ok(r, `${code}: the rule that uses the relation is reported`);
    assert.equal(r.code, code, 'the rule carries the relation problem code');
    assert.equal(r.severity, 'error');
    assert.match(r.message, /Relation "bad" is invalid/);
    assert.ok(a.errorCount > 0);
  }
  // A relation that uses an invalid one is invalid too, and so is a cycle that contains one.
  const chain = mutated([
    { type: 'CreateEntity', kind: 'integrityRelation', data: { id: 'bad', statement: 'x', params: [{ name: 'a', kinds: ['module'] }], clauses: ['!bad(a)'] } },
    { type: 'CreateEntity', kind: 'integrityRelation', data: { id: 'above', statement: 'x', params: [{ name: 'a', kinds: ['module'] }], clauses: ['bad(a)'] } },
  ]).analysis;
  const above = chain.diagnostics.find((x) => x.entityId === 'above');
  assert.equal(above?.code, 'integrity.relation-unstratified');
  assert.match(String(above?.message), /It uses relation "bad", which is invalid/);
  // Negation of a lower stratum is allowed, in a clause and in a rule.
  const ok = withRelation({ id: 'isolated', params: [{ name: 'a', kinds: ['module'] }], clauses: ['!(exists b : module, reaches(a, b) || reaches(b, a))'] }, 'forall m : module where m.deprecated == true, isolated(m)');
  assert.deepEqual(ok.diagnostics.filter((x) => x.severity === 'error'), []);
  // A rule with an unknown relation or a wrong arity carries the relation code.
  const unknown = mutated([{ type: 'CreateEntity', kind: 'integrityRule', data: { id: 'r', severity: 'error', statement: 'x', rule: 'forall m : module, nope(m)' } }]).analysis;
  assert.equal(unknown.diagnostics.find((x) => x.entityId === 'r')?.code, 'integrity.relation-unknown');
  const arity = mutated([{ type: 'CreateEntity', kind: 'integrityRule', data: { id: 'r', severity: 'error', statement: 'x', rule: 'forall m : module, !reaches(m)' } }]).analysis;
  assert.equal(arity.diagnostics.find((x) => x.entityId === 'r')?.code, 'integrity.relation-arity');
  // The transaction system refuses an invalid relation.
  const project = new Project({ specText: SPEC });
  const tx = project.apply({ type: 'CreateEntity', kind: 'integrityRelation', data: { id: 'bad', statement: 'x', params: two, clauses: ['!bad(a, b)'] } });
  assert.equal(tx.ok, false);
  assert.equal(tx.code, 'validation.failed');
});

// Set-valued arguments hold when some choice is a tuple; a parameter over * covers every entity.
// @evidence integrity-relations-evaluated
test('an atom holds when some choice of one value per argument is a tuple and a parameter over every kind ranges over every entity', () => {
  const { model } = mutated([
    { type: 'CreateEntity', kind: 'integrityRelation', data: { id: 'any-entity', statement: 'x', params: [{ name: 'e', kinds: '*' }], clauses: ['true'] } },
    { type: 'CreateEntity', kind: 'integrityRule', data: { id: 'shell-reaches-store', severity: 'error', statement: 'x', rule: 'forall m in ["m-shell"], reaches(m, ["m-legacy", "m-store"]) && !reaches(m, ["m-legacy"]) && !reaches(m, ["nothing"])' } },
    { type: 'CreateEntity', kind: 'integrityRule', data: { id: 'all-entities', severity: 'error', statement: 'x', rule: 'forall e : *, any-entity(e)' } },
  ]);
  assert.equal(resultOf(model, 'shell-reaches-store').status, 'holds');
  const all = resultOf(model, 'all-entities');
  assert.equal(all.status, 'holds');
  assert.equal(all.instances, model.entities.size);
  assert.equal(relationTables(model).get('any-entity')?.size, model.entities.size, 'every entity, rules and relations included');
});

test('only the relations the rules use are evaluated and tuple keys are unambiguous', () => {
  const { model } = mutated([{ type: 'CreateEntity', kind: 'integrityRelation', data: { id: 'unused', statement: 'x', params: [{ name: 'a', kinds: ['module'] }], clauses: ['true'] } }]);
  assert.deepEqual(evaluateIntegrity(model).map((r) => r.status), ['holds', 'holds', 'holds', 'holds', 'holds']);
  const computed = [...relationTables(model, []).keys()].sort();
  assert.deepEqual(computed, ['even-path', 'live', 'odd-path', 'reaches', 'stale-dep'], 'no rule uses "unused", so it is not computed');
  assert.equal(relationTables(model, ['unused']).get('unused')?.size, 6, 'it is computed when asked for');
  assert.notEqual(tupleKey(['s:a\u0000s:b', 's:c']), tupleKey(['s:a', 's:b\u0000s:c']));
  assert.deepEqual(tupleOf(tupleKey(['s:a\u0000b', 'n:1'])), ['s:a\u0000b', 'n:1']);
});
