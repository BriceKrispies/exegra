// Integrity rules (src/core/integrity.js): the rule language, evaluation with counterexamples and
// vacuity, validation diagnostics, the ratchet of Project.apply, and the `integrity` command.
// Fixture: tests/fixtures/integrity/spec.jsonc, where every rule holds, and mutations.json, which
// gives every rule an edit after which it must fail with a stated counterexample.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { Project } from '../../src/core/project.js';
import { analyzeSpec } from '../../src/core/analyze.js';
import { OPERATIONS, Tx } from '../../src/core/operations.js';
import { parseRule, evaluateFormula, evaluateIntegrity } from '../../src/core/integrity.js';
import { runCommand } from '../../cli/commands.js';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const DIR = path.join(HERE, '..', 'fixtures', 'integrity');
const SPEC = fs.readFileSync(path.join(DIR, 'spec.jsonc'), 'utf8');
const MUTATIONS = JSON.parse(fs.readFileSync(path.join(DIR, 'mutations.json'), 'utf8')).mutations;

/** The model after operations, without the transaction gate (a mutated specification). @param {string} text @param {any[]} ops */
function mutated(text, ops) {
  const p = new Project({ specText: text });
  const tx = new Tx(p.specText, p.layoutText, /** @type {any} */ (p.model));
  for (const op of ops) OPERATIONS[/** @type {keyof typeof OPERATIONS} */ (op.type)].apply(tx, op);
  const a = analyzeSpec(tx.specText);
  assert.ok(a.model, 'the mutated specification parses');
  return { model: a.model, text: tx.specText, analysis: a };
}

/** @param {any} model @param {string} ruleId */
const resultOf = (model, ruleId) => /** @type {any} */ (evaluateIntegrity(model).find((r) => r.ruleId === ruleId));

/** Counterexamples as {var: id} objects. @param {any} r */
const bindings = (r) => r.counterexamples.map((/** @type {any} */ c) => Object.fromEntries(c.vars.map((/** @type {string} */ v, /** @type {number} */ i) => [v, c.values[i].slice(2)])));

test('the rule language parses quantifiers, paths, comparisons and connectives', () => {
  const ok = [
    'forall d : decision, forall x in d.closes, x.resolvedBy == d',
    'forall e : *, e.status != "superseded" => nonempty e.basis',
    'exists d : decision | gap where d.status == \'confirmed\', true',
    'forall e : * where kindof e not in ["designArea", "seam"], !(e.origin == "proposed") || nonempty e.basis',
    'forall c : component, c.illustrative == true || c.size == 3',
    'forall x in ["dec-1"], x.status in ["stated", "confirmed"]',
  ];
  for (const src of ok) assert.ok(parseRule(src).ok, src);
  const bad = [
    ['forall d decision, true', /Expected ":" and a kind/],
    ['forall d : decision true', /Expected ","/],
    ['x.a ==', /Expected a literal/],
    ['forall e : *, e.a == "b" extra', /Unexpected "extra"/],
    ['forall e : *, e.a ~ 1', /Unexpected character "~"/],
    ['"open', /Unterminated string/],
  ];
  for (const [src, re] of bad) {
    const p = parseRule(/** @type {string} */ (src));
    assert.equal(p.ok, false, /** @type {string} */ (src));
    if (!p.ok) { assert.match(p.error.message, /** @type {RegExp} */ (re)); assert.ok(p.error.pos >= 0); }
  }
  // Precedence: && binds tighter than ||, which binds tighter than =>, which is right-associative.
  const p = parseRule('true || false && false => false => true');
  assert.ok(p.ok);
  if (p.ok) assert.equal(p.ast.t, 'imp');
});

test('every rule of the fixture holds, with the instances it checked', () => {
  const project = new Project({ specText: SPEC });
  assert.equal(project.errorCount, 0);
  assert.deepEqual(project.diagnostics.filter((d) => d.code.startsWith('integrity.')), []);
  const results = Object.fromEntries(evaluateIntegrity(/** @type {any} */ (project.model)).map((r) => [r.ruleId, [r.status, r.instances]]));
  assert.deepEqual(results, {
    'no-basis-on-superseded': ['holds', 4],
    'closes-agrees-with-resolved-by': ['holds', 1],
    'resolved-by-is-closed-or-narrowed': ['holds', 2],
    'proposed-has-source': ['holds', 6],
    'resolution-revisited': ['holds', 1],
  });
});

test('every rule can be made to fail: each mutation gives its stated counterexample, and apply refuses it', () => {
  const model = /** @type {any} */ (new Project({ specText: SPEC }).model);
  const rules = model.byKind.integrityRule.map((/** @type {any} */ r) => r.id);
  for (const id of rules) assert.ok(MUTATIONS.some((/** @type {any} */ m) => m.rule === id), `rule "${id}" has a mutation that must make it fail; a rule nothing can falsify checks nothing`);
  for (const m of MUTATIONS) {
    const { model: after } = mutated(SPEC, m.ops);
    const r = resultOf(after, m.rule);
    assert.equal(r.status, 'violated', `${m.rule}: ${m.note}`);
    assert.ok(bindings(r).some((/** @type {any} */ b) => JSON.stringify(b) === JSON.stringify(m.expect)), `${m.rule}: expected counterexample ${JSON.stringify(m.expect)}, got ${JSON.stringify(bindings(r))}`);
    const project = new Project({ specText: SPEC });
    const tx = project.apply(m.ops);
    assert.equal(tx.ok, false, `${m.rule}: the transaction must be refused`);
    assert.equal(tx.code, 'integrity.violated');
    assert.ok(tx.diagnostics.some((d) => d.message.includes(`"${m.rule}"`)), `${m.rule}: the refusal names the rule`);
    assert.equal(project.revision, 1, 'nothing was committed');
  }
});

test('a decision resting on the gap it resolves is not stale; without the resolver exclusion it would be', () => {
  const model = /** @type {any} */ (new Project({ specText: SPEC }).model);
  // dec-1 has basis [g-1] and g-1.resolvedBy == dec-1.
  assert.deepEqual(model.entities.get('dec-1').data.basis, ['g-1']);
  assert.equal(resultOf(model, 'resolution-revisited').status, 'holds');
  const naive = parseRule('forall e : *, forall b in e.basis where nonempty b.resolvedBy, b.resolvedBy in e.basis');
  assert.ok(naive.ok);
  if (naive.ok) assert.deepEqual(bindings(evaluateFormula(model, naive.ast)), [{ e: 'dec-1', b: 'g-1' }]);
});

test('validation reports each violation with the rule severity at the first entity it names', () => {
  const { analysis } = mutated(SPEC, [
    { type: 'SetProperty', id: 's-2', property: 'encodes', value: null },
    { type: 'SetProperty', id: 'proposed-has-source', property: 'severity', value: 'warning' },
  ]);
  const v = analysis.diagnostics.filter((d) => d.code === 'integrity.violated');
  assert.equal(v.length, 1);
  assert.equal(v[0].severity, 'warning');
  assert.equal(v[0].entityId, 's-2');
  assert.ok(v[0].loc.line > 1);
  assert.match(v[0].message, /e = s-2 \(seam, line \d+\)/);
  const e = mutated(SPEC, [{ type: 'SetProperty', id: 's-2', property: 'encodes', value: null }]).analysis;
  const ve = e.diagnostics.filter((d) => d.code === 'integrity.violated');
  assert.equal(ve[0].severity, 'error');
  assert.equal(e.errorCount, 0, 'violations are ratcheted by apply, not counted as blocking errors');
});

test('invalid rules are blocking errors; a rule over nothing is vacuous', () => {
  /** @param {string} rule */
  const withRule = (rule) => mutated(SPEC, [{ type: 'CreateEntity', kind: 'integrityRule', data: { id: 'extra', severity: 'error', statement: 'x', rule } }]).analysis;
  for (const [rule, re] of [
    ['forall d : decison, true', /"decison" is not an entity kind/],
    ['forall d : decision, x.status == "a"', /"x" is not a bound variable/],
    ['forall d : decision, d.stauts == "a"', /No entity kind declares a property "stauts"/],
    ['forall d : decision,', /Expected a literal/],
  ]) {
    const a = withRule(/** @type {string} */ (rule));
    const d = a.diagnostics.find((x) => x.code === 'integrity.invalid');
    assert.ok(d, /** @type {string} */ (rule));
    assert.equal(d.severity, 'error');
    assert.match(d.message, /** @type {RegExp} */ (re));
    assert.ok(a.errorCount > 0);
  }
  const vac = withRule('forall e : decision where e.status == "withdrawn", false');
  const d = vac.diagnostics.find((x) => x.code === 'integrity.vacuous');
  assert.ok(d, 'a filter that selects nothing makes the rule vacuous');
  assert.equal(d.severity, 'warning');
  const project = new Project({ specText: SPEC });
  assert.equal(project.apply({ type: 'CreateEntity', kind: 'integrityRule', data: { id: 'extra', severity: 'error', statement: 'x', rule: 'forall d : decison, true' } }).code, 'validation.failed');
});

test('the ratchet: existing violations do not block unrelated edits, new ones do, fixes are accepted', () => {
  // Start from a specification that already violates "resolution-revisited" (s-1 drops dec-1).
  const start = mutated(SPEC, [{ type: 'SetProperty', id: 's-1', property: 'basis', value: ['g-1'] }]).text;
  const project = new Project({ specText: start });
  assert.equal(project.errorCount, 0, 'the existing violation does not count as a blocking error');
  assert.equal(project.diagnostics.filter((d) => d.code === 'integrity.violated').length, 1);
  const unrelated = project.apply({ type: 'SetProperty', id: 'g-3', property: 'topic', value: 'Which locales ship in the first release.' });
  assert.equal(unrelated.ok, true, 'an unrelated edit is accepted');
  const another = project.apply({ type: 'CreateEntity', kind: 'seam', data: { id: 's-9', question: 'q', basis: ['g-1'], origin: 'proposed' } });
  assert.equal(another.ok, false, 'a second violation of the same rule is new');
  assert.equal(another.code, 'integrity.violated');
  assert.match(another.diagnostics[0].message, /e = s-9/);
  const fix = project.apply({ type: 'SetProperty', id: 's-1', property: 'basis', value: ['g-1', 'dec-1'] });
  assert.equal(fix.ok, true, 'the fix is accepted');
  assert.equal(project.diagnostics.filter((d) => d.code === 'integrity.violated').length, 0);
  // A warning rule is reported, never enforced.
  assert.equal(project.apply({ type: 'SetProperty', id: 'resolution-revisited', property: 'severity', value: 'warning' }).ok, true);
  assert.equal(project.apply({ type: 'SetProperty', id: 's-1', property: 'basis', value: ['g-1'] }).ok, true);
  // Promoting it to error keeps its existing violations (they are not new) and stops new ones.
  assert.equal(project.apply({ type: 'SetProperty', id: 'resolution-revisited', property: 'severity', value: 'error' }).ok, true);
  assert.equal(project.apply({ type: 'CreateEntity', kind: 'seam', data: { id: 's-9', question: 'q', basis: ['g-1'], origin: 'proposed' } }).code, 'integrity.violated');
  // A new error rule that is already violated cannot be added: all its violations are new.
  const added = project.apply({ type: 'CreateEntity', kind: 'integrityRule', data: { id: 'every-gap-resolved', severity: 'error', statement: 'Every gap is resolved.', rule: 'forall g : gap, nonempty g.resolvedBy' } });
  assert.equal(added.ok, false);
  assert.equal(added.code, 'integrity.violated');
  assert.match(added.diagnostics[0].message, /g = g-3/);
});

test('the integrity command evaluates every rule, and --rules tries rules without editing the file', async () => {
  const specs = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-integrity-'));
  try {
    fs.mkdirSync(path.join(specs, 'fixture'));
    const broken = mutated(SPEC, [{ type: 'SetProperty', id: 's-2', property: 'encodes', value: null }]).text;
    fs.writeFileSync(path.join(specs, 'fixture', 'spec.jsonc'), broken);
    const env = await runCommand('integrity', [], { specs, project: 'fixture' });
    assert.equal(env.ok, false);
    assert.equal(env.error?.code, 'integrity.violated');
    const r = env.result.rules.find((/** @type {any} */ x) => x.ruleId === 'proposed-has-source');
    assert.equal(r.status, 'violated');
    assert.equal(r.counterexampleCount, 1);
    assert.deepEqual(r.counterexamples[0].map((/** @type {any} */ b) => [b.variable, b.entity, b.kind]), [['e', 's-2', 'seam']]);
    assert.ok(Number.isInteger(r.counterexamples[0][0].line));
    const one = await runCommand('integrity', ['closes-agrees-with-resolved-by'], { specs, project: 'fixture' });
    assert.equal(one.ok, true);
    assert.equal(one.result.total, 1);
    assert.equal(one.result.rules[0].instances, 1);
    const rules = path.join(specs, 'rules.json');
    fs.writeFileSync(rules, JSON.stringify([{ id: 'every-gap-resolved', severity: 'warning', statement: 'Every gap is resolved.', rule: 'forall g : gap, nonempty g.resolvedBy' }]));
    const tried = await runCommand('integrity', ['every-gap-resolved', '--rules', rules], { specs, project: 'fixture' });
    assert.equal(tried.ok, true, 'a violated warning rule does not fail the command');
    assert.deepEqual(tried.result.rules[0].counterexamples.map((/** @type {any} */ c) => c[0].entity), ['g-3']);
    assert.equal(fs.readFileSync(path.join(specs, 'fixture', 'spec.jsonc'), 'utf8'), broken, 'the specification file is unchanged');
  } finally {
    fs.rmSync(specs, { recursive: true, force: true });
  }
});
