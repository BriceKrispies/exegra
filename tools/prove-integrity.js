// Runs `exegra prove-integrity`: proves or refutes integrity rules in Lean. The pure part (facts,
// formula, Lean text) is src/core/integrity-export.js; the checker and its soundness proofs are
// formal/Exegra/Integrity.lean.
//
// Per rule:
//   1. the JavaScript evaluator decides it and lists its counterexamples;
//   2. `exegra-lean integrity` evaluates the same exported facts with the Lean checker (compiled):
//      verdict and witnesses must agree with step 1, or the rule is incomplete;
//   3. the proof file states `holds` (by reflection) or one `violated_<n>` per witness, each
//      discharged by `decide +kernel`, and `lake env lean` checks it. Each theorem must depend on
//      Lean's standard axioms only; native_decide (Lean.ofReduceBool) or sorry make it incomplete.

import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { evaluateRuleEntity, counterexampleJson } from '../src/core/integrity.js';
import { exportRule, integrityRequest, witnessNumbers, leanProofFile, valuesTable, proofFileName, parseAxioms, kernelChecked } from '../src/core/integrity-export.js';
import { FORMAL, LEAN_BIN, lakeAvailable, ProveError } from './prove.js';

/** @typedef {import('../src/core/types.js').Model} Model */

const SPAWN = { encoding: /** @type {const} */ ('utf8'), windowsHide: true, maxBuffer: 1 << 30 };

/** @param {string} text @param {number} n */
const tail = (text, n) => text.split(/\r?\n/).filter(Boolean).slice(-n).join('\n');

/** @param {number[][]} ws */
const witnessSet = (ws) => new Set(ws.map((w) => w.join(',')));

/**
 * Prove or refute integrity rules.
 * @param {Model} model
 * @param {string[]} ruleIds
 * @param {{maxWitnesses?: number, log?: (m: string) => void}} [opts]
 */
export function proveIntegrity(model, ruleIds, opts = {}) {
  const log = opts.log ?? (() => {});
  const maxWitnesses = opts.maxWitnesses ?? 10;
  if (!lakeAvailable()) throw new ProveError('prove.no-lake', 'Lake is not on the PATH; install elan (the toolchain is pinned in formal/lean-toolchain).');
  log('prove-integrity: lake build (formal/)');
  const build = spawnSync('lake', ['build'], { ...SPAWN, cwd: FORMAL });
  if (build.status !== 0) throw new ProveError('prove.build-failed', `lake build failed in formal/:\n${tail(`${build.stdout}${build.stderr}`, 30)}`);

  return ruleIds.map((ruleId) => {
    const rule = model.entities.get(ruleId);
    if (!rule || rule.kind !== 'integrityRule') throw new ProveError('prove.unknown-rule', `"${ruleId}" is not an integrity rule.`);
    const js = evaluateRuleEntity(model, rule);
    /** @type {Record<string, any>} */
    const out = { ruleId, severity: js.severity, statement: js.statement, instances: js.instances, vacuous: js.vacuous, evaluateMs: Math.round(js.ms) };
    if (js.status === 'invalid') return { ...out, result: 'incomplete', explanation: `The rule is invalid: ${js.problem}` };

    const t0 = Date.now();
    const ex = exportRule(model, ruleId);
    const jsWitnesses = js.counterexamples.map((c) => witnessNumbers(ex, c.values));
    out.facts = { entities: ex.entities.length, properties: ex.props, values: ex.intern.size };
    out.exportMs = Date.now() - t0;

    log(`prove-integrity: ${ruleId}: Lean evaluation over ${ex.entities.length} entities`);
    const t1 = Date.now();
    const run = spawnSync(LEAN_BIN, ['integrity'], { ...SPAWN, input: integrityRequest(ex) });
    out.leanEvalMs = Date.now() - t1;
    if (run.status !== 0) throw new ProveError('prove.explore-failed', `exegra-lean integrity failed: ${tail(`${run.stderr}${run.stdout}`, 10) || `exit status ${run.status}`}`);
    const lean = JSON.parse(run.stdout);
    const lr = lean.results[0];
    const a = witnessSet(jsWitnesses), b = witnessSet(lr.witnesses);
    const agree = lr.holds === (js.counterexamples.length === 0) && a.size === b.size && [...a].every((w) => b.has(w));
    out.differential = { agree, jsCounterexamples: a.size, leanWitnesses: b.size, searchTree: lean.searchTree };
    if (!agree) return { ...out, result: 'incomplete', explanation: `The JavaScript evaluator and the Lean checker disagree (${js.status}, ${a.size} counterexample(s); Lean ${lr.holds ? 'holds' : 'violated'}, ${b.size} witness(es)). Nothing is claimed.` };

    const holds = js.counterexamples.length === 0;
    const proved = holds ? [] : jsWitnesses.slice(0, maxWitnesses);
    const rel = proofFileName(ruleId);
    const file = path.join(FORMAL, rel);
    fs.mkdirSync(path.dirname(file), { recursive: true });
    fs.writeFileSync(file, leanProofFile(ex, holds ? { holds: true } : { holds: false, witnesses: proved }), 'utf8');
    fs.writeFileSync(file.replace(/\.lean$/, '.values.json'), valuesTable(ex), 'utf8');

    log(`prove-integrity: ${ruleId}: checking formal/${rel}`);
    const t2 = Date.now();
    const check = spawnSync('lake', ['env', 'lean', rel], { ...SPAWN, cwd: FORMAL });
    out.checkMs = Date.now() - t2;
    out.file = `formal/${rel}`;
    const output = `${check.stdout}${check.stderr}`;
    if (check.status !== 0 || /:\d+:\d+: error/.test(output)) {
      return { ...out, result: 'incomplete', explanation: `Lean did not accept formal/${rel}:\n${tail(output, 15)}` };
    }
    const axioms = parseAxioms(output);
    const theorems = ['facts_search_tree', ...(holds ? ['holds'] : proved.map((_, i) => `violated_${i}`))];
    for (const t of theorems) {
      const ax = axioms.get(t);
      if (!ax) return { ...out, result: 'incomplete', explanation: `Lean reported no axioms for ${t}; the check is incomplete.` };
      if (!kernelChecked(ax)) return { ...out, result: 'incomplete', explanation: `${t} depends on ${ax.join(', ')}: not kernel-checked with standard axioms only.` };
    }
    out.axioms = [...new Set(theorems.flatMap((t) => /** @type {string[]} */ (axioms.get(t))))].sort();
    out.theorems = theorems;
    if (holds) {
      return { ...out, result: 'holds', explanation: `Holds on ${js.instances} instance(s)${js.vacuous ? ' (vacuous: the quantifier ranges over nothing)' : ''}. Lean proved Sat facts [] rule by reflection (eval_iff, decide +kernel) with standard axioms only.` };
    }
    return {
      ...out,
      result: 'violated',
      counterexamples: js.counterexamples.length,
      provedWitnesses: proved.length,
      witnesses: js.counterexamples.slice(0, maxWitnesses).map((c) => counterexampleJson(model, c)),
      explanation: `Violated by ${js.counterexamples.length} counterexample(s); Lean proved ¬ Sat facts [] rule from ${proved.length} of them (refutes_sound, decide +kernel), each from the witness alone.`,
    };
  });
}
