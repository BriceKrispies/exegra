// Runs `exegra prove-integrity`: proves or refutes integrity rules in Lean. The pure part (facts,
// formula, Lean text) is src/core/integrity-export.js; the checker and its soundness proofs are
// formal/Exegra/Integrity.lean.
//
// Per rule:
//   1. the JavaScript evaluator decides it and lists its counterexamples;
//   2. `exegra-lean integrity` evaluates the same exported facts with the Lean checker (compiled):
//      the program of the derived relations the rule uses must be stratified (`wf`) and solved, the
//      solved tables must equal the JavaScript tables, and the verdict and witnesses must agree with
//      step 1, or the rule is incomplete;
//   3. the proof file states `prog_wf`, `prog_solved` and `holds` (by reflection) or one
//      `violated_<n>` per witness, each discharged by `decide +kernel`, and `lake env lean` checks
//      it. `holds` and `violated_<n>` are about Sat under `Least` (the least-model meaning). Each
//      theorem must depend on Lean's standard axioms only; native_decide (Lean.ofReduceBool) or sorry
//      make it incomplete.
//
// Every Lean process runs under a time limit (`timeoutMs`, default DEFAULT_TIMEOUT_MS each), and a
// rule whose relations have more candidate tuples than `maxCandidates` (default
// DEFAULT_MAX_CANDIDATES) is not sent to the kernel: both give `incomplete` with the reason, never a
// hang. The proof file is checked by running `lean` directly in the environment `lake env` prints,
// so the time limit stops the process that does the work.

import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { evaluateRuleEntity, counterexampleJson } from '../src/core/integrity.js';
import { exportRule, integrityRequest, witnessNumbers, leanProofFile, valuesTable, proofFileName, parseAxioms, kernelChecked, PROOF_PRELUDE_THEOREMS } from '../src/core/integrity-export.js';
import { FORMAL, LEAN_BIN, lakeAvailable, ProveError } from './prove.js';

/** @typedef {import('../src/core/types.js').Model} Model */

const SPAWN = { encoding: /** @type {const} */ ('utf8'), windowsHide: true, maxBuffer: 1 << 30 };

/** @param {string} text @param {number} n */
const tail = (text, n) => text.split(/\r?\n/).filter(Boolean).slice(-n).join('\n');

/** @param {number[][]} ws */
const witnessSet = (ws) => new Set(ws.map((w) => w.join(',')));

/**
 * Relation tables as a set of "id:tuple" strings, to compare the JavaScript and Lean tables.
 * @param {{id: number, tuples: number[][]}[]} table
 */
export const tableSet = (table) => new Set(table.flatMap((e) => e.tuples.map((w) => `${e.id}:${w.join(',')}`)));

/** Do two tables hold the same relations with the same tuples? @param {{id: number, tuples: number[][]}[]} a @param {{id: number, tuples: number[][]}[]} b */
export function sameTables(a, b) {
  const ids = (/** @type {{id: number}[]} */ t) => t.map((e) => e.id).sort((x, y) => x - y).join(',');
  const x = tableSet(a), y = tableSet(b);
  return ids(a) === ids(b) && x.size === y.size && [...x].every((k) => y.has(k));
}

/** The time limit of each Lean process, in milliseconds, unless the caller gives one. */
export const DEFAULT_TIMEOUT_MS = 300000;

/**
 * The most candidate tuples (summed over the relations a rule uses) a proof is attempted for. The
 * kernel evaluates the fixpoint iteration over every candidate tuple, by structural reduction; above
 * this the check would take too long to be useful.
 */
export const DEFAULT_MAX_CANDIDATES = 500;

/** Did a spawnSync stop on its time limit? @param {import('node:child_process').SpawnSyncReturns<string>} r */
const timedOut = (r) => /** @type {any} */ (r.error)?.code === 'ETIMEDOUT' || (r.status === null && r.signal !== null);

/** The environment `lake env` gives `lean` in formal/, once per process. @type {Record<string, string> | null} */
let LEAN_ENV = null;
function leanEnv() {
  if (LEAN_ENV) return LEAN_ENV;
  const r = spawnSync('lake', ['env'], { ...SPAWN, cwd: FORMAL });
  if (r.status !== 0) throw new ProveError('prove.build-failed', `lake env failed in formal/:\n${tail(`${r.stdout}${r.stderr}`, 10)}`);
  /** @type {Record<string, string>} */
  const vars = {};
  for (const line of r.stdout.split(/\r?\n/)) {
    const i = line.indexOf('=');
    if (i > 0) vars[line.slice(0, i)] = line.slice(i + 1);
  }
  // Windows names variables case-insensitively: drop the inherited spelling of each one lake sets.
  /** @type {Record<string, string>} */
  const env = {};
  const set = new Set(Object.keys(vars).map((k) => k.toUpperCase()));
  for (const [k, v] of Object.entries(process.env)) if (v !== undefined && !set.has(k.toUpperCase())) env[k] = v;
  LEAN_ENV = { ...env, ...vars };
  return LEAN_ENV;
}

/**
 * Prove or refute integrity rules.
 * @param {Model} model
 * @param {string[]} ruleIds
 * @param {{maxWitnesses?: number, timeoutMs?: number, maxCandidates?: number, log?: (m: string) => void}} [opts]
 *   maxWitnesses: refutations per violated rule (at least 1); timeoutMs: the time limit of each Lean
 *   process; maxCandidates: the most candidate tuples of the rule's relations a proof is attempted for
 */
export function proveIntegrity(model, ruleIds, opts = {}) {
  const log = opts.log ?? (() => {});
  const timeoutMs = Math.max(1, Math.floor(opts.timeoutMs ?? DEFAULT_TIMEOUT_MS));
  const maxCandidates = Math.max(0, Math.floor(opts.maxCandidates ?? DEFAULT_MAX_CANDIDATES));
  // At least one witness: a violated result always carries a kernel-checked refutation.
  const maxWitnesses = Math.max(1, Math.floor(opts.maxWitnesses ?? 10));
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
    out.facts = { entities: ex.entities.length, properties: ex.props, values: ex.intern.size, relations: ex.relations, candidates: ex.candidates };
    out.exportMs = Date.now() - t0;
    if (ex.candidates > maxCandidates) {
      return { ...out, result: 'incomplete', explanation: `Too large to prove in the kernel: the relations the rule uses have ${ex.candidates} candidate tuples, more than ${maxCandidates} (--max-candidates). The JavaScript result (${js.status}) stands unproved.` };
    }

    log(`prove-integrity: ${ruleId}: Lean evaluation over ${ex.entities.length} entities`);
    const t1 = Date.now();
    const run = spawnSync(LEAN_BIN, ['integrity'], { ...SPAWN, input: integrityRequest(ex), timeout: timeoutMs });
    out.leanEvalMs = Date.now() - t1;
    if (timedOut(run)) return { ...out, result: 'incomplete', explanation: `The Lean checker (exegra-lean integrity) did not finish within ${timeoutMs} ms (--timeout). Nothing is claimed.` };
    if (run.status !== 0) throw new ProveError('prove.explore-failed', `exegra-lean integrity failed: ${tail(`${run.stderr}${run.stdout}`, 10) || `exit status ${run.status}`}`);
    const lean = JSON.parse(run.stdout);
    const lr = lean.results[0];
    const a = witnessSet(jsWitnesses), b = witnessSet(lr.witnesses);
    const tablesAgree = lean.wf === true && lean.solved === true && sameTables(ex.table, lean.tables);
    const agree = tablesAgree && lr.holds === (js.counterexamples.length === 0) && a.size === b.size && [...a].every((w) => b.has(w));
    out.differential = { agree, jsCounterexamples: a.size, leanWitnesses: b.size, searchTree: lean.searchTree, stratified: lean.wf, solved: lean.solved, tablesAgree, tuples: tableSet(ex.table).size };
    if (!lean.wf) return { ...out, result: 'incomplete', explanation: 'The Lean stratification check (wf) refuses the program of the relations the rule uses. Nothing is claimed.' };
    if (!lean.solved) return { ...out, result: 'incomplete', explanation: 'The Lean checker did not reach the fixpoint of the relations within its fuel. Nothing is claimed.' };
    if (!agree) return { ...out, result: 'incomplete', explanation: `The JavaScript evaluator and the Lean checker disagree (${tablesAgree ? 'same relation tables' : 'different relation tables'}; ${js.status}, ${a.size} counterexample(s); Lean ${lr.holds ? 'holds' : 'violated'}, ${b.size} witness(es)). Nothing is claimed.` };

    const holds = js.counterexamples.length === 0;
    const proved = holds ? [] : jsWitnesses.slice(0, maxWitnesses);
    const rel = proofFileName(ruleId);
    const file = path.join(FORMAL, rel);
    fs.mkdirSync(path.dirname(file), { recursive: true });
    fs.writeFileSync(file, leanProofFile(ex, holds ? { holds: true } : { holds: false, witnesses: proved }), 'utf8');
    fs.writeFileSync(file.replace(/\.lean$/, '.values.json'), valuesTable(ex), 'utf8');

    log(`prove-integrity: ${ruleId}: checking formal/${rel}`);
    const t2 = Date.now();
    const env = leanEnv();
    const check = spawnSync(env.LEAN ?? 'lean', [rel], { ...SPAWN, cwd: FORMAL, env, timeout: timeoutMs });
    out.checkMs = Date.now() - t2;
    out.file = `formal/${rel}`;
    if (timedOut(check)) return { ...out, result: 'incomplete', explanation: `Lean did not finish checking formal/${rel} within ${timeoutMs} ms (--timeout). Nothing is claimed.` };
    const output = `${check.stdout}${check.stderr}`;
    if (check.status !== 0 || /:\d+:\d+: error/.test(output)) {
      return { ...out, result: 'incomplete', explanation: `Lean did not accept formal/${rel}:\n${tail(output, 15)}` };
    }
    const axioms = parseAxioms(output);
    const theorems = [...PROOF_PRELUDE_THEOREMS, ...(holds ? ['holds'] : proved.map((_, i) => `violated_${i}`))];
    for (const t of theorems) {
      const ax = axioms.get(t);
      if (!ax) return { ...out, result: 'incomplete', explanation: `Lean reported no axioms for ${t}; the check is incomplete.` };
      if (!kernelChecked(ax)) return { ...out, result: 'incomplete', explanation: `${t} depends on ${ax.join(', ')}: not kernel-checked with standard axioms only.` };
    }
    out.axioms = [...new Set(theorems.flatMap((t) => /** @type {string[]} */ (axioms.get(t))))].sort();
    out.theorems = theorems;
    if (holds) {
      return { ...out, result: 'holds', explanation: `Holds on ${js.instances} instance(s)${js.vacuous ? ' (vacuous: the quantifier ranges over nothing)' : ''}. Lean proved Sat facts (Least facts prog) [] rule by reflection (eval_iff, least_eq_table, decide +kernel) with standard axioms only.` };
    }
    return {
      ...out,
      result: 'violated',
      counterexamples: js.counterexamples.length,
      provedWitnesses: proved.length,
      witnesses: js.counterexamples.slice(0, maxWitnesses).map((c) => counterexampleJson(model, c)),
      explanation: `Violated by ${js.counterexamples.length} counterexample(s); Lean proved ¬ Sat facts (Least facts prog) [] rule from ${proved.length} of them (refutes_sound, least_eq_table, decide +kernel), each from the witness alone.`,
    };
  });
}
