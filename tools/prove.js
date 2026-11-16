// Runs `exegra prove`: explores a scenario with the verified explorer of the formal semantics, writes
// the Lean proof file under formal/generated/ (ignored by git) and checks it with Lake. The pure part
// (the request, the Lean text, the results) is src/core/proof-export.js.
//
// Steps:
//   1. `lake build` in formal/ (no work when it is up to date), so the explorer and its proofs are built;
//   2. `exegra-lean explore` runs the compiled explorer on the scenario's engine input and invariants;
//   3. the proof file states, per claim, `explore env inv bound maxStates = <that result>`, discharged
//      by native_decide, and `lake env lean` checks it and prints the axioms of each theorem. The
//      modules' native shared libraries (precompileModules in formal/lakefile.toml) are loaded into
//      Lean, so native_decide runs the compiled explorer instead of interpreting it.
// A claim is reported only when step 3 accepted its theorem.

import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { exploreRequest, temporalRequest, leanProofFile, parseAxioms, proofFileName, proofNamespace, proofPlan, proofResults } from '../src/core/proof-export.js';

/** @typedef {import('../src/core/types.js').Model} Model */

const HERE = path.dirname(fileURLToPath(import.meta.url));
export const REPO_ROOT = path.resolve(HERE, '..');
export const FORMAL = path.join(REPO_ROOT, 'formal');
export const LEAN_BIN = path.join(FORMAL, '.lake', 'build', 'bin', `exegra-lean${process.platform === 'win32' ? '.exe' : ''}`);

const SPAWN = { encoding: /** @type {const} */ ('utf8'), windowsHide: true, maxBuffer: 1 << 30 };

/** Is Lake on the PATH? */
export function lakeAvailable() {
  const probe = spawnSync('lake', ['--version'], SPAWN);
  return probe.status === 0;
}

export class ProveError extends Error {
  /** @param {string} code @param {string} message */
  constructor(code, message) {
    super(message);
    this.code = code;
  }
}

/** The modules a proof file needs, in import order. */
const NATIVE_MODULES = ['Number', 'Value', 'Json', 'Expr', 'Input', 'Trace', 'Semantics', 'Explore', 'Search', 'Prove', 'Temporal'];

/**
 * `--load-dynlib` options for the modules' shared libraries, or none when one is missing (Lean then
 * interprets the explorer, which gives the same result more slowly).
 * @returns {string[]}
 */
export function nativeLibOptions() {
  const dir = path.join(FORMAL, '.lake', 'build', 'lib', 'lean');
  const names = fs.existsSync(dir) ? fs.readdirSync(dir) : [];
  const libs = NATIVE_MODULES.map((m) => names.find((n) => new RegExp(`^(lib)?exegra_Exegra_${m}\\.(dll|so|dylib)$`).test(n)));
  if (libs.some((l) => l === undefined)) return [];
  return libs.map((l) => `--load-dynlib=${path.join(dir, /** @type {string} */ (l))}`);
}

/** @param {string} text @param {number} n */
const tail = (text, n) => text.split(/\r?\n/).filter(Boolean).slice(-n).join('\n');

/**
 * Prove the state-invariant claims of one scenario.
 * @param {Model} model
 * @param {string} scenarioId
 * @param {{bound?: number, maxStates?: number, withSteps?: boolean, log?: (m: string) => void}} [opts]
 */
export function proveScenario(model, scenarioId, opts = {}) {
  const log = opts.log ?? (() => {});
  const plan = proofPlan(model, scenarioId, { bound: opts.bound, maxStates: opts.maxStates });
  const base = {
    scenarioId,
    bound: plan.bound,
    stepLimit: plan.stepLimit,
    maxStates: plan.maxStates,
    faults: plan.faults,
  };
  if (!plan.claims.length) {
    return { ...base, note: 'No state-invariant or temporal claim lists this scenario; nothing to explore.', claims: plan.skipped };
  }
  if (!lakeAvailable()) throw new ProveError('prove.no-lake', 'Lake is not on the PATH; install elan (the toolchain is pinned in formal/lean-toolchain).');

  log('prove: lake build (formal/)');
  const build = spawnSync('lake', ['build'], { ...SPAWN, cwd: FORMAL });
  if (build.status !== 0) throw new ProveError('prove.build-failed', `lake build failed in formal/:\n${tail(`${build.stdout}${build.stderr}`, 30)}`);

  log(`prove: exploring ${scenarioId} (${plan.claims.length} claim${plan.claims.length === 1 ? '' : 's'}, bound ${plan.bound})`);
  const t0 = Date.now();
  const run = spawnSync(LEAN_BIN, ['explore'], { ...SPAWN, input: exploreRequest(plan) });
  const exploreMs = Date.now() - t0;
  if (run.status !== 0) throw new ProveError('prove.explore-failed', `exegra-lean explore failed: ${tail(`${run.stderr}${run.stdout}`, 10) || `exit status ${run.status}`}`);
  const explored = JSON.parse(run.stdout);
  if (plan.claims.some((c) => c.temporal)) {
    const trun = spawnSync(LEAN_BIN, ['temporal'], { ...SPAWN, input: temporalRequest(plan) });
    if (trun.status !== 0) throw new ProveError('prove.explore-failed', `exegra-lean temporal failed: ${tail(`${trun.stderr}${trun.stdout}`, 10) || `exit status ${trun.status}`}`);
    const tex = JSON.parse(trun.stdout);
    explored.leanInput = tex.leanInput;
    const byId = new Map([...explored.results.map((/** @type {any} */ r) => [r.id, r]), ...tex.results.map((/** @type {any} */ r) => [r.id, { ...r, temporal: true }])]);
    explored.results = plan.claims.map((c) => byId.get(c.claimId));
  } else {
    const byId = new Map(explored.results.map((/** @type {any} */ r) => [r.id, r]));
    explored.results = plan.claims.map((c) => byId.get(c.claimId));
  }

  const rel = proofFileName(scenarioId);
  const file = path.join(FORMAL, rel);
  fs.mkdirSync(path.dirname(file), { recursive: true });
  fs.writeFileSync(file, leanProofFile(plan, explored), 'utf8');

  log(`prove: checking formal/${rel}`);
  const t1 = Date.now();
  const dynlibs = nativeLibOptions();
  const check = spawnSync('lake', ['env', 'lean', ...dynlibs, rel], { ...SPAWN, cwd: FORMAL });
  const checkMs = Date.now() - t1;
  const output = `${check.stdout}${check.stderr}`;
  if (check.status !== 0 || /:\d+:\d+: error/.test(output)) {
    throw new ProveError('prove.check-failed', `Lean did not accept formal/${rel}:\n${tail(output, 30)}`);
  }
  const axioms = parseAxioms(output);
  for (const c of plan.claims) {
    if (!axioms.has(c.claimId.replace(/[«»]/g, ''))) throw new ProveError('prove.check-failed', `Lean reported no axioms for the theorem of "${c.claimId}"; the check is incomplete.`);
  }
  const claims = proofResults(model, plan, explored, axioms, {
    file: `formal/${rel}`,
    namespace: proofNamespace(scenarioId),
    withSteps: opts.withSteps,
  });
  /** @type {Record<string, any>} */
  const out = { ...base, exploreMs, checkMs, nativeCode: dynlibs.length > 0, claims };
  if (plan.boundCapped) out.note = `The requested bound was larger than the scenario's step limit; ${plan.bound} steps were explored, the most a run of this scenario takes.`;
  return out;
}
