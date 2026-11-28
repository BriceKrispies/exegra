// Runs `exegra prove`: explores a scenario with the explorer of the behaviour calculus, writes
// the Lean proof file under formal/generated/ (ignored by git) and checks it with Lake. The pure part
// (the request, the Lean text, the results) is src/core/proof-export.js.
//
// Steps:
//   1. `lake build` in formal/ (no work when it is up to date), so the explorer and its proofs are built;
//   2. `exegra-lean explore` runs the compiled explorer on the scenario's engine input and invariants;
//   3. the proof file states, per claim, `verdictOf inputText inv bound maxStates = <that result>`, discharged
//      by native_decide, and `lake env lean` checks it and prints the axioms of each theorem. The
//      modules' native shared libraries (precompileModules in formal/lakefile.toml) are loaded into
//      Lean, so native_decide runs the compiled explorer instead of interpreting it.
// A claim is reported only when step 3 accepted its theorem.

import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { exploreRequest, temporalRequest, livenessRequest, certificateRequest, sysName, leanProofFile, parseAxioms, proofFileName, proofNamespace, proofPlan, proofResults } from '../src/core/proof-export.js';

/** @typedef {import('../src/core/types.js').Model} Model */

const HERE = path.dirname(fileURLToPath(import.meta.url));
export const REPO_ROOT = path.resolve(HERE, '..');
export const FORMAL = path.join(REPO_ROOT, 'formal');
export const LEAN_BIN = path.join(FORMAL, '.lake', 'build', 'bin', `exegra-lean${process.platform === 'win32' ? '.exe' : ''}`);

const SPAWN = { encoding: /** @type {const} */ ('utf8'), windowsHide: true, maxBuffer: 1 << 30 };

/** Is Lake on the PATH? */
export function lakeAvailable() {
  // From formal/, so that elan resolves the toolchain pinned there even without a default one.
  const probe = spawnSync('lake', ['--version'], { ...SPAWN, cwd: FORMAL });
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
const NATIVE_MODULES = ['Number', 'Value', 'Json', 'Expr', 'Input', 'Trace', 'Random', 'Resource', 'Workload', 'Format2',
  'Search', 'Core_LTS', 'Core_Live', 'Core_Search', 'Core_Behav', 'Core_BehavExec', 'Core_BehavCheck', 'Core_BehavLive', 'Elab', 'Format2B',
  'ProveB', 'ProveLive'];

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

/** The module name of a scenario's kernel-checked proofs: Exegra.Proofs.<Scenario in Pascal case>. @param {string} scenarioId */
export function kernelModuleName(scenarioId) {
  const pascal = scenarioId.split(/[^A-Za-z0-9]+/).filter(Boolean).map((p) => p[0].toUpperCase() + p.slice(1)).join('');
  return `Exegra.Proofs.${/^[A-Za-z]/.test(pascal) ? pascal : `S${pascal}`}`;
}

/**
 * Write formal/Exegra/Proofs/<Scenario>.lean: the scenario's calculus system written out, and for each
 * state-invariant claim that holds, its invariant proved by a closed-set certificate the kernel checks with
 * `decide` (Exegra.V2.ProveKernel.kernelModule). The module is checked with `lake env lean`; import it from
 * formal/Exegra.lean to have lake build check it.
 * @param {ReturnType<typeof proofPlan>} plan @param {any[]} claims @param {(m: string) => void} log
 */
function writeKernelModule(plan, claims, log) {
  const held = plan.claims.filter((c) => !c.temporal && !c.live && claims.find((r) => r.claimId === c.claimId)?.result === 'holds');
  if (!held.length) return { written: false, note: 'No state-invariant claim of the scenario holds; no module was written.' };
  // WG-5683: the kernel's `decide` does not reduce the settling of a world, so a module for a scenario
  // with resources would be refused; its invariants keep the native closed-set certificate only.
  if (plan.input?.resources?.length) return { written: false, note: 'The scenario uses resources, whose settling decide does not reduce in the kernel; no kernel-only module was written (the closed-set certificates checked by native_decide stand).' };
  const name = kernelModuleName(plan.scenarioId);
  const request = JSON.stringify({ input: plan.input, module: name, sysName: sysName(plan.scenarioId), claims: held.map((c) => ({ id: c.claimId, expr: c.expr })), bound: plan.bound, maxStates: plan.maxStates });
  const run = spawnSync(LEAN_BIN, ['module'], { ...SPAWN, input: request });
  if (run.status !== 0) throw new ProveError('prove.module-failed', `exegra-lean module failed: ${tail(`${run.stderr}${run.stdout}`, 10) || `exit status ${run.status}`}`);
  const rel = path.join('Exegra', 'Proofs', `${name.split('.').pop()}.lean`);
  fs.mkdirSync(path.join(FORMAL, 'Exegra', 'Proofs'), { recursive: true });
  fs.writeFileSync(path.join(FORMAL, rel), JSON.parse(run.stdout).text, 'utf8');
  log(`prove: checking formal/${rel.replace(/\\/g, '/')} (kernel only)`);
  const check = spawnSync('lake', ['env', 'lean', rel], { ...SPAWN, cwd: FORMAL });
  const output = `${check.stdout}${check.stderr}`;
  if (check.status !== 0 || /:\d+:\d+: error/.test(output)) throw new ProveError('prove.check-failed', `Lean did not accept formal/${rel}:\n${tail(output, 30)}`);
  return { written: true, file: `formal/${rel.replace(/\\/g, '/')}`, module: name, theorems: held.map((c) => `${name}.${c.claimId.replace(/-/g, '_')}`) };
}

/** @param {string} text @param {number} n */
const tail = (text, n) => text.split(/\r?\n/).filter(Boolean).slice(-n).join('\n');

/**
 * Prove the state-invariant claims of one scenario.
 * @param {Model} model
 * @param {string} scenarioId
 * @param {{bound?: number, maxStates?: number, withSteps?: boolean, module?: boolean, log?: (m: string) => void}} [opts]
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
  /** @type {Map<string, any>} */
  const byId = new Map(explored.results.map((/** @type {any} */ r) => [r.id, r]));
  /** @param {string} cmd @param {string} request @param {Record<string, any>} mark */
  const runMore = (cmd, request, mark) => {
    const more = spawnSync(LEAN_BIN, [cmd], { ...SPAWN, input: request });
    if (more.status !== 0) throw new ProveError('prove.explore-failed', `exegra-lean ${cmd} failed: ${tail(`${more.stderr}${more.stdout}`, 10) || `exit status ${more.status}`}`);
    for (const r of JSON.parse(more.stdout).results) byId.set(r.id, { ...r, ...mark });
  };
  if (plan.claims.some((c) => c.temporal)) runMore('temporal', temporalRequest(plan), { temporal: true });
  if (plan.claims.some((c) => c.live)) runMore('liveness', livenessRequest(plan), { live: true });
  explored.results = plan.claims.map((c) => byId.get(c.claimId));
  // The closed-set certificate of the invariants that hold: the states the explorer visited.
  if (plan.claims.some((c, i) => !c.temporal && !c.live && explored.results[i]?.verdict === 'holds')) {
    const cert = spawnSync(LEAN_BIN, ['certificate'], { ...SPAWN, input: certificateRequest(plan) });
    if (cert.status !== 0) throw new ProveError('prove.explore-failed', `exegra-lean certificate failed: ${tail(`${cert.stderr}${cert.stdout}`, 10) || `exit status ${cert.status}`}`);
    explored.certificate = JSON.parse(cert.stdout).states;
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
    certificate: explored.certificate ?? null,
  });
  /** @type {Record<string, any>} */
  const out = { ...base, exploreMs, checkMs, nativeCode: dynlibs.length > 0, claims };
  if (opts.module) out.module = writeKernelModule(plan, claims, log);
  if (plan.boundCapped) out.note = `The requested bound was larger than the scenario's step limit; ${plan.bound} steps were explored, the most a run of this scenario takes.`;
  return out;
}
