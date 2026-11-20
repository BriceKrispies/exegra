// Agent-facing command implementations. Each command returns a plain result
// object; runCommand wraps it in the JSON envelope printed by cli/exegra.js.
//
// Every mutation goes through Project.apply with the operations in OPERATIONS,
// the same pipeline the UI uses. Nothing here edits specification text.
//
// Envelope:
//   success: { ok: true, command, project, semanticHash?, result }
//   failure: { ok: false, command, project, error: {code, message}, diagnostics, result? }
// `semanticHash` is present when the command read a project. `result` is present
// on a failure only for validate and verify, which report findings even when they fail.

import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { parseArgs } from 'node:util';
import { createWorkspace, WorkspaceError, isValidProjectName, PROJECT_FILE } from '../tools/workspace.js';
import { checkTraceability } from '../tools/traceability.js';
import { readinessGaps } from '../src/core/readiness.js';
import { machineCoverage, coverageOperations, DEFAULT_BOUND, DEFAULT_MAX_RUNS } from '../src/core/machine-coverage.js';
import { functionCoverage } from '../src/core/function-coverage.js';
import { resolveRoots, splitRootRef, collectExternalResults, RootsError } from '../tools/realisation-roots.js';
import { Project } from '../src/core/project.js';
import { OPERATIONS, OpError, Tx, planDelete } from '../src/core/operations.js';
import { analyzeSpec } from '../src/core/analyze.js';
import { analyzeLayers } from '../src/core/layers.js';
import { evaluateIntegrity, counterexampleJson } from '../src/core/integrity.js';
import { proveIntegrity } from '../tools/prove-integrity.js';
import {
  entityLabel, childrenOf, ancestorsOf, inboundRefs, relationshipsOf, dependencies, contractsOf,
} from '../src/core/query.js';
import { evaluateClaims, evaluateClaim, checkTrace, theoremRequests } from '../src/core/claims.js';
import { applyConcordance } from '../src/core/concordance.js';
import { checkTheorems } from '../tools/lean-theorems.js';
import { requestLog } from '../src/core/contract-trace.js';
import { runScenario } from '../src/core/engine.js';
import { proveScenario, ProveError } from '../tools/prove.js';
import { CLAIM_STATUSES } from '../src/core/claim-methods.js';
import { stableStringify } from '../src/core/stable-json.js';
import { testRefProblem, describeTestRefProblem } from '../src/core/evidence-ref.js';
import { treeStamp } from '../tools/tree-stamp.js';
import { createOutcomeReuse } from './outcomes.js';
import { snapshot, compare, sideCounts, NON_ACKNOWLEDGEABLE, withClaimStrength } from './admit.js';
import { claimStrength } from '../src/core/claim-strength.js';

/** @typedef {import('../src/core/types.js').Model} Model */
/** @typedef {import('../src/core/types.js').Entity} Entity */
/** @typedef {import('../src/core/types.js').Diagnostic} Diagnostic */

const HERE = path.dirname(fileURLToPath(import.meta.url));
export const REPO_ROOT = path.resolve(HERE, '..');
export const DEFAULT_SPECS = path.join(REPO_ROOT, 'specs');
export const DEFAULT_PROJECT = 'exegra';

const TEST_TIMEOUT_MS = 10 * 60 * 1000;
const TEST_OUTPUT_MAX_BYTES = 64 * 1024 * 1024;
const TEST_OUTPUT_TAIL_LINES = 20;
const BROWSER_TEST_PREFIX = 'tests/browser/';

/** Failure raised by a command. `code` is stable and machine-readable. */
export class CliError extends Error {
  /**
   * @param {string} code
   * @param {string} message
   * @param {{diagnostics?: any[], result?: any}} [extra]
   */
  constructor(code, message, extra = {}) {
    super(message);
    this.name = 'CliError';
    this.code = code;
    this.diagnostics = extra.diagnostics ?? [];
    this.result = extra.result;
  }
}

/** @param {string} name @param {string} message */
const usage = (name, message) => new CliError(`usage.${name}`, message);

/** Options accepted by every command. @type {Record<string, import('node:util').ParseArgsOptionDescriptor>} */
const GLOBAL_OPTIONS = {
  project: { type: 'string' },
  specs: { type: 'string' },
  pretty: { type: 'boolean' },
};

/**
 * Options of the read-only commands that take --project: the project given inline, as a specification
 * file and its product files, with no registration under specs/.
 * @type {Record<string, import('node:util').ParseArgsOptionDescriptor>}
 */
const INLINE_OPTIONS = {
  spec: { type: 'string' },
  product: { type: 'string', multiple: true },
};

// ---------------------------------------------------------------------------
// Serialisation and small helpers
// ---------------------------------------------------------------------------

/** @param {Diagnostic} d */
export function serializeDiagnostic(d) {
  return {
    code: d.code,
    severity: d.severity,
    message: d.message,
    entityId: d.entityId ?? null,
    line: d.loc?.line ?? null,
    column: d.loc?.column ?? null,
    // The product file a diagnostic of a layered project is in; absent for the specification itself.
    ...(d.loc?.file !== undefined ? { file: d.loc.file } : {}),
  };
}

/** @param {Entity} e @param {boolean} withData */
function entityJson(e, withData) {
  /** @type {Record<string, any>} */
  const out = {
    id: e.id,
    kind: e.kind,
    owner: e.owner ?? null,
    label: entityLabel(e),
    source: { line: e.loc.line, column: e.loc.column, ...(e.loc.file !== undefined ? { file: e.loc.file } : {}) },
  };
  if (withData) out.data = e.data;
  return out;
}

/**
 * Path of a reference relative to the entity that holds it, e.g. "from" or "ports.0.contract".
 * @param {Model} model @param {{from: string, path: (string|number)[]}} ref
 */
function viaOf(model, ref) {
  const from = model.entities.get(ref.from);
  return ref.path.slice(from ? from.path.length : 0).map(String).join('.');
}

/** @param {Diagnostic[]} diagnostics */
function countSeverities(diagnostics) {
  const count = (/** @type {string} */ s) => diagnostics.filter((d) => d.severity === s).length;
  return { errors: count('error'), warnings: count('warning'), gaps: count('info') };
}

/**
 * The check and grounding of a claim (src/core/claim-strength.js), as fields of its result.
 * @param {Map<string, import('../src/core/claim-strength.js').Strength>} strength @param {string} claimId
 */
function strengthFields(strength, claimId) {
  const s = strength.get(claimId);
  return s ? { check: s.check, grounding: s.grounding, strength: s.details } : {};
}

/** @param {{status: string}[]} results */
function summarize(results) {
  /** @type {Record<string, number>} */
  const summary = { total: results.length, proved: 0, verified: 0, supported: 0, violated: 0, inconclusive: 0, 'not-evaluated': 0 };
  for (const r of results) {
    if (r.status in summary) summary[r.status] += 1;
  }
  return summary;
}

/**
 * The theorem checks of the model's lean-theorem claims: checked now by Lean when it is installed
 * (tools/lean-theorems.js), merged over the recorded ones; the recorded ones alone otherwise, or
 * when EXEGRA_NO_LEAN=1. Returns the merged map and whether Lean ran.
 * @param {Model} model @param {any} recorded @param {(msg: string) => void} [log]
 * @returns {{theorems: Record<string, any>, checked: boolean}}
 */
function leanTheoremChecks(model, recorded, log) {
  const prior = recorded && typeof recorded === 'object' && recorded.theorems && typeof recorded.theorems === 'object' ? recorded.theorems : {};
  const requests = theoremRequests(model);
  if (!requests.length || process.env.EXEGRA_NO_LEAN === '1') return { theorems: prior, checked: false };
  log?.(`lean: checking ${requests.length} theorem(s)`);
  const r = checkTheorems(requests);
  if (!r.available) {
    log?.(`lean: not checked, the recorded checks are used (${r.reason.split(/\r?\n/)[0]})`);
    return { theorems: prior, checked: false };
  }
  return { theorems: { ...prior, ...r.results }, checked: true };
}

/** The recorded results with fresh Lean theorem checks applied. @param {Model} model @param {any} recorded @param {(msg: string) => void} [log] */
function withLean(model, recorded, log) {
  const { theorems, checked } = leanTheoremChecks(model, recorded, log);
  if (!checked) return recorded ?? undefined;
  return { ...(recorded && typeof recorded === 'object' ? recorded : {}), theorems };
}

/** Split "a,b" into ["a", "b"]; an absent flag gives []. @param {string|undefined} value */
function listValue(value) {
  if (value === undefined) return [];
  return value.split(',').map((s) => s.trim()).filter((s) => s !== '');
}

/** @param {Model} model @param {string} id @param {string} [kind] @returns {Entity} */
function requireEntity(model, id, kind) {
  const e = model.entities.get(id);
  if (!e) throw new CliError('entity.unknown', `No entity has id "${id}".`);
  if (kind && e.kind !== kind) throw new CliError('entity.kind', `"${id}" is a ${e.kind}, not a ${kind}.`);
  return e;
}

/** @param {Project} project @returns {Model} */
function requireModel(project) {
  if (!project.model) {
    throw new CliError('model.unavailable', 'The specification has syntax errors; fix them before running this command.', {
      diagnostics: project.diagnostics.map(serializeDiagnostic),
    });
  }
  return project.model;
}

/** @param {any} ctx @param {number} index @param {string} name */
function positional(ctx, index, name) {
  const value = ctx.positionals[index];
  if (value === undefined || value === '') throw usage('missing-argument', `Missing argument <${name}>.`);
  return value;
}

/** Parse a --faults value and check every id names a fault. @param {Model} model @param {string|undefined} value @returns {string[]|undefined} */
function resolveFaults(model, value) {
  if (value === undefined) return undefined;
  const ids = listValue(value);
  for (const id of ids) requireEntity(model, id, 'fault');
  return ids;
}

/** @param {string} text */
function sha256Hex(text) {
  return createHash('sha256').update(text, 'utf8').digest('hex');
}

/** @param {string} child @param {string} base */
function isInside(base, child) {
  const rel = path.relative(base, child);
  return rel !== '' && !path.isAbsolute(rel) && rel !== '..' && !rel.startsWith(`..${path.sep}`);
}

// ---------------------------------------------------------------------------
// Project loading and input
// ---------------------------------------------------------------------------

/**
 * The project given inline (--spec <file> and --product <file or directory>...), as absolute paths
 * resolved against the working directory; null when the command was given a registered project.
 * @param {any} ctx @returns {{spec: string, products: string[]}|null}
 */
function inlineProject(ctx) {
  const { spec, product } = ctx.values;
  if (spec === undefined) {
    if (product !== undefined) throw usage('invalid-argument', '--product needs --spec: it names a product file of the project given inline.');
    return null;
  }
  if (ctx.values.project !== undefined) throw usage('invalid-argument', 'Give --project or --spec, not both: --spec is the project given inline.');
  return { spec: path.resolve(process.cwd(), spec), products: (product ?? []).map((/** @type {string} */ p) => path.resolve(process.cwd(), p)) };
}

/**
 * Read the project's files and build a Project from them.
 * @param {any} ctx
 */
async function loadProject(ctx) {
  const ws = createWorkspace(ctx.specs);
  const inline = inlineProject(ctx);
  let data;
  try {
    data = inline ? await ws.readInline(inline.spec, inline.products) : await ws.read(ctx.projectName);
  } catch (err) {
    if (err instanceof WorkspaceError && err.code === 'not-found') {
      throw new CliError('project.not-found', inline ? err.message : `Project "${ctx.projectName}" was not found in ${ctx.specs}.`);
    }
    throw err;
  }
  const project = new Project({
    name: ctx.projectName,
    specText: data.spec.text,
    layoutText: data.layout?.text ?? null,
    layers: data.layers.map((/** @type {any} */ l) => ({ file: l.file, text: l.text, platform: l.platform })),
  });
  // Concordance results named by project.jsonc become derived evidence in the recorded results
  // handed to claim evaluation; their diagnostics are reported by validate.
  const applied = applyConcordance(project.model, data.recorded, data.concordance);
  data.recorded = applied.recorded;
  data.concordanceDiagnostics = applied.diagnostics;
  return { ws, data, project };
}

/**
 * The realisation roots project.jsonc declares (none for most projects).
 * @param {any} ws @param {any} ctx
 * @returns {import('../tools/realisation-roots.js').RealisationRoot[]}
 */
function loadRoots(ws, ctx) {
  try {
    return resolveRoots(ws.projectConfig(ctx.projectName));
  } catch (err) {
    if (err instanceof RootsError) throw new CliError(err.code, `${ctx.projectName}/project.jsonc: ${err.message}`);
    throw err;
  }
}

/**
 * project add / remove / list: the link a project is registered by, specs/<name>/project.jsonc
 * ({"spec": "<path relative to the project directory>", "products": [...]}).
 * @param {any} ctx
 */
async function runProjectCommand(ctx) {
  const verb = ctx.positionals[0];
  if (verb !== 'add' && verb !== 'remove' && verb !== 'list') throw usage('missing-argument', 'Give project add <name> --spec <file>, project remove <name> or project list.');
  const ws = createWorkspace(ctx.specs);
  if (verb === 'list') {
    if (ctx.positionals.length > 1 || ctx.values.spec !== undefined || ctx.values.product !== undefined || ctx.values.force) throw usage('invalid-argument', 'project list takes no argument.');
    const out = [];
    for (const p of await ws.listProjects()) {
      const config = ws.projectConfig(p.name);
      out.push({ name: p.name, title: p.title, spec: ws.specLocation(p.name), products: Array.isArray(config?.value.products) ? config.value.products : [] });
    }
    return { result: out };
  }
  const name = positional(ctx, 1, 'name');
  if (ctx.positionals.length > 2) throw usage('invalid-argument', `Unexpected argument "${ctx.positionals[2]}".`);
  if (!isValidProjectName(name)) throw new CliError('name.invalid', `"${name}" is not a valid project name: use lower-case letters, digits, "-" and "_", starting with a letter or digit, at most 64 characters.`);
  const dir = path.join(ctx.specs, name);
  const file = path.join(dir, PROJECT_FILE);
  if (verb === 'remove') {
    if (ctx.values.spec !== undefined || ctx.values.product !== undefined || ctx.values.force) throw usage('invalid-argument', 'project remove takes only the name.');
    if (!fs.existsSync(file)) {
      throw new CliError('project.not-found', fs.existsSync(path.join(dir, 'spec.jsonc'))
        ? `Project "${name}" keeps its specification in ${dir} and is not a registered link; remove it by hand.`
        : `Project "${name}" is not registered in ${ctx.specs}.`);
    }
    fs.rmSync(file);
    // The directory goes with the link only when nothing else (a layout, recorded results, a history) lives in it.
    let removedDirectory = false;
    if (fs.readdirSync(dir).length === 0) { fs.rmdirSync(dir); removedDirectory = true; }
    return { project: name, result: { name, removed: true, removedDirectory } };
  }
  const { spec, product, force } = ctx.values;
  if (spec === undefined) throw usage('missing-argument', 'project add needs --spec <file>.');
  if (fs.existsSync(path.join(dir, 'spec.jsonc'))) throw new CliError('project.exists', `Project "${name}" keeps its own specification (${path.join(dir, 'spec.jsonc')}); a registration would be refused beside it. Choose another name.`);
  const replaced = fs.existsSync(file);
  if (replaced && !force) throw new CliError('project.exists', `Project "${name}" is already registered (${file}); give --force to replace it.`);
  const specAbs = path.resolve(process.cwd(), spec);
  const productsAbs = (product ?? []).map((/** @type {string} */ p) => path.resolve(process.cwd(), p));
  if (!specAbs.endsWith('.jsonc')) throw new CliError('project.invalid', `The specification ${specAbs} must be a .jsonc file.`);
  // Refuse a spec or product that cannot be read before writing anything.
  await ws.readInline(specAbs, productsAbs);
  const rel = (/** @type {string} */ target) => {
    const r = path.relative(dir, target);
    if (path.isAbsolute(r)) throw new CliError('project.invalid', `${target} cannot be written relative to ${dir} (another drive); keep the specs directory and the specification on one drive.`);
    return r.split(path.sep).join('/');
  };
  const link = { spec: rel(specAbs), ...(productsAbs.length ? { products: productsAbs.map(rel) } : {}) };
  fs.mkdirSync(dir, { recursive: true });
  fs.writeFileSync(file, `${JSON.stringify(link, null, 2)}\n`, 'utf8');
  return { project: name, result: { name, file, ...link, replaced } };
}

/** Text of stdin when it is piped, '' when nothing is piped. */
async function readStdin(ctx) {
  if (typeof ctx.stdin === 'string') return ctx.stdin;
  if (process.stdin.isTTY) return '';
  const chunks = [];
  for await (const chunk of process.stdin) chunks.push(chunk);
  return Buffer.concat(chunks).toString('utf8');
}

/**
 * The operations to apply: from --file, from --ops, or from stdin.
 * @param {any} ctx
 * @returns {Promise<any[]>}
 */
async function readOperations(ctx) {
  const { file, ops } = ctx.values;
  if (file !== undefined && ops !== undefined) throw usage('invalid-argument', 'Give --file or --ops, not both.');
  let text;
  if (file !== undefined) {
    try {
      text = fs.readFileSync(path.resolve(process.cwd(), file), 'utf8');
    } catch {
      throw usage('invalid-argument', `Cannot read operations file "${file}".`);
    }
  } else if (ops !== undefined) {
    text = ops;
  } else {
    text = await readStdin(ctx);
    if (!text.trim()) throw usage('missing-argument', 'Give operations with --file, --ops, or on stdin.');
  }
  let parsed;
  try {
    parsed = JSON.parse(text);
  } catch (err) {
    throw usage('invalid-argument', `Operations are not valid JSON: ${/** @type {Error} */ (err).message}`);
  }
  const list = Array.isArray(parsed) ? parsed : [parsed];
  if (!list.every((o) => o !== null && typeof o === 'object' && !Array.isArray(o))) {
    throw usage('invalid-argument', 'Each operation must be a JSON object with a "type" field.');
  }
  return list;
}

/**
 * Write the files a committed transaction changed, each with the base hash read at the start.
 * @param {any} ctx @param {any} ws @param {any} data @param {Project} project
 * @param {string} initialSpec @param {string} initialLayout @param {{label: string, origin: string}} meta
 */
async function writeProjectFiles(ctx, ws, data, project, initialSpec, initialLayout, meta) {
  /** @type {('spec'|'layout')[]} */
  const written = [];
  /** @type {string[]} */
  const journalWarnings = [];
  if (project.specText !== initialSpec) {
    const w = await ws.write(ctx.projectName, 'spec', project.specText, data.spec.hash, meta);
    if (!w.ok) throw new CliError('write.conflict', 'spec.jsonc changed on disk since it was read; nothing was written.');
    written.push('spec');
    if (w.journal && !w.journal.written) journalWarnings.push(`spec: ${w.journal.message}`);
  }
  if (project.layoutText !== initialLayout) {
    const w = await ws.write(ctx.projectName, 'layout', project.layoutText, data.layout?.hash ?? null, meta);
    if (!w.ok) {
      const note = written.length ? ' The specification was already written; the layout was not.' : ' Nothing was written.';
      throw new CliError('write.conflict', `layout.jsonc changed on disk since it was read.${note}`);
    }
    written.push('layout');
    if (w.journal && !w.journal.written) journalWarnings.push(`layout: ${w.journal.message}`);
  }
  return { written, journalWarnings };
}

/**
 * The model with the integrity rules of `--rules <file>` (a JSON array of integrityRule entities)
 * added in memory, so that rules can be tried on a specification without editing it. The ratchet
 * is not applied: the point is to see what a rule finds.
 * @param {any} ctx @param {Project} project
 * @returns {Model}
 */
function modelWithRules(ctx, project) {
  const model = requireModel(project);
  const file = ctx.values.rules;
  if (file === undefined) return model;
  let rules;
  try {
    rules = JSON.parse(fs.readFileSync(path.resolve(process.cwd(), file), 'utf8'));
  } catch (err) {
    throw usage('invalid-argument', `Cannot read rules file "${file}": ${/** @type {Error} */ (err).message}`);
  }
  if (!Array.isArray(rules) || !rules.every((r) => r && typeof r === 'object' && !Array.isArray(r))) throw usage('invalid-argument', 'The rules file must be a JSON array of integrityRule entities.');
  const tx = new Tx(project.specText, project.layoutText, project.baseModel ?? model);
  try {
    for (const data of rules) OPERATIONS.CreateEntity.apply(tx, { type: 'CreateEntity', kind: 'integrityRule', data });
  } catch (err) {
    if (err instanceof OpError) throw new CliError(err.code, err.message, { diagnostics: err.diagnostics.map(serializeDiagnostic) });
    throw err;
  }
  const a = project.layers.length ? analyzeLayers(tx.specText, project.layers) : analyzeSpec(tx.specText);
  if (!a.model || a.errorCount) throw new CliError('validation.failed', 'The specification with these rules has validation errors.', { diagnostics: a.diagnostics.filter((d) => d.severity === 'error').map(serializeDiagnostic) });
  return a.model;
}

/** Integrity rule ids: the one named, or all. @param {any} ctx @param {Model} model */
function selectRules(ctx, model) {
  const id = ctx.positionals[0];
  const all = (model.byKind.integrityRule ?? []).map((r) => r.id);
  if (id === undefined) return all;
  requireEntity(model, id, 'integrityRule');
  return [id];
}

/**
 * Run a scenario to completion, mapping engine failures to a command error.
 * @param {Model} model @param {string} scenarioId @param {string[]|undefined} faults
 */
function runTrace(model, scenarioId, faults) {
  try {
    return runScenario(model, scenarioId, faults === undefined ? {} : { faults });
  } catch (err) {
    throw new CliError('simulate.failed', /** @type {Error} */ (err).message);
  }
}

// ---------------------------------------------------------------------------
// verify
// ---------------------------------------------------------------------------

/**
 * Read the summary counts of a node:test run: "# tests N" / "# pass N" / "# fail N"
 * (tap reporter) or "ℹ tests N" (spec reporter). Null when no tests line is found.
 * @param {string} output
 * @returns {{tests: number, pass: number, fail: number}|null}
 */
export function parseTestCounts(output) {
  /** @type {Record<string, number>} */
  const found = {};
  for (const m of String(output).matchAll(/^[ \t]*(?:#|ℹ)[ \t]+(tests|pass|fail)[ \t]+(\d+)[ \t]*$/gm)) found[m[1]] = Number(m[2]);
  if (found.tests === undefined) return null;
  return { tests: found.tests, pass: found.pass ?? 0, fail: found.fail ?? 0 };
}

/** @param {string} t */
const stripAnsi = (t) => String(t).replace(/\x1b\[[0-9;]*m/g, '');

/**
 * Number of tests Playwright's summary line reports as passed (0 when none ran or all skipped).
 * @param {string} output the list reporter's text
 */
export function countPassedBrowserTests(output) {
  const m = stripAnsi(output).match(/\b(\d+) passed\b/);
  return m ? Number(m[1]) : 0;
}

/**
 * Number of passing top-level tests in node's TAP output, not counting the
 * entry node prints for the test file itself. When a name pattern matches no
 * test, node still exits 0 and reports the file as one passing test; this
 * count is then 0, which is how an empty run is recognised.
 * @param {string} output TAP text @param {string} file the test file that was run
 */
export function countPassingTests(output, file) {
  const norm = (/** @type {string} */ t) => t.replace(/\\+/g, '/').trim();
  const target = norm(file);
  let n = 0;
  for (const m of String(output).matchAll(/^ok \d+ - (.*)$/gm)) {
    // A skipped test is reported as "ok ... # SKIP"; it ran nothing, so it is not a pass.
    if (/#\s*SKIP\b/i.test(m[1])) continue;
    const name = norm(m[1]);
    if (name === target || name.endsWith('/' + target) || target.endsWith('/' + name)) continue;
    n++;
  }
  return n;
}

/**
 * The `results` object to record after a verify run. A run that skipped (browser evidence under --skip-browser,
 * or a test that skipped itself) did not execute, so it keeps the outcome recorded before rather than erasing it;
 * with no earlier outcome it records nothing. Outcomes that ran replace the earlier ones.
 * @param {Record<string, any>} prior the `results` object recorded before this run
 * @param {{id: string, outcome: 'pass'|'fail'|'skipped'|'not-run', detail?: string, ranAt: string, obtained?: 'run'|'reused'}[]} runs this run, per evidence id (not-run: a realisation root's test that did not run)
 * @returns {Record<string, any>}
 */
export function mergeRecordedResults(prior, runs) {
  /** @type {Record<string, any>} */
  const results = {};
  for (const run of runs) {
    if (run.outcome === 'skipped') {
      if (Object.hasOwn(prior, run.id)) results[run.id] = prior[run.id];
      continue;
    }
    results[run.id] = { outcome: run.outcome, ...(run.detail !== undefined ? { detail: run.detail } : {}), ranAt: run.ranAt, ...(run.obtained ? { obtained: run.obtained } : {}) };
  }
  return results;
}

/**
 * Execute one test evidence reference.
 * @param {string} ref
 * @param {{repoRoot: string, skipBrowser: boolean, log: (m: string) => void, reuse?: ReturnType<typeof createOutcomeReuse>|null}} env
 * @returns {{outcome: 'pass'|'fail'|'skipped', detail?: string, obtained: 'run'|'reused', ranAt?: string}}
 */
function runTestReference(ref, env) {
  const problem = testRefProblem(ref);
  if (problem) return { outcome: 'fail', detail: `unsafe reference: ${describeTestRefProblem(ref, problem)}`, obtained: 'run' };
  const hashAt = ref.indexOf('#');
  const file = (hashAt < 0 ? ref : ref.slice(0, hashAt)).trim();
  const pattern = hashAt < 0 ? '' : ref.slice(hashAt + 1).trim();
  const abs = path.resolve(env.repoRoot, file);
  if (!isInside(env.repoRoot, abs)) return { outcome: 'fail', detail: 'unsafe reference', obtained: 'run' };
  if (!fs.existsSync(abs) || !fs.statSync(abs).isFile()) return { outcome: 'fail', detail: 'test file not found', obtained: 'run' };

  const browser = file.startsWith(BROWSER_TEST_PREFIX);
  if (browser && env.skipBrowser) return { outcome: 'skipped', obtained: 'run' };

  const hit = env.reuse?.lookup(ref, browser);
  if (hit) {
    env.log(`verify: reusing the recorded outcome of ${ref}`);
    return { ...hit, obtained: 'reused' };
  }

  const isWin = process.platform === 'win32';
  env.log(`verify: running ${ref}`);
  /** @type {import('node:child_process').SpawnSyncReturns<string>} */
  let run;
  if (browser) {
    // npx is a .cmd shim on Windows and needs a shell. The reference is limited to
    // SAFE_TEST_REF (no quotes or shell metacharacters), so quoting it is sufficient.
    const args = ['playwright', 'test', isWin ? `"${file}"` : file];
    if (pattern) args.push('-g', isWin ? `"${pattern}"` : pattern);
    run = spawnSync('npx', args, {
      cwd: env.repoRoot, shell: isWin, encoding: 'utf8', timeout: TEST_TIMEOUT_MS,
      maxBuffer: TEST_OUTPUT_MAX_BYTES, windowsHide: true,
    });
  } else {
    const args = ['--test', '--test-reporter=tap'];
    if (pattern) args.push(`--test-name-pattern=${pattern}`);
    args.push(file);
    run = spawnSync(process.execPath, args, {
      cwd: env.repoRoot, shell: false, encoding: 'utf8', timeout: TEST_TIMEOUT_MS,
      maxBuffer: TEST_OUTPUT_MAX_BYTES, windowsHide: true,
    });
  }
  if (run.status === 0) {
    if (browser) {
      // playwright exits 0 when every selected test skipped, and when the pattern matched nothing.
      const out = String(run.stdout ?? '');
      if (countPassedBrowserTests(out) === 0) {
        if (/\b[1-9]\d* skipped\b/.test(stripAnsi(out))) return { outcome: 'skipped', detail: 'the matching test skipped itself', obtained: 'run' };
        return { outcome: 'fail', detail: 'the reference matched no test', obtained: 'run' };
      }
    } else {
      // node exits 0 when the pattern or file matches no test; that is not a pass.
      if (countPassingTests(String(run.stdout ?? ''), file) === 0) {
        // A test that matched but skipped itself (a gated fixture, a missing tool) ran nothing: it is not
        // evidence either way, so it is recorded as skipped rather than as a failure.
        if (/^ok \d+ - .*#\s*SKIP\b/im.test(String(run.stdout ?? ''))) return { outcome: 'skipped', detail: 'the matching test skipped itself', obtained: 'run' };
        return { outcome: 'fail', detail: 'the reference matched no test', obtained: 'run' };
      }
    }
    return { outcome: 'pass', obtained: 'run' };
  }
  if (run.error) return { outcome: 'fail', detail: run.error.message, obtained: 'run' };
  const lines = `${run.stdout ?? ''}${run.stderr ?? ''}`.replace(/\s+$/, '').split(/\r?\n/);
  return { outcome: 'fail', detail: lines.slice(-TEST_OUTPUT_TAIL_LINES).join('\n'), obtained: 'run' };
}

/**
 * The verification pipeline. See docs/agent-interface.md.
 * @param {any} ctx
 */
async function runVerify(ctx) {
  const { ws, data, project } = await loadProject(ctx);
  if (!project.model) {
    throw new CliError('verify.failed', 'The specification has syntax errors; verification did not run.', {
      diagnostics: project.diagnostics.map(serializeDiagnostic),
    });
  }
  const model = project.model;
  const expectViolated = listValue(ctx.values['expect-violated']);
  for (const id of expectViolated) requireEntity(model, id, 'claim');

  // (1) validation
  const counts = countSeverities(project.diagnostics);
  const validationErrors = project.diagnostics.filter((d) => d.severity === 'error').map(serializeDiagnostic);

  // (2) traceability
  const roots = loadRoots(ws, ctx);
  const traceability = checkTraceability(model, ctx.repoRoot, roots);

  // (3) execute test evidence; evidence in a realisation root comes from its JUnit reports
  const skipBrowser = ctx.values['skip-browser'] === true;
  const testEvidence = (model.byKind.evidence ?? []).filter((ev) => ev.data.kind === 'test');
  const externalEvidence = roots.length
    ? testEvidence.filter((ev) => splitRootRef(String(ev.data.ref)) !== null).map((ev) => ({ id: ev.id, ref: String(ev.data.ref) }))
    : [];
  const external = collectExternalResults(externalEvidence, roots, { ingestOnly: ctx.values['ingest-only'] === true, log: ctx.log });
  // Outcomes recorded by earlier runs. A skipped run keeps these rather than erasing them.
  // Outcomes that `npm test` and `npm run test:browser` recorded on this very tree are reused (cli/outcomes.js).
  const reuse = ctx.values.fresh === true ? null : createOutcomeReuse(ctx.repoRoot, treeStamp(ctx.repoRoot));
  if (reuse) for (const [kind, why] of Object.entries(reuse.notes)) ctx.log(`verify: not reusing ${kind} outcomes: ${why}`);
  const priorRecorded = (await ws.read(ctx.projectName)).recorded;
  const priorResults = priorRecorded && typeof priorRecorded === 'object' && priorRecorded.results && typeof priorRecorded.results === 'object'
    ? priorRecorded.results : {};
  /** @type {{id: string, outcome: 'pass'|'fail'|'skipped'|'not-run', detail?: string, ranAt: string, obtained?: 'run'|'reused'}[]} */
  const runs = [];
  /** @type {Record<string, any>[]} */
  const evidence = [];
  for (const ev of model.byKind.evidence ?? []) {
    const base = { id: ev.id, kind: ev.data.kind, ref: ev.data.ref, claim: ev.data.claim };
    if (ev.data.kind !== 'test') {
      evidence.push({ ...base, outcome: 'not-executed' });
      continue;
    }
    const ext = external.results.get(ev.id);
    if (ext) {
      const ranAt = ext.ranAt ?? new Date().toISOString();
      runs.push({ id: ev.id, outcome: ext.outcome, ...(ext.detail !== undefined ? { detail: ext.detail } : {}), ranAt });
      evidence.push({ ...base, ...ext, ranAt });
      continue;
    }
    const run = runTestReference(String(ev.data.ref), { repoRoot: ctx.repoRoot, skipBrowser, log: ctx.log, reuse });
    const ranAt = run.ranAt ?? new Date().toISOString();
    runs.push({ id: ev.id, outcome: run.outcome, ...(run.detail !== undefined ? { detail: run.detail } : {}), ranAt, obtained: run.obtained });
    if (run.outcome === 'skipped') {
      const kept = priorResults[ev.id];
      evidence.push({ ...base, outcome: 'skipped', ...(kept ? { recorded: { outcome: kept.outcome, ranAt: kept.ranAt } } : {}) });
      continue;
    }
    evidence.push({ ...base, outcome: run.outcome, obtained: run.obtained, ...(run.detail !== undefined ? { detail: run.detail } : {}), ranAt });
  }
  const results = mergeRecordedResults(priorResults, runs);
  // A root's results also carry the root and its reports, which the merge would drop.
  for (const [id, ext] of external.results) results[id] = ext;

  // (4) record the results
  // Outcomes an external verification tool recorded per claim live in the same
  // file; this command owns only `results` and `traceability` and keeps the rest.
  /** @type {Record<string, any>} */
  const kept = {};
  const prior = priorRecorded;
  if (prior && typeof prior === 'object') for (const k of ['tool', 'version', 'source', 'claims', 'lint']) if (Object.hasOwn(prior, k)) kept[k] = /** @type {any} */ (prior)[k];
  // (4b) the Lean checks of the lean-theorem claims; without Lean the recorded checks are kept
  const { theorems } = leanTheoremChecks(model, prior, ctx.log);
  await ws.writeRecorded(ctx.projectName, { ...kept, results, traceability, ...(Object.keys(theorems).length ? { theorems } : {}) });

  // (5) re-evaluate the claims with the new results
  const claimResults = evaluateClaims(model, { recorded: { results, theorems, ...(data.recorded?.derived ? { derived: data.recorded.derived } : {}) } });
  const violated = claimResults.filter((r) => r.status === 'violated').map((r) => r.claimId);
  const unexpectedViolated = violated.filter((id) => !expectViolated.includes(id));
  const failedEvidence = evidence.filter((e) => e.outcome === 'fail');

  const result = {
    validation: { errors: counts.errors, warnings: counts.warnings, gaps: counts.gaps },
    traceability,
    evidence,
    ...(roots.length ? { roots: external.reports, notRun: evidence.filter((e) => e.outcome === 'not-run').map((e) => e.id) } : {}),
    claims: {
      summary: summarize(claimResults),
      violated,
      expectedViolated: violated.filter((id) => expectViolated.includes(id)),
      unexpectedViolated,
    },
  };

  const problems = [];
  if (counts.errors) problems.push(`${counts.errors} validation error(s)`);
  if (failedEvidence.length) problems.push(`${failedEvidence.length} evidence item(s) failed`);
  if (unexpectedViolated.length) problems.push(`${unexpectedViolated.length} claim(s) violated`);
  if (problems.length) {
    throw new CliError('verify.failed', `Verification failed: ${problems.join(', ')}.`, { diagnostics: validationErrors, result });
  }
  return { result, semanticHash: project.semanticHash };
}

// ---------------------------------------------------------------------------
// Command table
// ---------------------------------------------------------------------------

/**
 * @typedef {{usage: string, summary: string, options?: Record<string, any>, run: (ctx: any) => Promise<{result: any, semanticHash?: string, project?: string}>}} CommandDef
 */

/** @type {Record<string, CommandDef>} */
export const COMMANDS = {
  projects: {
    usage: 'projects',
    summary: 'List the projects in the specs directory.',
    run: async (ctx) => {
      const list = await createWorkspace(ctx.specs).listProjects();
      return { result: list.map((p) => ({ name: p.name, title: p.title })) };
    },
  },

  project: {
    usage: 'project add <name> --spec <file> [--product <file or directory>]... [--force] | project remove <name> | project list',
    summary: 'Register a spec file (and product files) as project <name> under specs/, remove such a registration, or list the projects with where their specification is.',
    options: { spec: { type: 'string' }, product: { type: 'string', multiple: true }, force: { type: 'boolean' } },
    run: async (ctx) => runProjectCommand(ctx),
  },

  validate: {
    usage: 'validate',
    summary: 'Validate the project. ok is true only when there are no errors.',
    options: { ...INLINE_OPTIONS },
    run: async (ctx) => {
      const { data, project } = await loadProject(ctx);
      const counts = countSeverities(project.diagnostics);
      /** @type {Record<string, any>} */
      const result = { ...counts, diagnostics: project.diagnostics.map(serializeDiagnostic), concordance: data.concordanceDiagnostics };
      // A layered project (product files in project.jsonc): semanticHash stays the platform's alone, the
      // combined model's hash is layeredHash, and each product file is listed with what it declares.
      if (project.layers.length) {
        result.layeredHash = project.layeredHash;
        result.products = project.layerSummary;
      }
      if (counts.errors > 0) {
        throw new CliError('validation.failed', `${counts.errors} validation error(s).`, { diagnostics: result.diagnostics, result });
      }
      return { result, semanticHash: project.semanticHash };
    },
  },

  list: {
    usage: 'list [--kind <kind>] [--owner <id>]',
    summary: 'List entities in declaration order (without data).',
    options: { kind: { type: 'string' }, owner: { type: 'string' }, ...INLINE_OPTIONS },
    run: async (ctx) => {
      const { project } = await loadProject(ctx);
      const model = requireModel(project);
      const { kind, owner } = ctx.values;
      if (kind !== undefined && !model.meta.entities[kind]) throw usage('invalid-argument', `Unknown entity kind "${kind}".`);
      const result = [];
      for (const e of model.entities.values()) {
        if (kind !== undefined && e.kind !== kind) continue;
        if (owner !== undefined && e.owner !== owner) continue;
        result.push(entityJson(e, false));
      }
      return { result, semanticHash: project.semanticHash };
    },
  },

  show: {
    usage: 'show <id>',
    summary: 'One entity with its data, owned entities and inbound references; components add relationships, children and ancestors.',
    options: { ...INLINE_OPTIONS },
    run: async (ctx) => {
      const { project } = await loadProject(ctx);
      const model = requireModel(project);
      const e = requireEntity(model, positional(ctx, 0, 'id'));
      /** @type {Record<string, any>} */
      const result = {
        ...entityJson(e, true),
        ownedEntities: [...model.entities.values()].filter((x) => x.owner === e.id).map((x) => x.id),
        referencedBy: inboundRefs(model, e.id).map((r) => ({ from: r.from, via: viaOf(model, r) })),
      };
      if (e.kind === 'component') {
        result.relationships = relationshipsOf(model, e.id).map((r) => ({
          id: r.relationship.id,
          kind: r.relationship.data.kind,
          direction: r.direction,
          other: r.other?.id ?? null,
        }));
        result.children = childrenOf(model, e.id).map((c) => c.id);
        result.ancestors = ancestorsOf(model, e.id);
      }
      return { result, semanticHash: project.semanticHash };
    },
  },

  deps: {
    usage: 'deps <id> [--direction out|in] [--transitive] [--kinds a,b]',
    summary: 'Dependencies of a component. Default: what it depends on, direct only.',
    options: { direction: { type: 'string' }, transitive: { type: 'boolean' }, kinds: { type: 'string' }, ...INLINE_OPTIONS },
    run: async (ctx) => {
      const { project } = await loadProject(ctx);
      const model = requireModel(project);
      const id = positional(ctx, 0, 'id');
      requireEntity(model, id, 'component');
      const direction = ctx.values.direction ?? 'out';
      if (direction !== 'out' && direction !== 'in') throw usage('invalid-argument', '--direction must be "out" or "in".');
      const kinds = listValue(ctx.values.kinds);
      const result = dependencies(model, id, {
        direction,
        transitive: ctx.values.transitive === true,
        kinds: kinds.length ? kinds : undefined,
      });
      return { result, semanticHash: project.semanticHash };
    },
  },

  contracts: {
    usage: 'contracts [<componentId>]',
    summary: 'All contracts, or the contracts bound to one component through its ports and relationships.',
    options: { ...INLINE_OPTIONS },
    run: async (ctx) => {
      const { project } = await loadProject(ctx);
      const model = requireModel(project);
      const id = ctx.positionals[0];
      if (id === undefined) {
        return { result: { contracts: (model.byKind.contract ?? []).map((c) => entityJson(c, true)) }, semanticHash: project.semanticHash };
      }
      requireEntity(model, id, 'component');
      const bindings = contractsOf(model, id).map((b) => ({ contract: b.contract.id, via: b.via, role: b.role }));
      const ids = [...new Set(bindings.map((b) => b.contract))];
      const contracts = ids.map((cid) => entityJson(requireEntity(model, cid), true));
      return { result: { component: id, bindings, contracts }, semanticHash: project.semanticHash };
    },
  },

  claims: {
    usage: 'claims [--status <status>]',
    summary: 'Evaluated claim results, with the recorded evidence results applied.',
    options: { status: { type: 'string' }, ...INLINE_OPTIONS },
    run: async (ctx) => {
      const { data, project } = await loadProject(ctx);
      const model = requireModel(project);
      const { status } = ctx.values;
      if (status !== undefined && !(status in CLAIM_STATUSES)) {
        throw usage('invalid-argument', `--status must be one of: ${Object.keys(CLAIM_STATUSES).join(', ')}.`);
      }
      const strength = claimStrength(model);
      const result = evaluateClaims(model, { recorded: withLean(model, data.recorded, ctx.log) })
        .map((r) => {
          const claim = model.entities.get(r.claimId);
          return { ...r, statement: claim?.data.statement ?? null, kind: claim?.data.kind ?? r.kind, ...strengthFields(strength, r.claimId) };
        })
        .filter((r) => status === undefined || r.status === status);
      return { result, semanticHash: project.semanticHash };
    },
  },

  evaluate: {
    usage: 'evaluate [<claimId>]',
    summary: 'Evaluate one claim or all claims. A violated claim is a finding; the command still succeeds.',
    options: { ...INLINE_OPTIONS },
    run: async (ctx) => {
      const { data, project } = await loadProject(ctx);
      const model = requireModel(project);
      const recorded = withLean(model, data.recorded, ctx.log);
      const id = ctx.positionals[0];
      const strength = claimStrength(model);
      const results = (id !== undefined
        ? [evaluateClaim(model, requireEntity(model, id, 'claim').id, { recorded })]
        : evaluateClaims(model, { recorded })).map((r) => ({ ...r, ...strengthFields(strength, r.claimId) }));
      return { result: { results, summary: summarize(results) }, semanticHash: project.semanticHash };
    },
  },

  gaps: {
    usage: 'gaps',
    summary: 'Unspecified or inconsistent things: warnings and gaps, open unknowns, unevaluated claims, components without realisation.',
    options: { ...INLINE_OPTIONS },
    run: async (ctx) => {
      const { data, project } = await loadProject(ctx);
      const model = requireModel(project);
      const components = model.byKind.component ?? [];
      /** @type {{component: string, text: string}[]} */
      const unknowns = [];
      for (const c of components) {
        if (!Array.isArray(c.data.unknowns)) continue;
        for (const text of c.data.unknowns) unknowns.push({ component: c.id, text });
      }
      const results = evaluateClaims(model, { recorded: data.recorded ?? undefined });
      const result = {
        diagnostics: project.diagnostics.filter((d) => d.severity !== 'error').map(serializeDiagnostic),
        unknowns,
        unevaluatedClaims: results.filter((r) => r.status === 'not-evaluated').map((r) => r.claimId),
        undeclaredRealisation: components.filter((c) => c.data.implementation === undefined).map((c) => c.id),
      };
      return { result, semanticHash: project.semanticHash };
    },
  },

  ops: {
    usage: 'ops',
    summary: 'The operation protocol: every operation with its parameters, preconditions, effects and persistence.',
    run: async () => ({
      result: {
        operations: Object.entries(OPERATIONS).map(([type, def]) => ({
          type,
          doc: def.doc,
          params: def.params,
          preconditions: def.preconditions,
          effects: def.effects,
          persistence: def.persistence,
          semantic: def.semantic,
        })),
      },
    }),
  },

  apply: {
    usage: "apply [--file <ops.json> | --ops '<json>'] [--expect-hash <hash>] [--dry-run] [--label <text>]",
    summary: 'Apply one operation or an array atomically through the validated pipeline, then write the changed files.',
    options: {
      file: { type: 'string' },
      ops: { type: 'string' },
      'expect-hash': { type: 'string' },
      'dry-run': { type: 'boolean' },
      label: { type: 'string' },
    },
    run: async (ctx) => {
      const list = await readOperations(ctx);
      const { ws, data, project } = await loadProject(ctx);
      const initialSpec = project.specText;
      const initialLayout = project.layoutText;
      const hashBefore = project.semanticHash;
      const { label } = ctx.values;
      const tx = project.apply(list, { label, origin: 'cli', expectHash: ctx.values['expect-hash'] });
      if (!tx.ok) {
        throw new CliError(tx.code ?? 'apply.failed', tx.message ?? 'The transaction was rejected.', {
          diagnostics: tx.diagnostics.map(serializeDiagnostic),
        });
      }

      const dryRun = ctx.values['dry-run'] === true;
      const { written, journalWarnings } = dryRun
        ? { written: /** @type {('spec'|'layout')[]} */ ([]), journalWarnings: /** @type {string[]} */ ([]) }
        : await writeProjectFiles(ctx, ws, data, project, initialSpec, initialLayout, { label: label ?? list.map((o) => o.type).join(', '), origin: 'cli' });

      const result = {
        revision: project.revision,
        semanticHashBefore: hashBefore,
        semanticHashAfter: project.semanticHash,
        semanticChanged: tx.semanticChanged,
        affected: tx.affected,
        written,
        dryRun,
        ...(journalWarnings.length ? { journalWarnings } : {}),
      };
      return { result, semanticHash: dryRun ? hashBefore : project.semanticHash };
    },
  },

  admit: {
    usage: "admit [--file <ops.json> | --ops '<json>'] [--label <text>] [--write] [--accept <code[,code...]>]...",
    summary: "Admit a change set only if everything the specification held still holds and the change's own claims hold: the before/after diff and a verdict with every reason. Writes only with --write and only when admitted; fails with admit.rejected otherwise.",
    options: { file: { type: 'string' }, ops: { type: 'string' }, label: { type: 'string' }, write: { type: 'boolean' }, accept: { type: 'string', multiple: true } },
    run: async (ctx) => {
      const accept = (/** @type {string[]} */ (ctx.values.accept ?? [])).flatMap(listValue);
      const fixed = accept.filter((c) => NON_ACKNOWLEDGEABLE.has(c));
      if (fixed.length) throw new CliError('admit.not-acknowledgeable', `Cannot accept ${fixed.join(', ')}: a reason without "acknowledgeable" is a failure to fix, not a decision to accept.`);
      const list = await readOperations(ctx);
      const { ws, data, project } = await loadProject(ctx);
      const beforeModel = requireModel(project);
      const initialSpec = project.specText;
      const initialLayout = project.layoutText;
      const hashBefore = project.semanticHash;
      const { label } = ctx.values;
      const write = ctx.values.write === true;
      const before = snapshot(beforeModel, project.diagnostics, evaluateClaims(beforeModel, { recorded: withLean(beforeModel, data.recorded, ctx.log) }));
      // The transaction runs on this in-memory project; nothing reaches disk unless the verdict allows it.
      const tx = project.apply(list, { label, origin: 'cli' });
      /** @type {any} */
      let report;
      if (!tx.ok) {
        const diagnostics = tx.diagnostics.map(serializeDiagnostic);
        report = {
          verdict: 'rejected',
          reasons: [{ code: 'admit.transaction-refused', transactionCode: tx.code, message: tx.message ?? 'The transaction was refused.', diagnostics }],
          transaction: { accepted: false, code: tx.code, message: tx.message, diagnostics },
          diff: null,
          counts: { before: sideCounts(before) },
        };
      } else {
        const afterModel = requireModel(project);
        const after = snapshot(afterModel, project.diagnostics, evaluateClaims(afterModel, { recorded: withLean(afterModel, data.recorded, ctx.log) }));
        report = { ...withClaimStrength(compare(before, after, { accept }), beforeModel, afterModel, accept), transaction: { accepted: true, affected: [...tx.affected].sort(), semanticChanged: tx.semanticChanged } };
      }
      if (report.refusedAccept) {
        throw new CliError('admit.not-acknowledgeable', `Cannot accept ${report.refusedAccept.join(', ')}: the reason is not acknowledgeable.`, { result: report });
      }
      const admitted = report.verdict === 'admitted';
      /** @type {string[]} */
      let written = [];
      /** @type {string[]} */
      let journalWarnings = [];
      if (admitted && write) {
        ({ written, journalWarnings } = await writeProjectFiles(ctx, ws, data, project, initialSpec, initialLayout, { label: label ?? list.map((o) => o.type).join(', '), origin: 'cli' }));
      }
      const result = {
        ...report,
        semanticHashBefore: hashBefore,
        semanticHashAfter: admitted ? project.semanticHash : hashBefore,
        written,
        ...(journalWarnings.length ? { journalWarnings } : {}),
      };
      if (!admitted) {
        throw new CliError('admit.rejected', `Rejected: ${report.reasons.map((/** @type {any} */ r) => r.code + (r.id ? ` (${r.id})` : '')).join(', ')}. Nothing was written.`, { result });
      }
      return { result, semanticHash: write ? project.semanticHash : hashBefore };
    },
  },

  'plan-delete': {
    usage: 'plan-delete <id>',
    summary: 'What a cascade delete of an entity would remove and repair. Changes nothing.',
    options: { ...INLINE_OPTIONS },
    run: async (ctx) => {
      const { project } = await loadProject(ctx);
      const model = requireModel(project);
      const id = positional(ctx, 0, 'id');
      requireEntity(model, id);
      return { result: planDelete(model, id), semanticHash: project.semanticHash };
    },
  },

  simulate: {
    usage: 'simulate <scenarioId> [--faults a,b] [--steps]',
    summary: 'Run a scenario and check the invariant and temporal claims and the contract events that apply to its trace. Contract events are also listed as a request log.',
    options: { faults: { type: 'string' }, steps: { type: 'boolean' }, ...INLINE_OPTIONS },
    run: async (ctx) => {
      const { project } = await loadProject(ctx);
      const model = requireModel(project);
      const id = requireEntity(model, positional(ctx, 0, 'scenarioId'), 'scenario').id;
      const trace = runTrace(model, id, resolveFaults(model, ctx.values.faults));
      /** @type {Record<string, any>} */
      const result = {
        scenarioId: id,
        faults: trace.faults,
        outcome: trace.outcome,
        stepCount: trace.steps.length,
        final: trace.final,
        checks: checkTrace(model, trace),
      };
      const log = requestLog(model, trace);
      if (log.length) result.requestLog = log.map((e) => `#${e.step} t=${e.time} ${e.text}`);
      if (ctx.values.steps === true) result.steps = trace.steps;
      return { result, semanticHash: project.semanticHash };
    },
  },

  prove: {
    usage: 'prove <scenarioId> [--bound N] [--max-states N] [--steps]',
    summary: 'Explore every configuration of a scenario within a bound (every order of simultaneous events, every subset of its faults) with the verified explorer of the Lean semantics, and check each state-invariant claim that lists it in Lean: holds for all N configurations, or a counterexample run. Temporal claims (never, precedes, eventually) are checked on every complete run: holds, a violating run, or incomplete. Needs lake.',
    options: { bound: { type: 'string' }, 'max-states': { type: 'string' }, steps: { type: 'boolean' }, ...INLINE_OPTIONS },
    run: async (ctx) => {
      const { project } = await loadProject(ctx);
      const model = requireModel(project);
      const id = requireEntity(model, positional(ctx, 0, 'scenarioId'), 'scenario').id;
      /** @param {string} name */
      const count = (name) => {
        const v = ctx.values[name];
        if (v === undefined) return undefined;
        const n = Number(v);
        if (!Number.isInteger(n) || n < 1) throw usage('invalid-argument', `--${name} must be a positive integer.`);
        return n;
      };
      try {
        const result = proveScenario(model, id, { bound: count('bound'), maxStates: count('max-states'), withSteps: ctx.values.steps === true, log: ctx.log });
        return { result, semanticHash: project.semanticHash };
      } catch (err) {
        if (err instanceof ProveError) throw new CliError(err.code, err.message);
        throw err;
      }
    },
  },

  integrity: {
    usage: 'integrity [<ruleId>] [--rules <file>] [--limit N]',
    summary: 'Evaluate the integrity rules (or one): holds with the number of instances checked, or violated with counterexamples (bindings, entity ids, lines); vacuous rules are flagged. --rules adds rules from a JSON file in memory. Fails when an error rule is violated or a rule is invalid.',
    options: { rules: { type: 'string' }, limit: { type: 'string' }, ...INLINE_OPTIONS },
    run: async (ctx) => {
      const { project } = await loadProject(ctx);
      const model = modelWithRules(ctx, project);
      const ids = new Set(selectRules(ctx, model));
      const limit = ctx.values.limit === undefined ? 20 : Number(ctx.values.limit);
      if (!Number.isInteger(limit) || limit < 0) throw usage('invalid-argument', '--limit must be a non-negative integer.');
      const rules = evaluateIntegrity(model).filter((r) => ids.has(r.ruleId)).map((r) => ({
        ruleId: r.ruleId, severity: r.severity, status: r.status, statement: r.statement,
        instances: r.instances, vacuous: r.vacuous, counterexampleCount: r.counterexamples.length,
        counterexamples: r.counterexamples.slice(0, limit).map((c) => counterexampleJson(model, c)),
        ms: Math.round(r.ms * 10) / 10, ...(r.problem ? { problem: r.problem } : {}),
      }));
      const result = { total: rules.length, holds: rules.filter((r) => r.status === 'holds').length, violated: rules.filter((r) => r.status === 'violated').length, invalid: rules.filter((r) => r.status === 'invalid').length, rules };
      const failing = rules.filter((r) => r.status === 'invalid' || (r.status === 'violated' && r.severity === 'error'));
      if (failing.length) throw new CliError('integrity.violated', `${failing.length} integrity rule(s) violated or invalid: ${failing.map((r) => r.ruleId).join(', ')}.`, { result });
      return { result, semanticHash: project.semanticHash };
    },
  },

  'prove-integrity': {
    usage: 'prove-integrity [<ruleId>] [--rules <file>] [--max-witnesses N] [--timeout S] [--max-candidates N]',
    summary: 'Prove or refute integrity rules in Lean: holds (a kernel-checked proof by reflection), violated (a kernel-checked refutation from each concrete witness, up to --max-witnesses, default 10), or incomplete. The Lean checker and the JavaScript evaluator must agree. Each Lean process stops after --timeout seconds (default 300), and a rule whose relations have more than --max-candidates candidate tuples (default 500) is not sent to the kernel; both make the rule incomplete. Needs lake. Fails when a rule is incomplete.',
    options: { rules: { type: 'string' }, 'max-witnesses': { type: 'string' }, timeout: { type: 'string' }, 'max-candidates': { type: 'string' }, ...INLINE_OPTIONS },
    run: async (ctx) => {
      const { project } = await loadProject(ctx);
      const model = modelWithRules(ctx, project);
      const ids = selectRules(ctx, model);
      const mw = ctx.values['max-witnesses'] === undefined ? undefined : Number(ctx.values['max-witnesses']);
      if (mw !== undefined && !(Number.isInteger(mw) && mw >= 1)) throw usage('invalid-argument', '--max-witnesses must be a positive integer.');
      const to = ctx.values.timeout === undefined ? undefined : Number(ctx.values.timeout);
      if (to !== undefined && !(Number.isFinite(to) && to > 0)) throw usage('invalid-argument', '--timeout must be a positive number of seconds.');
      const mc = ctx.values['max-candidates'] === undefined ? undefined : Number(ctx.values['max-candidates']);
      if (mc !== undefined && !(Number.isInteger(mc) && mc >= 0)) throw usage('invalid-argument', '--max-candidates must be a non-negative integer.');
      let rules;
      try {
        rules = proveIntegrity(model, ids, { maxWitnesses: mw, timeoutMs: to === undefined ? undefined : Math.round(to * 1000), maxCandidates: mc, log: ctx.log });
      } catch (err) {
        if (err instanceof ProveError) throw new CliError(err.code, err.message);
        throw err;
      }
      const result = { total: rules.length, holds: rules.filter((r) => r.result === 'holds').length, violated: rules.filter((r) => r.result === 'violated').length, incomplete: rules.filter((r) => r.result === 'incomplete').length, rules };
      if (result.incomplete) throw new CliError('integrity.incomplete', `${result.incomplete} rule(s) could not be decided in Lean.`, { result });
      return { result, semanticHash: project.semanticHash };
    },
  },

  trace: {
    usage: 'trace <scenarioId> [--faults a,b] [--out <file>]',
    summary: 'The complete trace of a scenario. With --out, the trace is written as stable JSON to that file.',
    options: { faults: { type: 'string' }, out: { type: 'string' } },
    run: async (ctx) => {
      const { project } = await loadProject(ctx);
      const model = requireModel(project);
      const id = requireEntity(model, positional(ctx, 0, 'scenarioId'), 'scenario').id;
      const trace = runTrace(model, id, resolveFaults(model, ctx.values.faults));
      if (ctx.values.out === undefined) return { result: trace, semanticHash: project.semanticHash };
      const target = path.resolve(process.cwd(), ctx.values.out);
      fs.mkdirSync(path.dirname(target), { recursive: true });
      fs.writeFileSync(target, `${stableStringify(trace, 2)}\n`, 'utf8');
      return { result: { written: target, stepCount: trace.steps.length }, semanticHash: project.semanticHash };
    },
  },

  generate: {
    usage: 'generate [--all] [--write]',
    summary: 'Generate artifacts from the model. Deterministic: same model, same bytes. --write also stores them under generated/.',
    options: { all: { type: 'boolean' }, write: { type: 'boolean' } },
    run: async (ctx) => {
      const { ws, data, project } = await loadProject(ctx);
      const model = requireModel(project);
      const claimResults = evaluateClaims(model, { recorded: data.recorded ?? undefined });
      const traceability = checkTraceability(model, ctx.repoRoot, loadRoots(ws, ctx));
      const generatorFile = path.join(HERE, '..', 'src', 'core', 'generate', 'index.js');
      if (!fs.existsSync(generatorFile)) throw new CliError('generate.unavailable', 'src/core/generate/index.js does not exist.');
      const { generateAll } = await import(pathToFileURL(generatorFile).href);
      const files = generateAll(model, { claimResults, diagnostics: project.diagnostics, traceability });
      /** @type {Record<string, {bytes: number, sha256: string}>} */
      const summary = {};
      for (const name of Object.keys(files).sort()) {
        summary[name] = { bytes: Buffer.byteLength(files[name], 'utf8'), sha256: sha256Hex(files[name]) };
      }
      if (ctx.values.write !== true) return { result: { files: summary }, semanticHash: project.semanticHash };
      const written = await ws.writeGenerated(ctx.projectName, files);
      return { result: { files: summary, written: written.written }, semanticHash: project.semanticHash };
    },
  },

  markdown: {
    usage: 'markdown [<documentPath>] [--out <dir>]',
    summary: 'Render documents to Markdown from a specification that holds them (document, section and caseTable entities, as an imported Markdown specification does). With a path: the text of that document. With --out: every document written under <dir>. Otherwise: the document paths.',
    options: { out: { type: 'string' } },
    run: async (ctx) => {
      const { data, project } = await loadProject(ctx);
      const { parse } = await import('jsonc-parser');
      const { reconstructMarkdown } = await import('../tools/import-markdown.js');
      const value = parse(data.spec.text);
      if (!Array.isArray(value?.documents) || value.documents.length === 0) throw new CliError('markdown.none', 'The specification declares no documents to render.');
      /** @type {Map<string, string>} */
      let files;
      try { files = reconstructMarkdown(value); } catch (err) { throw new CliError('markdown.render', /** @type {Error} */ (err).message); }
      const wanted = ctx.positionals[0];
      if (wanted !== undefined) {
        const text = files.get(wanted);
        if (text === undefined) throw new CliError('markdown.unknown', `No document has the path "${wanted}".`);
        return { result: { path: wanted, text }, semanticHash: project.semanticHash };
      }
      if (typeof ctx.values.out === 'string') {
        const outDir = path.resolve(ctx.values.out);
        for (const [p, text] of files) {
          const dest = path.resolve(outDir, ...p.split('/'));
          if (path.relative(outDir, dest).startsWith('..') || path.isAbsolute(path.relative(outDir, dest))) throw new CliError('markdown.path', `Document path "${p}" leaves the output directory.`);
          fs.mkdirSync(path.dirname(dest), { recursive: true });
          fs.writeFileSync(dest, text);
        }
        return { result: { out: outDir, written: files.size }, semanticHash: project.semanticHash };
      }
      return { result: { documents: [...files.keys()] }, semanticHash: project.semanticHash };
    },
  },

  traceability: {
    usage: 'traceability',
    summary: 'Compare declared implementation modules with the files on disk: this repository, or the realisation roots project.jsonc declares.',
    run: async (ctx) => {
      const { ws, project } = await loadProject(ctx);
      const model = requireModel(project);
      return { result: checkTraceability(model, ctx.repoRoot, loadRoots(ws, ctx)), semanticHash: project.semanticHash };
    },
  },

  store: {
    usage: 'store import|export [--db <file>] [--out <file>]',
    summary: 'Copy the specification into its SQLite store (import) or write the store back as JSONC text (export), byte for byte. The store defaults to <spec>.sqlite beside the specification; export writes the specification itself unless --out names another file, and refuses when the specification changed since the store last synchronised with it.',
    options: { db: { type: 'string' }, out: { type: 'string' } },
    run: async (ctx) => {
      const action = positional(ctx, 0, 'import|export');
      if (action !== 'import' && action !== 'export') throw usage('invalid-argument', `Unknown store action "${action}"; expected import or export.`);
      const { importFile, exportFile, defaultDbPath, StoreError } = await import('../tools/spec-store.js');
      const ws = createWorkspace(ctx.specs);
      const specFile = ws.specFile(ctx.projectName);
      const db = ctx.values.db !== undefined ? path.resolve(process.cwd(), ctx.values.db) : defaultDbPath(specFile);
      try {
        if (action === 'import') {
          const started = performance.now();
          const r = importFile(specFile, db, { project: ctx.projectName });
          return { result: { action, spec: specFile, db, entities: r.entities, trivia: r.trivia, refs: r.refs, length: r.length, ms: Math.round(performance.now() - started) }, semanticHash: r.semanticHash };
        }
        const out = ctx.values.out !== undefined ? path.resolve(process.cwd(), ctx.values.out) : specFile;
        const started = performance.now();
        const r = exportFile(db, out, { guard: out === specFile });
        return { result: { action, db, out, changed: r.changed, length: r.length, bytes: r.bytes, sha256: r.sha256, ms: Math.round(performance.now() - started) } };
      } catch (err) {
        if (err instanceof StoreError) throw new CliError(err.code, err.message, { diagnostics: err.diagnostics });
        throw err;
      }
    },
  },

  readiness: {
    usage: 'readiness',
    summary: 'List what the specification still lacks before code can be generated from it (codes ready.*). Exits 0 with or without gaps; validate reports them as errors only when system.generation is set.',
    options: { ...INLINE_OPTIONS },
    run: async (ctx) => {
      const { project } = await loadProject(ctx);
      const model = requireModel(project);
      return { result: { gaps: readinessGaps(model) }, semanticHash: project.semanticHash };
    },
  },

  'cover-machines': {
    usage: `cover-machines [<behaviorId>] [--bound N] [--max-runs N] [--write <dir>]`,
    summary: `Transition and guard-outcome coverage of every shipped implementation machine: what the scenarios exercise (from their traces), and for the rest a bounded breadth-first search over sequences of the machine's input events (default bound ${DEFAULT_BOUND} actions, ${DEFAULT_MAX_RUNS} engine runs per machine) that generates the scenarios reaching them. A transition nothing reaches is a finding, machine.transition-unreachable (an error when system.generation is set, and the command fails). --write <dir> writes the generated scenarios as apply operations to <dir>/ops.json.`,
    options: { bound: { type: 'string' }, 'max-runs': { type: 'string' }, write: { type: 'string' } },
    run: async (ctx) => {
      const { project } = await loadProject(ctx);
      const model = requireModel(project);
      /** @param {string} name */
      const count = (name) => {
        const v = ctx.values[name];
        if (v === undefined) return undefined;
        const n = Number(v);
        if (!Number.isInteger(n) || n < 1) throw usage('invalid-argument', `--${name} must be a positive integer.`);
        return n;
      };
      const id = ctx.positionals[0];
      if (id !== undefined) requireEntity(model, id, 'behavior');
      const { machines, findings } = machineCoverage(model, { bound: count('bound'), maxRuns: count('max-runs'), machines: id === undefined ? undefined : [id] });
      if (id !== undefined && !machines.length) throw new CliError('cover.not-shipped', `"${id}" is not a shipped implementation-level machine.`);
      const sum = (/** @type {'transitions'|'guards'} */ k, /** @type {'covered'|'total'|'byScenarios'} */ f) => machines.reduce((n, m) => n + m[k][f], 0);
      /** @type {Record<string, any>} */
      const result = {
        summary: {
          machines: machines.length,
          transitions: { covered: sum('transitions', 'covered'), total: sum('transitions', 'total'), byScenarios: sum('transitions', 'byScenarios') },
          guards: { covered: sum('guards', 'covered'), total: sum('guards', 'total'), byScenarios: sum('guards', 'byScenarios') },
          generated: machines.reduce((n, m) => n + m.generated.length, 0),
          unreachable: findings.length,
        },
        table: machines.map((m) => ({
          machine: m.machine,
          transitions: `${m.transitions.covered}/${m.transitions.total}`,
          guards: `${m.guards.covered}/${m.guards.total}`,
          byScenarios: `${m.transitions.byScenarios}/${m.transitions.total} transitions, ${m.guards.byScenarios}/${m.guards.total} guard outcomes`,
          generated: m.generated.length,
          open: m.items.filter((i) => i.by === null).map((i) => (i.kind === 'transition' ? i.transition : `${i.transition} (guard ${i.outcome})`)),
        })),
        machines,
        findings: findings.map(serializeDiagnostic),
      };
      if (ctx.values.write !== undefined) {
        const dir = path.resolve(process.cwd(), ctx.values.write);
        const ops = coverageOperations(model, machines);
        fs.mkdirSync(dir, { recursive: true });
        const target = path.join(dir, 'ops.json');
        fs.writeFileSync(target, `${JSON.stringify(ops, null, 2)}\n`, 'utf8');
        result.written = { file: target, operations: ops.length };
      }
      const errors = findings.filter((d) => d.severity === 'error');
      if (errors.length) throw new CliError('cover.unreachable', `${errors.length} transition(s) of shipped machines are reached by no scenario and no sequence the search tried.`, { diagnostics: result.findings, result });
      return { result, semanticHash: project.semanticHash };
    },
  },

  'cover-functions': {
    usage: 'cover-functions [<functionId>] [--branches]',
    summary: 'Branch coverage of the function examples: for each function, the branches (if then and else, match arms, try value and error paths, fail) its examples take, covered/total, with the uncovered branches and where they are. --branches lists every branch. Exits 0; readiness reports the uncovered branches as ready.function-branch-uncovered.',
    options: { branches: { type: 'boolean' } },
    run: async (ctx) => {
      const { project } = await loadProject(ctx);
      const model = requireModel(project);
      const id = ctx.positionals[0];
      if (id !== undefined) requireEntity(model, id, 'function');
      const all = functionCoverage(model);
      const rows = all.filter((c) => id === undefined || c.id === id);
      const branch = (/** @type {any} */ b) => ({ id: b.id, kind: b.kind, label: b.label, where: b.where, line: b.line, column: b.column, text: b.text, ...(ctx.values.branches === true ? { covered: b.covered } : {}) });
      const result = {
        summary: {
          functions: all.length,
          withBranches: all.filter((c) => c.total > 0).length,
          fullyCovered: all.filter((c) => c.total > 0 && c.covered === c.total).length,
          branches: { covered: all.reduce((n, c) => n + c.covered, 0), total: all.reduce((n, c) => n + c.total, 0) },
          notEvaluated: all.filter((c) => !c.usable).map((c) => c.id),
        },
        functions: rows.map((c) => ({
          id: c.id, line: c.line, covered: c.covered, total: c.total, examples: c.examples, failedExamples: c.failedExamples, usable: c.usable,
          uncovered: c.branches.filter((b) => !b.covered).map(branch),
          ...(ctx.values.branches === true ? { branches: c.branches.map(branch) } : {}),
        })),
      };
      return { result, semanticHash: project.semanticHash };
    },
  },

  verify: {
    usage: 'verify [--skip-browser] [--ingest-only] [--fresh] [--expect-violated a,b]',
    summary: "Validate, check traceability, execute test evidence (reusing outcomes recorded on the same tree unless --fresh), record the results and re-evaluate the claims. Evidence in a realisation root is read from its JUnit reports; --ingest-only reads them without running the roots' test commands.",
    options: { 'skip-browser': { type: 'boolean' }, 'ingest-only': { type: 'boolean' }, fresh: { type: 'boolean' }, 'expect-violated': { type: 'string' } },
    run: async (ctx) => {
      const result = await runVerify(ctx);
      return result;
    },
  },

  help: {
    usage: 'help',
    summary: 'List the commands.',
    run: async () => ({
      result: {
        commands: Object.entries(COMMANDS).map(([name, c]) => ({ name, usage: c.usage, summary: c.summary })),
      },
    }),
  },
};

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/**
 * Run one command and return the envelope.
 * @param {string} name command name
 * @param {string[]} [args] tokens after the command name (positionals and --flags)
 * @param {{specs?: string, project?: string, repoRoot?: string, stdin?: string, log?: (message: string) => void}} [options]
 *   Flags given in args take precedence over options; options take precedence over defaults.
 * @returns {Promise<{ok: boolean, command: string, project: string|null, semanticHash?: string, result?: any, error?: {code: string, message: string}, diagnostics?: any[]}>}
 */
export async function runCommand(name, args = [], options = {}) {
  const command = Object.hasOwn(COMMANDS, name) ? COMMANDS[name] : null;
  if (!command) {
    return failure(name, null, 'usage.unknown-command', `Unknown command "${name}". Run "exegra help" for the list.`);
  }

  let parsed;
  try {
    parsed = parseArgs({
      args: [...args],
      options: { ...GLOBAL_OPTIONS, ...(command.options ?? {}) },
      allowPositionals: true,
      strict: true,
    });
  } catch (err) {
    return failure(name, null, 'usage.invalid-argument', /** @type {Error} */ (err).message);
  }

  // A project given inline (--spec) has no name; the project command names the project it works on itself.
  const projectName = name !== 'project' && parsed.values.spec !== undefined ? null : parsed.values.project ?? options.project ?? DEFAULT_PROJECT;
  const ctx = {
    values: parsed.values,
    positionals: parsed.positionals,
    projectName,
    specs: path.resolve(parsed.values.specs ?? options.specs ?? DEFAULT_SPECS),
    repoRoot: options.repoRoot ?? REPO_ROOT,
    stdin: options.stdin,
    log: options.log ?? (() => {}),
  };

  try {
    const out = await command.run(ctx);
    /** @type {any} */
    const envelope = { ok: true, command: name, project: projectName };
    if (out.project !== undefined) envelope.project = out.project;
    if (out.semanticHash !== undefined) envelope.semanticHash = out.semanticHash;
    envelope.result = out.result;
    return envelope;
  } catch (err) {
    if (err instanceof CliError) {
      return failure(name, projectName, err.code, err.message, err.diagnostics, err.result);
    }
    if (err instanceof WorkspaceError) return failure(name, projectName, err.code, err.message);
    return failure(name, projectName, 'internal.error', /** @type {Error} */ (err)?.message ?? String(err));
  }
}

/**
 * @param {string} command @param {string|null} project @param {string} code @param {string} message
 * @param {any[]} [diagnostics] @param {any} [result]
 */
function failure(command, project, code, message, diagnostics = [], result) {
  /** @type {any} */
  const envelope = { ok: false, command, project, error: { code, message }, diagnostics };
  if (result !== undefined) envelope.result = result;
  return envelope;
}

/** Exit code for an envelope: 0 ok, 2 usage error, 1 command failure. @param {{ok: boolean, error?: {code: string}}} envelope */
export function exitCodeOf(envelope) {
  if (envelope.ok) return 0;
  return envelope.error?.code.startsWith('usage.') ? 2 : 1;
}
