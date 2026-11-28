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
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { parseArgs } from 'node:util';
import { createWorkspace, WorkspaceError, isValidProjectName, PROJECT_FILE, FACT_FILES } from '../tools/workspace.js';
import { checkTraceability } from '../tools/traceability.js';
import { extractRepository, readFacts, factsDrift, factsText } from '../tools/extract.js';
import { attachObserved, reconcile, extractionOf, stripExtracted } from '../src/core/extraction.js';
import { readinessGaps } from '../src/core/readiness.js';
import { machineCoverage, coverageOperations, DEFAULT_BOUND, DEFAULT_MAX_RUNS } from '../src/core/machine-coverage.js';
import { functionCoverage } from '../src/core/function-coverage.js';
import { resolveRoots, splitRootRef, collectExternalResults, RootsError } from '../tools/realisation-roots.js';
import { Project } from '../src/core/project.js';
import { locate, setLocator } from './locations.js';
import { OPERATIONS, OpError, Tx, planDelete } from '../src/core/operations.js';
import { analyzeSpec } from '../src/core/analyze.js';
import { analyzeLayers } from '../src/core/layers.js';
import { evaluateIntegrity, counterexampleJson } from '../src/core/integrity.js';
import { proveIntegrity } from '../tools/prove-integrity.js';
import {
  entityLabel, childrenOf, ancestorsOf, inboundRefs, relationshipsOf, dependencies, contractsOf,
  hierarchyIds, hierarchyOf, cutMap, cutBlocksOf, abstractionOf, elementKindOf, knowledgeOf,
} from '../src/core/query.js';
import { evaluateClaims, evaluateClaim, checkTrace, theoremRequests } from '../src/core/claims.js';
import { applyConcordance } from '../src/core/concordance.js';
import { checkTheorems } from '../tools/lean-theorems.js';
import { requestLog } from '../src/core/contract-trace.js';
import { runScenario, runEngine } from '../src/core/engine.js';
import { checkEditHistory } from '../src/core/edit-history.js';
import { proveScenario, ProveError } from '../tools/prove.js';
import { CLAIM_STATUSES } from '../src/core/claim-methods.js';
import { stableStringify } from '../src/core/stable-json.js';
import { testRefProblem, describeTestRefProblem } from '../src/core/evidence-ref.js';
import { treeStamp, currentStamps } from '../tools/tree-stamp.js';
import { scanImports, importScanRecord, IMPORT_ASSUMPTION } from '../tools/import-scan.js';
import { dependencyGraph, impactedClaims, fileNodes, changeImpact } from '../src/core/impact.js';
import { executeEvidence, pendingTestEvidence } from './evidence-run.js';
import { createOutcomeReuse } from './outcomes.js';
import { evidenceRefDiagnostics } from '../tools/test-names.js';
import { countPassedBrowserTests, coveredFiles, createCoverHasher, expandCoverage, planReuse, runTestBatches, tapTests } from './test-batch.js';
import { snapshot, compare, sideCounts, NON_ACKNOWLEDGEABLE, withClaimStrength, claimBaseline, verifyRegressions } from './admit.js';
import { claimStrength } from '../src/core/claim-strength.js';
import { readCommands } from './read-commands.js';
import { compositionCommands, parseLevels } from './composition-commands.js';
import { behaviorsAtLevels, inputWith, environmentReport, scenarioCut } from '../src/core/composition.js';
import { deriveModel, derivedJson, levelOf } from '../src/core/abstraction.js';
import { coherenceReport, checkCoherence, checkContractConformance } from '../src/core/coherence.js';
import { functionComposition } from '../src/core/function-composition.js';
import { liftFaults } from '../src/core/fault-lifting.js';
import { generateCandidates, compareCandidates, candidatesOfData, acceptCandidate, VALIDITY_CONDITIONS, BEHAVIOURAL_CONDITIONS, GRAINS, SOURCES, NOT_MEANING } from '../src/core/decomposition.js';
import { PROVENANCES } from '../src/core/interactions.js';

/** @typedef {import('../src/core/types.js').Model} Model */
/** @typedef {import('../src/core/types.js').Entity} Entity */
/** @typedef {import('../src/core/types.js').Diagnostic} Diagnostic */

const HERE = path.dirname(fileURLToPath(import.meta.url));
export const REPO_ROOT = path.resolve(HERE, '..');
export const DEFAULT_SPECS = path.join(REPO_ROOT, 'specs');
export const DEFAULT_PROJECT = 'exegra';


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
  const at = locate(d.loc);
  return {
    code: d.code,
    severity: d.severity,
    message: d.message,
    entityId: d.entityId ?? null,
    line: at.line,
    column: at.column,
    // The product file a diagnostic of a layered project is in, or the part file of a manifest; absent for a one-file specification.
    ...(at.file !== undefined ? { file: at.file } : {}),
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
    source: (({ file, line, column }) => ({ line, column, ...(file !== undefined ? { file } : {}) }))(locate(e.loc)),
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

/** @param {{status: string, verdict?: {established: boolean}}[]} results */
function summarize(results) {
  /** @type {Record<string, number>} */
  const summary = { total: results.length, proved: 0, verified: 0, supported: 0, 'model-holds': 0, asserted: 0, violated: 0, inconclusive: 0, 'not-evaluated': 0, established: 0 };
  for (const r of results) {
    if (r.status in summary) summary[r.status] += 1;
    if (r.verdict?.established) summary.established += 1;
  }
  return summary;
}

/**
 * The theorem checks of the model's lean-theorem claims: checked now by Lean when it is installed
 * (tools/lean-theorems.js), merged over the recorded ones; the recorded ones alone otherwise, or
 * when EXEGRA_NO_LEAN=1. Returns the merged map and whether Lean ran. Recorded checks carry the hash
 * of the formal/ sources they ran on; claim evaluation compares it with the current sources and reads
 * a check of other sources as stale, so a kept record never proves a claim about changed sources.
 * @param {Model} model @param {any} recorded @param {(msg: string) => void} [log]
 * @returns {{theorems: Record<string, any>, checked: boolean}}
 */
function leanTheoremChecks(model, recorded, log) {
  const prior = recorded && typeof recorded === 'object' && recorded.theorems && typeof recorded.theorems === 'object' ? recorded.theorems : {};
  const requests = theoremRequests(model);
  if (!requests.length) return { theorems: prior, checked: false };
  if (process.env.EXEGRA_NO_LEAN === '1') {
    log?.('lean: not checked (EXEGRA_NO_LEAN=1); the recorded checks are kept and are stale wherever formal/ changed since');
    return { theorems: prior, checked: false };
  }
  log?.(`lean: checking ${requests.length} theorem(s)`);
  const r = checkTheorems(requests);
  if (!r.available) {
    log?.(`lean: not checked, the recorded checks are kept and are stale wherever formal/ changed since (${r.reason.split(/\r?\n/)[0]})`);
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
  setLocator(data.spec.locate);
  const project = new Project({
    name: ctx.projectName,
    specText: data.spec.text,
    layoutText: data.layout?.text ?? null,
    layers: data.layers.map((/** @type {any} */ l) => ({ file: l.file, text: l.text, platform: l.platform })),
    extracted: data.extracted ?? null,
    observed: data.observed ?? null,
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

// The readers of test runner output live in cli/test-batch.js; these are re-exported for their callers.
export { countPassedBrowserTests, coveredFiles, tapTests };

/**
 * Number of executed, passing leaf tests in node's TAP output (tapTests): skipped tests, todo tests, suites and
 * the entry for the test file itself are not passes. A pattern that matches no test counts zero.
 * @param {string} output TAP text @param {string} file the test file that was run
 */
export function countPassingTests(output, file) {
  return tapTests(output, file).filter((t) => !t.suite && t.outcome === 'pass').length;
}

/**
 * The `results` object to record after a verify run. Outcomes that ran replace the earlier ones. A reference
 * that skipped (a test that skipped itself, a match part of which skipped, or browser evidence under
 * --skip-browser) did not execute in full, so it is recorded as not-run, which counts as no result, and never
 * keeps an older pass; the one exception is a browser test that was not started and whose earlier result was
 * recorded on the same tree stamp.
 * @param {Record<string, any>} prior the `results` object recorded before this run
 * @param {{id: string, outcome: 'pass'|'fail'|'skipped'|'not-run', detail?: string, ranAt: string, obtained?: 'run'|'reused'|'impact', attempted?: boolean, covers?: string[], coverage?: string, ref?: string}[]} runs
 *   this run, per evidence id (not-run: a realisation root's test that did not run; attempted false: a browser
 *   test verify did not start, under --skip-browser)
 * @param {string|null} [stamp] the stamp of the tree the run recorded (tools/tree-stamp.js, recordsStamp), written
 *   into every result so a later read can tell whether the result still describes the tree
 * @returns {Record<string, any>}
 */
export function mergeRecordedResults(prior, runs, stamp = null) {
  /** @type {Record<string, any>} */
  const results = {};
  for (const run of runs) {
    if (run.outcome === 'skipped') {
      // A test that skipped itself, or any of whose matched tests skipped, established nothing on this tree: an
      // older pass is not kept, the reference is recorded as not run. Only a browser test that verify did not
      // start (--skip-browser) keeps a result recorded on this very tree, which is still a fact about it.
      const kept = Object.hasOwn(prior, run.id) ? prior[run.id] : undefined;
      if (run.attempted === false && kept && stamp !== null && kept.stamp === stamp) { results[run.id] = kept; continue; }
      results[run.id] = {
        outcome: 'not-run',
        detail: run.detail ?? (run.attempted === false ? 'not started (--skip-browser)' : 'the matching test skipped itself'),
        ranAt: run.ranAt,
        ...(run.obtained ? { obtained: run.obtained } : {}),
        ...(run.ref !== undefined ? { ref: run.ref } : {}), ...(run.coverage ? { coverage: run.coverage } : {}),
        ...(stamp !== null ? { stamp } : {}),
      };
      continue;
    }
    results[run.id] = {
      outcome: run.outcome, ...(run.detail !== undefined ? { detail: run.detail } : {}), ranAt: run.ranAt,
      ...(run.obtained ? { obtained: run.obtained } : {}), ...(run.ref !== undefined ? { ref: run.ref } : {}), ...(run.covers ? { covers: run.covers } : {}), ...(run.coverage ? { coverage: run.coverage } : {}), ...(stamp !== null ? { stamp } : {}),
    };
  }
  return results;
}

/**
 * Read a change set: `{ops?: [operation], files?: [path], entities?: [id]}`. `ops` are transaction operations
 * applied to the specification (admit, impact); `files` are the repository files the change touches (Lean sources,
 * tests, measurements); `entities` are specification entities that changed since the last verification (verify).
 * @param {any} ctx @param {string} file
 * @returns {{ops: any[], files: string[], entities: string[]}}
 */
function readChangeSet(ctx, file) {
  const abs = path.resolve(ctx.cwd ?? process.cwd(), file);
  let value;
  try {
    value = JSON.parse(fs.readFileSync(abs, 'utf8'));
  } catch (e) {
    throw new CliError('change.invalid', `Cannot read the change set ${file}: ${/** @type {Error} */ (e).message}`);
  }
  const strs = (/** @type {any} */ v, /** @type {string} */ what) => {
    if (v === undefined) return [];
    if (!Array.isArray(v) || !v.every((x) => typeof x === 'string')) throw new CliError('change.invalid', `The change set's "${what}" must be a list of strings.`);
    return v;
  };
  if (!value || typeof value !== 'object' || Array.isArray(value)) throw new CliError('change.invalid', 'A change set is an object {ops, files, entities}.');
  if (value.ops !== undefined && !Array.isArray(value.ops)) throw new CliError('change.invalid', 'The change set\'s "ops" must be a list of operations.');
  return { ops: value.ops ?? [], files: strs(value.files, 'files'), entities: strs(value.entities, 'entities') };
}

/** The nodes of named specification entities (unknown ids are specification entities that no longer exist). @param {Model} model @param {string[]} ids */
function changedEntityNodes(model, ids) {
  return ids.map((id) => {
    const e = model.entities.get(id);
    const kind = e?.kind === 'claim' ? 'claim' : e?.kind === 'assumption' ? 'assumption' : e?.kind === 'evidence' ? 'evidence' : 'specEntity';
    return { kind: /** @type {import('../src/core/impact.js').NodeKind} */ (kind), id };
  });
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
  const diagnostics = [...project.diagnostics, ...evidenceRefDiagnostics(model, ctx.repoRoot)];
  const counts = countSeverities(diagnostics);
  const validationErrors = diagnostics.filter((d) => d.severity === 'error').map(serializeDiagnostic);

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
  // The stamps every recorded result is written with, taken before anything runs (tools/tree-stamp.js).
  const stamps = currentStamps(ctx.repoRoot);
  // Outcomes recorded by earlier runs. A reference that skips now is recorded as not run, never as its older pass.
  // Outcomes that `npm test` and `npm run test:browser` recorded on this very tree are reused (cli/outcomes.js).
  const reuse = ctx.values.fresh === true ? null : createOutcomeReuse(ctx.repoRoot, treeStamp(ctx.repoRoot));
  if (reuse) for (const [kind, why] of Object.entries(reuse.notes)) ctx.log(`verify: not reusing ${kind} outcomes: ${why}`);
  // (2b) the import scan: a fact about the assumption that the extracted facts describe the tree (tools/import-scan.js)
  const importScan = scanImports(model, ctx.repoRoot);
  const assumptions = { [IMPORT_ASSUMPTION]: importScanRecord(importScan, stamps.tree) };
  const priorRecorded = (await ws.read(ctx.projectName)).recorded;
  const priorResults = priorRecorded && typeof priorRecorded === 'object' && priorRecorded.results && typeof priorRecorded.results === 'object'
    ? priorRecorded.results : {};
  // (3b) with a change set, only the evidence of the claims it re-marks runs (src/core/impact.js, decided in Lean);
  // the others keep the results the last verification recorded fresh
  const change = ctx.values.change !== undefined ? readChangeSet(ctx, String(ctx.values.change)) : null;
  if (change && change.ops.length) throw new CliError('verify.change-ops', 'A change set for verify names the entities and files that changed since the last verification ("entities", "files"); the specification on disk already holds the change, so it takes no operations.');
  const remark = change ? new Set(impactedClaims(dependencyGraph(model, { recorded: expandCoverage(priorRecorded) ?? undefined }), [...changedEntityNodes(model, change.entities), ...fileNodes(change.files)])) : null;
  const priorStamp = priorRecorded && typeof priorRecorded === 'object' && typeof priorRecorded.stamp === 'string' ? priorRecorded.stamp : null;
  // The test references that nothing else answers run in batches, once per test file and once for the browser
  // (cli/test-batch.js); a file whose recorded pass still stands, because nothing it covered changed, does not run.
  const hasher = createCoverHasher(ctx.repoRoot);
  const priorCoverage = priorRecorded && typeof priorRecorded === 'object' && priorRecorded.coverage && typeof priorRecorded.coverage === 'object' ? priorRecorded.coverage : {};
  const pending = pendingTestEvidence(model, { external: external.results, remark, priorResults, priorStamp });
  const plan = ctx.values.fresh === true ? { reused: new Map(), run: pending } : planReuse(pending, { priorResults, priorCoverage, hasher });
  if (plan.reused.size) ctx.log(`verify: ${plan.reused.size} of ${pending.length} test evidence entities keep their recorded pass: what they covered is unchanged`);
  const expectedMs = Object.fromEntries(Object.entries(priorCoverage).map(([f, c]) => [f, Number(/** @type {any} */ (c)?.ms) || 0]));
  const batch = await runTestBatches(plan.run, { repoRoot: ctx.repoRoot, skipBrowser, log: ctx.log, hasher, reuse, expectedMs });
  const executed = executeEvidence(model, {
    run: (ref, id) => {
      const kept = plan.reused.get(id);
      if (kept) return { outcome: kept.outcome, ...(kept.detail !== undefined ? { detail: kept.detail } : {}), obtained: 'reused', ranAt: kept.ranAt, coverage: kept.coverage };
      return batch.results.get(id) ?? { outcome: 'fail', detail: 'the reference was not run', obtained: 'run' };
    },
    external: external.results, remark, priorResults, priorStamp,
  });
  const runs = executed.runs;
  const evidence = executed.evidence;
  const results = mergeRecordedResults(priorResults, runs, stamps.tree);
  // A root's results also carry the root and its reports, which the merge would drop.
  for (const [id, ext] of external.results) results[id] = { ...ext, ...(stamps.tree !== null ? { stamp: stamps.tree } : {}) };

  // (4) record the results. Outcomes an external verification tool recorded per claim live in the same file;
  // this command owns `results`, `traceability`, `assumptions`, `theorems` and `claimBaseline` and keeps the rest.
  /** @type {Record<string, any>} */
  const kept = {};
  const prior = priorRecorded;
  if (prior && typeof prior === 'object') for (const k of ['tool', 'version', 'source', 'claims', 'lint']) if (Object.hasOwn(prior, k)) kept[k] = /** @type {any} */ (prior)[k];
  // (4b) the Lean checks of the lean-theorem claims; without Lean the recorded checks are kept, and claim
  // evaluation reads those checked on other formal/ sources as stale
  const { theorems } = leanTheoremChecks(model, prior, ctx.log);
  const baseline = prior && typeof prior === 'object' && prior.claimBaseline && typeof prior.claimBaseline === 'object' ? prior.claimBaseline : null;
  // What each test file's run covered, for the references that point at it (and only those).
  const coverage = Object.fromEntries([...new Set(Object.values(results).map((r) => r.coverage).filter((k) => typeof k === 'string'))].sort()
    .flatMap((k) => { const c = Object.hasOwn(batch.coverage, k) ? batch.coverage[k] : Object.hasOwn(priorCoverage, k) ? priorCoverage[k] : null; return c ? [[k, c]] : []; }));
  const recordedNow = { ...kept, ...(stamps.tree !== null ? { stamp: stamps.tree } : {}), results, ...(Object.keys(coverage).length ? { coverage } : {}), traceability, assumptions, ...(Object.keys(theorems).length ? { theorems } : {}), ...(baseline ? { claimBaseline: baseline } : {}) };
  await ws.writeRecorded(ctx.projectName, recordedNow);

  // (5) evaluate the claims with the new results, against the stamps they were recorded with
  const claimResults = evaluateClaims(model, { recorded: { results, theorems, assumptions, ...(data.recorded?.derived ? { derived: data.recorded.derived } : {}) }, stamps });
  const violated = claimResults.filter((r) => r.status === 'violated').map((r) => r.claimId);
  const unexpectedViolated = violated.filter((id) => !expectViolated.includes(id));
  const failedEvidence = evidence.filter((e) => e.outcome === 'fail');
  // Downgrades against the statuses the last passing verify recorded (claimBaseline): a positive claim that fell or
  // was removed, and a changed counterexample of an expected-violated claim, fail unless --accept-change names it.
  const acceptChange = listValue(ctx.values['accept-change']);
  const current = claimBaseline(claimResults);
  const regressions = baseline ? verifyRegressions(baseline, current, { expectViolated, accept: acceptChange }) : [];

  const result = {
    validation: { errors: counts.errors, warnings: counts.warnings, gaps: counts.gaps },
    traceability,
    importScan: { checked: importScan.checked, imports: importScan.imports, undeclared: importScan.undeclared },
    ...(remark ? { change: { remark: [...remark].sort(), reused: executed.reused } } : {}),
    evidence,
    ...(roots.length ? { roots: external.reports, notRun: evidence.filter((e) => e.outcome === 'not-run').map((e) => e.id) } : {}),
    claims: {
      summary: summarize(claimResults),
      violated,
      expectedViolated: violated.filter((id) => expectViolated.includes(id)),
      unexpectedViolated,
      regressions,
      ...(acceptChange.length ? { acceptedChanges: acceptChange } : {}),
    },
  };

  const problems = [];
  if (counts.errors) problems.push(`${counts.errors} validation error(s)`);
  if (failedEvidence.length) problems.push(`${failedEvidence.length} evidence item(s) failed`);
  if (unexpectedViolated.length) problems.push(`${unexpectedViolated.length} claim(s) violated`);
  if (regressions.length) problems.push(`${regressions.length} claim(s) regressed (${regressions.map((r) => r.id).join(', ')})`);

  // (6) a passing run records its claim statuses as the new baseline, in the same file. The baseline moves only
  // with a passing run, so running verify again does not wave a regression through.
  if (!problems.length && JSON.stringify(current) !== JSON.stringify(baseline)) {
    await ws.writeRecorded(ctx.projectName, { ...recordedNow, claimBaseline: current });
  }

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

/**
 * Apply a list of operations as one transaction of the loaded project and write the changed files (the whole of `apply`,
 * shared with `accept-decomposition`, which builds its operations from a candidate). A dry run writes nothing.
 * @param {any} ctx @param {any[]} list
 * @param {{label?: string, loaded?: Awaited<ReturnType<typeof loadProject>>}} [extra] a project already loaded for this command
 */
async function applyOperationList(ctx, list, extra = {}) {
  const { ws, data, project } = extra.loaded ?? await loadProject(ctx);
  const initialSpec = project.specText;
  const initialLayout = project.layoutText;
  const hashBefore = project.semanticHash;
  const label = extra.label ?? ctx.values.label;
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
}

/**
 * The candidates a decompose or accept-decomposition command works on: those given in --file, then the generated ones.
 * @param {any} ctx @param {Model} model
 */
function gatherCandidates(ctx, model) {
  const v = ctx.values;
  const scope = v.scope ?? model.system?.id;
  if (!scope || !elementKindOf(model, scope)) throw usage('invalid-argument', `--scope must name an element; "${String(scope)}" is not one.`);
  const grain = v.grain ?? 'children';
  if (!GRAINS.includes(/** @type {any} */ (grain))) throw usage('invalid-argument', `--grain is one of ${GRAINS.join(', ')}.`);
  const sources = listValue(v.source);
  for (const s of sources) if (!SOURCES.includes(s)) throw usage('invalid-argument', `--source names "${s}"; the sources are ${SOURCES.join(', ')}.`);
  const provenance = v.provenance === undefined ? null : listValue(v.provenance);
  if (provenance) for (const p of provenance) if (!PROVENANCES.includes(/** @type {any} */ (p))) throw usage('invalid-argument', `--provenance names "${p}"; the provenances are ${PROVENANCES.join(', ')}.`);
  const dirDepth = v['dir-depth'] === undefined ? undefined : Number(v['dir-depth']);
  if (dirDepth !== undefined && (!Number.isInteger(dirDepth) || dirDepth < 1)) throw usage('invalid-argument', '--dir-depth must be a whole number of at least 1.');
  /** @type {any[]} */
  let given = [];
  if (v.file !== undefined) {
    const file = path.resolve(process.cwd(), v.file);
    let doc;
    try { doc = JSON.parse(fs.readFileSync(file, 'utf8')); } catch (err) { throw usage('invalid-argument', `--file ${v.file} is not readable JSON: ${/** @type {Error} */ (err).message}`); }
    given = candidatesOfData(doc);
  }
  const common = { scope, grain: /** @type {any} */ (grain), provenance };
  const generated = generateCandidates(model, { ...common, sources: sources.length ? sources : undefined, dirDepth, bases: given.map((c) => ({ scope, grain, ...c })) });
  const all = [...given.map((c) => ({ scope, grain, ...c })), ...generated.candidates];
  const ids = new Set();
  for (const c of all) { if (ids.has(c.id)) throw usage('invalid-argument', `Two candidates have the id "${c.id}".`); ids.add(c.id); }
  return { scope, grain, provenance, common, generated, all };
}

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
      // What needs the file system: a test reference must name a test its file declares (tools/test-names.js).
      const diagnostics = [...project.diagnostics, ...(project.model ? evidenceRefDiagnostics(project.model, ctx.repoRoot) : [])];
      const counts = countSeverities(diagnostics);
      /** @type {Record<string, any>} */
      const result = { ...counts, diagnostics: diagnostics.map(serializeDiagnostic), concordance: data.concordanceDiagnostics };
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
    summary: 'One entity with its data, owned entities and inbound references; components add relationships, children and ancestors; components and the system add their members in the logical hierarchy (module elements included) and their knowledge status.',
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
      if (e.kind === 'component' || e.kind === 'system') {
        // The element's place in the logical hierarchy, module elements included, and what is known of its inside.
        result.members = /** @type {any} */ (hierarchyOf(model, 'logical')).children.get(e.id) ?? [];
        result.knowledge = knowledgeOf(model, e.id);
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
      const result = evaluateClaims(model, { recorded: withLean(model, data.recorded, ctx.log), stamps: currentStamps(ctx.repoRoot) })
        .map((r) => {
          const claim = model.entities.get(r.claimId);
          return { ...r, statement: claim?.data.statement ?? null, kind: claim?.data.kind ?? r.kind, ...strengthFields(strength, r.claimId) };
        })
        .filter((r) => status === undefined || r.status === status);
      return { result, semanticHash: project.semanticHash };
    },
  },

  evaluate: {
    usage: 'evaluate [<claimId>] [--cut <id> | --hierarchy <id> --depth N | --expand a,b | --finest]',
    summary: 'Evaluate one claim or all claims. A violated claim is a finding; the command still succeeds. With a cut (--cut names a declared one; --hierarchy with --depth, --expand or --finest gives an ad hoc one), every claim stated at a cut is evaluated at that cut instead: what the application shows for it at the cut a view draws.',
    options: { cut: { type: 'string' }, hierarchy: { type: 'string' }, depth: { type: 'string' }, expand: { type: 'string' }, finest: { type: 'boolean' }, ...INLINE_OPTIONS },
    run: async (ctx) => {
      const { data, project } = await loadProject(ctx);
      const model = requireModel(project);
      const id = ctx.positionals[0];
      // Lean theorem checks matter only to lean-theorem claims (and to a requirement, through the claims modelling it).
      const one = id !== undefined ? model.entities.get(id) : undefined;
      const needsLean = !one || one.data.kind === 'requirement' || one.data.evaluate?.method === 'lean-theorem' || one.data.evaluate?.method === 'conformance-verified-refinement';
      const recorded = needsLean ? withLean(model, data.recorded, ctx.log) : data.recorded ?? undefined;
      const stamps = currentStamps(ctx.repoRoot);
      const strength = claimStrength(model);
      const { cut, hierarchy, depth, expand, finest } = ctx.values;
      /** @type {string|{hierarchy: string, blocks: string[]}|null} */
      let atCut = null;
      if (cut !== undefined) {
        if (hierarchy !== undefined || depth !== undefined || expand !== undefined || finest !== undefined) throw usage('invalid-argument', '--cut names a declared cut; it takes none of --hierarchy, --depth, --expand, --finest.');
        atCut = requireEntity(model, cut, 'cut').id;
      } else if (hierarchy !== undefined || depth !== undefined || expand !== undefined || finest !== undefined) {
        const hid = hierarchy ?? 'logical';
        if (!hierarchyOf(model, hid)) throw usage('invalid-argument', `Unknown hierarchy "${hid}"; the hierarchies are: ${hierarchyIds(model).join(', ')}.`);
        const d = depth === undefined ? undefined : Number(depth);
        if (d !== undefined && (!Number.isInteger(d) || d < 0)) throw usage('invalid-argument', '--depth must be a whole number of at least 0.');
        const level = /** @type {any} */ (levelOf(model, { hierarchy: hid, expand: listValue(expand), depth: d, finest: finest === true }));
        atCut = { hierarchy: hid, blocks: level.blocks };
      }
      const results = (id !== undefined
        ? [evaluateClaim(model, requireEntity(model, id, 'claim').id, { recorded, stamps, atCut })]
        : evaluateClaims(model, { recorded, stamps, atCut })).map((r) => ({ ...r, ...strengthFields(strength, r.claimId) }));
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
      const results = evaluateClaims(model, { recorded: data.recorded ?? undefined, stamps: currentStamps(ctx.repoRoot) });
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
    run: async (ctx) => applyOperationList(ctx, await readOperations(ctx)),
  },

  admit: {
    usage: "admit [--file <ops.json> | --ops '<json>' | --change <change.json>] [--label <text>] [--write] [--accept <code-or-claim[,...]>]...",
    summary: "Admit a change set only if everything the specification held still holds and the change's own claims hold: the before/after diff and a verdict with every reason. A change set (--change: {ops, files}) may also touch Lean sources, tests and measurement files; the claims it re-marks and the changes to guarantees are listed, and a weakened lean-theorem claim is refused (admit.theorem-weakened) unless --accept names the claim. Writes only with --write and only when admitted; fails with admit.rejected otherwise.",
    options: { file: { type: 'string' }, ops: { type: 'string' }, change: { type: 'string' }, label: { type: 'string' }, write: { type: 'boolean' }, accept: { type: 'string', multiple: true } },
    run: async (ctx) => {
      const accept = (/** @type {string[]} */ (ctx.values.accept ?? [])).flatMap(listValue);
      const fixed = accept.filter((c) => NON_ACKNOWLEDGEABLE.has(c));
      if (fixed.length) throw new CliError('admit.not-acknowledgeable', `Cannot accept ${fixed.join(', ')}: a reason without "acknowledgeable" is a failure to fix, not a decision to accept.`);
      if (ctx.values.change !== undefined && (ctx.values.file !== undefined || ctx.values.ops !== undefined)) throw usage('invalid-argument', 'Give --change or --file/--ops, not both.');
      const changeSet = ctx.values.change !== undefined ? readChangeSet(ctx, String(ctx.values.change)) : null;
      const list = changeSet ? changeSet.ops : await readOperations(ctx);
      const { ws, data, project } = await loadProject(ctx);
      const beforeModel = requireModel(project);
      const initialSpec = project.specText;
      const initialLayout = project.layoutText;
      const hashBefore = project.semanticHash;
      const { label } = ctx.values;
      const write = ctx.values.write === true;
      // Both sides read the recorded results against the same current stamps.
      const stamps = currentStamps(ctx.repoRoot);
      const before = snapshot(beforeModel, project.diagnostics, evaluateClaims(beforeModel, { recorded: withLean(beforeModel, data.recorded, ctx.log), stamps }));
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
        const recordedAfter = withLean(afterModel, data.recorded, ctx.log);
        const after = snapshot(afterModel, project.diagnostics, evaluateClaims(afterModel, { recorded: recordedAfter, stamps }));
        const theorems = { old: data.recorded?.theorems ?? {}, new: recordedAfter?.theorems ?? {} };
        const impact = changeImpact(beforeModel, afterModel, { files: changeSet?.files ?? [], recorded: expandCoverage(data.recorded) ?? undefined });
        report = {
          ...withClaimStrength(compare(before, after, { accept, theorems }), beforeModel, afterModel, accept),
          impact: { remark: impact.remark, files: changeSet?.files ?? [] },
          transaction: { accepted: true, affected: [...tx.affected].sort(), semanticChanged: tx.semanticChanged },
        };
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

  impact: {
    usage: 'impact --change <change.json>',
    summary: 'The claims a change set re-marks: those that depend, through the dependency graph (assumptions, discharging claims, the entities their evaluate names, evidence and the files its tests cover, theorems, the declarations and files their statements use, measurements), on an entity the change\'s operations add, change or remove, or on a file it names. Decided in Lean (formal/Exegra/Impact.lean). Changes to guarantees (a claim\'s statement or evaluate) are listed apart. Changes nothing.',
    options: { change: { type: 'string' } },
    run: async (ctx) => {
      if (ctx.values.change === undefined) throw usage('missing-argument', 'Give the change set with --change <change.json>.');
      const change = readChangeSet(ctx, String(ctx.values.change));
      const { data, project } = await loadProject(ctx);
      const beforeModel = requireModel(project);
      const hash = project.semanticHash;
      let afterModel = beforeModel;
      if (change.ops.length) {
        const tx = project.apply(change.ops, { origin: 'cli' });
        if (!tx.ok) throw new CliError('impact.transaction-refused', tx.message ?? 'The change set\'s operations were refused.', { diagnostics: tx.diagnostics.map(serializeDiagnostic) });
        afterModel = requireModel(project);
      }
      const nodes = [...changedEntityNodes(afterModel, change.entities), ...fileNodes(change.files)];
      const fromOps = changeImpact(beforeModel, afterModel, { files: change.files, recorded: expandCoverage(data.recorded) ?? undefined });
      const extra = change.entities.length ? impactedClaims(dependencyGraph(afterModel, { recorded: expandCoverage(data.recorded) ?? undefined }), nodes) : [];
      const remark = [...new Set([...fromOps.remark, ...extra])].sort();
      return { result: { remark, guaranteeChanges: fromOps.guaranteeChanges, changed: [...fromOps.changed, ...changedEntityNodes(afterModel, change.entities)] }, semanticHash: hash };
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

  'replay-edits': {
    usage: 'replay-edits --file <capture.json>',
    summary: 'Check captured replies and a durable read against both serial orders of the two-session edit scenario.',
    options: { file: { type: 'string' }, ...INLINE_OPTIONS },
    run: async (ctx) => {
      if (!ctx.values.file) throw usage('missing-argument', 'Give a capture with --file.');
      let capture;
      try {
        capture = JSON.parse(fs.readFileSync(ctx.values.file, 'utf8'));
      } catch (err) {
        throw usage('invalid-argument', `Cannot read the edit capture: ${/** @type {Error} */ (err).message}`);
      }
      const { project } = await loadProject(ctx);
      const model = requireModel(project);
      requireEntity(model, 'two-session-edit-race', 'scenario');
      const result = checkEditHistory(model, capture);
      if (result.verdict !== 'compatible') {
        throw new CliError(`replay.${result.verdict}`, result.reason, { result: { ...result, semanticHash: project.semanticHash } });
      }
      return { result, semanticHash: project.semanticHash };
    },
  },

  simulate: {
    usage: 'simulate <scenarioId> [--faults a,b] [--level <abstraction>=abstract|members|finest,...] [--steps]',
    summary: 'Run a scenario and check the invariant and temporal claims and the contract events that apply to its trace. Contract events are also listed as a request log. The result names the behavioural cut of the scenario and its environment report (events an omitted element would receive with no environment assumption: scenario.environment-unassumed). --level runs regions at another level than the scenario declares (docs/composition.md): the cut is always given on the command line or in the scenario, never taken from a view.',
    options: { faults: { type: 'string' }, level: { type: 'string' }, steps: { type: 'boolean' }, ...INLINE_OPTIONS },
    run: async (ctx) => {
      const { project } = await loadProject(ctx);
      const model = requireModel(project);
      const id = requireEntity(model, positional(ctx, 0, 'scenarioId'), 'scenario').id;
      const faults = resolveFaults(model, ctx.values.faults);
      const levels = parseLevels(ctx.values.level, usage);
      /** @type {any} */
      let at = null;
      /** @type {any} */
      let trace;
      if (Object.keys(levels).length) {
        try { at = behaviorsAtLevels(model, id, levels, faults); } catch (err) { throw new CliError('simulate.level', /** @type {Error} */ (err).message); }
        trace = runEngine(inputWith(model, id, at.behaviors, at.faults));
      } else trace = runTrace(model, id, faults);
      const env = environmentReport(model, id, trace, at?.behaviors);
      /** @type {Record<string, any>} */
      const result = {
        scenarioId: id,
        faults: trace.faults,
        outcome: trace.outcome,
        stepCount: trace.steps.length,
        final: trace.final,
        checks: checkTrace(model, trace),
        cut: scenarioCut(model, id),
        ...(at ? { atLevels: at } : {}),
        environment: { assumed: env.assumed, unassumed: env.unassumed },
        diagnostics: env.unassumed.map((u) => ({ severity: 'warning', code: 'scenario.environment-unassumed', message: `Step ${u.step} delivers "${u.event}"${u.emitter ? ` from ${u.emitter}` : ''}, which no running machine reacts to and which ${u.receivers.map((r) => `"${r}"`).join(', ')} would receive, but the scenario declares no environment assumption for ${u.receivers.length === 1 ? 'it' : 'them'}.`, entityId: id })),
      };
      const log = requestLog(model, trace);
      if (log.length) result.requestLog = log.map((e) => `#${e.step} t=${e.time} ${e.text}`);
      if (ctx.values.steps === true) result.steps = trace.steps;
      return { result, semanticHash: project.semanticHash };
    },
  },

  prove: {
    usage: 'prove <scenarioId> [--bound N] [--max-states N] [--steps] [--module]',
    summary: 'Explore every configuration of a scenario within a bound (every order of simultaneous events, every subset of its faults) with the verified explorer of the Lean semantics, and check each state-invariant claim that lists it in Lean: holds for all N configurations (with a closed-set certificate of the states visited), or a counterexample run, or incomplete because a run hit the bound or the state budget truncated the search. Temporal claims (never, precedes, eventually) are checked on every complete run: holds, a violating run, or incomplete. Liveness claims (GF, FG under the weak fairness their assumptions declare) are proved by a ranking, violated by a lasso (flagged when it is a Zeno run), incomplete or not supported. --module writes formal/Exegra/Proofs/<Scenario>.lean, a module the kernel checks with the standard axioms only, stating the invariant of each state-invariant claim that holds. Needs lake.',
    options: { bound: { type: 'string' }, 'max-states': { type: 'string' }, steps: { type: 'boolean' }, module: { type: 'boolean' }, ...INLINE_OPTIONS },
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
        const result = proveScenario(model, id, { bound: count('bound'), maxStates: count('max-states'), withSteps: ctx.values.steps === true, module: ctx.values.module === true, log: ctx.log });
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
      const claimResults = evaluateClaims(model, { recorded: data.recorded ?? undefined, stamps: currentStamps(ctx.repoRoot) });
      const traceability = checkTraceability(model, ctx.repoRoot, loadRoots(ws, ctx));
      const generatorFile = path.join(HERE, '..', 'src', 'core', 'generate', 'index.js');
      if (!fs.existsSync(generatorFile)) throw new CliError('generate.unavailable', 'src/core/generate/index.js does not exist.');
      const { generateAll } = await import(pathToFileURL(generatorFile).href);
      // The documents describe the declared model: the extracted relationships (hundreds of them) are facts to query, not prose.
      const files = generateAll(stripExtracted(model), { claimResults, diagnostics: project.diagnostics, traceability });
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
    summary: 'Compare declared implementation modules with the files on disk: this repository, or the realisation roots project.jsonc declares. Missing modules and unclaimed files are listed and exit 0; a file covered by two module elements (traceability.multiple-owners) is an error.',
    run: async (ctx) => {
      const { ws, project } = await loadProject(ctx);
      const model = requireModel(project);
      const result = checkTraceability(model, ctx.repoRoot, loadRoots(ws, ctx));
      if (result.errors.length) throw new CliError('traceability.multiple-owners', `${result.errors.length} file(s) belong to more than one module element.`, { diagnostics: result.errors, result });
      return { result, semanticHash: project.semanticHash };
    },
  },

  extract: {
    usage: 'extract [--check]',
    summary: 'Run the static extractor (tools/extract.js) over the implementation surface and write the fact file (specs/<project>/extracted/facts.json): per file its digest and its imports, re-exports and dynamic imports, with the extractor identity and version, and the claim markers of the test files (// @evidence <claim>...), from which the model derives the test evidence. With --check, write nothing and report whether the fact file describes the tree (exit 1 when it does not). Static structure only.',
    options: { check: { type: 'boolean' } },
    run: async (ctx) => {
      const { project } = await loadProject(ctx);
      const target = path.join(ctx.specs, ctx.projectName, FACT_FILES.extracted);
      if (ctx.values.check === true) {
        const stored = readFacts(target);
        const drift = stored ? factsDrift(stored, ctx.repoRoot) : null;
        const ok = !!drift && !drift.changed.length && !drift.missing.length && !drift.gone.length && !drift.extractor && !drift.evidence;
        if (!ok) throw new CliError('extract.stale', stored ? `The fact file does not describe the tree: ${drift?.changed.length} changed, ${drift?.missing.length} new, ${drift?.gone.length} gone file(s)${drift?.evidence ? ', and the claim markers of the tests changed' : ''}${drift?.extractor ? ', and another extractor version wrote it' : ''}.` : 'There is no fact file.', { result: { drift } });
        return { result: { current: true, files: stored?.files.length ?? 0 }, semanticHash: project.semanticHash };
      }
      const facts = extractRepository(ctx.repoRoot);
      fs.mkdirSync(path.dirname(target), { recursive: true });
      fs.writeFileSync(target, factsText(facts));
      return { result: { wrote: path.relative(ctx.repoRoot, target).split(path.sep).join('/'), files: facts.files.length, imports: facts.files.reduce((n, f) => n + f.imports.length, 0), evidence: facts.evidence?.length ?? 0, evidenceProblems: facts.evidenceProblems?.length ?? 0, extractor: facts.extractor }, semanticHash: project.semanticHash };
    },
  },

  reconcile: {
    usage: 'reconcile [--observed <recording facts file>]',
    summary: 'Reconcile the declared relationships with the extracted facts attached to the project (inside the extraction surface a static dependency is derived from the code, so a declared one is redundant, unwitnessed, reversed or of another kind), and with an observed recording when --observed names its fact file (tools/observe.js): an observed interaction with no declared relationship is reported, and a declared runtime interaction the recording does not show is reported as not observed, never as false. Extracted dependencies with no declared counterpart are not reported: they are the dependency. Runtime wiring is declared and never flagged for being unextracted.',
    options: { observed: { type: 'string' } },
    run: async (ctx) => {
      const { project } = await loadProject(ctx);
      const base = requireModel(project);
      /** @type {any} */
      let observed = null;
      if (typeof ctx.values.observed === 'string') {
        try { observed = JSON.parse(fs.readFileSync(path.resolve(process.cwd(), ctx.values.observed), 'utf8')); } catch (e) { throw new CliError('reconcile.observed', `The observed facts ${ctx.values.observed} cannot be read: ${/** @type {Error} */ (e).message}`); }
      }
      const model = attachObserved(base, observed);
      const r = reconcile(model);
      return { result: { extraction: extractionOf(model) ? { extractor: extractionOf(model)?.facts.extractor, files: extractionOf(model)?.facts.files.length, relationships: extractionOf(model)?.edges.length, external: extractionOf(model)?.external.length } : null, observed: observed ? observed.recording : null, ...r }, semanticHash: project.semanticHash };
    },
  },

  cut: {
    usage: 'cut [--cut <id>] [--hierarchy <id>] [--depth N | --expand a,b | --finest]',
    summary: 'The blocks of a cut and its abstraction map: every element at or below the cut -> its block (alpha_C), and the elements the cut opens. --cut names a declared cut; otherwise --hierarchy (default logical) with --depth, --expand or --finest gives an ad hoc one. With no option, lists the hierarchies and the declared cuts.',
    options: { cut: { type: 'string' }, hierarchy: { type: 'string' }, depth: { type: 'string' }, expand: { type: 'string' }, finest: { type: 'boolean' }, ...INLINE_OPTIONS },
    run: async (ctx) => {
      const { project } = await loadProject(ctx);
      const model = requireModel(project);
      const { cut, hierarchy, depth, expand, finest } = ctx.values;
      if (cut === undefined && hierarchy === undefined && depth === undefined && expand === undefined && finest === undefined) {
        const hierarchies = hierarchyIds(model).map((id) => {
          const h = /** @type {any} */ (hierarchyOf(model, id));
          return { id, roots: h.roots.length, elements: h.order.length, depth: Math.max(0, ...h.depth.values()) };
        });
        const cuts = (model.byKind.cut ?? []).map((c) => {
          const m = cutMap(model, c.id);
          return { id: c.id, name: c.data.name ?? null, hierarchy: m?.hierarchy ?? null, blocks: m?.blocks.length ?? null };
        });
        return { result: { hierarchies, cuts }, semanticHash: project.semanticHash };
      }
      /** @type {{cut: string|null, hierarchy: string, blocks: string[], expanded: string[], map: Map<string, string>, problems: any[]}} */
      let m;
      if (cut !== undefined) {
        if (hierarchy !== undefined || depth !== undefined || expand !== undefined || finest !== undefined) throw usage('invalid-argument', '--cut names a declared cut; it takes none of --hierarchy, --depth, --expand, --finest.');
        requireEntity(model, cut, 'cut');
        const found = cutMap(model, cut);
        if (!found) throw new CliError('cut.hierarchy', `Cut "${cut}" is of a hierarchy the model does not have.`);
        m = found;
      } else {
        const hid = hierarchy ?? 'logical';
        const h = hierarchyOf(model, hid);
        if (!h) throw usage('invalid-argument', `Unknown hierarchy "${hid}"; the hierarchies are: ${hierarchyIds(model).join(', ')}.`);
        let d;
        if (depth !== undefined) {
          d = Number(depth);
          if (!Number.isInteger(d) || d < 0) throw usage('invalid-argument', '--depth must be a whole number of at least 0.');
        }
        const r = cutBlocksOf(h, { expand: listValue(expand), depth: d, finest: finest === true });
        m = { cut: null, hierarchy: hid, blocks: r.blocks, expanded: r.expanded, map: abstractionOf(h, r.blocks), problems: r.problems };
      }
      if (m.problems.length) throw new CliError('cut.invalid', `The cut is not well formed: ${m.problems.map((p) => p.message).join(' ')}`, { result: { problems: m.problems } });
      /** @type {Record<string, string[]>} */
      const members = {};
      for (const [e, b] of m.map) (members[b] ??= []).push(e);
      return {
        result: {
          cut: m.cut, hierarchy: m.hierarchy,
          blocks: m.blocks.map((b) => ({ id: b, kind: elementKindOf(model, b), elements: members[b]?.length ?? 0 })),
          expanded: m.expanded,
          map: Object.fromEntries(m.map),
        },
        semanticHash: project.semanticHash,
      };
    },
  },

  'compose-functions': {
    usage: 'compose-functions [<functionId>]',
    summary: 'Functional composition along the hierarchy (src/core/function-composition.js): the functions attached to elements (function.element) and, for each function that declares a composition, its stages with their signatures, the signature the composition derives (first stage parameters, last stage returns, the shared error union), the declared one, and every disagreement (function.composition-*). With a function id, only that composite. A project whose composition does not hold still succeeds; the problems are the finding.',
    options: { ...INLINE_OPTIONS },
    run: async (ctx) => {
      const { project } = await loadProject(ctx);
      const model = requireModel(project);
      const id = ctx.positionals[0];
      const r = functionComposition(model);
      if (id !== undefined) requireEntity(model, id, 'function');
      const composites = id === undefined ? r.composites : r.composites.filter((c) => c.function === id);
      return { result: { attached: id === undefined ? r.attached : r.attached.filter((a) => a.function === id), composites, holds: composites.every((c) => c.holds) }, semanticHash: project.semanticHash };
    },
  },

  'lift-faults': {
    usage: 'lift-faults [--cut <id>] [--hierarchy <id>] [--depth N | --expand a,b | --finest]',
    summary: 'Fault lifting (src/core/fault-lifting.js): each failure mode located at an element or an interaction, with the logical interactions it fails directly and through realisation maps (a hop of a realisation path, or an element of the realisation hierarchy such as a host that a hop runs through), as the interaction failure its kind causes (unavailable, delayed, lost, ...). Then lifted with a cut: the failure of each derived interaction (from, to, kind) and the failures internal to a block. A deployment-level fault thus appears at the logical level as the interaction failures it causes. --cut names a declared cut; otherwise --hierarchy (default logical) with --depth, --expand or --finest (default: finest) gives an ad hoc one.',
    options: { cut: { type: 'string' }, hierarchy: { type: 'string' }, depth: { type: 'string' }, expand: { type: 'string' }, finest: { type: 'boolean' }, ...INLINE_OPTIONS },
    run: async (ctx) => {
      const { project } = await loadProject(ctx);
      const model = requireModel(project);
      const { cut, hierarchy, depth, expand, finest } = ctx.values;
      /** @type {{hierarchy: string, cut: string|null, map: Map<string, string>}} */
      let level;
      if (cut !== undefined) {
        if (hierarchy !== undefined || depth !== undefined || expand !== undefined || finest !== undefined) throw usage('invalid-argument', '--cut names a declared cut; it takes none of --hierarchy, --depth, --expand, --finest.');
        requireEntity(model, cut, 'cut');
        const found = cutMap(model, cut);
        if (!found) throw new CliError('cut.hierarchy', `Cut "${cut}" is of a hierarchy the model does not have.`);
        if (found.problems.length) throw new CliError('cut.invalid', `The cut is not well formed: ${found.problems.map((p) => p.message).join(' ')}`, { result: { problems: found.problems } });
        level = { hierarchy: found.hierarchy, cut: found.cut, map: found.map };
      } else {
        const hid = hierarchy ?? 'logical';
        const h = hierarchyOf(model, hid);
        if (!h) throw usage('invalid-argument', `Unknown hierarchy "${hid}"; the hierarchies are: ${hierarchyIds(model).join(', ')}.`);
        let d;
        if (depth !== undefined) {
          d = Number(depth);
          if (!Number.isInteger(d) || d < 0) throw usage('invalid-argument', '--depth must be a whole number of at least 0.');
        }
        const useFinest = finest === true || (d === undefined && expand === undefined);
        const r = cutBlocksOf(h, { expand: listValue(expand), depth: d, finest: useFinest });
        if (r.problems.length) throw new CliError('cut.invalid', `The cut is not well formed: ${r.problems.map((p) => p.message).join(' ')}`, { result: { problems: r.problems } });
        level = { hierarchy: hid, cut: null, map: abstractionOf(h, r.blocks) };
      }
      return { result: liftFaults(model, level), semanticHash: project.semanticHash };
    },
  },

  derive: {
    usage: 'derive [--cut <id>] [--hierarchy <id>] [--depth N | --expand a,b | --finest] [--coarsen <kinds>|all]',
    summary: 'The derived architectural model at a cut (src/core/abstraction.js): its blocks (with the implicit blocks of opened elements that facts are attached to), the lifted interactions per kind with their complete witness sets, summaries and footprints, the fibre of each block, its boundary, and its derived interface compared with its declared ports, connector contractions, contract realisation paths, realisation maps between hierarchies, and the diagnostics of the abstraction (V1 partition, V2 witnessed facts, V3 interface agreement, V4 kind preservation, port connections, realisations). --cut names a declared cut; otherwise --hierarchy (default logical) with --depth, --expand or --finest gives an ad hoc one. --coarsen relabels each kind to its nearest listed ancestor kind (all: to the kinds directly under interacts-with). Loads no renderer code.',
    options: { cut: { type: 'string' }, hierarchy: { type: 'string' }, depth: { type: 'string' }, expand: { type: 'string' }, finest: { type: 'boolean' }, coarsen: { type: 'string' }, ...INLINE_OPTIONS },
    run: async (ctx) => {
      const { project } = await loadProject(ctx);
      const model = requireModel(project);
      const { cut, hierarchy, depth, expand, finest, coarsen } = ctx.values;
      /** @type {any} */
      let ref;
      if (cut !== undefined) {
        if (hierarchy !== undefined || depth !== undefined || expand !== undefined || finest !== undefined) throw usage('invalid-argument', '--cut names a declared cut; it takes none of --hierarchy, --depth, --expand, --finest.');
        requireEntity(model, cut, 'cut');
        ref = { cut };
      } else {
        const hid = hierarchy ?? 'logical';
        if (!hierarchyOf(model, hid)) throw usage('invalid-argument', `Unknown hierarchy "${hid}"; the hierarchies are: ${hierarchyIds(model).join(', ')}.`);
        let d;
        if (depth !== undefined) {
          d = Number(depth);
          if (!Number.isInteger(d) || d < 0) throw usage('invalid-argument', '--depth must be a whole number of at least 0.');
        }
        ref = { hierarchy: hid, expand: listValue(expand), depth: d, finest: finest === true };
      }
      const kinds = coarsen === undefined ? null : coarsen === 'all' ? 'all' : listValue(coarsen);
      if (Array.isArray(kinds)) for (const k of kinds) if (!Object.hasOwn(model.meta.relationshipKinds, k)) throw usage('invalid-argument', `--coarsen names "${k}", which is not a relationship kind.`);
      const derived = deriveModel(model, ref, { coarsen: kinds });
      if (!derived) throw new CliError('cut.hierarchy', 'The cut is of a hierarchy the model does not have.');
      const invalid = derived.diagnostics.filter((x) => x.condition === 'V1' && x.severity === 'error');
      if (invalid.length) throw new CliError('cut.invalid', `The cut is not a valid abstraction: ${invalid.map((x) => x.message).join(' ')}`, { result: { diagnostics: invalid } });
      return { result: derivedJson(derived), semanticHash: project.semanticHash };
    },
  },

  coherence: {
    usage: 'coherence [--cut <id>]',
    summary: 'Structure-behaviour coherence (V5, src/core/coherence.js). Message interactions are derived from behaviours alone: an event emitted by a behavior whose subject is one element and consumed by a behavior whose subject is another is a message between the two. Each must be witnessed by a relationship of message class (a kind that moves control or data) between the same two elements at the base, and at a cut by a derived interaction whose witnesses include such a relationship between those two elements: a coarse edge over a different witness is reported as different-witness, never accepted. Without --cut it checks the base, every hierarchy at its finest cut and every declared cut, and lists each unwitnessed message once with the cuts that report it. Reports the event, the emitting and consuming behaviors, the elements and the cut.',
    options: { cut: { type: 'string' }, ...INLINE_OPTIONS },
    run: async (ctx) => {
      const { project } = await loadProject(ctx);
      const model = requireModel(project);
      const { cut } = ctx.values;
      if (cut === undefined) return { result: coherenceReport(model), semanticHash: project.semanticHash };
      requireEntity(model, cut, 'cut');
      const one = checkCoherence(model, { cut });
      return { result: { ok: one.findings.length === 0, ...one }, semanticHash: project.semanticHash };
    },
  },

  'boundary-contracts': {
    usage: 'boundary-contracts',
    summary: 'Contract conformance at boundaries (V7, src/core/coherence.js): every relationship that declares a contract must have the events that cross it typed by that contract. Reports each hop where events pass between the two elements and none belongs to the contract (untyped), with the events that pass; hops where no behavior exchanges an event are listed apart as unmodelled (nothing crosses, so nothing is untyped, but nothing shows the contract is followed).',
    options: { ...INLINE_OPTIONS },
    run: async (ctx) => {
      const { project } = await loadProject(ctx);
      return { result: checkContractConformance(requireModel(project)), semanticHash: project.semanticHash };
    },
  },

  decompose: {
    usage: 'decompose --scope <element> [--grain children|leaves|modules] [--source <sources>] [--file <candidates.json>] [--provenance <list>] [--dir-depth N] [--candidate <id>] [--evidence]',
    summary: 'Candidate decompositions of an element (src/core/decomposition.js, M7 structural): a candidate is a hierarchy over the same elements and never changes a fact. Candidates are generated from the established semantics (--source: declared, directory, cycles, contracts, connectors, refinement; default all) and read from --file (a JSON list, or {scope, grain, candidates: [{id, blocks: [{id, members}], rest}]}). Each is checked against the validity conditions: the structural ones V1 partition, V2 witnessed coarse facts, V3 interface agreement and V4 kind preservation, and the behavioural ones V5 structure-behaviour coherence of the messages between blocks, V6 refinement where a block declares abstract behaviour (not applicable, with the reason, where none does) and V7 contract conformance of the boundaries between blocks; an invalid candidate is rejected with its failing condition and witnesses. `accept-decomposition` records one as a named hierarchy. A valid one is measured (boundary size, cohesion, coupling, cycles by class with back edges, interface size, contract coverage, redundancy, knowledge and provenance mix) and the measurements are put side by side in `comparison`; nothing is ranked or accepted, valid is not meaningful, and no fact changes. --candidate reports one candidate in full with the evidence of each boundary (crossing witnesses, cycle back edges, interactions no contract covers); --evidence adds it to every candidate. --provenance restricts the fact base (declared reproduces the audit\'s declared-relationship base). --grain names the elements regrouped: the scope\'s children (default), its leaves, or its module elements.',
    options: { scope: { type: 'string' }, grain: { type: 'string' }, source: { type: 'string' }, file: { type: 'string' }, provenance: { type: 'string' }, 'dir-depth': { type: 'string' }, candidate: { type: 'string' }, evidence: { type: 'boolean' }, ...INLINE_OPTIONS },
    run: async (ctx) => {
      const { project } = await loadProject(ctx);
      const model = requireModel(project);
      const { scope, grain, provenance, common, generated, all } = gatherCandidates(ctx, model);
      const v = ctx.values;
      const chosen = v.candidate === undefined ? all : all.filter((c) => c.id === v.candidate);
      if (v.candidate !== undefined && !chosen.length) throw new CliError('candidate.unknown', `No candidate "${v.candidate}"; the candidates are ${all.map((c) => c.id).join(', ')}.`);
      const cmp = compareCandidates(model, chosen, { ...common, evidence: true });
      const full = v.candidate !== undefined || v.evidence === true;
      const reports = cmp.reports.map((r) => (full ? r : { ...r, evidence: null, acceptance: undefined }));
      return {
        result: {
          scope, grain, provenance: provenance ?? 'all', grainElements: generated.universe.length,
          conditions: VALIDITY_CONDITIONS.map((c) => c.id), notEvaluated: BEHAVIOURAL_CONDITIONS.filter((id) => !VALIDITY_CONDITIONS.some((c) => c.id === id)),
          candidates: reports, comparison: { candidates: cmp.candidates, rows: cmp.rows }, skipped: generated.skipped, note: NOT_MEANING,
        },
        semanticHash: project.semanticHash,
      };
    },
  },

  'accept-decomposition': {
    usage: "accept-decomposition --candidate <id> [--scope <element>] [--grain children|leaves] [--source <sources>] [--file <candidates.json>] [--provenance <list>] [--dir-depth N] [--dry-run] [--label <text>] [--expect-hash <hash>]",
    summary: 'Accept one candidate decomposition (src/core/decomposition.js, M7): a person deciding, recorded as one transaction that is one entry of the undo history. The candidate is generated or read as `decompose` does and evaluated first; it is refused (accept.not-valid, with its report) unless every validity condition V1 to V7 holds, and a measurement never accepts anything. The transaction creates the components the blocks need, the named hierarchy (the logical placement with the blocks under the scope) and two cuts of it, `<id>-top` (the scope as one block) and `<id>-cut` (the scope opened into the blocks), so the application navigates it at once (hierarchy and cut selectors) and a claim stated at a cut evaluates at them. --dry-run runs the transaction and writes nothing. Blocks of module elements cannot be recorded (accept.unrecordable).',
    options: { scope: { type: 'string' }, grain: { type: 'string' }, source: { type: 'string' }, file: { type: 'string' }, provenance: { type: 'string' }, 'dir-depth': { type: 'string' }, candidate: { type: 'string' }, 'dry-run': { type: 'boolean' }, label: { type: 'string' }, 'expect-hash': { type: 'string' } },
    run: async (ctx) => {
      const loaded = await loadProject(ctx);
      const { project } = loaded;
      const model = requireModel(project);
      const { common, all } = gatherCandidates(ctx, model);
      const id = ctx.values.candidate;
      if (id === undefined) throw usage('missing-argument', '--candidate names the candidate to accept.');
      const cand = all.find((c) => c.id === id);
      if (!cand) throw new CliError('candidate.unknown', `No candidate "${id}"; the candidates are ${all.map((c) => c.id).join(', ')}.`);
      const decided = acceptCandidate(project, cand, { ...common, dryRun: true });
      if (!decided.ok) throw new CliError(/** @type {string} */ (decided.code), /** @type {string} */ (decided.message), { result: { candidate: decided.report } });
      const applied = await applyOperationList(ctx, decided.operations, { label: ctx.values.label ?? `Accept decomposition ${id}`, loaded });
      const a = /** @type {NonNullable<typeof decided.report.acceptance>} */ (decided.report.acceptance);
      return {
        result: {
          accepted: id, scope: decided.report.scope, hierarchy: a.hierarchy.id, unrecorded: a.unrecorded, emptied: a.emptied, cuts: a.cuts.map((c) => c.id), components: a.components.map((c) => c.id), operations: decided.operations,
          conditions: decided.report.conditions.map((c) => ({ id: c.id, status: c.status, ...('reason' in c ? { reason: c.reason } : {}) })),
          transaction: applied.result, note: 'Accepted by a person through a transaction; undo reverses it as one step. Valid is not meaningful.',
        },
        semanticHash: applied.semanticHash,
      };
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
    summary: 'Branch coverage of the function examples: for each function, the branches (if then and else, match arms, try value and error paths, fail) its examples take, covered/total, with the uncovered branches and where they are. --branches lists every branch. Exits 0; informational only, readiness does not ask for every branch to be taken.',
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
    usage: 'verify [--skip-browser] [--ingest-only] [--fresh] [--expect-violated a,b] [--accept-change a,b] [--change <change.json>]',
    summary: "Validate, check traceability, execute test evidence (reusing outcomes recorded on the same tree unless --fresh), record the results with the tree stamp and re-evaluate the claims. Fails on a claim that fell from a positive status or was removed since the last passing run, and on a changed counterexample of an expected-violated claim, unless --accept-change names it. Evidence in a realisation root is read from its JUnit reports; --ingest-only reads them without running the roots' test commands. With --change (a change set naming the entities and files changed since the last verification), only the evidence of the claims the change re-marks runs; the others keep the results the last verification recorded fresh.",
    options: { 'skip-browser': { type: 'boolean' }, 'ingest-only': { type: 'boolean' }, fresh: { type: 'boolean' }, 'expect-violated': { type: 'string' }, 'accept-change': { type: 'string' }, change: { type: 'string' } },
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

Object.assign(COMMANDS, readCommands({ loadProject, requireModel, requireEntity, usage, INLINE_OPTIONS, listValue, entityLabel }));
Object.assign(COMMANDS, compositionCommands({ loadProject, requireModel, requireEntity, usage, INLINE_OPTIONS, listValue, CliError }));

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
