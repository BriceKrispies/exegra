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
import { createWorkspace, WorkspaceError } from '../tools/workspace.js';
import { checkTraceability } from '../tools/traceability.js';
import { resolveRoots, splitRootRef, collectExternalResults, RootsError } from '../tools/realisation-roots.js';
import { Project } from '../src/core/project.js';
import { OPERATIONS, OpError, Tx, planDelete } from '../src/core/operations.js';
import { analyzeSpec } from '../src/core/analyze.js';
import { evaluateIntegrity, counterexampleJson } from '../src/core/integrity.js';
import { proveIntegrity } from '../tools/prove-integrity.js';
import {
  entityLabel, childrenOf, ancestorsOf, inboundRefs, relationshipsOf, dependencies, contractsOf,
} from '../src/core/query.js';
import { evaluateClaims, evaluateClaim, checkTrace } from '../src/core/claims.js';
import { requestLog } from '../src/core/contract-trace.js';
import { runScenario } from '../src/core/engine.js';
import { proveScenario, ProveError } from '../tools/prove.js';
import { CLAIM_STATUSES } from '../src/core/claim-methods.js';
import { stableStringify } from '../src/core/hash.js';

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
const SAFE_TEST_REF = /^[A-Za-z0-9_./\- #:]+$/;
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
    source: { line: e.loc.line, column: e.loc.column },
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

/** @param {{status: string}[]} results */
function summarize(results) {
  /** @type {Record<string, number>} */
  const summary = { total: results.length, verified: 0, supported: 0, violated: 0, inconclusive: 0, 'not-evaluated': 0 };
  for (const r of results) {
    if (r.status in summary) summary[r.status] += 1;
  }
  return summary;
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
 * Read the project's files and build a Project from them.
 * @param {any} ctx
 */
async function loadProject(ctx) {
  const ws = createWorkspace(ctx.specs);
  let data;
  try {
    data = await ws.read(ctx.projectName);
  } catch (err) {
    if (err instanceof WorkspaceError && err.code === 'not-found') {
      throw new CliError('project.not-found', `Project "${ctx.projectName}" was not found in ${ctx.specs}.`);
    }
    throw err;
  }
  const project = new Project({
    name: ctx.projectName,
    specText: data.spec.text,
    layoutText: data.layout?.text ?? null,
  });
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
  const tx = new Tx(project.specText, project.layoutText, model);
  try {
    for (const data of rules) OPERATIONS.CreateEntity.apply(tx, { type: 'CreateEntity', kind: 'integrityRule', data });
  } catch (err) {
    if (err instanceof OpError) throw new CliError(err.code, err.message, { diagnostics: err.diagnostics.map(serializeDiagnostic) });
    throw err;
  }
  const a = analyzeSpec(tx.specText);
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
 * Execute one test evidence reference.
 * @param {string} ref
 * @param {{repoRoot: string, skipBrowser: boolean, log: (m: string) => void}} env
 * @returns {{outcome: 'pass'|'fail'|'skipped', detail?: string}}
 */
function runTestReference(ref, env) {
  if (!SAFE_TEST_REF.test(ref)) return { outcome: 'fail', detail: 'unsafe reference' };
  const hashAt = ref.indexOf('#');
  const file = (hashAt < 0 ? ref : ref.slice(0, hashAt)).trim();
  const pattern = hashAt < 0 ? '' : ref.slice(hashAt + 1).trim();
  if (file === '') return { outcome: 'fail', detail: 'unsafe reference' };
  const abs = path.resolve(env.repoRoot, file);
  if (!isInside(env.repoRoot, abs)) return { outcome: 'fail', detail: 'unsafe reference' };
  if (!fs.existsSync(abs) || !fs.statSync(abs).isFile()) return { outcome: 'fail', detail: 'test file not found' };

  const browser = file.startsWith(BROWSER_TEST_PREFIX);
  if (browser && env.skipBrowser) return { outcome: 'skipped' };

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
    if (!browser) {
      // node exits 0 when the pattern or file matches no test; that is not a pass.
      if (countPassingTests(String(run.stdout ?? ''), file) === 0) return { outcome: 'fail', detail: 'the reference matched no test' };
    }
    return { outcome: 'pass' };
  }
  if (run.error) return { outcome: 'fail', detail: run.error.message };
  const lines = `${run.stdout ?? ''}${run.stderr ?? ''}`.replace(/\s+$/, '').split(/\r?\n/);
  return { outcome: 'fail', detail: lines.slice(-TEST_OUTPUT_TAIL_LINES).join('\n') };
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
  /** @type {Record<string, {outcome: 'pass'|'fail'|'not-run', detail?: string, ranAt?: string}>} */
  const results = {};
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
      results[ev.id] = ext;
      evidence.push({ ...base, ...ext });
      continue;
    }
    const run = runTestReference(String(ev.data.ref), { repoRoot: ctx.repoRoot, skipBrowser, log: ctx.log });
    if (run.outcome === 'skipped') {
      evidence.push({ ...base, outcome: 'skipped' });
      continue;
    }
    const record = { outcome: run.outcome, ...(run.detail !== undefined ? { detail: run.detail } : {}), ranAt: new Date().toISOString() };
    results[ev.id] = record;
    evidence.push({ ...base, ...record });
  }

  // (4) record the results
  // Outcomes an external verification tool recorded per claim live in the same
  // file; this command owns only `results` and `traceability` and keeps the rest.
  /** @type {Record<string, any>} */
  const kept = {};
  const prior = (await ws.read(ctx.projectName)).recorded;
  if (prior && typeof prior === 'object') for (const k of ['tool', 'version', 'source', 'claims', 'lint']) if (Object.hasOwn(prior, k)) kept[k] = /** @type {any} */ (prior)[k];
  await ws.writeRecorded(ctx.projectName, { ...kept, results, traceability });

  // (5) re-evaluate the claims with the new results
  const claimResults = evaluateClaims(model, { recorded: { results } });
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
 * @typedef {{usage: string, summary: string, options?: Record<string, any>, run: (ctx: any) => Promise<{result: any, semanticHash?: string}>}} CommandDef
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

  validate: {
    usage: 'validate',
    summary: 'Validate the project. ok is true only when there are no errors.',
    run: async (ctx) => {
      const { project } = await loadProject(ctx);
      const counts = countSeverities(project.diagnostics);
      const result = { ...counts, diagnostics: project.diagnostics.map(serializeDiagnostic) };
      if (counts.errors > 0) {
        throw new CliError('validation.failed', `${counts.errors} validation error(s).`, { diagnostics: result.diagnostics, result });
      }
      return { result, semanticHash: project.semanticHash };
    },
  },

  list: {
    usage: 'list [--kind <kind>] [--owner <id>]',
    summary: 'List entities in declaration order (without data).',
    options: { kind: { type: 'string' }, owner: { type: 'string' } },
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
    options: { direction: { type: 'string' }, transitive: { type: 'boolean' }, kinds: { type: 'string' } },
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
    options: { status: { type: 'string' } },
    run: async (ctx) => {
      const { data, project } = await loadProject(ctx);
      const model = requireModel(project);
      const { status } = ctx.values;
      if (status !== undefined && !(status in CLAIM_STATUSES)) {
        throw usage('invalid-argument', `--status must be one of: ${Object.keys(CLAIM_STATUSES).join(', ')}.`);
      }
      const result = evaluateClaims(model, { recorded: data.recorded ?? undefined })
        .map((r) => {
          const claim = model.entities.get(r.claimId);
          return { ...r, statement: claim?.data.statement ?? null, kind: claim?.data.kind ?? r.kind };
        })
        .filter((r) => status === undefined || r.status === status);
      return { result, semanticHash: project.semanticHash };
    },
  },

  evaluate: {
    usage: 'evaluate [<claimId>]',
    summary: 'Evaluate one claim or all claims. A violated claim is a finding; the command still succeeds.',
    run: async (ctx) => {
      const { data, project } = await loadProject(ctx);
      const model = requireModel(project);
      const recorded = data.recorded ?? undefined;
      const id = ctx.positionals[0];
      const results = id !== undefined
        ? [evaluateClaim(model, requireEntity(model, id, 'claim').id, { recorded })]
        : evaluateClaims(model, { recorded });
      return { result: { results, summary: summarize(results) }, semanticHash: project.semanticHash };
    },
  },

  gaps: {
    usage: 'gaps',
    summary: 'Unspecified or inconsistent things: warnings and gaps, open unknowns, unevaluated claims, components without realisation.',
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
      /** @type {('spec'|'layout')[]} */
      const written = [];
      if (!dryRun) {
        const meta = { label: label ?? list.map((o) => o.type).join(', '), origin: 'cli' };
        if (project.specText !== initialSpec) {
          const w = await ws.write(ctx.projectName, 'spec', project.specText, data.spec.hash, meta);
          if (!w.ok) throw new CliError('write.conflict', 'spec.jsonc changed on disk since it was read; nothing was written.');
          written.push('spec');
        }
        if (project.layoutText !== initialLayout) {
          const w = await ws.write(ctx.projectName, 'layout', project.layoutText, data.layout?.hash ?? null, meta);
          if (!w.ok) {
            const note = written.length ? ' The specification was already written; the layout was not.' : ' Nothing was written.';
            throw new CliError('write.conflict', `layout.jsonc changed on disk since it was read.${note}`);
          }
          written.push('layout');
        }
      }

      const result = {
        revision: project.revision,
        semanticHashBefore: hashBefore,
        semanticHashAfter: project.semanticHash,
        semanticChanged: tx.semanticChanged,
        affected: tx.affected,
        written,
        dryRun,
      };
      return { result, semanticHash: dryRun ? hashBefore : project.semanticHash };
    },
  },

  'plan-delete': {
    usage: 'plan-delete <id>',
    summary: 'What a cascade delete of an entity would remove and repair. Changes nothing.',
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
    options: { faults: { type: 'string' }, steps: { type: 'boolean' } },
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
    options: { bound: { type: 'string' }, 'max-states': { type: 'string' }, steps: { type: 'boolean' } },
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
    options: { rules: { type: 'string' }, limit: { type: 'string' } },
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
    usage: 'prove-integrity [<ruleId>] [--rules <file>] [--max-witnesses N]',
    summary: 'Prove or refute integrity rules in Lean: holds (a kernel-checked proof by reflection), violated (a kernel-checked refutation from each concrete witness, up to --max-witnesses, default 10), or incomplete. The Lean checker and the JavaScript evaluator must agree. Needs lake. Fails when a rule is incomplete.',
    options: { rules: { type: 'string' }, 'max-witnesses': { type: 'string' } },
    run: async (ctx) => {
      const { project } = await loadProject(ctx);
      const model = modelWithRules(ctx, project);
      const ids = selectRules(ctx, model);
      const mw = ctx.values['max-witnesses'] === undefined ? undefined : Number(ctx.values['max-witnesses']);
      if (mw !== undefined && !(Number.isInteger(mw) && mw >= 1)) throw usage('invalid-argument', '--max-witnesses must be a positive integer.');
      let rules;
      try {
        rules = proveIntegrity(model, ids, { maxWitnesses: mw, log: ctx.log });
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

  verify: {
    usage: 'verify [--skip-browser] [--ingest-only] [--expect-violated a,b]',
    summary: "Validate, check traceability, execute test evidence, record the results and re-evaluate the claims. Evidence in a realisation root is read from its JUnit reports; --ingest-only reads them without running the roots' test commands.",
    options: { 'skip-browser': { type: 'boolean' }, 'ingest-only': { type: 'boolean' }, 'expect-violated': { type: 'string' } },
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

  const projectName = parsed.values.project ?? options.project ?? DEFAULT_PROJECT;
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
