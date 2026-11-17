// Realisation roots: other repositories a project is realised in, declared in
// specs/<project>/project.jsonc. Node-only. See docs/verification.md.
//
//   "roots": {
//     "platform": {
//       "path": "../../../other-repo",
//       "include": ["apps/*/src/**/*.ts"], "exclude": ["**/*.test.ts"],
//       "tests": [{ "command": ["bun", "test", "--reporter=junit", "--reporter-outfile=.exegra/junit.xml"],
//                   "cwd": "apps/api", "junit": "apps/api/.exegra/junit.xml" }],
//       "notRunWhen": ["ECONNREFUSED", "docker"]
//     }
//   }
//
// A module or test evidence ref written "<alias>:<path>" points into a root.

import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { parseJUnit } from './junit.js';

/** @typedef {import('./junit.js').JUnitCase} JUnitCase */
/**
 * @typedef {{command: string[]|null, cwd: string, junit: string, base: string}} TestRun
 *   cwd and base are relative to the root, junit is too unless absolute; base is the
 *   directory the report's file attributes are relative to (default: cwd).
 * @typedef {{alias: string, path: string, include: string[], exclude: string[], tests: TestRun[], notRunWhen: RegExp[]}} RealisationRoot
 * @typedef {{outcome: 'pass'|'fail'|'not-run', detail?: string, ranAt?: string, root: string, reports: string[]}} ExternalResult
 */

const ALIAS = /^[a-z][a-z0-9_-]*$/;
const ROOT_REF = /^([a-z][a-z0-9_-]*):(.+)$/;
/** Failure texts that mean the environment was missing, not that the requirement failed. */
export const DEFAULT_NOT_RUN_WHEN = ['ECONNREFUSED', 'ENOTFOUND', 'EAI_AGAIN', 'docker', 'testcontainers', 'container runtime'];
const SKIP_DIRS = new Set(['node_modules', '.git']);
const RUN_TIMEOUT_MS = 30 * 60 * 1000;
const OUTPUT_MAX_BYTES = 64 * 1024 * 1024;
const DETAIL_TAIL_LINES = 20;

/** Error with a stable code, raised for a malformed roots declaration. */
export class RootsError extends Error {
  /** @param {string} message */
  constructor(message) {
    super(message);
    this.name = 'RootsError';
    this.code = 'roots.invalid';
  }
}

/** @param {string} p */
const slash = (p) => p.replace(/\\/g, '/');

/** @param {string} p relative path; '' for the root itself */
function relPath(p) {
  const n = path.posix.normalize(slash(p)).replace(/^\.\/?/, '').replace(/\/$/, '');
  return n === '.' ? '' : n;
}

/** @param {unknown} v */
const isObject = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);

/** @param {unknown} v @param {string} where @returns {string[]} */
function stringList(v, where) {
  if (v === undefined) return [];
  if (!Array.isArray(v) || !v.every((s) => typeof s === 'string' && s !== '')) throw new RootsError(`${where} must be a list of non-empty strings.`);
  return v;
}

/**
 * The roots a project.jsonc declares, sorted by alias. Relative paths resolve
 * against the project directory. Empty when there is no project.jsonc or no roots.
 * @param {{dir: string, value: Record<string, any>}|null} config
 * @returns {RealisationRoot[]}
 */
export function resolveRoots(config) {
  const raw = config?.value?.roots;
  if (raw === undefined) return [];
  if (!isObject(raw)) throw new RootsError('"roots" must be an object of alias -> root.');
  /** @type {RealisationRoot[]} */
  const out = [];
  for (const alias of Object.keys(raw).sort()) {
    const r = raw[alias];
    const where = `roots.${alias}`;
    if (!ALIAS.test(alias)) throw new RootsError(`Root alias "${alias}" must match ${ALIAS}.`);
    if (!isObject(r) || typeof r.path !== 'string' || r.path === '') throw new RootsError(`${where} must be an object with a non-empty "path".`);
    const runs = r.tests === undefined ? [] : Array.isArray(r.tests) ? r.tests : [r.tests];
    const tests = runs.map((/** @type {any} */ t, /** @type {number} */ i) => {
      const at = `${where}.tests[${i}]`;
      if (!isObject(t) || typeof t.junit !== 'string' || t.junit === '') throw new RootsError(`${at} must name its JUnit report in "junit".`);
      if (t.command !== undefined && (!Array.isArray(t.command) || !t.command.length || !t.command.every((/** @type {unknown} */ s) => typeof s === 'string'))) {
        throw new RootsError(`${at}.command must be a non-empty list of strings (program and arguments; no shell).`);
      }
      for (const k of ['cwd', 'base']) if (t[k] !== undefined && typeof t[k] !== 'string') throw new RootsError(`${at}.${k} must be a string.`);
      const cwd = relPath(t.cwd ?? '');
      return { command: t.command ?? null, cwd, junit: path.isAbsolute(t.junit) ? slash(path.resolve(t.junit)) : relPath(t.junit), base: relPath(t.base ?? cwd) };
    });
    const patterns = r.notRunWhen === undefined ? DEFAULT_NOT_RUN_WHEN : stringList(r.notRunWhen, `${where}.notRunWhen`);
    /** @type {RegExp[]} */
    let notRunWhen;
    try {
      notRunWhen = patterns.map((p) => new RegExp(p, 'i'));
    } catch (err) {
      throw new RootsError(`${where}.notRunWhen: ${/** @type {Error} */ (err).message}`);
    }
    out.push({
      alias,
      path: path.resolve(config?.dir ?? '.', r.path),
      include: stringList(r.include, `${where}.include`),
      exclude: stringList(r.exclude, `${where}.exclude`),
      tests,
      notRunWhen,
    });
  }
  return out;
}

/**
 * Split "<alias>:<rest>" (the alias part before any "#"). Null when the text
 * does not have that form.
 * @param {string} ref
 * @returns {{alias: string, rest: string}|null}
 */
export function splitRootRef(ref) {
  const hashAt = ref.indexOf('#');
  const head = hashAt < 0 ? ref : ref.slice(0, hashAt);
  const m = ROOT_REF.exec(head);
  if (!m) return null;
  return { alias: m[1], rest: m[2] + (hashAt < 0 ? '' : ref.slice(hashAt)) };
}

// ---------------------------------------------------------------------------
// Traceability
// ---------------------------------------------------------------------------

/** @param {string} abs @param {boolean} dir */
function exists(abs, dir) {
  try {
    return dir ? fs.statSync(abs).isDirectory() : fs.statSync(abs).isFile();
  } catch {
    return false;
  }
}

/** The directory part of a glob before its first wildcard segment. @param {string} glob */
function globBase(glob) {
  const segments = slash(glob).split('/');
  const fixed = [];
  for (const s of segments.slice(0, -1)) {
    if (/[*?[{]/.test(s)) break;
    fixed.push(s);
  }
  return fixed.join('/');
}

/**
 * Files of a root matching an include glob and no exclude glob, root-relative.
 * Only the directories an include glob can reach are walked.
 * @param {RealisationRoot} root
 * @returns {string[]}
 */
export function scanRoot(root) {
  /** @type {Set<string>} */
  const found = new Set();
  /** @param {string} rel */
  const keep = (rel) => root.include.some((g) => path.posix.matchesGlob(rel, g)) && !root.exclude.some((g) => path.posix.matchesGlob(rel, g));
  /** @param {string} rel */
  const walk = (rel) => {
    let entries;
    try {
      entries = fs.readdirSync(path.join(root.path, rel), { withFileTypes: true });
    } catch {
      return;
    }
    for (const entry of entries) {
      const child = rel ? `${rel}/${entry.name}` : entry.name;
      if (entry.isDirectory()) {
        if (!SKIP_DIRS.has(entry.name)) walk(child);
      } else if (entry.isFile() && keep(child)) found.add(child);
    }
  };
  const bases = [...new Set(root.include.map(globBase))].sort();
  // A base under another base is already walked.
  for (const base of bases.filter((b, _i, all) => !all.some((o) => o !== b && (o === '' || b.startsWith(`${o}/`))))) walk(base);
  return [...found].sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
}

/**
 * Check modules declared in roots, and the include surface of each root.
 * Unclaimed files are reported as "<alias>:<path>".
 * @param {{component: string, module: string}[]} declared every module of the model, as declared
 * @param {RealisationRoot[]} roots
 */
export function traceRoots(declared, roots) {
  const byAlias = new Map(roots.map((r) => [r.alias, r]));
  /** @type {{component: string, module: string, root?: string, reason?: string}[]} */
  const missingModules = [];
  /** @type {Map<string, string[]>} alias -> claimed root-relative module paths */
  const claims = new Map(roots.map((r) => [r.alias, []]));
  /** @type {{component: string, module: string}[]} */
  const local = [];
  for (const d of declared) {
    const split = splitRootRef(d.module);
    if (!split) {
      local.push(d);
      continue;
    }
    const root = byAlias.get(split.alias);
    if (!root) {
      missingModules.push({ ...d, root: split.alias, reason: 'root not declared' });
      continue;
    }
    const isDir = split.rest.endsWith('/');
    const rel = relPath(split.rest) + (isDir ? '/' : '');
    claims.get(root.alias)?.push(rel);
    if (!exists(path.join(root.path, rel), isDir)) missingModules.push({ ...d, root: root.alias });
  }

  /** @type {string[]} */
  const unclaimedFiles = [];
  let claimedFiles = 0;
  /** @type {Record<string, {path: string, found: boolean, checkedModules: number, scanned: boolean, scannedFiles: number, unclaimedFiles: number}>} */
  const summary = {};
  for (const root of roots) {
    const mods = claims.get(root.alias) ?? [];
    const found = exists(root.path, true);
    const scanned = found && root.include.length > 0;
    const files = scanned ? scanRoot(root) : [];
    const unclaimed = files.filter((f) => !mods.some((m) => (m.endsWith('/') ? f.startsWith(m) : f === m)));
    claimedFiles += files.length - unclaimed.length;
    for (const f of unclaimed) unclaimedFiles.push(`${root.alias}:${f}`);
    summary[root.alias] = {
      path: slash(root.path), found, checkedModules: mods.length, scanned, scannedFiles: files.length, unclaimedFiles: unclaimed.length,
    };
  }
  return { local, missingModules, unclaimedFiles, claimedFiles, roots: summary };
}

// ---------------------------------------------------------------------------
// Test evidence
// ---------------------------------------------------------------------------

/**
 * Run a root's test commands (unless ingestOnly), read its JUnit reports and
 * decide each external test evidence entry.
 * @param {{id: string, ref: string}[]} evidence test evidence whose ref names a root
 * @param {RealisationRoot[]} roots
 * @param {{ingestOnly?: boolean, log?: (m: string) => void}} [opts]
 * @returns {{results: Map<string, ExternalResult>, reports: Record<string, {ran: boolean, reports: string[], problems: string[]}>}}
 */
export function collectExternalResults(evidence, roots, opts = {}) {
  const log = opts.log ?? (() => {});
  const byAlias = new Map(roots.map((r) => [r.alias, r]));
  /** @type {Map<string, ExternalResult>} */
  const results = new Map();
  /** @type {Record<string, {ran: boolean, reports: string[], problems: string[]}>} */
  const reports = {};

  /** @type {Map<string, {id: string, rest: string}[]>} */
  const wanted = new Map();
  for (const ev of evidence) {
    const split = splitRootRef(ev.ref);
    if (!split) continue;
    if (!byAlias.has(split.alias)) {
      results.set(ev.id, { outcome: 'not-run', detail: `root "${split.alias}" is not declared in project.jsonc`, root: split.alias, reports: [] });
      continue;
    }
    const list = wanted.get(split.alias) ?? [];
    list.push({ id: ev.id, rest: split.rest });
    wanted.set(split.alias, list);
  }

  for (const [alias, items] of [...wanted].sort((a, b) => (a[0] < b[0] ? -1 : 1))) {
    const root = /** @type {RealisationRoot} */ (byAlias.get(alias));
    const state = { ran: false, reports: /** @type {string[]} */ ([]), problems: /** @type {string[]} */ ([]) };
    reports[alias] = state;
    /** @type {JUnitCase[]} */
    const cases = [];
    let latest = 0;
    if (!root.tests.length) state.problems.push('the root declares no tests (JUnit report)');
    for (const run of root.tests) {
      const reportAbs = path.resolve(root.path, run.junit);
      const before = mtimeOf(reportAbs);
      if (run.command && !opts.ingestOnly) {
        state.ran = true;
        // bun refuses to write a report into a directory that does not exist.
        fs.mkdirSync(path.dirname(reportAbs), { recursive: true });
        log(`verify: running ${run.command.join(' ')} in ${alias}:${run.cwd || '.'}`);
        const proc = spawnSync(run.command[0], run.command.slice(1), {
          cwd: path.join(root.path, run.cwd), shell: false, encoding: 'utf8', timeout: RUN_TIMEOUT_MS, maxBuffer: OUTPUT_MAX_BYTES, windowsHide: true,
        });
        const after = mtimeOf(reportAbs);
        if (proc.error) {
          state.problems.push(`${run.command[0]} could not run: ${proc.error.message}`);
          continue;
        }
        // A report not rewritten by this run would be stale; ignore it.
        if (after === null || after === before) {
          state.problems.push(`${run.command.join(' ')} exited ${proc.status} and wrote no report at ${run.junit}`);
          continue;
        }
      }
      let xml;
      try {
        xml = fs.readFileSync(reportAbs, 'utf8');
      } catch {
        state.problems.push(`no JUnit report at ${run.junit}`);
        continue;
      }
      state.reports.push(run.junit);
      latest = Math.max(latest, mtimeOf(reportAbs) ?? 0);
      for (const c of parseJUnit(xml)) cases.push({ ...c, file: caseFile(c.file, run, root) });
    }
    const ranAt = latest ? new Date(latest).toISOString() : '';
    for (const item of items) {
      const decided = decide(item.rest, cases, root, state.problems);
      results.set(item.id, { ...decided, ...(ranAt ? { ranAt } : {}), root: alias, reports: [...state.reports] });
    }
  }
  return { results, reports };
}

/** @param {string} abs @returns {number|null} */
function mtimeOf(abs) {
  try {
    return fs.statSync(abs).mtimeMs;
  } catch {
    return null;
  }
}

/** A report's file attribute as a root-relative path. @param {string} file @param {TestRun} run @param {RealisationRoot} root */
function caseFile(file, run, root) {
  if (path.isAbsolute(file)) return relPath(path.relative(root.path, file));
  return relPath(run.base ? `${run.base}/${file}` : file);
}

/**
 * Pass, fail or not-run for one reference "<file>[#<describe> > ... > <name>]".
 * A name path selects the cases it equals or is a prefix of.
 * @param {string} rest @param {JUnitCase[]} cases @param {RealisationRoot} root @param {string[]} problems
 * @returns {{outcome: 'pass'|'fail'|'not-run', detail?: string}}
 */
export function decide(rest, cases, root, problems = []) {
  const hashAt = rest.indexOf('#');
  const file = relPath(hashAt < 0 ? rest : rest.slice(0, hashAt));
  const want = hashAt < 0 ? [] : rest.slice(hashAt + 1).split('>').map((s) => s.trim()).filter(Boolean);
  const matched = cases.filter((c) => {
    if (c.file !== file) return false;
    const full = [...c.suites, c.name].map((s) => s.trim());
    return want.length <= full.length && want.every((s, i) => s === full[i]);
  });
  if (!matched.length) {
    const why = problems.length ? problems.join('; ') : 'the test is not in the JUnit report';
    return { outcome: 'not-run', detail: why };
  }
  const label = (/** @type {JUnitCase} */ c) => [...c.suites, c.name].join(' > ');
  const env = (/** @type {JUnitCase} */ c) => root.notRunWhen.some((re) => re.test(c.message));
  const failed = matched.filter((c) => c.status === 'fail' && !env(c));
  if (failed.length) {
    const text = failed.map((c) => `${label(c)}: ${c.message}`).join('\n').split(/\r?\n/);
    return { outcome: 'fail', detail: text.slice(-DETAIL_TAIL_LINES).join('\n') };
  }
  const blocked = matched.filter((c) => c.status === 'error' || (c.status === 'fail' && env(c)));
  if (blocked.length) {
    const first = blocked[0].message.split(/\r?\n/)[0] ?? '';
    return { outcome: 'not-run', detail: `${blocked.length} test(s) did not run to a verdict (environment): ${label(blocked[0])}: ${first}` };
  }
  if (matched.some((c) => c.status === 'pass')) return { outcome: 'pass' };
  return { outcome: 'not-run', detail: 'every matched test was skipped' };
}
