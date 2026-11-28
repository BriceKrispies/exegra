// Running the test evidence of `exegra verify` in batches (WG-5717), and deciding which recorded passes still stand.
//
// Node references run once per test file: one `node --test` process per file, given every name pattern the file's
// references use, with the modules it loads and the files it reads recorded (tools/trace-reads.js). Browser references run once: one
// Playwright process (two workers) for all files. At most two processes run at the same time, a Playwright run
// counting for both. Each reference's outcome is attributed from the runner's own per-test results by the same
// matching rule the reuse path applies to recorded outcomes (cli/outcomes.js): a reference that matches no test
// fails, a failing test fails only the references matching it, a skipped test stays skipped.
//
// Coverage is per file run: what a run executed (the modules it loaded) and read (the fs trace) is recorded once per test
// file, `coverage[<test file>]`, and every reference of that file points at it. Per-test attribution is not
// attempted: each reference of a file is taken to depend on everything the file's referenced tests touched.
//
// Reuse: a recorded pass is reused when its reference is unchanged and the content of every file its coverage names
// (and the listing of every directory it read) still hashes to the recorded `hash`. The references of one test file
// stand or fall together: if one cannot be reused the whole file runs again.

import { createHash } from 'node:crypto';
import { spawn, spawnSync } from 'node:child_process';
import fs from 'node:fs';
import { createRequire } from 'node:module';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { testRefProblem, describeTestRefProblem } from '../src/core/evidence-ref.js';
import { formalSourcesHash, isRecordFile, recordsStamp, stampedFiles } from '../tools/tree-stamp.js';
import { compilePattern, splitRef, testsVerdict } from './outcomes.js';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const TRACE_PRELOAD = pathToFileURL(path.resolve(HERE, '..', 'tools', 'trace-reads.js')).href;
const TEST_TIMEOUT_MS = 10 * 60 * 1000;
const OUTPUT_MAX_CHARS = 64 * 1024 * 1024;
const TAIL_LINES = 20;
export const BROWSER_TEST_PREFIX = 'tests/browser/';
/** Processes that run at the same time. A Playwright run (two workers) takes both slots. */
export const MAX_PROCESSES = 2;

/** @param {string} child @param {string} base */
function isInside(base, child) {
  const rel = path.relative(base, child);
  return rel !== '' && !path.isAbsolute(rel) && rel !== '..' && !rel.startsWith(`..${path.sep}`);
}

// ---------------------------------------------------------------------------
// Reading runner output
// ---------------------------------------------------------------------------

/** @param {string} t */
export const stripAnsi = (t) => String(t).replace(/\x1b\[[0-9;]*m/g, '');

/**
 * Number of tests Playwright's summary line reports as passed (0 when none ran or all skipped).
 * @param {string} output the list reporter's text
 */
export function countPassedBrowserTests(output) {
  const m = stripAnsi(output).match(/\b(\d+) passed\b/);
  return m ? Number(m[1]) : 0;
}

/**
 * Every test result in node's TAP output, at any depth, in output order: its name, nesting, outcome and whether
 * it is a suite. A result is a suite when node marks it `type: 'suite'` (a describe block) or when the result
 * printed just before it is deeper (its subtests print first). `ok … # SKIP` is skipped and `# TODO` a todo,
 * whether ok or not ok. Left out: the entry node prints for the test file itself (when a name pattern matches no
 * test, node still exits 0 and reports the file as one passing test), and the "test name does not match
 * pattern" skips older node versions print for tests a pattern did not select.
 * @param {string} output TAP text @param {string} file the test file that was run
 * @returns {{name: string, nesting: number, outcome: 'pass'|'fail'|'skipped'|'todo', suite: boolean, ms: number|null}[]}
 */
export function tapTests(output, file) {
  const norm = (/** @type {string} */ t) => t.replace(/\\+/g, '/').trim();
  const target = norm(file);
  const lines = String(output).split(/\r?\n/);
  /** @type {{name: string, nesting: number, outcome: 'pass'|'fail'|'skipped'|'todo', suite: boolean, ms: number|null}[]} */
  const out = [];
  let previousIndent = -1;
  for (let i = 0; i < lines.length; i++) {
    const m = /^(\s*)(not ok|ok) \d+ - (.*)$/.exec(lines[i]);
    if (!m) continue;
    const indent = m[1].length;
    const deeperBefore = previousIndent > indent;
    previousIndent = indent;
    // The directive follows an unescaped " # "; node escapes a "#" inside a test name as "\#".
    const d = /^(.*?)(?<!\\)\s#\s*(SKIP|TODO)\b(.*)$/i.exec(m[3]);
    const name = (d ? d[1] : m[3]).replace(/\\#/g, '#').trim();
    const directive = d ? d[2].toUpperCase() : null;
    if (directive === 'SKIP' && /does not match pattern/i.test(d?.[3] ?? '')) continue;
    if (indent === 0 && (norm(name) === target || norm(name).endsWith('/' + target) || target.endsWith('/' + norm(name)))) continue;
    let suite = deeperBefore;
    /** @type {number|null} */
    let ms = null;
    for (let j = i + 1; j < lines.length; j++) {
      const l = lines[j];
      if (/^\s*\.\.\.\s*$/.test(l) || /^(\s*)(not ok|ok) \d+ - /.test(l) || /^\s*# Subtest:/.test(l)) break;
      if (/^\s*type:\s*'suite'\s*$/.test(l)) suite = true;
      const dm = /^\s*duration_ms:\s*([\d.]+)/.exec(l);
      if (dm) ms = Number(dm[1]);
    }
    const outcome = directive === 'SKIP' ? 'skipped' : directive === 'TODO' ? 'todo' : m[2] === 'ok' ? 'pass' : 'fail';
    out.push({ name, nesting: indent, outcome, suite, ms });
  }
  return out;
}

/**
 * The tests of a node TAP run with the path of each: its name preceded by the names of the suites around it
 * (what a name pattern is also matched against). TAP prints subtests before their parent, so a test's parent is the
 * next result with a smaller indentation.
 * @param {string} output @param {string} file
 */
export function tapTestsWithPaths(output, file) {
  const tests = tapTests(output, file);
  return tests.map((t, i) => {
    const names = [t.name];
    let level = t.nesting;
    for (let j = i + 1; j < tests.length && level > 0; j++) {
      if (tests[j].nesting < level) { names.unshift(tests[j].name); level = tests[j].nesting; }
    }
    return { ...t, path: names.join(' ') };
  });
}

/**
 * The repository files a run executed, from the V8 coverage files Node wrote (NODE_V8_COVERAGE): each script under
 * the repository, outside node_modules, of which at least one range ran. Repository-relative, sorted.
 * @param {string} dir @param {string} repoRoot
 * @returns {string[]}
 */
export function coveredFiles(dir, repoRoot) {
  const out = new Set();
  let names = [];
  try { names = fs.readdirSync(dir); } catch { return []; }
  for (const name of names) {
    if (!name.endsWith('.json')) continue;
    let doc;
    try { doc = JSON.parse(fs.readFileSync(path.join(dir, name), 'utf8')); } catch { continue; }
    for (const script of Array.isArray(doc?.result) ? doc.result : []) {
      if (typeof script?.url !== 'string' || !script.url.startsWith('file:')) continue;
      let abs;
      try { abs = fileURLToPath(script.url); } catch { continue; }
      if (!isInside(repoRoot, abs) || abs.split(path.sep).includes('node_modules')) continue;
      const ran = (Array.isArray(script.functions) ? script.functions : []).some((f) => (Array.isArray(f.ranges) ? f.ranges : []).some((/** @type {any} */ r) => r.count > 0));
      if (ran) out.add(path.relative(repoRoot, abs).split(path.sep).join('/'));
    }
  }
  return [...out].sort();
}

// ---------------------------------------------------------------------------
// What a run read and executed
// ---------------------------------------------------------------------------

/**
 * @typedef {{covers: string[], lists: string[], tools: string[], hash: string, ranAt: string, ms: number}} CoverageEntry
 *   covers: repository files the run executed or read; lists: directories whose listing it read; tools: programs
 *   other than node and git it started (their inputs are not seen by the trace); hash: over all of it
 */

/**
 * The files and directories a run read, and the programs it started, from the trace files the preload wrote.
 * @param {string} dir
 * @returns {{files: string[], dirs: string[], tools: string[]}}
 */
function readTraces(dir) {
  const files = new Set(); const dirs = new Set(); const tools = new Set();
  let names = [];
  try { names = fs.readdirSync(dir); } catch { return { files: [], dirs: [], tools: [] }; }
  for (const name of names) {
    if (!/^reads-.*\.json$/.test(name)) continue;
    try {
      const doc = JSON.parse(fs.readFileSync(path.join(dir, name), 'utf8'));
      for (const f of doc.files ?? []) files.add(f);
      for (const d of doc.dirs ?? []) dirs.add(d);
      for (const t of doc.tools ?? []) tools.add(t);
    } catch { /* a trace cut short is skipped */ }
  }
  return { files: [...files], dirs: [...dirs], tools: [...tools] };
}

/**
 * Hashes what a run depended on: file contents, directory listings and, for programs the trace cannot see into,
 * the sources they work from (formal/ for Lean, the whole tree for anything else). Contents are read once.
 * @param {string} repoRoot
 */
export function createCoverHasher(repoRoot) {
  /** @type {Map<string, string>} */
  const fileHashes = new Map();
  /** @type {Map<string, string>} */
  const toolHashes = new Map();
  /** @param {string} rel */
  const fileHash = (rel) => {
    let h = fileHashes.get(rel);
    if (h === undefined) {
      try { h = createHash('sha256').update(fs.readFileSync(path.join(repoRoot, rel))).digest('hex'); } catch { h = 'absent'; }
      fileHashes.set(rel, h);
    }
    return h;
  };
  /** @param {string} rel */
  const listHash = (rel) => {
    try { return createHash('sha256').update(fs.readdirSync(path.join(repoRoot, rel)).sort().join('\0')).digest('hex'); } catch { return 'absent'; }
  };
  /** @param {string} tool */
  const toolHash = (tool) => {
    let h = toolHashes.get(tool);
    if (h === undefined) {
      try {
        // Whether the program is installed decides whether a test that needs it skips, so it is part of the hash.
        const present = spawnSync(tool, ['--version'], { cwd: repoRoot, shell: process.platform === 'win32', windowsHide: true, encoding: 'utf8', timeout: 20000 }).status === 0;
        h = `${present ? 'present' : 'absent'} ${tool === 'lake' || tool === 'lean' ? `formal ${formalSourcesHash(repoRoot)}` : `tree ${recordsStamp(repoRoot)}`}`;
      } catch { h = 'unknown'; }
      toolHashes.set(tool, h);
    }
    return h;
  };
  return {
    /** @param {{covers: string[], lists: string[], tools: string[]}} c */
    hash(c) {
      const all = createHash('sha256');
      all.update(`node ${process.version}\n`);
      for (const f of c.covers) all.update(`F ${f} ${fileHash(f)}\n`);
      for (const d of c.lists) all.update(`D ${d} ${listHash(d)}\n`);
      for (const t of c.tools) all.update(`T ${t} ${toolHash(t)}\n`);
      return all.digest('hex');
    },
  };
}

/**
 * The files a browser test depends on: the application, the engine builds, the test support files, the fixtures and
 * the specifications the pages load. Playwright runs the pages in a browser, where node's coverage does not reach, so a
 * browser reference depends on all of them, except the other spec files of the browser tests.
 * @param {string} repoRoot @param {string} specFile the reference's own spec file
 * @returns {string[]}
 */
export function browserInputs(repoRoot, specFile) {
  const roots = ['index.html', 'package.json', 'package-lock.json', 'vite.config.js', 'playwright.config.js'];
  return stampedFiles(repoRoot).filter((f) => !isRecordFile(f) && (
    roots.includes(f) || f.startsWith('src/') || f.startsWith('tools/') || f.startsWith('tests/fixtures/') || f.startsWith('specs/')
    || (f.startsWith(BROWSER_TEST_PREFIX) && (f === specFile || !f.endsWith('.spec.js')))));
}

/**
 * The coverage entry of one node test file run: the trace in `dir` (modules loaded and files read).
 * @param {string} dir @param {string} repoRoot @param {ReturnType<typeof createCoverHasher>} hasher @param {number} ms
 * @returns {CoverageEntry}
 */
function nodeCoverage(dir, repoRoot, hasher, ms) {
  const traces = readTraces(dir);
  const covers = [...new Set(traces.files)].filter((f) => !isRecordFile(f)).sort();
  const lists = traces.dirs.sort();
  const tools = traces.tools.sort();
  return { covers, lists, tools, hash: hasher.hash({ covers, lists, tools }), ranAt: new Date().toISOString(), ms };
}

// ---------------------------------------------------------------------------
// Which recorded passes still stand
// ---------------------------------------------------------------------------

/** The test file of a reference, normalised. @param {string} ref */
export const refFile = (ref) => splitRef(ref).file.replace(/\\/g, '/');

/**
 * Split evidence into what a recorded pass still answers and what must run. The references of one test file are
 * decided together (see the header): all reused, or all run.
 * @param {{id: string, ref: string}[]} evidence test evidence that nothing else answers
 * @param {{priorResults: Record<string, any>, priorCoverage: Record<string, CoverageEntry>, hasher: ReturnType<typeof createCoverHasher>}} env
 * @returns {{reused: Map<string, {outcome: 'pass'|'skipped', detail?: string, ranAt: string, coverage: string}>, run: {id: string, ref: string}[]}}
 */
export function planReuse(evidence, env) {
  /** @type {Map<string, {id: string, ref: string}[]>} */
  const byFile = new Map();
  for (const ev of evidence) {
    const file = refFile(ev.ref);
    byFile.set(file, [...(byFile.get(file) ?? []), ev]);
  }
  /** @type {Map<string, {outcome: 'pass'|'skipped', detail?: string, ranAt: string, coverage: string}>} */
  const reused = new Map();
  /** @type {{id: string, ref: string}[]} */
  const run = [];
  for (const [file, group] of byFile) {
    const entry = Object.hasOwn(env.priorCoverage, file) ? env.priorCoverage[file] : undefined;
    const stands = entry !== undefined && Array.isArray(entry.covers) && typeof entry.hash === 'string'
      && entry.hash === env.hasher.hash({ covers: entry.covers, lists: entry.lists ?? [], tools: entry.tools ?? [] })
      && group.every((ev) => {
        const kept = Object.hasOwn(env.priorResults, ev.id) ? env.priorResults[ev.id] : undefined;
        return kept && (kept.outcome === 'pass' || kept.outcome === 'not-run') && kept.ref === ev.ref && kept.coverage === file;
      });
    if (stands) {
      for (const ev of group) {
        const kept = env.priorResults[ev.id];
        reused.set(ev.id, kept.outcome === 'pass'
          ? { outcome: 'pass', ranAt: String(kept.ranAt), coverage: file }
          : { outcome: 'skipped', ranAt: String(kept.ranAt), coverage: file, ...(kept.detail !== undefined ? { detail: String(kept.detail) } : {}) });
      }
    } else {
      run.push(...group);
    }
  }
  return { reused, run };
}

// ---------------------------------------------------------------------------
// Running
// ---------------------------------------------------------------------------

/**
 * @typedef {{outcome: 'pass'|'fail'|'skipped', detail?: string, obtained: 'run'|'reused', ranAt?: string, attempted?: boolean, coverage?: string}} Attributed
 */

/**
 * Run a command, collecting its output. Never rejects: a failure to start or a timeout is in the result.
 * @param {string} command @param {string[]} args
 * @param {{cwd: string, env?: Record<string, string|undefined>}} opts
 * @returns {Promise<{status: number|null, stdout: string, stderr: string, error?: string}>}
 */
function exec(command, args, opts) {
  return new Promise((resolve) => {
    let stdout = ''; let stderr = ''; let settled = false;
    /** @type {string|undefined} */
    let error;
    /** @type {NodeJS.Timeout|undefined} */
    let timer;
    const done = (/** @type {number|null} */ status) => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      resolve({ status, stdout, stderr, ...(error ? { error } : {}) });
    };
    const child = spawn(command, args, { cwd: opts.cwd, env: opts.env, windowsHide: true, shell: false, stdio: ['ignore', 'pipe', 'pipe'] });
    timer = setTimeout(() => { error = `timed out after ${TEST_TIMEOUT_MS / 1000} s`; child.kill(); }, TEST_TIMEOUT_MS);
    child.stdout.setEncoding('utf8'); child.stderr.setEncoding('utf8');
    child.stdout.on('data', (d) => { if (stdout.length < OUTPUT_MAX_CHARS) stdout += d; });
    child.stderr.on('data', (d) => { if (stderr.length < OUTPUT_MAX_CHARS) stderr += d; });
    child.on('error', (e) => { error = e.message; done(null); });
    child.on('close', (code) => done(code));
  });
}

/** @param {string} text */
const tail = (text) => text.replace(/\s+$/, '').split(/\r?\n/).slice(-TAIL_LINES).join('\n');

/**
 * Attribute one node test file's run to its references.
 * @param {string} file @param {string[]} patterns the distinct patterns of the references ('' for a whole file)
 * @param {{status: number|null, stdout: string, stderr: string, error?: string}} run
 * @returns {Map<string, Attributed>} by pattern
 */
export function attributeNodeRun(file, patterns, run) {
  /** @type {Map<string, Attributed>} */
  const out = new Map();
  const tests = tapTestsWithPaths(run.stdout, file);
  const crashed = run.error !== undefined || (run.status !== 0 && !tests.some((t) => t.outcome === 'fail'));
  for (const pattern of patterns) {
    const re = pattern ? compilePattern(pattern, '') : null;
    if (pattern && !re) { out.set(pattern, { outcome: 'fail', detail: 'the name pattern is not a regular expression', obtained: 'run' }); continue; }
    const matched = re ? tests.filter((t) => re.test(t.name) || re.test(t.path)) : tests;
    const verdict = testsVerdict(matched);
    if (verdict.outcome === 'none') {
      out.set(pattern, { outcome: 'fail', detail: crashed ? tail(`${run.error ?? ''}\n${run.stdout}${run.stderr}`) : 'the reference matched no test', obtained: 'run' });
    } else if (verdict.outcome === 'fail') {
      const names = matched.filter((t) => !t.suite && t.outcome === 'fail').map((t) => t.path);
      out.set(pattern, { outcome: 'fail', detail: `a matching test failed: ${names.slice(0, 3).join('; ')}`, obtained: 'run' });
    } else if (crashed) {
      out.set(pattern, { outcome: 'fail', detail: `the test file did not finish cleanly (${run.error ?? `exit status ${run.status}`})\n${tail(`${run.stdout}${run.stderr}`)}`, obtained: 'run' });
    } else if (verdict.outcome === 'skipped') {
      out.set(pattern, { outcome: 'skipped', detail: verdict.detail, obtained: 'run' });
    } else {
      out.set(pattern, { outcome: 'pass', obtained: 'run' });
    }
  }
  return out;
}

/** A spec file as the JSON report names it (relative to the test directory) as a repository path. @param {string} f */
const browserFile = (f) => { const n = f.replaceAll('\\', '/'); return n.startsWith(BROWSER_TEST_PREFIX) ? n : `${BROWSER_TEST_PREFIX}${n}`; };

/**
 * The tests of a Playwright JSON report: file, the title Playwright matches `-g` against, and the outcome.
 * @param {any} report
 * @returns {{file: string, title: string, outcome: 'pass'|'fail'|'skipped', error?: string}[]}
 */
export function playwrightTests(report) {
  /** @type {{file: string, title: string, outcome: 'pass'|'fail'|'skipped', error?: string}[]} */
  const out = [];
  /** @param {any} suite @param {string[]} titles */
  const visit = (suite, titles) => {
    const here = suite.title ? [...titles, suite.title] : titles;
    for (const spec of suite.specs ?? []) {
      const tags = Array.isArray(spec.tags) && spec.tags.length ? ` ${spec.tags.map((/** @type {string} */ t) => (t.startsWith('@') ? t : `@${t}`)).join(' ')}` : '';
      for (const t of spec.tests ?? []) {
        const status = t.status;
        const outcome = status === 'skipped' ? 'skipped' : status === 'expected' || status === 'flaky' ? 'pass' : 'fail';
        // titlePath: '' (root), the project, the file, the describe blocks, the test title.
        out.push({ file: browserFile(String(spec.file ?? '')), title: `${['', t.projectName, ...here, spec.title].join(' ')}${tags}`, outcome, ...(outcome === 'fail' ? { error: stripAnsi(String(t.results?.at(-1)?.error?.message ?? '')).split(/\r?\n/).slice(0, 4).join(' ').slice(0, 300) } : {}) });
      }
    }
    for (const s of suite.suites ?? []) visit(s, here);
  };
  for (const s of report?.suites ?? []) visit(s, []);
  return out;
}

/**
 * Attribute a Playwright run to references.
 * @param {{file: string, pattern: string}[]} refs
 * @param {{file: string, title: string, outcome: 'pass'|'fail'|'skipped', error?: string}[]|null} tests null when no report was written
 * @param {{status: number|null, stdout: string, stderr: string, error?: string}} run
 * @returns {Map<string, Attributed>} by `file#pattern`
 */
export function attributeBrowserRun(refs, tests, run) {
  /** @type {Map<string, Attributed>} */
  const out = new Map();
  for (const r of refs) {
    const key = `${r.file}#${r.pattern}`;
    if (!tests) { out.set(key, { outcome: 'fail', detail: tail(`${run.error ?? ''}\n${run.stdout}${run.stderr}`), obtained: 'run' }); continue; }
    const re = r.pattern ? compilePattern(r.pattern, 'i') : null;
    if (r.pattern && !re) { out.set(key, { outcome: 'fail', detail: 'the name pattern is not a regular expression', obtained: 'run' }); continue; }
    const matched = tests.filter((t) => t.file === r.file && (!re || re.test(t.title)));
    const verdict = testsVerdict(matched);
    if (verdict.outcome === 'none') out.set(key, { outcome: 'fail', detail: 'the reference matched no test', obtained: 'run' });
    else if (verdict.outcome === 'fail') out.set(key, { outcome: 'fail', detail: `a matching test failed: ${matched.filter((t) => t.outcome === 'fail').slice(0, 3).map((t) => `${t.title.trim()}${t.error ? ` (${t.error})` : ''}`).join('; ')}`, obtained: 'run' });
    else if (verdict.outcome === 'skipped') out.set(key, { outcome: 'skipped', detail: `${verdict.skipped} matching test(s) skipped, so the reference was not executed in full`, obtained: 'run' });
    else out.set(key, { outcome: 'pass', obtained: 'run' });
  }
  return out;
}

/**
 * Run jobs with at most `capacity` units of weight at a time, starting them in the order given.
 * @param {{weight: number, run: () => Promise<void>}[]} jobs @param {number} capacity
 */
async function runPool(jobs, capacity) {
  const queue = [...jobs];
  let used = 0;
  /** @type {Set<Promise<void>>} */
  const active = new Set();
  while (queue.length || active.size) {
    while (queue.length && (used === 0 || used + queue[0].weight <= capacity)) {
      const job = /** @type {{weight: number, run: () => Promise<void>}} */ (queue.shift());
      used += job.weight;
      const p = job.run().finally(() => { used -= job.weight; active.delete(p); });
      active.add(p);
    }
    if (active.size) await Promise.race(active);
  }
}

/**
 * Run test references in batches and attribute each one's outcome.
 * @param {{id: string, ref: string}[]} evidence the references to run (several evidence entities may share one)
 * @param {{repoRoot: string, skipBrowser: boolean, log: (m: string) => void, hasher: ReturnType<typeof createCoverHasher>,
 *   reuse?: {lookup: (ref: string, browser: boolean) => any}|null, expectedMs?: Record<string, number>}} env
 *   expectedMs: the duration the last run of each test file took, to start the longest files first
 * @returns {Promise<{results: Map<string, Attributed>, coverage: Record<string, CoverageEntry>}>} results by evidence id
 */
export async function runTestBatches(evidence, env) {
  /** @type {Record<string, CoverageEntry>} */
  const coverage = {};
  /** @type {Map<string, Attributed>} */
  const byRef = new Map();
  /** @type {Map<string, Set<string>>} node file -> refs */
  const nodeFiles = new Map();
  /** @type {Map<string, Set<string>>} browser file -> refs */
  const browserFiles = new Map();
  for (const ref of new Set(evidence.map((e) => e.ref))) {
    const problem = testRefProblem(ref);
    if (problem) { byRef.set(ref, { outcome: 'fail', detail: `unsafe reference: ${describeTestRefProblem(ref, problem)}`, obtained: 'run' }); continue; }
    const file = refFile(ref);
    const abs = path.resolve(env.repoRoot, file);
    if (!isInside(env.repoRoot, abs)) { byRef.set(ref, { outcome: 'fail', detail: 'unsafe reference', obtained: 'run' }); continue; }
    if (!fs.existsSync(abs) || !fs.statSync(abs).isFile()) { byRef.set(ref, { outcome: 'fail', detail: 'test file not found', obtained: 'run' }); continue; }
    const browser = file.startsWith(BROWSER_TEST_PREFIX);
    const hit = env.reuse?.lookup(ref, browser);
    if (hit) { env.log(`verify: reusing the recorded outcome of ${ref}`); byRef.set(ref, { ...hit, obtained: 'reused' }); continue; }
    if (browser && env.skipBrowser) { byRef.set(ref, { outcome: 'skipped', detail: 'not started (--skip-browser)', obtained: 'run', attempted: false }); continue; }
    const group = browser ? browserFiles : nodeFiles;
    group.set(file, new Set([...(group.get(file) ?? []), ref]));
  }

  /** @type {{weight: number, ms: number, run: () => Promise<void>}[]} */
  const jobs = [];
  for (const [file, refs] of nodeFiles) {
    jobs.push({
      weight: 1, ms: env.expectedMs?.[file] ?? 0,
      run: async () => {
        const patterns = [...new Set([...refs].map((r) => splitRef(r).pattern))];
        const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-coverage-'));
        const t0 = Date.now();
        try {
          env.log(`verify: running ${file} (${refs.size} reference${refs.size === 1 ? '' : 's'})`);
          const args = ['--test', '--test-reporter=tap'];
          if (!patterns.includes('')) for (const p of patterns) args.push(`--test-name-pattern=${p}`);
          args.push(file);
          // Not as a child of a test run we may be inside (its context makes node:test print for a parent runner).
          const base = { ...process.env };
          delete base.NODE_TEST_CONTEXT;
          const run = await exec(process.execPath, args, {
            cwd: env.repoRoot,
            env: {
              ...base, EXEGRA_TRACE_DIR: dir, EXEGRA_TRACE_ROOT: env.repoRoot,
              NODE_OPTIONS: `${base.NODE_OPTIONS ?? ''} --import=${TRACE_PRELOAD}`.trim(),
            },
          });
          const attributed = attributeNodeRun(file, patterns, run);
          const ran = Date.now() - t0;
          coverage[file] = nodeCoverage(dir, env.repoRoot, env.hasher, ran);
          env.log(`verify: ran ${file} in ${(ran / 1000).toFixed(1)} s (${(Date.now() - t0 - ran) / 1000} s to record coverage)`);
          for (const r of refs) byRef.set(r, { ...(/** @type {Attributed} */ (attributed.get(splitRef(r).pattern))), coverage: file });
        } finally {
          fs.rmSync(dir, { recursive: true, force: true });
        }
      },
    });
  }
  if (browserFiles.size) {
    const files = [...browserFiles.keys()];
    jobs.push({
      weight: MAX_PROCESSES, ms: files.reduce((n, f) => n + (env.expectedMs?.[f] ?? 0), 0),
      run: async () => {
        const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-playwright-'));
        const reportFile = path.join(dir, 'report.json');
        const t0 = Date.now();
        try {
          const refs = [...browserFiles.values()].flatMap((s) => [...s]);
          env.log(`verify: running ${refs.length} browser reference(s) in ${files.length} file(s), ${MAX_PROCESSES} workers`);
          const patterns = [...new Set(refs.map((r) => splitRef(r).pattern))];
          // Playwright reads -g as a case-insensitive expression over the full title; a file with no pattern runs whole.
          const args = [createRequire(import.meta.url).resolve('@playwright/test/cli'), 'test', `--workers=${MAX_PROCESSES}`, '--reporter=dot,json', ...files];
          if (!patterns.includes('')) args.push('-g', patterns.map((p) => `(?:${p})`).join('|'));
          const run = await exec(process.execPath, args, { cwd: env.repoRoot, env: { ...process.env, PLAYWRIGHT_JSON_OUTPUT_NAME: reportFile } });
          /** @type {ReturnType<typeof playwrightTests>|null} */
          let tests = null;
          try { tests = playwrightTests(JSON.parse(fs.readFileSync(reportFile, 'utf8'))); } catch { /* no report: the run failed as a whole */ }
          const attributed = attributeBrowserRun(refs.map((r) => splitRef(r)), tests, run);
          const ms = Math.round((Date.now() - t0) / files.length);
          for (const [file, set] of browserFiles) {
            const covers = browserInputs(env.repoRoot, file);
            coverage[file] = { covers, lists: [], tools: [], hash: env.hasher.hash({ covers, lists: [], tools: [] }), ranAt: new Date().toISOString(), ms };
            for (const r of set) { const s = splitRef(r); byRef.set(r, { ...(/** @type {Attributed} */ (attributed.get(`${s.file}#${s.pattern}`))), coverage: file }); }
          }
        } finally {
          fs.rmSync(dir, { recursive: true, force: true });
        }
      },
    });
  }
  jobs.sort((a, b) => b.ms - a.ms);
  await runPool(jobs, MAX_PROCESSES);
  /** @type {Map<string, Attributed>} */
  const results = new Map();
  for (const ev of evidence) {
    const r = byRef.get(ev.ref);
    if (r) results.set(ev.id, r);
  }
  return { results, coverage };
}

/**
 * The recorded results with each result's `covers` filled in from the coverage of the test file it points at, which
 * is what the dependency graph (src/core/impact.js) reads. Results recorded before coverage was kept per file
 * already carry `covers`.
 * @param {any} recorded the recorded results file, or null
 * @returns {any}
 */
export function expandCoverage(recorded) {
  if (!recorded || typeof recorded !== 'object' || !recorded.coverage || !recorded.results) return recorded;
  /** @type {Record<string, any>} */
  const results = {};
  for (const [id, r] of Object.entries(recorded.results)) {
    const run = typeof r?.coverage === 'string' && Object.hasOwn(recorded.coverage, r.coverage) ? recorded.coverage[r.coverage] : null;
    results[id] = run && Array.isArray(run.covers) ? { ...r, covers: [...new Set([...(Array.isArray(r.covers) ? r.covers : []), ...run.covers])] } : r;
  }
  return { ...recorded, results };
}
