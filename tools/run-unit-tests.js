// `npm test`: node --test over tests/core, two files at a time, with the spec reporter on the terminal and
// the outcomes reporter writing .outcomes/node.json (tools/outcomes-node-reporter.js) for `exegra verify`.
// Extra arguments (a file, a name pattern) are passed on; such a run is recorded as partial.
//
// The files run in ten batches, two at a time, each batch in one node process (--test-isolation=none; EXEGRA_UNIT_ISOLATION=process runs a process per
// file instead).
// The suite has a wall-clock budget of BUDGET_SECONDS on a warm derivation cache (the cache is keyed by src/core and the
// Lean build, so the first run after a change to either derives every specification again and has COLD_BUDGET_SECONDS).
// The routine suite has a wall-clock budget of BUDGET_SECONDS. Past it the whole test process tree is killed,
// the slowest tests seen so far (read from the spec reporter's output) are listed, and the exit status is 1.
// The budget is a ceiling, never a setting to raise: EXEGRA_UNIT_BUDGET_SECONDS can only lower it. A test that
// needs more than a few seconds belongs in tests/proofs (npm run test:proofs, run by `npm run verify` and the
// Check workflow), or shrinks.

import { spawn, spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

export const BUDGET_SECONDS = 35;
/** The budget of the first run after a source change, when every specification is derived again. */
export const COLD_BUDGET_SECONDS = 150;
const SLOWEST_SHOWN = 15;
/** How many batches the files are dealt into, two running at a time. */
const BATCHES = 10;

/**
 * The tests a spec-reporter text shows as finished, slowest first.
 * @param {string} output
 * @returns {{name: string, ms: number}[]}
 */
export function slowestTests(output, limit = SLOWEST_SHOWN) {
  /** @type {{name: string, ms: number}[]} */
  const tests = [];
  for (const line of String(output).split(/\r?\n/)) {
    const m = /^\s*[✔✖] (.*) \(([\d.]+)ms\)\s*$/.exec(line);
    if (m) tests.push({ name: m[1], ms: Number(m[2]) });
  }
  return tests.sort((a, b) => b.ms - a.ms).slice(0, limit);
}

/** Kill a process and everything it started. @param {number} pid */
function killTree(pid) {
  if (process.platform === 'win32') spawnSync('taskkill', ['/PID', String(pid), '/T', '/F'], { windowsHide: true, stdio: 'ignore' });
  else { try { process.kill(-pid, 'SIGKILL'); } catch { try { process.kill(pid, 'SIGKILL'); } catch { /* gone */ } } }
}

/** The newest modification time under a directory, 0 when it is absent. @param {string} dir @returns {number} */
function newestMtime(dir) {
  let newest = 0;
  let entries;
  try { entries = fs.readdirSync(dir, { withFileTypes: true }); } catch { return 0; }
  for (const e of entries) {
    const p = path.join(dir, e.name);
    newest = Math.max(newest, e.isDirectory() ? newestMtime(p) : fs.statSync(p).mtimeMs);
  }
  return newest;
}

/** Deal files into batches, largest first, round robin: each batch holds a share of the big files. @param {string} root @param {string[]} files @param {number} count */
function batches(root, files, count) {
  const sized = files.map((f) => ({ f, n: fs.statSync(path.join(root, f)).size })).sort((x, y) => y.n - x.n);
  /** @type {string[][]} */
  const out = Array.from({ length: Math.min(count, sized.length) }, () => []);
  sized.forEach(({ f }, i) => out[i % out.length].push(f));
  return out;
}

/** Merge the outcome records of the batches into node.json and remove them. @param {string} dir @param {string[]} names */
function mergeOutcomes(dir, names) {
  const docs = names.map((n) => JSON.parse(fs.readFileSync(path.join(dir, n), 'utf8')));
  const merged = {
    ...docs[0],
    treeAfter: docs[docs.length - 1].treeAfter,
    finishedAt: docs[docs.length - 1].finishedAt,
    complete: docs.every((d) => d.complete),
    files: Object.assign({}, ...docs.map((d) => d.files)),
  };
  const fd = fs.openSync(path.join(dir, 'node.json'), 'w');
  fs.writeSync(fd, JSON.stringify(merged, null, 1) + '\n');
  fs.closeSync(fd);
  for (const n of names) fs.rmSync(path.join(dir, n), { force: true });
}

function main() {
  const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
  const extra = process.argv.slice(2);
  const outDir = path.join(repoRoot, '.outcomes');
  fs.mkdirSync(outDir, { recursive: true });
  // The derivation cache is keyed by Exegra's own sources, so the first run after a source change derives every
  // specification again. That run has COLD_BUDGET_SECONDS; the budget of a run on a warm cache is BUDGET_SECONDS.
  const marker = path.join(outDir, 'model-cache-warm');
  const sourcesAt = Math.max(newestMtime(path.join(repoRoot, 'src', 'core')), newestMtime(path.join(repoRoot, 'src', 'engine', 'lean')));
  const warm = fs.existsSync(marker) && fs.statSync(marker).mtimeMs >= sourcesAt;
  const ceiling = warm ? BUDGET_SECONDS : COLD_BUDGET_SECONDS;
  const requested = Number(process.env.EXEGRA_UNIT_BUDGET_SECONDS);
  const budget = Number.isFinite(requested) && requested > 0 ? Math.min(ceiling, requested) : ceiling;
  // A run that is killed records nothing; an older record must not stand in for it.
  for (const f of fs.readdirSync(outDir)) if (/^node(-\d+)?\.json$/.test(f)) fs.rmSync(path.join(outDir, f), { force: true });
  const narrowed = extra.some((a) => !a.startsWith('-'));
  const reporters = (/** @type {string} */ dest) => [
    '--test-reporter=spec', '--test-reporter-destination=stdout',
    '--test-reporter=./tools/outcomes-node-reporter.js', '--test-reporter-destination=' + path.join(outDir, dest),
  ];
  /** @type {{args: string[], record: string}[]} */
  let runs;
  if (narrowed || process.env.EXEGRA_UNIT_ISOLATION === 'process') {
    // A named file or pattern, or a process per file: one run, two files at a time.
    runs = [{ record: 'node.json', args: ['--test', '--test-concurrency=2', ...reporters('node.json'), ...extra, ...(narrowed ? [] : ['tests/core/*.test.js'])] }];
  } else {
    // Batches of files, each loaded into one process: the sources and the Lean core load once per batch, not once per
    // file (about 0.35 s each). Two batches run at a time (the cap for test jobs) and a finished one makes room for the
    // next, so the two lanes end together whatever the files weigh. A larger young generation keeps the garbage of the
    // many derived models from slowing a long-lived process.
    const files = fs.readdirSync(path.join(repoRoot, 'tests', 'core')).filter((f) => f.endsWith('.test.js')).map((f) => 'tests/core/' + f);
    runs = batches(repoRoot, files, BATCHES).map((group, i) => ({
      record: 'node-' + (i + 1) + '.json',
      args: ['--max-semi-space-size=64', '--test', '--test-isolation=none', ...reporters('node-' + (i + 1) + '.json'), ...extra, ...group],
    }));
  }
  // The derivation cache is shared by every checkout; its default size (512 MiB) is less than one run of
  // the suite writes, so the run would evict its own entries. Larger only for this process tree.
  const env = { ...process.env, EXEGRA_MODEL_CACHE_MAX_BYTES: process.env.EXEGRA_MODEL_CACHE_MAX_BYTES ?? String(4 * 1024 ** 3) };
  const started = Date.now();
  /** @type {import('node:child_process').ChildProcess[]} */
  const live = [];
  let seen = '';
  let overBudget = false;
  let failed = false;
  let next = 0;
  let open = 0;
  const timer = setTimeout(() => {
    overBudget = true;
    for (const c of live) if (c.pid !== undefined && c.exitCode === null) killTree(c.pid);
  }, budget * 1000);

  const finish = () => {
    clearTimeout(timer);
    if (overBudget) {
      console.error(`\nunit tests: killed after ${budget} s, the budget of the routine suite (${warm ? 'warm' : 'cold'} model cache). The slowest tests that had finished:`);
      for (const t of slowestTests(seen)) console.error(`  ${(t.ms / 1000).toFixed(1).padStart(6)} s  ${t.name}`);
      console.error('Shrink or move the slow ones (tests/proofs holds what re-checks proofs); the budget is not raised.');
      process.exit(1);
    }
    if (runs.length > 1) {
      try { mergeOutcomes(outDir, runs.map((r) => r.record)); } catch (e) { console.error('unit tests: could not merge the outcome records: ' + /** @type {Error} */ (e).message); failed = true; }
    }
    if (!failed && !narrowed) fs.closeSync(fs.openSync(marker, 'w'));
    console.error(`unit tests: ${((Date.now() - started) / 1000).toFixed(1)} s of the ${budget} s budget (${warm ? 'warm' : 'cold'} model cache)`);
    process.exit(failed ? 1 : 0);
  };

  const launch = () => {
    while (open < 2 && next < runs.length && !overBudget) {
      const run = runs[next++];
      const child = spawn(process.execPath, run.args, { cwd: repoRoot, env, stdio: ['ignore', 'pipe', 'inherit'], windowsHide: true, detached: process.platform !== 'win32' });
      live.push(child);
      open++;
      child.stdout.on('data', (chunk) => { process.stdout.write(chunk); seen += chunk.toString('utf8'); });
      child.on('error', (e) => { console.error(`unit tests: could not start node: ${e.message}`); process.exit(1); });
      child.on('close', (code) => {
        if (code !== 0) failed = true;
        open--;
        if (next < runs.length && !overBudget) launch();
        else if (open === 0) finish();
      });
    }
  };
  launch();
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) main();
