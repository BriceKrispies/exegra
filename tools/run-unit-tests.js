// `npm test`: node --test over tests/core, two files at a time, with the spec reporter on the terminal and
// the outcomes reporter writing .outcomes/node.json (tools/outcomes-node-reporter.js) for `exegra verify`.
// Extra arguments (a file, a name pattern) are passed on; such a run is recorded as partial.
//
// The routine suite has a wall-clock budget of BUDGET_SECONDS. Past it the whole test process tree is killed,
// the slowest tests seen so far (read from the spec reporter's output) are listed, and the exit status is 1.
// The budget is a ceiling, never a setting to raise: EXEGRA_UNIT_BUDGET_SECONDS can only lower it. A test that
// needs more than a few seconds belongs in tests/proofs (npm run test:proofs, run by `npm run verify` and the
// Check workflow), or shrinks.

import { spawn, spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

export const BUDGET_SECONDS = 120;
const SLOWEST_SHOWN = 15;

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

function main() {
  const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
  const extra = process.argv.slice(2);
  const requested = Number(process.env.EXEGRA_UNIT_BUDGET_SECONDS);
  const budget = Number.isFinite(requested) && requested > 0 ? Math.min(BUDGET_SECONDS, requested) : BUDGET_SECONDS;
  fs.mkdirSync(path.join(repoRoot, '.outcomes'), { recursive: true });
  // A run that is killed records nothing; an older record must not stand in for it.
  fs.rmSync(path.join(repoRoot, '.outcomes', 'node.json'), { force: true });
  const args = [
    '--test', '--test-concurrency=2',
    '--test-reporter=spec', '--test-reporter-destination=stdout',
    '--test-reporter=./tools/outcomes-node-reporter.js', '--test-reporter-destination=.outcomes/node.json',
    ...extra,
    ...(extra.some((a) => !a.startsWith('-')) ? [] : ['tests/core/*.test.js']),
  ];
  // The derivation cache is shared by every checkout; its default size (512 MiB) is less than one run of
  // the suite writes, so the run would evict its own entries. Larger only for this process tree.
  const env = { ...process.env, EXEGRA_MODEL_CACHE_MAX_BYTES: process.env.EXEGRA_MODEL_CACHE_MAX_BYTES ?? String(4 * 1024 ** 3) };
  const started = Date.now();
  const child = spawn(process.execPath, args, { cwd: repoRoot, env, stdio: ['ignore', 'pipe', 'inherit'], windowsHide: true, detached: process.platform !== 'win32' });
  let seen = '';
  child.stdout.on('data', (chunk) => { process.stdout.write(chunk); seen += chunk.toString('utf8'); });
  let overBudget = false;
  const timer = setTimeout(() => {
    overBudget = true;
    if (child.pid !== undefined) killTree(child.pid);
  }, budget * 1000);
  child.on('close', (code) => {
    clearTimeout(timer);
    if (overBudget) {
      console.error(`\nunit tests: killed after ${budget} s, the budget of the routine suite. The slowest tests that had finished:`);
      for (const t of slowestTests(seen)) console.error(`  ${(t.ms / 1000).toFixed(1).padStart(6)} s  ${t.name}`);
      console.error('Shrink or move the slow ones (tests/proofs holds what re-checks proofs); the budget is not raised.');
      process.exit(1);
    }
    console.error(`unit tests: ${((Date.now() - started) / 1000).toFixed(1)} s of the ${budget} s budget`);
    process.exit(code ?? 1);
  });
  child.on('error', (e) => { console.error(`unit tests: could not start node: ${e.message}`); process.exit(1); });
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) main();
