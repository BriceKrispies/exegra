// A node:test reporter that writes the outcome of every test, per test file, with the stamp of the tree
// it ran on (tools/tree-stamp.js). `npm test` loads it next to the spec reporter. `exegra verify` reads the
// file back (cli/outcomes.js) instead of running the same tests again when the stamp is still current.
// The stamp is taken when the run starts and again when it ends; a run during which the tree changed is
// recorded as not clean, and verify never uses it.

import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { treeStamp } from './tree-stamp.js';

const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');

/** @param {string} p */
const slash = (p) => p.replace(/\\/g, '/');

/**
 * Whether the run was narrowed by an option; such a run's outcomes are never reused.
 * @returns {boolean}
 */
function runIsPartial() {
  const argv = [...process.execArgv, ...process.argv];
  return argv.some((a) => /^--test-(name-pattern|skip-pattern|only|shard)\b/.test(a));
}

/**
 * @param {AsyncIterable<{type: string, data: any}>} source
 */
export default async function* outcomesReporter(source) {
  const treeBefore = treeStamp(repoRoot);
  /** @type {Record<string, {fileOutcome: 'pass'|'fail', tests: {name: string, path: string, nesting: number, outcome: 'pass'|'fail'|'skipped'|'todo', suite?: boolean}[]}>} */
  const files = {};
  /** @type {Map<string, string[]>} */
  const stacks = new Map();
  for await (const event of source) {
    const data = event.data;
    if (!data || typeof data.file !== 'string') continue;
    const file = slash(path.relative(repoRoot, data.file));
    if (event.type === 'test:start') {
      const stack = stacks.get(file) ?? [];
      stack.length = data.nesting;
      stack[data.nesting] = data.name;
      stacks.set(file, stack);
    } else if (event.type === 'test:pass' || event.type === 'test:fail') {
      const entry = files[file] ?? (files[file] = { fileOutcome: 'pass', tests: [] });
      const failed = event.type === 'test:fail';
      if (data.nesting === 0 && slash(String(data.name)).endsWith(file)) {
        // The entry node prints for the test file itself.
        if (failed) entry.fileOutcome = 'fail';
        continue;
      }
      const stack = (stacks.get(file) ?? []).slice(0, data.nesting);
      // A todo test reports test:pass with `todo` set; it proves nothing, like a skipped test. A describe
      // block is a suite (details.type), not a test of its own: cli/outcomes.js leaves it out of verdicts.
      const flagged = (/** @type {any} */ v) => v !== undefined && v !== false;
      entry.tests.push({
        name: String(data.name),
        path: [...stack, String(data.name)].join(' '),
        nesting: data.nesting,
        outcome: failed ? 'fail' : flagged(data.skip) ? 'skipped' : flagged(data.todo) ? 'todo' : 'pass',
        ...(data.details?.type === 'suite' ? { suite: true } : {}),
      });
    }
  }
  const treeAfter = treeStamp(repoRoot);
  yield `${JSON.stringify({
    kind: 'node', finishedAt: new Date().toISOString(), treeBefore, treeAfter,
    complete: !runIsPartial(), files,
  }, null, 1)}\n`;
}
