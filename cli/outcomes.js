// Reuse of test outcomes that `npm test` and `npm run test:browser` already recorded
// (tools/outcomes-node-reporter.js, tools/outcomes-playwright-reporter.js, both writing to .outcomes/).
// `exegra verify` asks this module for the outcome of an evidence reference before it runs the test again.
//
// Freshness rule: an outcome file is used only when it is a complete run, the tree did not change while it
// ran (treeBefore equals treeAfter), and that stamp equals the stamp of the tree verify runs on. A reference
// that no recorded test matches, a failure, or a matched set that proves nothing (everything skipped, for a
// browser test) is never reused: verify runs it. Pure apart from reading the outcome files.
//
// What a set of matched tests establishes is decided by one function, testsVerdict, for the fresh path (the
// TAP output verify reads, cli/commands.js) and the reuse path (the recorded outcomes read here) alike: only
// executed leaf tests count, a suite is never a test of its own, and a match passes only when at least one
// matched leaf test executed and passed and none failed, skipped or was a todo.

import fs from 'node:fs';
import path from 'node:path';
import { testFact } from '../src/core/facts.js';
import { factStamps } from '../tools/tree-stamp.js';

export const OUTCOMES_DIR = '.outcomes';

/**
 * A name pattern as node and Playwright read it: a regular expression, written bare or as /source/flags.
 * Null when it does not compile.
 * @param {string} pattern @param {string} defaultFlags
 * @returns {RegExp|null}
 */
export function compilePattern(pattern, defaultFlags) {
  const slashed = /^\/(.*)\/([a-z]*)$/.exec(pattern);
  try {
    return slashed ? new RegExp(slashed[1], slashed[2]) : new RegExp(pattern, defaultFlags);
  } catch {
    return null;
  }
}

/**
 * Split a test reference into its file and name pattern.
 * @param {string} ref
 * @returns {{file: string, pattern: string}}
 */
export function splitRef(ref) {
  const hashAt = ref.indexOf('#');
  return { file: (hashAt < 0 ? ref : ref.slice(0, hashAt)).trim(), pattern: hashAt < 0 ? '' : ref.slice(hashAt + 1).trim() };
}

/**
 * Read one outcome file; null when absent or unreadable.
 * @param {string} repoRoot @param {'node'|'playwright'} kind
 * @returns {any}
 */
export function readOutcomeFile(repoRoot, kind) {
  try {
    return JSON.parse(fs.readFileSync(path.join(repoRoot, OUTCOMES_DIR, `${kind}.json`), 'utf8'));
  } catch {
    return null;
  }
}

/**
 * Why an outcome file may not be used for the tree with the stamp `current`, or null when it may.
 * @param {any} doc @param {string} current
 * @returns {string|null}
 */
export function staleReason(doc, current) {
  if (!doc || typeof doc !== 'object') return 'no recorded outcomes';
  if (doc.complete !== true) return 'the recorded run was partial';
  if (typeof doc.treeBefore !== 'string' || doc.treeBefore !== doc.treeAfter) return 'the tree changed while the recorded run ran';
  if (doc.treeAfter !== current) return 'the tree changed after the recorded run';
  return null;
}

/**
 * @typedef {{outcome: 'pass'|'fail'|'skipped'|'todo', suite?: boolean}} MatchedTest
 *   one matched test: `suite` marks a describe block or a test with subtests, which is not a test of its own
 */

/**
 * What a reference's matched tests establish, on the fresh and the reuse path alike. Suites are left out.
 * `pass` needs at least one executed leaf test that passed and no leaf that failed, skipped or was a todo;
 * any failure is `fail`; no leaf at all is `none` (the reference matched no test); otherwise `skipped`: a
 * reference part or all of whose matched tests did not execute established nothing, so it is not a pass.
 * @param {MatchedTest[]} tests
 * @returns {{outcome: 'pass'|'fail'|'skipped'|'none', executed: number, skipped: number, detail?: string}}
 */
export function testsVerdict(tests) {
  const leaves = tests.filter((t) => !t.suite);
  const executed = leaves.filter((t) => t.outcome === 'pass' || t.outcome === 'fail').length;
  const notRun = leaves.filter((t) => t.outcome === 'skipped' || t.outcome === 'todo').length;
  if (!leaves.length) return { outcome: 'none', executed: 0, skipped: 0 };
  if (leaves.some((t) => t.outcome === 'fail')) return { outcome: 'fail', executed, skipped: notRun };
  if (notRun === 0) return { outcome: 'pass', executed, skipped: 0 };
  const detail = notRun === leaves.length
    ? `every matching test (${notRun}) skipped itself or is a todo, so nothing was executed`
    : `${notRun} of ${leaves.length} matching tests skipped themselves or are todos, so the reference was not executed in full`;
  return { outcome: 'skipped', executed, skipped: notRun, detail };
}

/**
 * The fact a test reference's outcome makes about the part of the claim its evidence entity stands for
 * (Exegra.Verdict.Fact, kind test), as this adapter, the browser adapter and the JUnit adapter of
 * tools/realisation-roots.js record it: a pass, a failure (also a reference that matched no test), or not run
 * (skipped, a todo, or a realisation root's test that did not run). Stamped with the records stamp it was recorded
 * on against the current one.
 * @param {string} evidenceId @param {'pass'|'fail'|'skipped'|'not-run'|'none'} outcome
 * @param {string|null|undefined} recorded @param {{tree: string|null, formal: string|null}} current
 */
export function referenceFact(evidenceId, outcome, recorded, current) {
  const o = outcome === 'pass' ? 'pass' : outcome === 'skipped' || outcome === 'not-run' ? 'not-run' : 'fail';
  return testFact(evidenceId, o, factStamps(recorded, current));
}

/**
 * The recorded tests of one file that are suites: those the reporter flagged, and, for outcome files that
 * predate the flag, every test whose path is the prefix of a deeper test's path.
 * @param {any[]} tests
 * @returns {Set<any>}
 */
function suitesOf(tests) {
  const out = new Set();
  for (const t of tests) {
    if (t.suite === true) out.add(t);
    else if (tests.some((u) => u !== t && u.nesting > t.nesting && String(u.path).startsWith(`${t.path} `))) out.add(t);
  }
  return out;
}

/**
 * The outcome of a node:test reference from a recorded run, or null when the run cannot answer it.
 * Matched tests are those whose name, or whose name with its ancestors, the pattern matches (all tests of the
 * file for a reference without a pattern); suites are not tests of their own. Any failure, a failed file, or no
 * matched leaf test: null (run it). Otherwise testsVerdict decides: `pass`, or `skipped` when any matched test
 * skipped itself or is a todo.
 * @param {any} doc a node outcome file already checked fresh
 * @param {string} ref
 * @returns {{outcome: 'pass'|'skipped', detail?: string, ranAt: string}|null}
 */
export function nodeOutcome(doc, ref) {
  const { file, pattern } = splitRef(ref);
  const entry = doc?.files?.[file.replace(/\\/g, '/')];
  if (!entry || entry.fileOutcome === 'fail' || !Array.isArray(entry.tests)) return null;
  /** @type {any[]} */
  let matched = entry.tests;
  if (pattern) {
    const re = compilePattern(pattern, '');
    if (!re) return null;
    matched = entry.tests.filter((/** @type {any} */ t) => re.test(t.name) || re.test(t.path));
  }
  const suites = suitesOf(entry.tests);
  const verdict = testsVerdict(matched.map((t) => ({ outcome: t.outcome, suite: suites.has(t) })));
  if (verdict.outcome === 'none' || verdict.outcome === 'fail') return null;
  const ranAt = String(doc.finishedAt);
  if (verdict.outcome === 'skipped') return { outcome: 'skipped', detail: /** @type {string} */ (verdict.detail), ranAt };
  return { outcome: 'pass', ranAt };
}

/**
 * The outcome of a Playwright reference from a recorded run, or null when the run cannot answer it.
 * Playwright reads the file as a substring of the test path and the pattern as a case-insensitive regular
 * expression over the full title.
 * @param {any} doc a playwright outcome file already checked fresh
 * @param {string} ref
 * @returns {{outcome: 'pass', ranAt: string}|null}
 */
export function playwrightOutcome(doc, ref) {
  const { file, pattern } = splitRef(ref);
  if (!Array.isArray(doc?.tests)) return null;
  const re = pattern ? compilePattern(pattern, 'i') : null;
  if (pattern && !re) return null;
  const wanted = file.replace(/\\/g, '/');
  const matched = doc.tests.filter((/** @type {any} */ t) => String(t.file).includes(wanted) && (!re || re.test(t.title)));
  // Only a full pass is reused; a failure, no match, or any skipped match is run again.
  if (testsVerdict(matched.map((t) => ({ outcome: t.outcome }))).outcome !== 'pass') return null;
  return { outcome: 'pass', ranAt: String(doc.finishedAt) };
}

/**
 * Looks up recorded outcomes for evidence references. `lookup` returns null for anything it cannot answer.
 * @param {string} repoRoot @param {string} currentStamp
 * @returns {{lookup: (ref: string, browser: boolean) => {outcome: 'pass'|'skipped', detail?: string, ranAt: string}|null, notes: Record<string, string>}}
 */
export function createOutcomeReuse(repoRoot, currentStamp) {
  /** @type {Record<string, string>} */
  const notes = {};
  /** @type {Record<string, any>} */
  const docs = {};
  for (const kind of /** @type {const} */ (['node', 'playwright'])) {
    const doc = readOutcomeFile(repoRoot, kind);
    const reason = staleReason(doc, currentStamp);
    if (reason) notes[kind] = reason;
    else docs[kind] = doc;
  }
  return {
    notes,
    lookup(ref, browser) {
      const doc = docs[browser ? 'playwright' : 'node'];
      if (!doc) return null;
      return browser ? playwrightOutcome(doc, ref) : nodeOutcome(doc, ref);
    },
  };
}
