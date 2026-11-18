// Reuse of test outcomes that `npm test` and `npm run test:browser` already recorded
// (tools/outcomes-node-reporter.js, tools/outcomes-playwright-reporter.js, both writing to .outcomes/).
// `exegra verify` asks this module for the outcome of an evidence reference before it runs the test again.
//
// Freshness rule: an outcome file is used only when it is a complete run, the tree did not change while it
// ran (treeBefore equals treeAfter), and that stamp equals the stamp of the tree verify runs on. A reference
// that no recorded test matches, a failure, or a matched set that proves nothing (everything skipped, for a
// browser test) is never reused: verify runs it. Pure apart from reading the outcome files.

import fs from 'node:fs';
import path from 'node:path';

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
 * The outcome of a node:test reference from a recorded run, or null when the run cannot answer it.
 * Matched tests are those whose name, or whose name with its ancestors, the pattern matches (all tests of the
 * file for a reference without a pattern). Any failure, a failed file, or no match: null (run it). All
 * matched tests skipped: `skipped`.
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
  if (matched.length === 0 || matched.some((t) => t.outcome === 'fail')) return null;
  const ranAt = String(doc.finishedAt);
  if (matched.every((t) => t.outcome === 'skipped')) return { outcome: 'skipped', detail: 'the matching test skipped itself', ranAt };
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
  if (matched.length === 0 || matched.some((t) => t.outcome === 'fail')) return null;
  if (!matched.some((t) => t.outcome === 'pass')) return null;
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
