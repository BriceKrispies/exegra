// The stamp of the working tree: one hash that changes when any file a test could depend on changes.
// Node-only. It covers every tracked file and every untracked file that git does not ignore (by content,
// so an edit that restores a file restores the stamp), the generated build outputs that tests load but git
// ignores (src/engine/lean/ and src/engine/pkg/), and the Node version. The test reporters write it beside
// each run's outcomes and `exegra verify` compares it with the current one to decide whether the outcomes of
// a run still describe the tree it is about to record. The records stamp (the same stamp without the files
// Exegra writes from its results) and the hash of formal/ are recorded with every evidence result and Lean
// theorem check, and compared at read time, so a result recorded for another tree is read as stale.

import { createHash } from 'node:crypto';
import { stampsOf } from '../src/core/facts.js';
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';

/** Ignored directories whose files the tests load (repo-relative, forward slashes). */
export const STAMPED_GENERATED_DIRS = ['src/engine/lean', 'src/engine/pkg'];

/** @param {string} p */
const slash = (p) => p.replace(/\\/g, '/');

/**
 * Every file under a directory, repo-relative with forward slashes.
 * @param {string} repoRoot @param {string} dir
 * @returns {string[]}
 */
function walk(repoRoot, dir) {
  /** @type {string[]} */
  const out = [];
  /** @param {string} abs */
  const visit = (abs) => {
    let entries;
    try {
      entries = fs.readdirSync(abs, { withFileTypes: true });
    } catch {
      return;
    }
    for (const entry of entries) {
      const child = path.join(abs, entry.name);
      if (entry.isDirectory()) visit(child);
      else if (entry.isFile()) out.push(slash(path.relative(repoRoot, child)));
    }
  };
  visit(path.join(repoRoot, dir));
  return out;
}

/**
 * The files the stamp covers, sorted.
 * @param {string} repoRoot
 * @returns {string[]}
 */
export function stampedFiles(repoRoot) {
  const listed = execFileSync('git', ['ls-files', '-z', '--cached', '--others', '--exclude-standard'], {
    cwd: repoRoot, encoding: 'utf8', maxBuffer: 64 * 1024 * 1024, windowsHide: true,
  });
  const files = new Set(listed.split('\0').filter(Boolean).map(slash));
  for (const dir of STAMPED_GENERATED_DIRS) for (const f of walk(repoRoot, dir)) files.add(f);
  return [...files].sort();
}

/**
 * The stamp of the tree at `repoRoot`: a sha256 over the sorted (path, content hash) pairs. A tracked file
 * deleted in the working tree is left out, as an absent file is.
 * @param {string} repoRoot
 * @param {{exclude?: (rel: string) => boolean, replace?: Record<string, string|Buffer>}} [opts] exclude: files left out of the
 *   stamp; replace: contents that stand in for files of the tree (repo-relative paths), the stamp a tree with
 *   those edits would have, computed without writing them
 * @returns {string}
 */
export function treeStamp(repoRoot, opts = {}) {
  const all = createHash('sha256');
  all.update(`node ${process.version}\n`);
  for (const rel of stampedFiles(repoRoot)) {
    if (opts.exclude?.(rel)) continue;
    let content;
    if (opts.replace && Object.hasOwn(opts.replace, rel)) content = opts.replace[rel];
    else {
      try {
        content = fs.readFileSync(path.join(repoRoot, rel));
      } catch {
        continue;
      }
    }
    all.update(`${rel}\0${createHash('sha256').update(content).digest('hex')}\n`);
  }
  return all.digest('hex');
}

/**
 * Whether a file is one Exegra writes from its own results: a project's recorded results
 * (specs/<project>/evidence/results.json) or its generated artifacts (specs/<project>/generated/). Writing them
 * must not make the results they hold stale, so the records stamp leaves them out.
 * @param {string} rel repo-relative, forward slashes
 */
export function isRecordFile(rel) {
  return /^specs\/[^/]+\/evidence\/results\.json$/.test(rel) || /^specs\/[^/]+\/generated\//.test(rel);
}

/**
 * The stamp recorded with each evidence result and Lean theorem check (exegra verify), and compared with the
 * current one when claims are evaluated from them: the tree stamp without the record files (isRecordFile).
 * @param {string} repoRoot @param {Record<string, string|Buffer>} [replace] contents standing in for files (treeStamp)
 */
export function recordsStamp(repoRoot, replace) {
  return treeStamp(repoRoot, { exclude: isRecordFile, ...(replace ? { replace } : {}) });
}

/**
 * A hash over the Lean sources of formal/ that a theorem check depends on: every stamped file under formal/
 * (the .lean files, the lakefile, lean-toolchain and lake-manifest.json; the ignored build directories
 * formal/.lake and formal/generated are not stamped), by path and content.
 * @param {string} repoRoot
 */
export function formalSourcesHash(repoRoot) {
  const all = createHash('sha256');
  for (const rel of stampedFiles(repoRoot)) {
    if (!rel.startsWith('formal/')) continue;
    let content;
    try {
      content = fs.readFileSync(path.join(repoRoot, rel));
    } catch {
      continue;
    }
    all.update(`${rel}\0${createHash('sha256').update(content).digest('hex')}\n`);
  }
  return all.digest('hex');
}

/**
 * The current stamps a read of recorded results compares with: {tree: recordsStamp, formal: formalSourcesHash}.
 * Each is null when it cannot be computed (no git checkout at repoRoot); a null stamp makes every recorded
 * result's freshness unverifiable rather than trusted.
 * @param {string} repoRoot
 * @returns {{tree: string|null, formal: string|null}}
 */
export function currentStamps(repoRoot) {
  try {
    return { tree: recordsStamp(repoRoot), formal: formalSourcesHash(repoRoot) };
  } catch {
    return { tree: null, formal: null };
  }
}

/**
 * The `stamps` of a fact (Exegra.Verdict.Stamps) recorded with `recorded`, against the current stamps of the tree:
 * `which` selects the tree's records stamp (evidence results, external outcomes, import scans) or the hash of
 * formal/ (Lean theorem checks).
 * @param {string|null|undefined} recorded @param {{tree: string|null, formal: string|null}} current
 * @param {'tree'|'formal'} [which]
 */
export function factStamps(recorded, current, which = 'tree') {
  return stampsOf(recorded, current[which]);
}
