// The stamp of the working tree: one hash that changes when any file a test could depend on changes.
// Node-only. It covers every tracked file and every untracked file that git does not ignore (by content,
// so an edit that restores a file restores the stamp), the generated build outputs that tests load but git
// ignores (src/engine/lean/ and src/engine/pkg/), and the Node version. The test reporters write it beside
// each run's outcomes and `exegra verify` compares it with the current one to decide whether the outcomes of
// a run still describe the tree it is about to record.

import { createHash } from 'node:crypto';
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
 * @returns {string}
 */
export function treeStamp(repoRoot) {
  const all = createHash('sha256');
  all.update(`node ${process.version}\n`);
  for (const rel of stampedFiles(repoRoot)) {
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
