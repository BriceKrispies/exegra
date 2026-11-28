// The implementation surface: the files of this repository that a component must claim (tools/traceability.js)
// and that the extractor reads (tools/extract.js). Node-only: it reads the file system. Not part of src/core.
//
//   src/, cli/, tools/   .js .json .css .html
//   formal/              .lean (the Lean sources)
//   engine/              .rs (the Rust sources)
//   index.html, vite.config.js at the root
//
// Build output under GENERATED_DIRS is not part of the surface: it is derived from sources that a component
// claims (src/engine/pkg/ from engine/exegra-engine-wasm, by npm run build:engine; src/engine/lean/ from
// formal/, by npm run build:formal-wasm) and exists only after a build. Files named local-* are local data.

import fs from 'node:fs';
import path from 'node:path';

/** Directories scanned, each with the extensions of the files that count. */
export const SURFACE_DIRS = /** @type {const} */ ([
  { dir: 'src', extensions: ['.js', '.json', '.css', '.html'] },
  { dir: 'cli', extensions: ['.js', '.json', '.css', '.html'] },
  { dir: 'tools', extensions: ['.js', '.json', '.css', '.html'] },
  { dir: 'formal', extensions: ['.lean'] },
  { dir: 'engine', extensions: ['.rs'] },
]);
export const SURFACE_ROOT_FILES = ['index.html', 'vite.config.js'];
/** Generated directories (repo-relative, trailing slash) left out of the surface; each is ignored by git (.gitignore). */
export const GENERATED_DIRS = ['src/engine/pkg/', 'src/engine/lean/', 'formal/generated/'];
/** Directories never entered, whatever their depth. */
const SKIPPED = new Set(['node_modules', '.lake', 'target']);

/** @param {string} p */
export const slash = (p) => p.replace(/[\\]/g, '/');

/**
 * Every implementation-surface file, as repo-relative forward-slash paths, sorted.
 * @param {string} repoRoot
 * @returns {string[]}
 */
export function scanSurface(repoRoot) {
  /** @type {string[]} */
  const out = [];
  /** @param {string} abs @param {Set<string>} ext */
  const walk = (abs, ext) => {
    let entries;
    try {
      entries = fs.readdirSync(abs, { withFileTypes: true });
    } catch {
      return;
    }
    for (const entry of entries) {
      if (SKIPPED.has(entry.name) || entry.name.startsWith('local-')) continue;
      const child = path.join(abs, entry.name);
      if (entry.isDirectory()) {
        if (!GENERATED_DIRS.includes(`${slash(path.relative(repoRoot, child))}/`)) walk(child, ext);
      } else if (entry.isFile() && ext.has(path.extname(entry.name))) out.push(slash(path.relative(repoRoot, child)));
    }
  };
  for (const { dir, extensions } of SURFACE_DIRS) walk(path.join(repoRoot, dir), new Set(extensions));
  for (const file of SURFACE_ROOT_FILES) if (fs.existsSync(path.join(repoRoot, file))) out.push(file);
  return out.sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
}
