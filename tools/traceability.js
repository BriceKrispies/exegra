// Traceability between a specification and the implementation files on disk.
// Node-only: it reads the file system. Not part of src/core.
//
// A component may declare `implementation.modules`: paths relative to the
// repository root (forward slashes). A module path ending in "/" claims every
// file beneath that directory. Files under src/, cli/ and tools/ (extensions
// .js, .json, .css, .html) plus index.html and vite.config.js at the root are
// the implementation surface; any of them that no component claims is reported.
// Build output under GENERATED_DIRS is not part of the surface: it is derived from
// sources that a component claims (src/engine/pkg/ from engine/exegra-engine-wasm,
// by npm run build:engine; src/engine/lean/ from formal/, by npm run build:formal-wasm) and
// exists only after a build.

import fs from 'node:fs';
import path from 'node:path';

/** @typedef {import('../src/core/types.js').Model} Model */

const SCAN_DIRS = ['src', 'cli', 'tools'];
const SCAN_EXT = new Set(['.js', '.json', '.css', '.html']);
const SCAN_ROOT_FILES = ['index.html', 'vite.config.js'];
/** Generated directories (repo-relative, trailing slash) left out of the surface. */
export const GENERATED_DIRS = ['src/engine/pkg/', 'src/engine/lean/'];

/** @param {string} p */
const slash = (p) => p.replace(/\\/g, '/');

/**
 * Every implementation-surface file, as repo-relative forward-slash paths.
 * @param {string} repoRoot
 * @returns {string[]}
 */
function scanSurface(repoRoot) {
  /** @type {string[]} */
  const out = [];
  /** @param {string} abs */
  const walk = (abs) => {
    let entries;
    try {
      entries = fs.readdirSync(abs, { withFileTypes: true });
    } catch {
      return;
    }
    for (const entry of entries) {
      if (entry.name === 'node_modules' || entry.name.startsWith('local-')) continue; // local-* files are local data (gitignored)
      const child = path.join(abs, entry.name);
      if (entry.isDirectory()) {
        if (!GENERATED_DIRS.includes(`${slash(path.relative(repoRoot, child))}/`)) walk(child);
      } else if (entry.isFile() && SCAN_EXT.has(path.extname(entry.name))) out.push(slash(path.relative(repoRoot, child)));
    }
  };
  for (const dir of SCAN_DIRS) walk(path.join(repoRoot, dir));
  for (const file of SCAN_ROOT_FILES) {
    if (fs.existsSync(path.join(repoRoot, file))) out.push(file);
  }
  return out.sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
}

/**
 * @param {string} repoRoot @param {string} modulePath
 * @returns {boolean}
 */
function moduleExists(repoRoot, modulePath) {
  const abs = path.join(repoRoot, modulePath);
  try {
    return modulePath.endsWith('/') ? fs.statSync(abs).isDirectory() : fs.statSync(abs).isFile();
  } catch {
    return false;
  }
}

/**
 * Compare a model's declared implementation modules with the files on disk.
 * `checkedModules` counts declared module entries (a directory entry counts once).
 * @param {Model} model
 * @param {string} repoRoot absolute path of the repository root
 * @returns {{checkedModules: number, missingModules: {component: string, module: string}[], unclaimedFiles: string[], claimedFiles: number}}
 */
export function checkTraceability(model, repoRoot) {
  const components = model.byKind.component ?? [];
  const declaring = components.filter((c) => c.data.implementation !== undefined && c.data.implementation !== null);
  if (!declaring.length) return { checkedModules: 0, missingModules: [], unclaimedFiles: [], claimedFiles: 0 };

  /** @type {{component: string, module: string}[]} */
  const declared = [];
  for (const c of components) {
    const modules = c.data.implementation?.modules;
    if (!Array.isArray(modules)) continue;
    for (const m of modules) {
      if (typeof m === 'string' && m !== '') declared.push({ component: c.id, module: slash(m) });
    }
  }

  const missingModules = declared.filter((d) => !moduleExists(repoRoot, d.module));

  const surface = scanSurface(repoRoot);
  /** @param {string} file */
  const claimedBy = (file) => declared.some((d) => (d.module.endsWith('/') ? file.startsWith(d.module) : file === d.module));
  const unclaimedFiles = surface.filter((f) => !claimedBy(f));

  return {
    checkedModules: declared.length,
    missingModules,
    unclaimedFiles,
    claimedFiles: surface.length - unclaimedFiles.length,
  };
}
