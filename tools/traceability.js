// Traceability between a specification and the implementation files on disk.
// Node-only: it reads the file system. Not part of src/core.
//
// A component may declare `implementation.modules`: paths relative to the
// repository root (forward slashes). A module path ending in "/" claims every
// file beneath that directory. The implementation surface (tools/surface.js) is the files under src/, cli/
// and tools/ (.js, .json, .css, .html), the Lean sources under formal/, the Rust sources under engine/, and
// index.html and vite.config.js at the root; any of them that no component claims is reported.
//
// With realisation roots (tools/realisation-roots.js), a module "<alias>:<path>"
// is checked in that root, and unclaimed files come only from roots that declare
// include globs: this repository's surface is not scanned, since the project is
// realised elsewhere.
//
// Each declared module path is a module element (src/core/query.js, moduleDeclarations), placed under
// the component that declares it. The map from surface files to module elements must be a function:
// a file covered by two module elements (two components declaring it, or a directory and a file inside
// it) is an error, traceability.multiple-owners, listed in `multipleOwners` and in `errors`.

import fs from 'node:fs';
import path from 'node:path';
import { traceRoots } from './realisation-roots.js';
import { moduleDeclarations } from '../src/core/query.js';
import { scanSurface, GENERATED_DIRS } from './surface.js';

/** @typedef {import('../src/core/types.js').Model} Model */
/** @typedef {import('./realisation-roots.js').RealisationRoot} RealisationRoot */

export { GENERATED_DIRS };

/** @param {string} p */
const slash = (p) => p.replace(/[\\]/g, '/');

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
 * @param {RealisationRoot[]} [roots] realisation roots of the project; none keeps the repository-only check
 * @returns {{checkedModules: number, missingModules: {component: string, module: string, root?: string, reason?: string}[], unclaimedFiles: string[], claimedFiles: number, multipleOwners: {file: string, modules: {module: string, component: string}[]}[], errors: {code: string, severity: 'error', message: string, file: string, components: string[]}[], roots?: Record<string, any>}}
 */
export function checkTraceability(model, repoRoot, roots = []) {
  const components = model.byKind.component ?? [];
  const declaring = components.filter((c) => c.data.implementation !== undefined && c.data.implementation !== null);
  if (!declaring.length && !roots.length) return { checkedModules: 0, missingModules: [], unclaimedFiles: [], claimedFiles: 0, multipleOwners: [], errors: [] };

  /** @type {{component: string, module: string}[]} */
  const declared = moduleDeclarations(model).map((d) => ({ component: d.component, module: slash(d.path) }));

  if (roots.length) {
    const traced = traceRoots(declared, roots);
    const missingModules = [...traced.local.filter((d) => !moduleExists(repoRoot, d.module)), ...traced.missingModules];
    return {
      checkedModules: declared.length,
      missingModules,
      unclaimedFiles: traced.unclaimedFiles,
      claimedFiles: traced.claimedFiles,
      multipleOwners: [],
      errors: [],
      roots: traced.roots,
    };
  }

  const missingModules = declared.filter((d) => !moduleExists(repoRoot, d.module));

  const surface = scanSurface(repoRoot);
  /** @param {string} file the module elements covering a file, one per distinct (component, path) */
  const coveringOf = (file) => {
    const seen = new Set();
    return declared.filter((d) => {
      if (!(d.module.endsWith('/') ? file.startsWith(d.module) : file === d.module)) return false;
      const key = `${d.component}\u0000${d.module}`;
      if (seen.has(key)) return false;
      seen.add(key);
      return true;
    });
  };
  /** @type {string[]} */
  const unclaimedFiles = [];
  /** @type {{file: string, modules: {module: string, component: string}[]}[]} */
  const multipleOwners = [];
  for (const f of surface) {
    const covering = coveringOf(f);
    if (!covering.length) unclaimedFiles.push(f);
    else if (covering.length > 1) multipleOwners.push({ file: f, modules: covering.map((d) => ({ module: d.module, component: d.component })) });
  }
  const errors = multipleOwners.map((m) => {
    const components = [...new Set(m.modules.map((x) => x.component))];
    return {
      code: 'traceability.multiple-owners', severity: /** @type {'error'} */ ('error'), file: m.file, components,
      message: `${m.file} is covered by ${m.modules.length} module elements (${m.modules.map((x) => `${x.module} of ${x.component}`).join(', ')}); every file belongs to exactly one module element, so a file several elements share goes to one shared element at their lowest common ancestor.`,
    };
  });

  return {
    checkedModules: declared.length,
    missingModules,
    unclaimedFiles,
    claimedFiles: surface.length - unclaimedFiles.length,
    multipleOwners,
    errors,
  };
}
