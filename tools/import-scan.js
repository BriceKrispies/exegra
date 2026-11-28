// The import scan: the fact producer for the assumption `extracted-facts-current` (WG-5684, epistemics defect D5 of
// the 2026-11-26 assessment; reworked by WG-5696). Node-only.
//
// Imports between files of the implementation surface are no longer compared with hand-declared relationships: the
// extractor (tools/extract.js) reads them into a fact file and the core derives the relationships from it
// (src/core/extraction.js). What the scan checks now is what extraction cannot vouch for itself:
//
//   fresh      the fact file describes the tree: the digest of every file of the surface equals the recorded one, and
//              the extractor identity and version are current. A stale fact file refutes the assumption.
//   external   an import of the file system (node:fs, node:fs/promises, fs) from a module element, which no extracted
//              element stands for. It is mapped to the `filesystem` component and is undeclared when no dependency
//              relationship leads from the importing component or one of its ancestors to the file system. Packages other
//              than the file system are not mapped and not reported.

import path from 'node:path';
import { assumptionFact } from '../src/core/facts.js';
import { moduleDeclarations } from '../src/core/query.js';
import { factStamps } from './tree-stamp.js';
import { jsImports, readFacts, factsDrift, FACTS_PATH } from './extract.js';

/** The assumption this scan checks. */
export const IMPORT_ASSUMPTION = 'extracted-facts-current';

/** Builtins that reach the file system, and the component that stands for it. */
const FILESYSTEM = new Set(['node:fs', 'node:fs/promises', 'fs', 'fs/promises']);
const FILESYSTEM_COMPONENT = 'filesystem';

/**
 * The module specifiers a JavaScript source text imports, in order of first appearance: static `import` and
 * `export ... from`, dynamic `import()`, `require()`, `process.getBuiltinModule()` and any `node:` builtin named in
 * the code. Comments are removed first. The one parser is the extractor's.
 * @param {string} text
 * @returns {string[]}
 */
export function importsOf(text) {
  return jsImports(text).map((i) => i.spec);
}

/**
 * @typedef {{from: string, component: string, imports: string, target: string}} UndeclaredImport
 *   `from` imports `imports`, which stands for component `target`, and no dependency relationship declares it
 * @typedef {{checked: number, imports: number, stale: string[], extractorChanged: boolean, undeclared: UndeclaredImport[]}} ImportScan
 */

/**
 * Check the fact file against the tree and the file-system imports against the declared relationships.
 * @param {import('../src/core/types.js').Model} model @param {string} repoRoot
 * @param {import('./extract.js').Facts|null} [facts] the fact file, else the repository's own
 * @returns {ImportScan}
 */
export function scanImports(model, repoRoot, facts = readFacts(path.join(repoRoot, FACTS_PATH))) {
  if (!facts) return { checked: 0, imports: 0, stale: [`${FACTS_PATH} (no fact file)`], extractorChanged: false, undeclared: [] };
  const drift = factsDrift(facts, repoRoot);
  const decls = moduleDeclarations(model);
  /** @param {string} file */
  const owner = (file) => {
    /** @type {string|null} */
    let best = null;
    let len = -1;
    for (const d of decls) {
      const dir = d.path.endsWith('/');
      if (!(dir ? file.startsWith(d.path) : file === d.path)) continue;
      const l = dir ? d.path.length : Infinity;
      if (l > len) { best = d.component; len = l; }
    }
    return best;
  };
  /** @param {string} id @returns {string[]} the component and its ancestors */
  const lineage = (id) => {
    const out = [];
    /** @type {string|undefined} */
    let cur = id;
    const seen = new Set();
    while (cur && !seen.has(cur)) {
      seen.add(cur);
      out.push(cur);
      const e = model.entities.get(cur);
      cur = typeof e?.data?.parent === 'string' ? e.data.parent : undefined;
    }
    return out;
  };
  const dependency = new Set(Object.entries(model.meta.relationshipKinds ?? {}).filter(([, v]) => /** @type {any} */ (v)?.dependency).map(([k]) => k));
  const edges = new Set((model.byKind.relationship ?? []).filter((r) => dependency.has(r.data.kind)).map((r) => `${r.data.from}\0${r.data.to}`));
  /** @param {string} a @param {string} b */
  const declaredEdge = (a, b) => lineage(a).some((x) => lineage(b).some((y) => edges.has(`${x}\0${y}`)));

  /** @type {UndeclaredImport[]} */
  const undeclared = [];
  let count = 0;
  for (const f of facts.files) {
    count += f.imports.length;
    const from = owner(f.path);
    if (!from || !model.entities.has(FILESYSTEM_COMPONENT)) continue;
    for (const i of f.imports) {
      if (!FILESYSTEM.has(i.spec) || from === FILESYSTEM_COMPONENT) continue;
      if (lineage(from).includes(FILESYSTEM_COMPONENT) || declaredEdge(from, FILESYSTEM_COMPONENT)) continue;
      if (!undeclared.some((u) => u.from === f.path && u.imports === i.spec)) undeclared.push({ from: f.path, component: from, imports: i.spec, target: FILESYSTEM_COMPONENT });
    }
  }
  return { checked: facts.files.length, imports: count, stale: [...drift.changed, ...drift.missing, ...drift.gone], extractorChanged: drift.extractor, undeclared };
}

/** Whether the scan found nothing to refute the assumption. @param {ImportScan} scan */
const clean = (scan) => !scan.stale?.length && !scan.extractorChanged && !scan.undeclared.length;

/**
 * The fact a scan makes about `extracted-facts-current`: refuted when the fact file is stale or a file-system import is
 * undeclared, holds otherwise; stamped with the records stamp it ran on against the current one.
 * @param {ImportScan} scan @param {string|null|undefined} recorded @param {{tree: string|null, formal: string|null}} current
 */
export function importScanFacts(scan, recorded, current) {
  return [assumptionFact(IMPORT_ASSUMPTION, 'importScan', clean(scan) ? 'pass' : 'fail', factStamps(recorded, current))];
}

/**
 * What `exegra verify` records for the assumption (results.json, `assumptions`), which claim evaluation reads.
 * @param {ImportScan} scan @param {string|null} stamp
 */
export function importScanRecord(scan, stamp) {
  /** @type {string[]} */
  const problems = [];
  if (scan.stale?.length) problems.push(`the fact file is stale for ${scan.stale.length} file${scan.stale.length === 1 ? '' : 's'} (${scan.stale.slice(0, 3).join(', ')}${scan.stale.length > 3 ? ', ...' : ''}); run node tools/extract.js`);
  if (scan.extractorChanged) problems.push('the fact file was written by another extractor version');
  if (scan.undeclared.length) problems.push(`${scan.undeclared.length} file-system import${scan.undeclared.length === 1 ? '' : 's'} with no declared relationship: ${scan.undeclared.map((u) => `${u.from} (${u.component}) imports ${u.imports} (${u.target})`).join('; ')}`);
  return {
    outcome: /** @type {'pass'|'fail'} */ (clean(scan) ? 'pass' : 'fail'),
    kind: /** @type {'importScan'} */ ('importScan'),
    detail: problems.length ? `the import scan found ${problems.join('; ')}` : `the fact file describes all ${scan.checked} files of the surface (${scan.imports} imports), and every file-system import has a declared relationship`,
    ...(stamp !== null ? { stamp } : {}),
  };
}

