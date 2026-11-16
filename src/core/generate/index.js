// The artifact generators. Every artifact is a pure function of the semantic model
// and the evaluation inputs: same inputs give byte-identical output. Nothing here
// reads the file system, the clock, or the environment.

import { generateManifest } from './manifest.js';
import { generateArchitectureDoc } from './architecture-doc.js';
import { generateClaimsReport, generateClaimsReportJson } from './claims-report.js';
import { generateTaskManifest } from './task-manifest.js';

/** @typedef {import('../types.js').Model} Model */
/** @typedef {import('../types.js').Diagnostic} Diagnostic */
/** @typedef {import('../claims.js').ClaimResult} ClaimResult */
/**
 * @typedef {Object} Traceability
 * @property {number} checkedModules
 * @property {{component: string, module: string}[]} missingModules
 * @property {string[]} unclaimedFiles
 */

export { generateManifest } from './manifest.js';
export { generateArchitectureDoc } from './architecture-doc.js';
export { generateClaimsReport, generateClaimsReportJson } from './claims-report.js';
export { generateTaskManifest } from './task-manifest.js';

/**
 * All generated artifacts, keyed by file name.
 * @param {Model} model
 * @param {{claimResults?: ClaimResult[], diagnostics?: Diagnostic[], traceability?: Traceability}} [opts]
 * @returns {Record<string, string>}
 */
export function generateAll(model, opts = {}) {
  const o = {
    claimResults: opts.claimResults ?? [],
    diagnostics: opts.diagnostics ?? [],
    traceability: opts.traceability,
  };
  return {
    'manifest.json': generateManifest(model),
    'ARCHITECTURE.md': generateArchitectureDoc(model, o),
    'claims-report.md': generateClaimsReport(model, o),
    'claims-report.json': generateClaimsReportJson(model, o),
    'tasks.json': generateTaskManifest(model, o),
  };
}
