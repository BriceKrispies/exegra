// What the session adopts from a read of the project's files on disk: the product layers as the Project
// takes them, and the reload of a Project from such a read. Kept apart from session.js (which needs the
// browser and the build's virtual modules) so the rules are testable on their own.

/** @typedef {import('../core/layers.js').ProductLayer} ProductLayer */
/** @typedef {import('../core/project.js').Project} Project */

/**
 * The product layers of a project read from disk (the `layers` the persistence service returns), as
 * Project takes them. A read without `layers` has none.
 * @param {{layers?: {file: string, text: string, platform?: ProductLayer['platform']}[]}|null|undefined} files
 * @returns {ProductLayer[]}
 */
export function layersOf(files) {
  return (files?.layers ?? []).map((l) => ({ file: l.file, text: l.text, platform: l.platform }));
}

/**
 * The facts read from outside the specification that a project carries (src/core/extraction.js): the extracted
 * facts (specs/<project>/extracted/facts.json) and the observed facts, as the persistence service returns them, or
 * null each. They become relationships of the model with their own provenance, exactly as the command line attaches them.
 * @param {{extracted?: any, observed?: any}|null|undefined} files
 * @returns {{extracted: import('../core/extraction.js').ExtractedFacts|null, observed: import('../core/extraction.js').ObservedFacts|null}}
 */
export function factsOf(files) {
  const obj = (/** @type {any} */ x) => (x && typeof x === 'object' && !Array.isArray(x) ? x : null);
  return { extracted: obj(files?.extracted), observed: obj(files?.observed) };
}

/**
 * Re-derive `project` from a read of its files on disk after `file` changed: a changed, added or removed
 * product file takes the product layers of the read (all of them); the specification and the layout take
 * their text. The product layers of the read are passed with every reload, since the platform check
 * of a layer depends on the specification it was read beside.
 * @param {Project} project
 * @param {'spec'|'layout'|'products'} file
 * @param {{spec: {text: string}, layout?: {text: string}|null, layers?: any[]}} files
 * @returns {ReturnType<Project['reload']>}
 */
export function reloadFromDisk(project, file, files) {
  const layers = layersOf(files);
  if (file === 'products') return project.reload({ layers });
  if (file === 'spec') return project.reload({ specText: files.spec.text, layers });
  return project.reload({ layoutText: files.layout?.text ?? undefined, layers });
}
