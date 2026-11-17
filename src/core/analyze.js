// One entry point for "what does this source text mean, and is it well-formed?"
import { parseSpec } from './parse.js';
import { validateModel } from './validate.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */

/**
 * Parse and validate specification source.
 * @param {string} text
 * errorCount counts the errors that block a transaction. Violations of integrity rules
 * (`integrity.violated`) are reported with their rule's severity but are left out of it: they are
 * ratcheted by Project.apply instead, so existing ones do not block unrelated edits.
 * @returns {{model: Model|null, diagnostics: Diagnostic[], errorCount: number}}
 */
export function analyzeSpec(text) {
  const { model, diagnostics } = parseSpec(text);
  // Semantic rules assume a structurally sound model; skip them when structure is broken.
  const structuralErrors = diagnostics.some((d) => d.severity === 'error');
  const all = model && !structuralErrors ? diagnostics.concat(validateModel(model)) : diagnostics;
  const rank = { error: 0, warning: 1, info: 2 };
  all.sort((a, b) => rank[a.severity] - rank[b.severity] || (a.loc?.offset ?? 0) - (b.loc?.offset ?? 0) || (a.code < b.code ? -1 : a.code > b.code ? 1 : 0));
  return { model, diagnostics: all, errorCount: all.filter((d) => d.severity === 'error' && d.code !== 'integrity.violated').length };
}
