// One entry point for "what does this source text mean, and is it well-formed?"
import { parseSpec } from './parse.js';
import { validateModel } from './validate.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */

/**
 * Parse and validate specification source.
 * @param {string} text
 * @param {{model: Model|null, diagnostics: Diagnostic[]}|null} [parsed] parseSpec(text), when the caller already has it
 * errorCount counts the errors that block a transaction. Violations of integrity rules
 * (`integrity.violated`) are reported with their rule's severity but are left out of it: they are
 * ratcheted by Project.apply instead, so existing ones do not block unrelated edits.
 * @returns {{model: Model|null, diagnostics: Diagnostic[], errorCount: number}}
 */
export function analyzeSpec(text, parsed) {
  const { model, diagnostics } = parsed ?? parseSpec(text);
  // Most semantic rules assume a structurally sound model, so they are skipped when structure is broken. The checks of
  // claims read only what they can resolve; they still run, so one unresolved reference does not hide their errors.
  const structuralErrors = diagnostics.some((d) => d.severity === 'error');
  /** @type {Diagnostic[]} */
  let semantic = [];
  if (model) {
    try { semantic = validateModel(model, structuralErrors ? { claimsOnly: true } : {}); } catch (e) { if (!structuralErrors) throw e; }
  }
  const all = diagnostics.concat(semantic);
  const rank = { error: 0, warning: 1, info: 2 };
  all.sort((a, b) => rank[a.severity] - rank[b.severity] || (a.loc?.offset ?? 0) - (b.loc?.offset ?? 0) || (a.code < b.code ? -1 : a.code > b.code ? 1 : 0));
  return { model, diagnostics: all, errorCount: all.filter((d) => d.severity === 'error' && d.code !== 'integrity.violated').length };
}
