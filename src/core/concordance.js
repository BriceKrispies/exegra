// Concordance results for a linked project. A project's project.jsonc may name a results file
// ("concordanceResults", relative to project.jsonc) that another tool, Concordance, writes per
// claim of the specification it checks. Each entry becomes a derived evidence item of kind
// `test` for that claim: a pass supports it, a fail contradicts it. The items live only in the
// recorded results handed to claim evaluation. They are never added to the model, so they are
// not spec entities, never written back and never part of the semantic hash.
//
// Pure: the file text and the resolved specification path come from the caller (tools/workspace.js).

/** The `tool` value a results file must carry to be applied. */
export const CONCORDANCE_TOOL = 'concordance';

/**
 * @typedef {{ id: string, claim: string, title: string, ref: string, outcome: 'pass'|'fail', revision: 'matches'|'unknown',
 *   detail?: string, proofs?: string[] }} DerivedEvidence
 * @typedef {{ severity: 'warning', code: string, message: string }} ConcordanceDiagnostic
 * @typedef {{ file: string, text: string|null, problem?: string, specPath: string, specSha256?: string }} ConcordanceInput
 *   file: the path as project.jsonc writes it; text: the file's content, null when unreadable; problem: why it is
 *   unreadable when it exists but cannot be read (a directory, no permission);
 *   specPath: the absolute path of the project's resolved specification; specSha256: the sha-256 of the
 *   specification text as read (src/core/sha256.js), absent when it could not be computed
 */

/**
 * Path segments, with forward and back slashes alike, lower-cased (Windows paths are case-insensitive).
 * @param {string} p
 */
function segments(p) {
  return String(p).split(/[\\/]/).filter((s) => s !== '' && s !== '.').map((s) => s.toLowerCase());
}

/**
 * Whether a results file's `source` names the project's specification. `source` is relative to the
 * other repository's root, so it matches when the resolved specification path ends with it on whole
 * path segments.
 * @param {string} source @param {string} specPath
 */
export function sourceNamesSpec(source, specPath) {
  const want = segments(source);
  const have = segments(specPath);
  if (want.length === 0 || want.includes('..') || want.length > have.length) return false;
  const offset = have.length - want.length;
  return want.every((seg, i) => seg === have[offset + i]);
}

/**
 * Turn a Concordance results file into derived evidence for the claims of a specification.
 * Nothing is derived when the file is missing, invalid, from another tool or about another
 * specification; each such case is a warning and the statuses are unchanged. An entry for an
 * unknown claim is a warning naming the id; the other entries still apply.
 * @param {ConcordanceInput} input
 * @param {string[]} claimIds the ids of the specification's claims
 * @returns {{ derived: DerivedEvidence[], diagnostics: ConcordanceDiagnostic[] }}
 */
export function concordanceEvidence(input, claimIds) {
  /** @type {ConcordanceDiagnostic[]} */
  const diagnostics = [];
  const warn = (/** @type {string} */ code, /** @type {string} */ message) => diagnostics.push({ severity: 'warning', code, message });
  const file = input.file;
  if (input.text === null && input.problem) {
    warn('concordance.unreadable', `Concordance results "${file}" ${input.problem}; claim statuses are unchanged.`);
    return { derived: [], diagnostics };
  }
  if (input.text === null) {
    warn('concordance.missing', `Concordance results "${file}" could not be read; claim statuses are unchanged.`);
    return { derived: [], diagnostics };
  }
  /** @type {any} */
  let data;
  try {
    data = JSON.parse(input.text);
  } catch {
    warn('concordance.invalid', `Concordance results "${file}" are not valid JSON; claim statuses are unchanged.`);
    return { derived: [], diagnostics };
  }
  if (!data || typeof data !== 'object' || Array.isArray(data)) {
    warn('concordance.invalid', `Concordance results "${file}" are not a JSON object; claim statuses are unchanged.`);
    return { derived: [], diagnostics };
  }
  if (data.tool !== CONCORDANCE_TOOL) {
    warn('concordance.tool', `Results file "${file}" names tool ${JSON.stringify(data.tool ?? null)}, not "${CONCORDANCE_TOOL}"; it is not applied.`);
    return { derived: [], diagnostics };
  }
  if (typeof data.source !== 'string' || !sourceNamesSpec(data.source, input.specPath)) {
    warn('concordance.source', `Concordance results "${file}" were written for ${JSON.stringify(data.source ?? null)}, which is not this project's specification; they are not applied.`);
    return { derived: [], diagnostics };
  }
  // A results file may name the revision of the specification it was computed for. Naming a different one
  // makes it stale: it is not applied. Naming none leaves the revision unknown, and the evidence says so.
  const named = typeof data.specSha256 === 'string' ? data.specSha256 : null;
  if (named !== null && input.specSha256 !== undefined && named !== input.specSha256) {
    warn('concordance.revision', `Concordance results "${file}" were computed for another revision of the specification (specSha256 ${named}, this text is ${input.specSha256}); they are not applied.`);
    return { derived: [], diagnostics };
  }
  const revision = named !== null && input.specSha256 !== undefined ? 'matches' : 'unknown';
  const claims = data.claims && typeof data.claims === 'object' && !Array.isArray(data.claims) ? data.claims : {};
  /** @type {DerivedEvidence[]} */
  const derived = [];
  for (const [claim, entry] of Object.entries(claims)) {
    if (!claimIds.includes(claim)) {
      warn('concordance.claim', `Concordance results "${file}" have an entry for "${claim}", which is not a claim of the specification; that entry is ignored.`);
      continue;
    }
    const outcome = entry && typeof entry === 'object' ? /** @type {any} */ (entry).outcome : undefined;
    if (outcome !== 'pass' && outcome !== 'fail') {
      warn('concordance.outcome', `Concordance results "${file}" give "${claim}" the outcome ${JSON.stringify(outcome ?? null)}; only "pass" and "fail" are applied.`);
      continue;
    }
    /** @type {DerivedEvidence} */
    const item = { id: `concordance-${claim}`, claim, title: `Concordance result for "${claim}"`, ref: `${file}#${claim}`, outcome, revision };
    if (typeof entry.detail === 'string' && entry.detail !== '') item.detail = entry.detail;
    if (Array.isArray(entry.proofs)) item.proofs = entry.proofs.filter((/** @type {unknown} */ p) => typeof p === 'string');
    derived.push(item);
  }
  return { derived, diagnostics };
}

/**
 * The recorded results of a project with the Concordance evidence applied. Without a configured
 * results file (`concordance` null) the recorded results are returned as they are.
 * @param {{ byKind?: Record<string, {id: string}[]> } | null | undefined} model
 * @param {any} recorded the parsed results.json of the project, or null
 * @param {ConcordanceInput|null|undefined} concordance
 * @returns {{ recorded: any, diagnostics: ConcordanceDiagnostic[] }}
 */
export function applyConcordance(model, recorded, concordance) {
  if (!concordance || !model) return { recorded, diagnostics: [] };
  const claimIds = (model.byKind?.claim ?? []).map((c) => c.id);
  const { derived, diagnostics } = concordanceEvidence(concordance, claimIds);
  if (!derived.length) return { recorded, diagnostics };
  const base = recorded && typeof recorded === 'object' ? recorded : {};
  return { recorded: { ...base, derived }, diagnostics };
}
