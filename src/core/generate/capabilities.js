// The capability matrix (generated/capabilities.md): for each guarantee class, the claims of the specification
// that establish it and the ones that do not yet. A claim belongs to a class through its `guaranteeClass`. A claim
// is listed as established only when the Lean verdict shows it established: proved, fresh and with no open
// assumption (Exegra.Verdict.shownEstablished); every other claim of the class is listed with its status. The
// counts of the specification that the README and docs/self-hosting.md used to carry by hand are generated here too.
// Pure: the same model and claim results give the same bytes.

/** @typedef {import('../types.js').Model} Model */
/** @typedef {import('../claims.js').ClaimResult} ClaimResult */

/** The guarantee classes, in the order and with the numbers of the matrix. */
export const GUARANTEE_CLASSES = [
  { id: 'well-formedness', row: '1. Well-formedness' },
  { id: 'consistency', row: '2. Consistency' },
  { id: 'safety', row: '3. Safety' },
  { id: 'liveness', row: '4. Liveness' },
  { id: 'compositionality', row: '5. Compositionality' },
  { id: 'refinement', row: '6. Refinement' },
  { id: 'conformance', row: '7. Implementation conformance' },
  { id: 'fidelity', row: '8. Simulation fidelity' },
  { id: 'change-impact', row: 'Change impact' },
];

/** @param {string} a @param {string} b */
const byText = (a, b) => (a < b ? -1 : a > b ? 1 : 0);

/**
 * The rows of the matrix: per class, the established claims and the others with their status, each sorted by id.
 * @param {Model} model @param {ClaimResult[]} claimResults
 * @returns {{id: string, row: string, established: string[], other: {id: string, status: string}[]}[]}
 */
export function capabilityRows(model, claimResults) {
  const results = new Map(claimResults.map((r) => [r.claimId, r]));
  return GUARANTEE_CLASSES.map((cls) => {
    const claims = (model.byKind.claim ?? []).filter((c) => c.data.guaranteeClass === cls.id).map((c) => c.id).sort(byText);
    const established = claims.filter((id) => {
      const r = results.get(id);
      return r?.status === 'proved' && r.verdict?.established === true && r.verdict.freshness === 'fresh' && r.verdict.openAssumptions.length === 0;
    });
    const other = claims.filter((id) => !established.includes(id)).map((id) => ({ id, status: results.get(id)?.status ?? 'not-evaluated' }));
    return { ...cls, established, other };
  });
}

/**
 * The capability matrix as Markdown.
 * @param {Model} model @param {{claimResults?: ClaimResult[]}} [opts]
 * @returns {string}
 */
export function generateCapabilities(model, opts = {}) {
  const claimResults = opts.claimResults ?? [];
  const rows = capabilityRows(model, claimResults);
  const cell = (/** @type {string[]} */ xs) => (xs.length ? xs.map((x) => `\`${x}\``).join(', ') : 'none');
  const count = (/** @type {string} */ kind) => (model.byKind[kind] ?? []).length;
  /** @type {Record<string, number>} */
  const statuses = {};
  for (const r of claimResults) statuses[r.status] = (statuses[r.status] ?? 0) + 1;
  const established = claimResults.filter((r) => r.verdict?.established).length;
  return [
    '# Capability matrix',
    '',
    'Generated from the specification by `exegra generate`; do not edit. A claim belongs to a class through its',
    '`guaranteeClass`. It is listed as established only when Lean shows it established: proved, fresh, and with no',
    'open assumption (formal/Exegra/Verdict.lean, `shownEstablished`). Every other claim of the class is listed with',
    'its status.',
    '',
    '| Class | Established | Not established |',
    '|---|---|---|',
    ...rows.map((r) => `| ${r.row} | ${cell(r.established)} | ${r.other.length ? r.other.map((o) => `\`${o.id}\` (${o.status})`).join(', ') : 'none'} |`),
    '',
    '## Counts',
    '',
    '| What | Count |',
    '|---|---|',
    `| Components | ${count('component')} |`,
    `| Relationships | ${count('relationship')} |`,
    `| Behaviors | ${count('behavior')} |`,
    `| Scenarios | ${count('scenario')} |`,
    `| Claims | ${count('claim')} |`,
    `| Claims shown established | ${established} |`,
    ...Object.keys(statuses).sort(byText).map((s) => `| Claims ${s} | ${statuses[s]} |`),
    '',
  ].join('\n');
}
