// Deterministic JSON text for output: object keys sorted at every level, so that files and
// command results written from equal values are equal byte for byte. Presentation of results
// only; the semantic hash (src/core/hash.js) is computed by the Lean kernel.

/**
 * JSON.stringify with object keys sorted at every level.
 * @param {any} value @param {number} [indent]
 * @returns {string}
 */
export function stableStringify(value, indent) {
  return JSON.stringify(sortKeys(value), null, indent);
}

/** @param {any} v @returns {any} */
function sortKeys(v) {
  if (Array.isArray(v)) return v.map(sortKeys);
  if (v && typeof v === 'object') {
    /** @type {Record<string, any>} */
    const out = {};
    for (const k of Object.keys(v).sort()) out[k] = sortKeys(v[k]);
    return out;
  }
  return v;
}
