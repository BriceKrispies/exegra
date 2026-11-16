// Deterministic normal form and hash of a semantic model. Two source texts that
// differ only in comments, whitespace, key order or top-level declaration order
// normalize to the same value. Order inside arrays is preserved because it can
// be meaningful (transition priority, scenario steps).

/** @typedef {import('./types.js').Model} Model */

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

/**
 * The normalized semantic content of a model as a plain JSON value.
 * Contains no source locations and no presentation state.
 * @param {Model} model
 */
export function normalize(model) {
  const top = [...model.entities.values()].filter((e) => e.owner === null);
  top.sort((a, b) => (a.id < b.id ? -1 : a.id > b.id ? 1 : 0));
  return sortKeys({
    schemaVersion: model.schemaVersion,
    vocabulary: model.vocabulary ?? {},
    entities: top.map((e) => ({ kind: e.kind, ...e.data })),
  });
}

/**
 * 53-bit string hash (cyrb53), rendered as 14 hex digits. Not cryptographic;
 * used for revision identity and change detection.
 * @param {string} str
 */
export function hashString(str) {
  let h1 = 0xdeadbeef, h2 = 0x41c6ce57;
  for (let i = 0; i < str.length; i++) {
    const ch = str.charCodeAt(i);
    h1 = Math.imul(h1 ^ ch, 2654435761);
    h2 = Math.imul(h2 ^ ch, 1597334677);
  }
  h1 = Math.imul(h1 ^ (h1 >>> 16), 2246822507) ^ Math.imul(h2 ^ (h2 >>> 13), 3266489909);
  h2 = Math.imul(h2 ^ (h2 >>> 16), 2246822507) ^ Math.imul(h1 ^ (h1 >>> 13), 3266489909);
  return (4294967296 * (2097151 & h2) + (h1 >>> 0)).toString(16).padStart(14, '0');
}

/**
 * Hash of the normalized semantic content.
 * @param {Model|null} model
 */
export function semanticHash(model) {
  return model ? hashString(JSON.stringify(normalize(model))) : '00000000000000';
}
