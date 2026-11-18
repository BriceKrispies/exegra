// The normal form and semantic hash of a model, computed by the verified kernel in Lean
// (formal/Exegra/Hash.lean). Two source texts that differ only in comments, whitespace, key
// order or top-level declaration order normalize to the same value; order inside arrays is kept
// because it can be meaningful (transition priority, scenario steps). The hash is cyrb53 over the
// UTF-16 code units of the normal form's JSON text, 14 hex digits: not cryptographic, used for
// revision identity and change detection.
//
// A model derived by parseSpec carries the hash Lean computed with it; any other model is sent to
// Lean as its top-level declarations.

import { call } from './lean.js';

/** @typedef {import('./types.js').Model} Model */

/** @param {Model} model */
function content(model) {
  return {
    schemaVersion: model.schemaVersion,
    vocabulary: model.vocabulary ?? {},
    entities: [...model.entities.values()].filter((e) => e.owner === null).map((e) => ({ id: e.id, kind: e.kind, data: e.data })),
  };
}

/**
 * The normalized semantic content of a model as a plain JSON value.
 * Contains no source locations and no presentation state.
 * @param {Model} model
 */
export function normalize(model) {
  const r = call('hash.normalize', content(model));
  if (!r.ok) throw new Error(r.error);
  return r.value;
}

/**
 * Hash of the normalized semantic content.
 * @param {Model|null} model
 * @returns {string}
 */
export function semanticHash(model) {
  if (!model) return '00000000000000';
  if (typeof model.semanticHash === 'string') return model.semanticHash;
  const r = call('hash.semantic', content(model));
  if (!r.ok) throw new Error(r.error);
  return r.value;
}
