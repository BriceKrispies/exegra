// Footprints of claim results (WG-5694, audit Q13): what a result read, so that an edit's affected set (the
// entities Project.apply reports as `affected`) determines exactly which results it can change.
//
// A footprint is a union of reads:
//   entities       ids read directly (the claim itself, the components its selectors picked, its cut);
//   entityKinds    every entity of these kinds (a query over a whole kind, such as every port for has-port);
//   selection      the resolution of selectors: any component added, removed, or changed in what selectors
//                  match on (parent, kind, category, tags, trust zone), and any facet;
//   relationships  a query footprint: every relationship that passes the filter (kinds, classes, where, and for a
//                  direct check the components it may start and end at), present or absent; an added relationship
//                  that passes it touches the result as much as an edited one;
//   structure      the abstraction structure of a hierarchy and cut (abstraction.js, structuralChange);
//   all            everything (results that rest on runs or recorded facts).
// The derived facts of abstraction.js record footprints of the same kind (witnesses plus a query over blocks).
// Footprints are about the model a result read. Whether recorded evidence describes the current files is the
// separate question claims.js answers with tree stamps (applyFreshness); the two are not mixed.

import { own } from './own.js';
import { kindInfo } from './interactions.js';
import { componentOf } from './query.js';
import { structuralChange } from './abstraction.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/**
 * @typedef {{kinds: string[]|null, classes: string[]|null, dependencyOnly?: boolean, where: {property: string, values: string[]}|null,
 *   from: string[]|null, to: string[]|null}} RelationshipQuery
 * @typedef {{all?: boolean, entities?: string[], entityKinds?: string[], selection?: boolean, relationships?: RelationshipQuery|null,
 *   structure?: {hierarchy: string, cut: string|null}|null}} Footprint
 */

/** Component properties selectors match on. */
const SELECTOR_KEYS = ['parent', 'kind', 'category', 'tags', 'trustZone'];

/**
 * Whether a relationship passes a relationship query.
 * @param {Model} model @param {RelationshipQuery} q @param {Entity} r
 */
export function relationshipMatches(model, q, r) {
  const kind = r.data.kind;
  if (q.kinds && !q.kinds.includes(kind)) return false;
  if (q.classes && !q.classes.includes(kindInfo(model.meta, kind).class)) return false;
  if (q.dependencyOnly && !/** @type {any} */ (own(model.meta.relationshipKinds, kind))?.dependency) return false;
  if (q.where && !q.where.values.includes(r.data[q.where.property])) return false;
  if (q.from && !q.from.includes(/** @type {string} */ (componentOf(model, r.data.from)?.id))) return false;
  if (q.to && !q.to.includes(/** @type {string} */ (componentOf(model, r.data.to)?.id))) return false;
  return true;
}

/**
 * Whether an edit (the models before and after it, and the ids it affected) touches a footprint.
 * @param {Footprint|undefined} fp @param {Model} before @param {Model} after @param {Iterable<string>} affected
 */
export function footprintTouched(fp, before, after, affected) {
  if (!fp || fp.all) return true;
  const ids = [...affected];
  if (!ids.length) return false;
  const direct = new Set(fp.entities ?? []);
  const kinds = new Set(fp.entityKinds ?? []);
  for (const id of ids) {
    if (direct.has(id)) return true;
    const a = before.entities.get(id), b = after.entities.get(id);
    const kind = (b ?? a)?.kind;
    if (kind === undefined) continue;
    if (kinds.has(kind)) return true;
    if (fp.selection && kind === 'facet') return true;
    if (fp.selection && kind === 'component' && (!a || !b || SELECTOR_KEYS.some((k) => JSON.stringify(a.data[k]) !== JSON.stringify(b.data[k])))) return true;
    if (fp.relationships && kind === 'relationship') {
      const q = fp.relationships;
      if ((a && a.kind === 'relationship' && relationshipMatches(before, q, a)) || (b && b.kind === 'relationship' && relationshipMatches(after, q, b))) return true;
    }
  }
  if (fp.structure && structuralChange(before, after, ids)) return true;
  return false;
}

/**
 * The claims whose results an edit can change: those whose recorded footprint it touches. Results without a
 * footprint are always recomputed.
 * @param {{claimId: string, footprint?: Footprint}[]} results @param {Model} before @param {Model} after @param {Iterable<string>} affected
 * @returns {Set<string>}
 */
export function claimsToRecompute(results, before, after, affected) {
  const ids = [...affected];
  /** @type {Set<string>} */
  const out = new Set();
  for (const r of results) if (footprintTouched(r.footprint, before, after, ids)) out.add(r.claimId);
  // A claim added by the edit has no result yet.
  for (const id of ids) if (after.entities.get(id)?.kind === 'claim') out.add(id);
  return out;
}
