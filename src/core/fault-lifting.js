// Fault lifting (WG-5730; docs/assessment/2026-11-27/multiscale.md, the distributed-application case study).
// A failure mode is located at an element or at an interaction (failureMode.target). The logical interactions it
// causes to fail are found two ways:
//
//   direct        a failure mode at a relationship fails that interaction; one at an element fails every
//                 relationship that crosses the boundary of the element and its logical members;
//   realisation   a realisation map (M3) says an interaction is realised in another hierarchy by a path of
//                 relationships. A mode at a hop of the path fails the interaction; so does a mode at an element
//                 of that hierarchy that contains a hop's endpoint (a host, a zone), because the hop runs through it.
//
// The failure each interaction suffers is the failure mode's kind read as an interaction failure (crash, stop,
// restart, partition, dependency outage and storage loss: unavailable; delay, slow storage and overload:
// delayed; and so on). The result is then lifted with a cut by the same abstraction map the derived model uses:
// an interaction between two blocks becomes a failure of the lifted interaction (from, to, kind) that the
// derived model at that cut carries; one inside a block is an internal failure of the block.
// A pure projection of the specification: it runs and decides nothing.

import { LOGICAL, hierarchyOf, ancestorsIn } from './query.js';
import { checkRealisations, endpointElement, interactionKey } from './abstraction.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */

/** The interaction failure a failure-mode kind causes. @type {Record<string, string>} */
const EFFECT = Object.freeze({
  crash: 'unavailable', stop: 'unavailable', restart: 'unavailable', partition: 'unavailable', 'dependency-outage': 'unavailable', 'storage-loss': 'unavailable',
  delay: 'delayed', 'slow-storage': 'delayed', overload: 'delayed',
  loss: 'lost', duplicate: 'duplicated', reorder: 'reordered', corruption: 'corrupted',
  'clock-skew': 'inconsistent', 'eventual-consistency': 'inconsistent', 'partial-apply': 'inconsistent', 'concurrent-change': 'inconsistent',
});

/** @param {string} kind */
export const interactionFailureOf = (kind) => EFFECT[kind] ?? 'degraded';

/** @param {string} a @param {string} b */
const byText = (a, b) => (a < b ? -1 : a > b ? 1 : 0);

/**
 * @typedef {{interaction: string, from: string, to: string, kind: string, via: 'direct'|'realisation', realisation?: string, reason: string}} Effect
 * @typedef {{id: string, kind: string, scope: string, target: string, targetKind: string, failure: string, locatedAt: string|null, effects: Effect[], reason?: string}} LiftedMode
 */

/**
 * Lift every failure mode of the model with a cut.
 * @param {Model} model
 * @param {{hierarchy: string, cut: string|null, map: Map<string, string>}} level the logical-hierarchy cut to lift to (an element maps to its block)
 */
export function liftFaults(model, level) {
  const logical = /** @type {import('./query.js').Hierarchy} */ (hierarchyOf(model, LOGICAL));
  const rels = new Map((model.byKind.relationship ?? []).map((r) => [r.id, r]));
  const ends = (/** @type {Entity} */ r) => ({ from: endpointElement(model, r.data.from)?.element ?? null, to: endpointElement(model, r.data.to)?.element ?? null });
  const block = (/** @type {string} */ e) => level.map.get(e) ?? e;
  const realisations = checkRealisations(model).filter((r) => r.holds);
  // Relationships that realise another interaction are the realisers, not logical interactions.
  const hops = new Set(realisations.flatMap((r) => r.path));
  const inside = (/** @type {string} */ root, /** @type {string} */ x) => x === root || ancestorsIn(logical, x).includes(root);

  /** @type {LiftedMode[]} */
  const modes = [];
  for (const m of model.byKind.failureMode ?? []) {
    const target = typeof m.data.target === 'string' ? m.data.target : '';
    const t = model.entities.get(target);
    const failure = interactionFailureOf(String(m.data.kind));
    /** @type {Effect[]} */
    const effects = [];
    /** @param {Entity} r @param {Omit<Effect, 'interaction'|'from'|'to'|'kind'>} how */
    const add = (r, how) => {
      const e = ends(r);
      if (!e.from || !e.to) return;
      if (effects.some((x) => x.interaction === r.id)) return;
      effects.push({ interaction: r.id, from: e.from, to: e.to, kind: String(r.data.kind), ...how });
    };
    /** @type {string|null} */
    let locatedAt = null;
    /** @type {string|undefined} */
    let reason;
    if (t?.kind === 'relationship') {
      const e = ends(t);
      locatedAt = e.from;
      if (!hops.has(t.id)) add(t, { via: 'direct', reason: `the failure mode is located at the interaction` });
      for (const r of realisations) if (r.path.includes(t.id)) add(/** @type {Entity} */ (rels.get(/** @type {string} */ (r.interaction))), { via: 'realisation', realisation: r.id, reason: `"${t.id}" is hop ${r.path.indexOf(t.id) + 1} of the path of realisation "${r.id}"` });
    } else if (t?.kind === 'component') {
      locatedAt = t.id;
      for (const r of rels.values()) {
        if (hops.has(r.id)) continue;
        const e = ends(r);
        if (!e.from || !e.to) continue;
        if (inside(t.id, e.from) !== inside(t.id, e.to)) add(r, { via: 'direct', reason: `the interaction crosses the boundary of "${t.id}"` });
      }
      for (const r of realisations) {
        const h = hierarchyOf(model, r.hierarchy);
        if (!h) continue;
        const inH = (/** @type {string} */ x) => x === t.id || ancestorsIn(h, x).includes(t.id);
        const touched = r.path.map((id) => ends(/** @type {Entity} */ (rels.get(id)))).filter((e) => (e.from && inH(e.from)) || (e.to && inH(e.to)));
        if (touched.length) add(/** @type {Entity} */ (rels.get(/** @type {string} */ (r.interaction))), { via: 'realisation', realisation: r.id, reason: `the path of realisation "${r.id}" runs through "${t.id}" in hierarchy "${r.hierarchy}"` });
      }
    } else {
      reason = t?.kind === 'environment' ? 'a failure mode of an environment is not located at an element or an interaction, so it lifts to none' : `the target "${target}" is not an element, an interaction or an environment`;
    }
    effects.sort((a, b) => byText(a.interaction, b.interaction));
    modes.push({ id: m.id, kind: String(m.data.kind), scope: String(m.data.scope ?? ''), target, targetKind: t?.kind ?? 'unknown', failure, locatedAt: locatedAt ? block(locatedAt) : null, effects, ...(reason ? { reason } : {}) });
  }
  modes.sort((a, b) => byText(a.id, b.id));

  // The lifted view: the interaction failures per derived interaction of the cut, and the internal ones per block.
  /** @type {Map<string, {key: string, from: string, to: string, kind: string, failures: {mode: string, failure: string, interactions: string[]}[]}>} */
  const lifted = new Map();
  /** @type {Map<string, {block: string, failures: {mode: string, failure: string, interactions: string[]}[]}>} */
  const internal = new Map();
  for (const m of modes) {
    /** @type {Map<string, string[]>} */
    const perKey = new Map();
    for (const e of m.effects) {
      const a = block(e.from);
      const b = block(e.to);
      if (a === b) {
        const g = internal.get(a) ?? { block: a, failures: [] };
        let f = g.failures.find((x) => x.mode === m.id);
        if (!f) g.failures.push((f = { mode: m.id, failure: m.failure, interactions: [] }));
        f.interactions.push(e.interaction);
        internal.set(a, g);
      } else {
        const key = interactionKey(a, b, e.kind);
        if (!lifted.has(key)) lifted.set(key, { key, from: a, to: b, kind: e.kind, failures: [] });
        const list = perKey.get(key) ?? [];
        list.push(e.interaction);
        perKey.set(key, list);
      }
    }
    for (const [key, interactions] of perKey) /** @type {any} */ (lifted.get(key)).failures.push({ mode: m.id, failure: m.failure, interactions: interactions.sort() });
  }
  return {
    hierarchy: level.hierarchy,
    cut: level.cut,
    modes,
    lifted: [...lifted.values()].sort((a, b) => byText(a.key, b.key)),
    internal: [...internal.values()].sort((a, b) => byText(a.block, b.block)),
    unlifted: modes.filter((m) => m.effects.length === 0).map((m) => ({ mode: m.id, reason: m.reason ?? 'no interaction of the model is affected' })),
  };
}
