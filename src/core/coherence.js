// Structure-behaviour coherence (V5) and contract conformance at boundaries (V7), multiscale M6.
//
// Message interactions are derived from behaviours alone: an event emitted by a behaviour whose subject is
// element X and consumed by a behaviour whose subject is a different element Y is a message from X to Y
// (`messageInteractions`). That derivation takes no event owner or interface, so it is the one place later
// checks (event interfaces, M7 decomposition validity) ask what messages a model's behaviours exchange.
//
// V5 asks that every such message is witnessed by a structural interaction of message class between the same
// two elements, at the base and at every cut:
//   - at the base, a relationship (declared, extracted or observed) of a message kind between X and Y, in
//     either direction (a response runs against an invocation), or a connector-mediated pair X to Y;
//   - at a cut, where X and Y fall in different blocks, the lifted message A to B needs a derived interaction
//     of message class between A and B whose base witnesses include such a relationship between X and Y
//     itself. A coarse edge that exists only over a different witness is reported (`different-witness`): it
//     is coarse agreement without structural agreement, never a pass.
// V7 asks that a boundary interaction that declares a contract has the events crossing it typed by that
// contract; an untyped hop is reported (`untyped`), as is a hop where no behaviour exchanges an event
// (`unmodelled`).
//
// Pure functions of a model: no engine, no simulation, no view state.

import { componentsFor } from './query.js';
import { baseFacts, deriveModel, declaredLevels, levelOf, blockAt, contractPaths } from './abstraction.js';
import { mediatedInteractions, kindInfo, effectiveKind } from './interactions.js';

/** @typedef {import('./types.js').Model} Model */

const byText = (/** @type {string} */ a, /** @type {string} */ b) => (a < b ? -1 : a > b ? 1 : 0);

/** @type {WeakMap<object, any>} */
const memo = new WeakMap();

/** The event an effect emits, or undefined. @param {any} fx */
const emittedBy = (fx) => (fx && typeof fx === 'object' ? (typeof fx.emit === 'string' ? fx.emit : typeof fx.then === 'string' ? fx.then : typeof fx.refused === 'string' ? fx.refused : undefined) : undefined);

/**
 * Every cross-element message the behaviours exchange: one per (event, emitting behaviour, consuming behaviour)
 * whose subjects are different elements. Sorted by event, then behaviours. A behaviour with no subject element
 * takes part in none.
 * @param {Model} model
 * @returns {{event: string, emitter: string, consumer: string, from: string, to: string}[]}
 */
export function messageInteractions(model) {
  const hit = memo.get(model)?.messages;
  if (hit) return hit;
  /** @type {Map<string, Set<string>>} */
  const emits = new Map(), consumes = new Map();
  const add = (/** @type {Map<string, Set<string>>} */ m, /** @type {string} */ event, /** @type {string} */ b) => { if (!m.has(event)) m.set(event, new Set()); /** @type {Set<string>} */ (m.get(event)).add(b); };
  for (const t of model.byKind.transition ?? []) {
    const b = t.owner ? model.entities.get(t.owner) : undefined;
    if (!b || b.kind !== 'behavior' || !componentsFor(model, b.id)[0]) continue;
    if (typeof t.data.on === 'string') add(consumes, t.data.on, b.id);
    for (const fx of Array.isArray(t.data.effects) ? t.data.effects : []) { const e = emittedBy(fx); if (e) add(emits, e, b.id); }
  }
  /** @type {{event: string, emitter: string, consumer: string, from: string, to: string}[]} */
  const out = [];
  for (const [event, emitters] of emits) {
    for (const emitter of emitters) for (const consumer of consumes.get(event) ?? []) {
      const from = componentsFor(model, emitter)[0], to = componentsFor(model, consumer)[0];
      if (from !== to) out.push({ event, emitter, consumer, from, to });
    }
  }
  out.sort((a, b) => byText(a.event, b.event) || byText(a.emitter, b.emitter) || byText(a.consumer, b.consumer));
  memo.set(model, { ...memo.get(model), messages: out });
  return out;
}

/**
 * Whether a relationship kind is of message class: a kind whose taxonomy says control or data moves along it
 * (a direction other than `none` for either), whatever its dependency class. Invocation, notification, data
 * flow, reads, writes, observation and lifecycle composition move something; imports and plain dependencies
 * (direction none, control and data) do not. A legacy kind counts as the kind that replaces it.
 * @param {any} meta @param {string} kind
 */
export function isMessageKind(meta, kind) {
  const { direction } = kindInfo(meta, effectiveKind(meta, kind));
  return direction.control !== 'none' || direction.data !== 'none';
}

/** The pair key of two elements, orientation-free. @param {string} a @param {string} b */
const pairKey = (a, b) => (a < b ? `${a}|${b}` : `${b}|${a}`);

/**
 * The structural witnesses of messages between two elements at the base: relationships of message class
 * between them (either direction) and connector-mediated pairs (their two relationships).
 * @param {Model} model
 * @returns {Map<string, string[]>} witness ids by element pair
 */
function baseWitnesses(model) {
  const hit = memo.get(model)?.witnesses;
  if (hit) return hit;
  /** @type {Map<string, Set<string>>} */
  const by = new Map();
  const put = (/** @type {string} */ a, /** @type {string} */ b, /** @type {string[]} */ ids) => { const k = pairKey(a, b); if (!by.has(k)) by.set(k, new Set()); for (const i of ids) /** @type {Set<string>} */ (by.get(k)).add(i); };
  for (const f of baseFacts(model).facts) if (isMessageKind(model.meta, f.kind) && f.from !== f.to) put(f.from, f.to, [f.id]);
  for (const m of mediatedInteractions(model)) put(m.from, m.to, m.via);
  const out = new Map([...by].map(([k, s]) => [k, [...s].sort(byText)]));
  memo.set(model, { ...memo.get(model), witnesses: out });
  return out;
}

/**
 * The relationships of each connector-mediated pair of elements, orientation-free: the publishes and the subscribes
 * that contract to a notification between them.
 * @param {Model} model
 * @returns {Map<string, string[][]>}
 */
function mediated(model) {
  const hit = memo.get(model)?.mediated;
  if (hit) return hit;
  /** @type {Map<string, string[][]>} */
  const out = new Map();
  for (const m of mediatedInteractions(model)) {
    const k = pairKey(m.from, m.to);
    if (!out.has(k)) out.set(k, []);
    /** @type {string[][]} */ (out.get(k)).push([...m.via]);
  }
  memo.set(model, { ...memo.get(model), mediated: out });
  return out;
}

/**
 * @typedef {Object} CoherenceFinding
 * @property {string} event the event that crosses
 * @property {string} emitter the emitting behaviour
 * @property {string} consumer the consuming behaviour
 * @property {string} from the emitting element
 * @property {string} to the consuming element
 * @property {string} cut `base` or the cut / hierarchy the finding is at
 * @property {string|null} fromBlock the block of the emitting element at the cut
 * @property {string|null} toBlock the block of the consuming element at the cut
 * @property {'unwitnessed'|'different-witness'} status `unwitnessed`: no structural witness (at a cut, no
 *   coarse interaction either); `different-witness`: a coarse interaction of message class joins the two blocks
 *   but none of its witnesses joins the two elements
 * @property {string[]} coarseWitnesses at a cut with status `different-witness`, the base relationships that
 *   make the coarse interaction
 * @property {string} message
 */

/**
 * V5 at one cut: the messages that cross it and are not structurally witnessed between their own elements.
 * `ref` is `null` for the base (every element its own block), a declared cut id, or a level reference.
 * @param {Model} model @param {Parameters<typeof levelOf>[1]|null} ref
 * @returns {{cut: string, hierarchy: string, messages: number, internal: number, unplaced: number, findings: CoherenceFinding[]}}
 */
export function checkCoherence(model, ref) {
  const witnesses = baseWitnesses(model);
  const messages = messageInteractions(model);
  /** @type {CoherenceFinding[]} */
  const findings = [];
  const label = ref === null ? 'base' : typeof ref === 'string' ? ref : (ref.cut ?? ref.hierarchy ?? 'logical');
  if (ref === null) {
    for (const m of messages) {
      if (witnesses.has(pairKey(m.from, m.to))) continue;
      findings.push({ ...m, cut: 'base', fromBlock: m.from, toBlock: m.to, status: 'unwitnessed', coarseWitnesses: [],
        message: `Event "${m.event}" is emitted by behavior "${m.emitter}" of "${m.from}" and consumed by behavior "${m.consumer}" of "${m.to}", and no relationship of message class joins "${m.from}" and "${m.to}".` });
    }
    return { cut: 'base', hierarchy: 'logical', messages: messages.length, internal: 0, unplaced: 0, findings };
  }
  const level = levelOf(model, ref);
  if (!level) return { cut: label, hierarchy: '', messages: messages.length, internal: 0, unplaced: messages.length, findings };
  return coherenceAtLevel(model, level, deriveModel(model, ref), label);
}

/**
 * V5 at a level the caller holds with its derived model: a declared cut or hierarchy (checkCoherence), or the level of
 * a candidate decomposition (src/core/decomposition.js), whose hierarchy no model declares.
 * @param {Model} model @param {NonNullable<ReturnType<typeof levelOf>>} level @param {ReturnType<typeof deriveModel>} d @param {string} label
 * @returns {{cut: string, hierarchy: string, messages: number, internal: number, unplaced: number, findings: CoherenceFinding[]}}
 */
export function coherenceAtLevel(model, level, d, label) {
  const witnesses = baseWitnesses(model);
  const messages = messageInteractions(model);
  /** @type {CoherenceFinding[]} */
  const findings = [];
  let internal = 0, unplaced = 0;
  for (const m of messages) {
    const a = blockAt(level, m.from), b = blockAt(level, m.to);
    if (a === null || b === null) { unplaced++; continue; }
    if (a === b) { internal++; continue; }
    const own = witnesses.get(pairKey(m.from, m.to)) ?? [];
    // A message that travels through a declared connector (publishes then subscribes) is witnessed by that path: both its
    // relationships lift to derived interactions at this level, so the path contracts there as it does at the base.
    const lifted = new Set(d ? d.interactions.flatMap((i) => i.witnesses) : []);
    if (mediated(model).get(pairKey(m.from, m.to))?.some((via) => via.every((w) => lifted.has(w)))) continue;
    const coarse = d ? d.interactions.filter((i) => ((i.from === a && i.to === b) || (i.from === b && i.to === a)) && isMessageKind(model.meta, i.kind)) : [];
    // The message is witnessed when a coarse interaction between the blocks is made by a relationship between
    // the two elements themselves.
    if (own.length && coarse.some((i) => i.witnesses.some((w) => own.includes(w)))) continue;
    const over = [...new Set(coarse.flatMap((i) => i.witnesses))].sort(byText);
    findings.push({ ...m, cut: label, fromBlock: a, toBlock: b, status: over.length ? 'different-witness' : 'unwitnessed', coarseWitnesses: over,
      message: over.length
        ? `Event "${m.event}" (behavior "${m.emitter}" of "${m.from}" to behavior "${m.consumer}" of "${m.to}") crosses from block "${a}" to block "${b}" at cut "${label}", where an interaction exists only over a different witness (${over.join(', ')}): no relationship joins "${m.from}" and "${m.to}" themselves.`
        : `Event "${m.event}" (behavior "${m.emitter}" of "${m.from}" to behavior "${m.consumer}" of "${m.to}") crosses from block "${a}" to block "${b}" at cut "${label}", and no interaction of message class joins them.` });
  }
  return { cut: label, hierarchy: level.hierarchy, messages: messages.length, internal, unplaced, findings };
}

/**
 * V5 at the base and at every declared cut and hierarchy. `ok` is true when nothing is reported anywhere.
 * `unwitnessed` lists each distinct message once, with the levels that report it.
 * @param {Model} model
 */
export function coherenceReport(model) {
  const { hierarchies, cuts } = declaredLevels(model);
  const levels = [
    checkCoherence(model, null),
    ...hierarchies.map((h) => ({ ...checkCoherence(model, { hierarchy: h, finest: true }), cut: `${h} (finest)` })),
    ...cuts.map((c) => checkCoherence(model, c)),
  ];
  /** @type {Map<string, {event: string, emitter: string, consumer: string, from: string, to: string, cuts: {cut: string, status: string, coarseWitnesses: string[]}[]}>} */
  const pairs = new Map();
  for (const l of levels) for (const f of l.findings) {
    const k = `${f.event}|${f.emitter}|${f.consumer}`;
    if (!pairs.has(k)) pairs.set(k, { event: f.event, emitter: f.emitter, consumer: f.consumer, from: f.from, to: f.to, cuts: [] });
    /** @type {any} */ (pairs.get(k)).cuts.push({ cut: l.cut, status: f.status, coarseWitnesses: f.coarseWitnesses });
  }
  const unwitnessed = [...pairs.values()].sort((a, b) => byText(a.event, b.event) || byText(a.emitter, b.emitter) || byText(a.consumer, b.consumer));
  return { ok: unwitnessed.length === 0, messages: messageInteractions(model).length, levels, unwitnessed };
}

/**
 * @typedef {Object} ContractFinding
 * @property {string} contract
 * @property {string} relationship the boundary interaction that declares the contract
 * @property {string} from @property {string} to
 * @property {'untyped'|'unmodelled'} status `untyped`: events pass between the two elements and none belongs
 *   to the contract; `unmodelled`: no behaviour exchanges an event between them
 * @property {string[]} events the events that pass
 * @property {string} message
 */

/**
 * V7: every relationship that declares a contract has the events that cross it typed by that contract. The hops
 * come from `contractPaths` (the chains of relationships typed by a contract, with the events each carries).
 * `findings` are the untyped hops; a hop no behaviour exchanges events over crosses nothing, so it is listed in
 * `unmodelled` and does not fail the check.
 * @param {Model} model
 * @returns {{ok: boolean, hops: number, findings: ContractFinding[], unmodelled: ContractFinding[]}}
 */
export function checkContractConformance(model) {
  /** @type {ContractFinding[]} */
  const findings = [], unmodelled = [];
  let hops = 0;
  const seen = new Set();
  for (const { contract, paths } of contractPaths(model)) for (const p of paths) for (const h of p.hops) {
    if (seen.has(h.relationship)) continue;
    seen.add(h.relationship);
    hops++;
    if (h.status === 'typed') continue;
    const status = /** @type {'untyped'|'unmodelled'} */ (h.status);
    (status === 'untyped' ? findings : unmodelled).push({ contract, relationship: h.relationship, from: h.from, to: h.to, status, events: h.events,
      message: status === 'untyped'
        ? `Relationship "${h.relationship}" (${h.from} to ${h.to}) declares contract "${contract}", but the events that pass between them (${h.events.join(', ')}) are not typed by it.`
        : `Relationship "${h.relationship}" (${h.from} to ${h.to}) declares contract "${contract}", but no behavior exchanges an event between them, so nothing shows the contract is followed.` });
  }
  const order = (/** @type {ContractFinding} */ a, /** @type {ContractFinding} */ b) => byText(a.contract, b.contract) || byText(a.relationship, b.relationship);
  findings.sort(order); unmodelled.sort(order);
  return { ok: findings.length === 0, hops, findings, unmodelled };
}
