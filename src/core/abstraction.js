// The semantic abstraction engine (WG-5694; docs/assessment/2026-11-27/multiscale.md, sections 2.3, 3.2, 3.3,
// 3.7, 3.8 and 3.10). Given a hierarchy, a cut of it and optionally a kind coarsening, it derives the
// architectural model at that cut from the authoritative fact base (the relationships):
//
//   blocks         the cut's blocks, plus an implicit block for each element strictly above the cut that a fact
//                  is attached to (a composite's own facts belong to it as an implicit member, audit Q4);
//   interactions   for each pair of distinct blocks and each (coarsened) kind, the lifted interaction with its
//                  complete witness set (relationship ids, sorted) and its summary;
//   fibres         the relationships internal to each block;
//   boundaries     the relationships with exactly one end in each block, split out / in;
//   interfaces     each block's derived interface (its boundary grouped by direction, kind and contract), the
//                  declared ports it is compared with, and how they match;
//   connectors     producer to consumer contractions through declared connector elements;
//   contracts      the realisation path of every contract used by relationships, hop by hop;
//   realisations   the declared realisation maps between hierarchies, each checked as a fact;
//   diagnostics    every way the abstraction is invalid (V1 partition, V2 witnessed facts, V3 interface agreement,
//                  V4 kind preservation), every incompatible port connection and every broken realisation map.
//
// Everything is a pure function of the model and the cut: no collapse state, viewport or layout reaches it, and
// the result is memoised per model snapshot and cut. Outputs are ordered canonically (by id), so they do not
// depend on the order declarations happen to have in the file.
//
// The lifting rule. The rule P3 (lift functoriality) refers to is `lift` below, and its summaries are the
// monoid `emptySummary` / `factSummary` / `combineSummaries`. It is the existential quotient of audit 2.3:
//
//   interaction(X, Y, k) with witnesses W  <=>  W = { r : alpha'(from r) = X, alpha'(to r) = Y, coarsen(kind r) = k }
//                                              and X != Y and W non-empty
//   fibre(X) = { r : alpha'(from r) = alpha'(to r) = X }
//
// where alpha' sends an element to its ancestor-or-self on the cut, or to itself when the cut opens it. It is not
// written in the integrity-rule language (src/core/integrity.js) because that language ranges over entities only
// (module elements, blocks and implicit blocks are not entities), its relations store no witnesses, and a
// relation's tuples are not summarised; the function is kept small so it reads as the rule above, and the
// property tests (tests/core/abstraction.test.js) check it against the invariants I1-I7 of WG-5694.

import { own } from './own.js';
import { kindInfo, refines, kindAncestors, provenanceOf, mediatedInteractions, ROOT_KIND } from './interactions.js';
import { LOGICAL, hierarchyOf, hierarchyIds, cutMap, cutBlocksOf, abstractionOf, ancestorsIn, elementsOf, knowledgeOf, componentsFor } from './query.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./query.js').Hierarchy} Hierarchy */

/**
 * One relationship as a base fact: its endpoints resolved to elements (a port to its owner, the port kept).
 * @typedef {{id: string, index: number, kind: string, from: string, to: string, fromPort: string|null, toPort: string|null,
 *   contract: string|null, carries: string[], provenance: string}} BaseFact
 * @typedef {{count: number, kinds: Record<string, number>, contracts: string[], carries: string[], delivery: string[],
 *   provenance: Record<string, number>, ports: string[]}} Summary
 * @typedef {{hierarchy: string, cut: string|null, blocks: string[], expanded: string[], problems: import('./query.js').HierarchyProblem[],
 *   map: Map<string, string>, h: Hierarchy}} Level
 * @typedef {{key: string, from: string, to: string, kind: string, class: string, lifted: boolean, witnesses: string[], summary: Summary,
 *   footprint: Footprint}} Interaction
 * @typedef {{witnesses?: string[], reads?: string[], query: {from?: string, to?: string, kind?: string, internalTo?: string, boundaryOf?: string}}} Footprint
 * @typedef {{code: string, condition: string, severity: 'error'|'warning'|'info', message: string, element?: string, relationship?: string,
 *   port?: string, entities: string[]}} AbstractionDiagnostic
 * @typedef {{direction: 'out'|'in', kind: string, contract: string|null, witnesses: string[], events: string[], ports: string[]}} InterfaceGroup
 */

// ---------------------------------------------------------------------------------------------
// Memoisation per model snapshot (models are immutable)

/** @type {WeakMap<object, Map<string, any>>} */
const memo = new WeakMap();
/** @template T @param {Model} model @param {string} key @param {() => T} make @returns {T} */
function cached(model, key, make) {
  let m = memo.get(model);
  if (!m) { m = new Map(); memo.set(model, m); }
  if (!m.has(key)) m.set(key, make());
  return m.get(key);
}

const byText = (/** @type {string} */ a, /** @type {string} */ b) => (a < b ? -1 : a > b ? 1 : 0);
/** @param {Iterable<string>} xs */
const sortedUnique = (xs) => [...new Set(xs)].sort(byText);

// ---------------------------------------------------------------------------------------------
// The fact base

/**
 * The element a relationship endpoint stands for: a component itself, or the owner of a port (the port kept).
 * The one place a relationship endpoint is turned into an element.
 * @param {Model} model @param {any} id
 * @returns {{element: string, port: string|null}|null}
 */
export function endpointElement(model, id) {
  if (typeof id !== 'string') return null;
  const e = model.entities.get(id);
  if (!e) return elementsOf(model).get(id)?.kind === 'module' ? { element: id, port: null } : null;
  if (e.kind === 'component') return { element: e.id, port: null };
  if (e.kind === 'port' && e.owner && model.entities.get(e.owner)?.kind === 'component') return { element: e.owner, port: e.id };
  return null;
}

/**
 * The relationships of a model as base facts, in declaration order. A relationship whose endpoints are not
 * elements is left out and listed in `unresolved` (validation reports the reference itself).
 * @param {Model} model
 * @returns {{facts: BaseFact[], byId: Map<string, BaseFact>, unresolved: string[]}}
 */
export function baseFacts(model) {
  return cached(model, 'baseFacts', () => {
    /** @type {BaseFact[]} */
    const facts = [];
    /** @type {string[]} */
    const unresolved = [];
    (model.byKind.relationship ?? []).forEach((r, index) => {
      const f = endpointElement(model, r.data.from);
      const t = endpointElement(model, r.data.to);
      if (!f || !t || typeof r.data.kind !== 'string') { unresolved.push(r.id); return; }
      facts.push({
        id: r.id, index, kind: r.data.kind, from: f.element, to: t.element, fromPort: f.port, toPort: t.port,
        contract: typeof r.data.contract === 'string' ? r.data.contract : null,
        carries: Array.isArray(r.data.carries) ? sortedUnique(r.data.carries.filter((/** @type {any} */ x) => typeof x === 'string')) : [],
        provenance: provenanceOf(r),
      });
    });
    return { facts, byId: new Map(facts.map((f) => [f.id, f])), unresolved };
  });
}

// ---------------------------------------------------------------------------------------------
// Summaries: a commutative monoid, so that lifting through an intermediate cut gives the same summary (I5).

/** The identity of the summary monoid. @returns {Summary} */
export function emptySummary() {
  return { count: 0, kinds: {}, contracts: [], carries: [], delivery: [], provenance: {}, ports: [] };
}

/**
 * The summary of one fact: count 1, its kind, its contract, what it carries, the delivery guarantees of the events
 * it carries, its provenance, and the ports it ends at.
 * @param {Model} model @param {BaseFact} f @returns {Summary}
 */
export function factSummary(model, f) {
  /** @type {string[]} */
  const delivery = [];
  for (const c of f.carries) {
    const e = model.entities.get(c);
    if (e?.kind === 'event' && typeof e.data.delivery === 'string') delivery.push(e.data.delivery);
  }
  return {
    count: 1, kinds: { [f.kind]: 1 }, contracts: f.contract ? [f.contract] : [], carries: [...f.carries], delivery: sortedUnique(delivery),
    provenance: { [f.provenance]: 1 }, ports: sortedUnique([f.fromPort, f.toPort].filter((/** @type {any} */ p) => typeof p === 'string')),
  };
}

/**
 * The monoid operation: counts add, sets unite (contracts, carried data, delivery guarantees, ports; the
 * delivery set is the join in the powerset lattice of guarantees), and the kind and provenance mixes add pointwise.
 * Associative and commutative, with emptySummary as identity.
 * @param {Summary} a @param {Summary} b @returns {Summary}
 */
export function combineSummaries(a, b) {
  /** @param {Record<string, number>} x @param {Record<string, number>} y */
  const add = (x, y) => {
    /** @type {Record<string, number>} */
    const out = {};
    for (const k of sortedUnique([...Object.keys(x), ...Object.keys(y)])) out[k] = (x[k] ?? 0) + (y[k] ?? 0);
    return out;
  };
  return {
    count: a.count + b.count, kinds: add(a.kinds, b.kinds), contracts: sortedUnique([...a.contracts, ...b.contracts]),
    carries: sortedUnique([...a.carries, ...b.carries]), delivery: sortedUnique([...a.delivery, ...b.delivery]),
    provenance: add(a.provenance, b.provenance), ports: sortedUnique([...a.ports, ...b.ports]),
  };
}

/** The summary of a witness set. @param {Model} model @param {Iterable<string>} witnesses @returns {Summary} */
export function summarise(model, witnesses) {
  const { byId } = baseFacts(model);
  let s = emptySummary();
  for (const w of witnesses) {
    const f = byId.get(w);
    if (f) s = combineSummaries(s, factSummary(model, f));
  }
  return s;
}

// ---------------------------------------------------------------------------------------------
// Kind coarsening

/**
 * The coarsening a derivation applies to kinds: null (kinds lift unchanged), a list of target kinds (each kind
 * becomes its nearest ancestor-or-self in the list), or 'all' (each kind becomes its nearest ancestor-or-self
 * whose parent is the root of the kind tree).
 * @param {any} meta @param {string[]|'all'|null|undefined} coarsen
 * @returns {(kind: string) => string}
 */
export function kindCoarsening(meta, coarsen) {
  if (!coarsen) return (k) => k;
  if (coarsen === 'all') {
    return (k) => {
      for (const a of [k, ...kindAncestors(meta, k)]) if (a === ROOT_KIND || kindInfo(meta, a).parent === ROOT_KIND) return a;
      return k;
    };
  }
  const targets = new Set(coarsen);
  return (k) => {
    for (const a of [k, ...kindAncestors(meta, k)]) if (targets.has(a)) return a;
    return k;
  };
}

// ---------------------------------------------------------------------------------------------
// Levels: a hierarchy and a cut of it

/**
 * A level: a declared cut (its id, or {cut}), or an ad hoc cut of a hierarchy given by {hierarchy, blocks} or
 * {hierarchy, expand, depth, finest}. null when the cut or the hierarchy is unknown.
 * @param {Model} model @param {string|{cut?: string, hierarchy?: string, blocks?: string[], expand?: string[], depth?: number, finest?: boolean}} ref
 * @returns {Level|null}
 */
export function levelOf(model, ref) {
  const r = typeof ref === 'string' ? { cut: ref } : ref;
  if (typeof r.cut === 'string') {
    const m = cutMap(model, r.cut);
    if (!m) return null;
    return { hierarchy: m.hierarchy, cut: m.cut, blocks: m.blocks, expanded: m.expanded, problems: m.problems, map: m.map, h: /** @type {Hierarchy} */ (hierarchyOf(model, m.hierarchy)) };
  }
  const hid = r.hierarchy ?? LOGICAL;
  const h = hierarchyOf(model, hid);
  if (!h) return null;
  const spec = Array.isArray(r.blocks) ? { blocks: r.blocks } : { expand: r.expand ?? [], depth: r.depth, finest: r.finest === true };
  const b = cutBlocksOf(h, spec);
  return { hierarchy: hid, cut: null, blocks: b.blocks, expanded: b.expanded, problems: b.problems, map: abstractionOf(h, b.blocks), h };
}

/**
 * alpha': the block of an element at a level. An element at or below the cut goes to its ancestor-or-self on it;
 * an element the cut opens is its own (implicit) block; anything else is null.
 * @param {Level} level @param {string} e @returns {string|null}
 */
export function blockAt(level, e) {
  const b = level.map.get(e);
  if (b !== undefined) return b;
  return level.h.depth.has(e) ? e : null;
}

/**
 * The cut of the logical hierarchy a structural picture with a collapse set draws: every element with members
 * other than module elements is opened unless it is a collapsed subsystem (an element of kind subsystem that the
 * set names and `visible` admits), and components whose only members are module elements stay closed.
 * A collapsed subsystem inside another collapsed one is not reached.
 * @param {Model} model @param {Set<string>} collapsed @param {(id: string) => boolean} [visible]
 * @returns {{hierarchy: string, blocks: string[]}}
 */
export function cutForCollapse(model, collapsed, visible = () => true) {
  const h = /** @type {Hierarchy} */ (hierarchyOf(model, LOGICAL));
  const elements = elementsOf(model);
  const hasNonModuleMembers = (/** @type {string} */ e) => (h.children.get(e) ?? []).some((c) => elements.get(c)?.kind !== 'module');
  /** @type {string[]} */
  const blocks = [];
  const walk = (/** @type {string} */ e) => {
    const isCollapsed = collapsed.has(e) && visible(e) && elements.get(e)?.kind === 'subsystem';
    if (hasNonModuleMembers(e) && !isCollapsed) { for (const c of /** @type {string[]} */ (h.children.get(e))) walk(c); }
    else blocks.push(e);
  };
  for (const r of h.roots) walk(r);
  return { hierarchy: LOGICAL, blocks };
}

// ---------------------------------------------------------------------------------------------
// Navigation: a cut given by the elements it expands (WG-5695)
//
// A view's interaction state names a hierarchy and the elements the viewer has expanded. The cut it denotes opens
// an element exactly when it is expanded, has members, and every ancestor of it is open: the walk from the roots
// below. Expanding or collapsing one element therefore changes only the blocks inside it, and an expansion under a
// collapsed ancestor is remembered without effect. These functions only choose cuts; what is derived at a cut is
// deriveModel's.

/**
 * The cut a set of expanded elements denotes in a hierarchy: its blocks and the elements it actually opens, both in
 * hierarchy order. null when the hierarchy is unknown.
 * @param {Model} model @param {string} hierarchy @param {Iterable<string>} expanded
 * @returns {{hierarchy: string, blocks: string[], expanded: string[]}|null}
 */
export function cutOfExpanded(model, hierarchy, expanded) {
  const h = hierarchyOf(model, hierarchy);
  if (!h) return null;
  const open = new Set(expanded);
  /** @type {string[]} */
  const blocks = [];
  /** @type {string[]} */
  const opened = [];
  const walk = (/** @type {string} */ e) => {
    const kids = h.children.get(e) ?? [];
    if (open.has(e) && kids.length) { opened.push(e); for (const c of kids) walk(c); }
    else blocks.push(e);
  };
  for (const r of h.roots) walk(r);
  const pos = new Map(h.order.map((e, i) => [e, i]));
  const byOrder = (/** @type {string} */ a, /** @type {string} */ b) => /** @type {number} */ (pos.get(a)) - /** @type {number} */ (pos.get(b));
  return { hierarchy, blocks: blocks.sort(byOrder), expanded: opened.sort(byOrder) };
}

/**
 * The expanded set after the viewer expands or collapses one element: an opened element is collapsed (only it
 * leaves the set, so expanding it again restores what was open inside); a block with members is expanded; an
 * element hidden inside a block is revealed by expanding its ancestors down to it. Anything else changes nothing.
 * @param {Model} model @param {string} hierarchy @param {Iterable<string>} expanded @param {string} id
 * @returns {string[]}
 */
export function toggleExpanded(model, hierarchy, expanded, id) {
  const h = hierarchyOf(model, hierarchy);
  const set = new Set(expanded);
  const cut = cutOfExpanded(model, hierarchy, set);
  if (!h || !cut || !h.depth.has(id)) return [...set];
  if (cut.expanded.includes(id)) set.delete(id);
  else if (cut.blocks.includes(id)) { if ((h.children.get(id) ?? []).length) set.add(id); }
  else for (const a of ancestorsIn(h, id)) set.add(a);
  const pos = new Map(h.order.map((e, i) => [e, i]));
  return [...set].filter((e) => pos.has(e)).sort((a, b) => /** @type {number} */ (pos.get(a)) - /** @type {number} */ (pos.get(b)));
}

/**
 * The expanded set that denotes a declared cut: the elements it opens.
 * @param {Model} model @param {string} cutId @returns {{hierarchy: string, expanded: string[]}|null}
 */
export function expandedOfCut(model, cutId) {
  const m = cutMap(model, cutId);
  return m ? { hierarchy: m.hierarchy, expanded: [...m.expanded] } : null;
}

/**
 * The declared cut of a hierarchy whose blocks are exactly these, or null: what names an interactive cut.
 * @param {Model} model @param {string} hierarchy @param {string[]} blocks
 */
export function declaredCutWithBlocks(model, hierarchy, blocks) {
  const key = [...blocks].sort(byText).join('\u0001');
  for (const c of model.byKind.cut ?? []) {
    const m = cutMap(model, c.id);
    if (m && m.hierarchy === hierarchy && !m.problems.length && [...m.blocks].sort(byText).join('\u0001') === key) return c.id;
  }
  return null;
}

/**
 * Derived path summaries through removed blocks (docs/assessment/2026-11-27/multiscale.md, section 2.5): when a
 * filter or the viewer removes blocks, each pair of kept blocks (A, C) that the derived interactions connect through
 * removed blocks only becomes one summary: the removed blocks on such paths (`via`) and every witness of the
 * interactions along them. Interactions are first restricted to the facts `keep` admits. A connection lost to a
 * removal is therefore either summarised here or counted by the caller; it is never silently dropped.
 * @param {Model} model @param {DerivedModel} d @param {Set<string>} removed @param {(f: BaseFact) => boolean} [keep]
 * @returns {{from: string, to: string, via: string[], witnesses: string[], kinds: string[]}[]}
 */
export function pathSummaries(model, d, removed, keep = () => true) {
  /** @type {Map<string, {to: string, witnesses: string[], kind: string}[]>} */
  const out = new Map();
  /** @type {Map<string, {from: string, witnesses: string[], kind: string}[]>} */
  const inn = new Map();
  for (const i of d.interactions) {
    const r = restrictInteraction(model, i, keep);
    if (!r) continue;
    if (!out.has(i.from)) out.set(i.from, []);
    /** @type {any[]} */ (out.get(i.from)).push({ to: i.to, witnesses: r.witnesses, kind: i.kind });
    if (!inn.has(i.to)) inn.set(i.to, []);
    /** @type {any[]} */ (inn.get(i.to)).push({ from: i.from, witnesses: r.witnesses, kind: i.kind });
  }
  /** Removed blocks reachable from `start` through removed blocks only, following `adj`. */
  const reach = (/** @type {string[]} */ start, /** @type {(b: string) => string[]} */ adj) => {
    const seen = new Set(start);
    const stack = [...start];
    while (stack.length) for (const n of adj(/** @type {string} */ (stack.pop()))) if (removed.has(n) && !seen.has(n)) { seen.add(n); stack.push(n); }
    return seen;
  };
  const fwd = (/** @type {string} */ b) => (out.get(b) ?? []).map((x) => x.to);
  const bwd = (/** @type {string} */ b) => (inn.get(b) ?? []).map((x) => x.from);
  /** @type {{from: string, to: string, via: string[], witnesses: string[], kinds: string[]}[]} */
  const summaries = [];
  const kept = d.blocks.map((b) => b.id).filter((b) => !removed.has(b));
  for (const a of kept) {
    const first = fwd(a).filter((n) => removed.has(n));
    if (!first.length) continue;
    const R = reach(first, fwd);
    /** @type {Set<string>} */
    const targets = new Set();
    for (const r of R) for (const n of fwd(r)) if (!removed.has(n) && n !== a) targets.add(n);
    for (const c of [...targets].sort(byText)) {
      const B = reach(bwd(c).filter((n) => removed.has(n)), bwd);
      const via = [...R].filter((x) => B.has(x)).sort(byText);
      const viaSet = new Set(via);
      /** @type {string[]} */
      const ws = [];
      /** @type {Set<string>} */
      const kinds = new Set();
      for (const src of [a, ...via]) for (const e of out.get(src) ?? []) {
        if ((viaSet.has(e.to) && (src === a || viaSet.has(src))) || (e.to === c && viaSet.has(src))) { ws.push(...e.witnesses); kinds.add(e.kind); }
      }
      if (via.length && ws.length) summaries.push({ from: a, to: c, via, witnesses: sortedUnique(ws), kinds: [...kinds].sort(byText) });
    }
  }
  return summaries;
}

/**
 * What the inspector shows about an element as a block, at the current cut (made coarse enough that the element
 * is a block: an opened element is collapsed, an element inside a block revealed): its purpose and
 * responsibilities, knowledge status, boundary, derived interface, declared ports and how they agree, the
 * diagnostics about it, and whether it meets coherence condition 1 (a stated purpose).
 * @param {Model} model @param {string} hierarchy @param {Iterable<string>} expanded @param {string} id
 */
export function blockReport(model, hierarchy, expanded, id) {
  const h = hierarchyOf(model, hierarchy);
  const el = elementsOf(model).get(id);
  if (!h || !el || !h.depth.has(id)) return null;
  const cur = /** @type {NonNullable<ReturnType<typeof cutOfExpanded>>} */ (cutOfExpanded(model, hierarchy, expanded));
  const asBlock = new Set([...cur.expanded, ...ancestorsIn(h, id)]);
  asBlock.delete(id);
  const cut = /** @type {NonNullable<ReturnType<typeof cutOfExpanded>>} */ (cutOfExpanded(model, hierarchy, asBlock));
  const d = /** @type {DerivedModel} */ (deriveModel(model, { hierarchy, blocks: cut.blocks }));
  const data = el.entity?.data ?? {};
  const purpose = typeof data.purpose === 'string' && data.purpose ? data.purpose : el.kind === 'system' && typeof data.description === 'string' ? data.description : null;
  const responsibilities = Array.isArray(data.responsibilities) ? data.responsibilities.filter((/** @type {any} */ r) => typeof r === 'string') : [];
  const knowledge = knowledgeOf(model, id);
  const diagnostics = d.diagnostics.filter((x) => x.element === id || (x.condition === 'V3' && x.entities.includes(id)));
  const ports = d.interfaces[id]?.ports ?? [];
  const v3 = diagnostics.filter((x) => x.condition === 'V3');
  return {
    element: id, kind: el.kind, entity: el.entity?.id ?? null, owners: el.owners ?? [], path: el.path ?? null,
    purpose, responsibilities, knowledge,
    planned: el.entity?.kind === 'component' && data.implementation?.status === 'not-implemented',
    members: (h.children.get(id) ?? []).length,
    asBlockAt: { hierarchy, blocks: cut.blocks, current: cur.blocks.includes(id) },
    boundary: d.boundaries[id] ?? { out: [], in: [] },
    interface: d.interfaces[id] ?? { authority: 'derived', groups: [], ports: [] },
    agreement: !ports.length ? 'no-declared-interface' : v3.length ? 'disagrees' : 'agrees',
    diagnostics,
    coherence: { purpose: purpose !== null || el.kind === 'module', note: el.kind === 'module' ? 'A module element: its purpose is that of the component that declares it.' : purpose !== null ? 'A purpose is stated.' : 'No purpose is stated (coherence condition 1).' },
  };
}

/**
 * Coherence condition 1 at a derived model: the blocks of the cut (not implicit, not module elements) that state
 * no purpose. Conditions 2 to 4 are the diagnostics, the witness sets and the claims stated at the cut.
 * @param {Model} model @param {DerivedModel} d @returns {string[]}
 */
export function blocksWithoutPurpose(model, d) {
  const elements = elementsOf(model);
  return d.blocks.filter((b) => {
    if (b.implicit) return false;
    const el = elements.get(b.id);
    if (!el || el.kind === 'module') return false;
    const data = el.entity?.data ?? {};
    return !(typeof data.purpose === 'string' && data.purpose) && !(el.kind === 'system' && typeof data.description === 'string' && data.description);
  }).map((b) => b.id);
}

// ---------------------------------------------------------------------------------------------
// The lifting rule (P3)

/**
 * The existential lift of a fact set through an abstraction map (see the header): interactions keyed by
 * from, to and kind with their witness sets, and the fibre of every block. Facts with an endpoint the map does not
 * place are returned in `unplaced`. Witness sets are sorted by id. Pure: generated fact bases are lifted by it too.
 * @param {Iterable<{id: string, kind: string, from: string, to: string}>} facts
 * @param {(element: string) => string|null} alpha
 * @param {(kind: string) => string} kindOf
 * @returns {{interactions: Map<string, {from: string, to: string, kind: string, witnesses: string[]}>, fibres: Map<string, string[]>, unplaced: string[]}}
 */
export function lift(facts, alpha, kindOf) {
  /** @type {Map<string, {from: string, to: string, kind: string, witnesses: string[]}>} */
  const interactions = new Map();
  /** @type {Map<string, string[]>} */
  const fibres = new Map();
  /** @type {string[]} */
  const unplaced = [];
  for (const f of facts) {
    const x = alpha(f.from), y = alpha(f.to);
    if (x === null || y === null) { unplaced.push(f.id); continue; }
    if (x === y) { if (!fibres.has(x)) fibres.set(x, []); /** @type {string[]} */ (fibres.get(x)).push(f.id); continue; }
    const kind = kindOf(f.kind);
    const key = interactionKey(x, y, kind);
    let i = interactions.get(key);
    if (!i) { i = { from: x, to: y, kind, witnesses: [] }; interactions.set(key, i); }
    i.witnesses.push(f.id);
  }
  for (const i of interactions.values()) i.witnesses.sort(byText);
  for (const w of fibres.values()) w.sort(byText);
  return { interactions, fibres, unplaced: unplaced.sort(byText) };
}

/** The key of a lifted interaction. @param {string} from @param {string} to @param {string} kind */
export const interactionKey = (from, to, kind) => `${from}->${to}:${kind}`;

/**
 * Lift an already lifted model one level further (alpha_{C->C'}), optionally coarsening kinds again: interactions
 * whose blocks meet become part of that block's fibre, the rest unite witnesses and summaries. With the summary
 * monoid this equals lifting the base straight to C' (I5); the property tests check exactly that.
 * @param {{interactions: {from: string, to: string, kind: string, witnesses: string[], summary: Summary}[], fibres: Record<string, string[]>}} finer
 * @param {(block: string) => string|null} map @param {(kind: string) => string} [kindOf]
 */
export function relift(finer, map, kindOf = (k) => k) {
  /** @type {Map<string, {from: string, to: string, kind: string, witnesses: string[], summary: Summary}>} */
  const interactions = new Map();
  /** @type {Map<string, string[]>} */
  const fibres = new Map();
  const toFibre = (/** @type {string} */ b, /** @type {string[]} */ ws) => { if (!fibres.has(b)) fibres.set(b, []); /** @type {string[]} */ (fibres.get(b)).push(...ws); };
  for (const [b, ws] of Object.entries(finer.fibres)) { const t = map(b); if (t !== null && ws.length) toFibre(t, ws); }
  for (const i of finer.interactions) {
    const x = map(i.from), y = map(i.to);
    if (x === null || y === null) continue;
    if (x === y) { toFibre(x, i.witnesses); continue; }
    const kind = kindOf(i.kind);
    const key = interactionKey(x, y, kind);
    const cur = interactions.get(key);
    if (!cur) interactions.set(key, { from: x, to: y, kind, witnesses: [...i.witnesses], summary: i.summary });
    else { cur.witnesses.push(...i.witnesses); cur.summary = combineSummaries(cur.summary, i.summary); }
  }
  for (const i of interactions.values()) i.witnesses.sort(byText);
  /** @type {Record<string, string[]>} */
  const fib = {};
  for (const [b, ws] of [...fibres].sort((a, c) => byText(a[0], c[0]))) fib[b] = [...ws].sort(byText);
  return { interactions: [...interactions.entries()].sort((a, c) => byText(a[0], c[0])).map(([key, i]) => ({ key, ...i })), fibres: fib };
}

// ---------------------------------------------------------------------------------------------
// Interfaces

/**
 * The derived interface of a block: its boundary grouped by direction, kind and contract. A function of the
 * boundary alone (I4): the facts and which of them leave the block.
 * @param {Model} model @param {{out: string[], in: string[]}} boundary @param {(kind: string) => string} [kindOf]
 * @returns {InterfaceGroup[]}
 */
export function interfaceOf(model, boundary, kindOf = (k) => k) {
  const { byId } = baseFacts(model);
  /** @type {Map<string, InterfaceGroup>} */
  const groups = new Map();
  for (const direction of /** @type {const} */ (['out', 'in'])) {
    for (const id of boundary[direction]) {
      const f = byId.get(id);
      if (!f) continue;
      const kind = kindOf(f.kind);
      const key = `${direction}|${kind}|${f.contract ?? ''}`;
      let g = groups.get(key);
      if (!g) { g = { direction, kind, contract: f.contract, witnesses: [], events: [], ports: [] }; groups.set(key, g); }
      g.witnesses.push(f.id);
      for (const c of f.carries) if (model.entities.get(c)?.kind === 'event') g.events.push(c);
      const port = direction === 'out' ? f.fromPort : f.toPort;
      if (port) g.ports.push(port);
    }
  }
  return [...groups.entries()].sort((a, b) => byText(a[0], b[0])).map(([, g]) => ({ ...g, witnesses: sortedUnique(g.witnesses), events: sortedUnique(g.events), ports: sortedUnique(g.ports) }));
}

/** The id of an interface group. @param {InterfaceGroup} g */
export const groupId = (g) => `${g.direction}:${g.kind}:${g.contract ?? '-'}`;

/**
 * Whether a declared port matches an interface group: a relationship of the group ends at the port, or the port's
 * contract is the group's and its direction fits (requires: out, provides: in).
 * @param {Entity} port @param {InterfaceGroup} g
 */
export function portMatches(port, g) {
  if (g.ports.includes(port.id)) return true;
  const dir = port.data.direction === 'requires' ? 'out' : port.data.direction === 'provides' ? 'in' : null;
  return typeof port.data.contract === 'string' && port.data.contract === g.contract && dir === g.direction;
}

/** The declared ports of an element, in declaration order. @param {Model} model @param {string} element */
export function declaredPorts(model, element) {
  return (model.byKind.port ?? []).filter((p) => p.owner === element);
}

// ---------------------------------------------------------------------------------------------
// Port connections (validated on every transaction)

/**
 * Relationships that end at ports and connect incompatibly: the source end must be a requires port and the target
 * end a provides port (a dependency runs from what requires to what provides), and the contracts named by the
 * relationship and by its ports must agree.
 * @param {Model} model
 * @returns {{code: string, relationship: string, port: string, message: string, path: string[]}[]}
 */
export function portConnectionProblems(model) {
  return cached(model, 'portProblems', () => {
    /** @type {{code: string, relationship: string, port: string, message: string, path: string[]}[]} */
    const out = [];
    for (const r of model.byKind.relationship ?? []) {
      /** @type {(Entity|null)[]} */
      const ends = ['from', 'to'].map((side) => {
        const e = typeof r.data[side] === 'string' ? model.entities.get(r.data[side]) : undefined;
        return e && e.kind === 'port' ? e : null;
      });
      const [fp, tp] = ends;
      if (!fp && !tp) continue;
      if (fp && fp.data.direction !== 'requires') {
        out.push({ code: 'relationship.port-direction', relationship: r.id, port: fp.id, path: ['from'],
          message: `Relationship "${r.id}" starts at port "${fp.id}", which ${fp.data.direction} ${fp.data.contract ? `"${fp.data.contract}"` : 'its contract'}; a relationship starts at a requires port and ends at a provides port.` });
      }
      if (tp && tp.data.direction !== 'provides') {
        out.push({ code: 'relationship.port-direction', relationship: r.id, port: tp.id, path: ['to'],
          message: `Relationship "${r.id}" ends at port "${tp.id}", which ${tp.data.direction} ${tp.data.contract ? `"${tp.data.contract}"` : 'its contract'}${fp && fp.data.direction === tp.data.direction ? ` (a ${tp.data.direction}-to-${tp.data.direction} connection)` : ''}; a relationship ends at a provides port.` });
      }
      /** @type {string[]} */
      const named = [];
      if (typeof r.data.contract === 'string') named.push(r.data.contract);
      for (const p of ends) if (p && typeof p.data.contract === 'string') named.push(p.data.contract);
      if (new Set(named).size > 1) {
        const at = /** @type {Entity} */ (tp ?? fp);
        out.push({ code: 'relationship.port-contract', relationship: r.id, port: at.id, path: [tp ? 'to' : 'from'],
          message: `Relationship "${r.id}" connects contracts that differ: ${[...new Set(named)].map((c) => `"${c}"`).join(' and ')} (the relationship's contract and its ports' contracts must be the same).` });
      }
    }
    return out;
  });
}

// ---------------------------------------------------------------------------------------------
// Events exchanged between elements (for contract realisation)

/** The event an effect emits, or undefined. @param {any} fx */
const emittedBy = (fx) => (fx && typeof fx === 'object' ? (typeof fx.emit === 'string' ? fx.emit : typeof fx.then === 'string' ? fx.then : typeof fx.refused === 'string' ? fx.refused : undefined) : undefined);

/**
 * The events each component emits and consumes through the behaviors whose subject it is (or whose subject is one
 * of its ports).
 * @param {Model} model @returns {{emits: Map<string, Set<string>>, consumes: Map<string, Set<string>>}}
 */
export function eventExchange(model) {
  return cached(model, 'eventExchange', () => {
    /** @type {Map<string, Set<string>>} */
    const emits = new Map();
    /** @type {Map<string, Set<string>>} */
    const consumes = new Map();
    const add = (/** @type {Map<string, Set<string>>} */ m, /** @type {string} */ c, /** @type {string} */ e) => { if (!m.has(c)) m.set(c, new Set()); /** @type {Set<string>} */ (m.get(c)).add(e); };
    for (const t of model.byKind.transition ?? []) {
      const b = t.owner ? model.entities.get(t.owner) : undefined;
      if (!b || b.kind !== 'behavior') continue;
      const comp = componentsFor(model, b.id)[0];
      if (!comp) continue;
      if (typeof t.data.on === 'string') add(consumes, comp, t.data.on);
      for (const fx of Array.isArray(t.data.effects) ? t.data.effects : []) { const e = emittedBy(fx); if (e) add(emits, comp, e); }
    }
    return { emits, consumes };
  });
}

/**
 * The events that pass between two components in either direction: emitted by one's behaviors and consumed by the
 * other's.
 * @param {Model} model @param {string} a @param {string} b @returns {{forward: string[], backward: string[]}}
 */
export function eventsBetween(model, a, b) {
  const { emits, consumes } = eventExchange(model);
  const pass = (/** @type {string} */ x, /** @type {string} */ y) => [...(emits.get(x) ?? [])].filter((e) => consumes.get(y)?.has(e)).sort(byText);
  return { forward: pass(a, b), backward: pass(b, a) };
}

/**
 * The realisation path of every contract that relationships name (audit Q8): the chains of relationships typed by
 * the contract, from an element that no such relationship enters to one that no such relationship leaves. Each hop
 * lists the events that pass along it (from behaviors) and is flagged: `typed` when some of them belong to the
 * contract, `untyped` when events pass but none does, `unmodelled` when no behavior exchanges events there.
 * @param {Model} model
 */
export function contractPaths(model) {
  return cached(model, 'contractPaths', () => {
    const { facts } = baseFacts(model);
    /** @type {Map<string, BaseFact[]>} */
    const byContract = new Map();
    for (const f of facts) if (f.contract) { if (!byContract.has(f.contract)) byContract.set(f.contract, []); /** @type {BaseFact[]} */ (byContract.get(f.contract)).push(f); }
    /** @type {{contract: string, paths: {hops: {relationship: string, from: string, to: string, events: string[], contractEvents: string[], status: 'typed'|'untyped'|'unmodelled'}[], flagged: string[]}[]}[]} */
    const out = [];
    for (const c of [...byContract.keys()].sort(byText)) {
      const edges = /** @type {BaseFact[]} */ (byContract.get(c)).slice().sort((a, b) => byText(a.id, b.id));
      const contractEvents = new Set((model.byKind.event ?? []).filter((e) => e.data.contract === c).map((e) => e.id));
      const entered = new Set(edges.map((e) => e.to));
      const starts = sortedUnique(edges.map((e) => e.from).filter((x) => !entered.has(x)));
      const roots = starts.length ? starts : sortedUnique(edges.map((e) => e.from));
      /** @type {BaseFact[][]} */
      const chains = [];
      const walk = (/** @type {string} */ at, /** @type {BaseFact[]} */ sofar, /** @type {Set<string>} */ seen) => {
        const next = edges.filter((e) => e.from === at && !seen.has(e.to));
        if (!next.length) { if (sofar.length) chains.push(sofar); return; }
        for (const e of next) walk(e.to, [...sofar, e], new Set([...seen, e.to]));
      };
      for (const r of roots) walk(r, [], new Set([r]));
      const paths = chains.map((chain) => {
        const hops = chain.map((f) => {
          const { forward, backward } = eventsBetween(model, f.from, f.to);
          const events = sortedUnique([...forward, ...backward]);
          const typed = events.filter((e) => contractEvents.has(e));
          return { relationship: f.id, from: f.from, to: f.to, events, contractEvents: typed, status: /** @type {'typed'|'untyped'|'unmodelled'} */ (!events.length ? 'unmodelled' : typed.length ? 'typed' : 'untyped') };
        });
        return { hops, flagged: hops.filter((h) => h.status !== 'typed').map((h) => h.relationship) };
      });
      out.push({ contract: c, paths });
    }
    return out;
  });
}

// ---------------------------------------------------------------------------------------------
// Realisation maps between hierarchies (audit Q10)

/**
 * Every declared realisation map, checked: the logical interaction it realises (a relationship) is realised in the
 * named hierarchy by its path, a list of relationships that must exist, run head to tail, start at the placement of
 * the interaction's source in that hierarchy (an ancestor-or-self of it there) and end at the placement of its
 * target. `holds` is true exactly when nothing is wrong.
 * @param {Model} model
 * @returns {{id: string, interaction: string|null, hierarchy: string, path: string[], holds: boolean, problems: {code: string, message: string, path: (string|number)[]}[]}[]}
 */
export function checkRealisations(model) {
  return cached(model, 'realisations', () => {
    const out = [];
    for (const m of model.byKind.realisation ?? []) {
      /** @type {{code: string, message: string, path: (string|number)[]}[]} */
      const problems = [];
      const hid = typeof m.data.hierarchy === 'string' ? m.data.hierarchy : LOGICAL;
      const h = hierarchyOf(model, hid);
      const path = Array.isArray(m.data.path) ? m.data.path.filter((/** @type {any} */ x) => typeof x === 'string') : [];
      const rel = typeof m.data.interaction === 'string' ? model.entities.get(m.data.interaction) : undefined;
      const logical = rel && rel.kind === 'relationship' ? rel : null;
      if (!h) problems.push({ code: 'realisation.hierarchy', message: `Realisation "${m.id}" names hierarchy "${hid}", which the model does not have.`, path: ['hierarchy'] });
      if (!logical) problems.push({ code: 'realisation.interaction', message: `Realisation "${m.id}" realises ${JSON.stringify(m.data.interaction)}, which is not a relationship.`, path: ['interaction'] });
      if (!path.length) problems.push({ code: 'realisation.path-missing', message: `Realisation "${m.id}" gives no path; a realisation is a path of one or more relationships in its hierarchy.`, path: ['path'] });
      /** @type {{from: string, to: string}[]} */
      const hops = [];
      path.forEach((/** @type {string} */ id, /** @type {number} */ i) => {
        const r = model.entities.get(id);
        const f = r?.kind === 'relationship' ? endpointElement(model, r.data.from) : null;
        const t = r?.kind === 'relationship' ? endpointElement(model, r.data.to) : null;
        if (!r || r.kind !== 'relationship' || !f || !t) { problems.push({ code: 'realisation.path-missing', message: `Hop ${i + 1} of realisation "${m.id}", "${id}", is not a relationship of the model, so the path does not exist.`, path: ['path', i] }); return; }
        hops.push({ from: f.element, to: t.element });
      });
      if (h && logical && hops.length === path.length && path.length) {
        for (let i = 1; i < hops.length; i++) {
          if (hops[i - 1].to !== hops[i].from) problems.push({ code: 'realisation.path-broken', message: `The path of realisation "${m.id}" is broken: hop ${i} ends at "${hops[i - 1].to}" but hop ${i + 1} starts at "${hops[i].from}".`, path: ['path', i] });
        }
        const a = endpointElement(model, logical.data.from)?.element;
        const b = endpointElement(model, logical.data.to)?.element;
        const placements = (/** @type {string|undefined} */ x) => (x ? [x, ...ancestorsIn(h, x)] : []);
        if (a && !placements(a).includes(hops[0].from)) problems.push({ code: 'realisation.endpoint', message: `The path of realisation "${m.id}" starts at "${hops[0].from}", which does not contain "${a}" in hierarchy "${hid}" (its placements there: ${placements(a).join(', ')}).`, path: ['path', 0] });
        if (b && !placements(b).includes(hops[hops.length - 1].to)) problems.push({ code: 'realisation.endpoint', message: `The path of realisation "${m.id}" ends at "${hops[hops.length - 1].to}", which does not contain "${b}" in hierarchy "${hid}" (its placements there: ${placements(b).join(', ')}).`, path: ['path', path.length - 1] });
      }
      out.push({ id: m.id, interaction: logical?.id ?? null, hierarchy: hid, path, holds: problems.length === 0, problems });
    }
    return out.sort((x, y) => byText(x.id, y.id));
  });
}

// ---------------------------------------------------------------------------------------------
// Declared coarse facts (V2 and V4)

/**
 * Relationships declared at a composite of the logical hierarchy (an element with members other than module
 * elements) are coarse facts. Each must be witnessed by a member fact: a relationship from inside its source to
 * inside its target, at least one end strictly inside, whose kind refines its kind. A coarse fact with no member
 * fact at all is unwitnessed (V2); one whose member facts are all of kinds that do not refine its kind breaks kind
 * preservation (V4). An opaque or unknown composite's facts are authoritative and not checked.
 * @param {Model} model @returns {AbstractionDiagnostic[]}
 */
export function declaredCoarseFacts(model) {
  return cached(model, 'coarseFacts', () => {
    const h = /** @type {Hierarchy} */ (hierarchyOf(model, LOGICAL));
    const elements = elementsOf(model);
    const composite = (/** @type {string} */ e) => (h.children.get(e) ?? []).some((c) => elements.get(c)?.kind !== 'module');
    const { facts } = baseFacts(model);
    /** @type {Map<string, Set<string>>} */
    const inside = new Map();
    const subtree = (/** @type {string} */ e) => {
      let s = inside.get(e);
      if (!s) { s = new Set([e]); const stack = [e]; while (stack.length) for (const c of h.children.get(/** @type {string} */ (stack.pop())) ?? []) { s.add(c); stack.push(c); } inside.set(e, s); }
      return s;
    };
    /** @type {AbstractionDiagnostic[]} */
    const out = [];
    for (const f of facts) {
      const coarseEnds = [f.from, f.to].filter((e) => composite(e) && knowledgeOf(model, e)?.status === 'transparent');
      if (!coarseEnds.length) continue;
      const A = subtree(f.from), B = subtree(f.to);
      const members = facts.filter((g) => g.id !== f.id && A.has(g.from) && B.has(g.to) && (g.from !== f.from || g.to !== f.to));
      if (!members.length) {
        out.push({ code: 'abstraction.unwitnessed', condition: 'V2', severity: 'warning', relationship: f.id, element: coarseEnds[0], entities: [f.id, ...coarseEnds],
          message: `Relationship "${f.id}" (${f.kind}) is declared at the composite ${coarseEnds.map((e) => `"${e}"`).join(' and ')}, but no relationship between their members witnesses it; a coarse fact at a transparent block is derived from its members' facts.` });
      } else if (!members.some((g) => refines(model.meta, g.kind, f.kind))) {
        out.push({ code: 'abstraction.kind-not-coarsening', condition: 'V4', severity: 'warning', relationship: f.id, element: coarseEnds[0], entities: [f.id, ...members.map((g) => g.id).sort(byText)],
          message: `Relationship "${f.id}" is of kind "${f.kind}", but its member facts are of kinds ${sortedUnique(members.map((g) => `"${g.kind}"`)).join(', ')}, none of which coarsens to "${f.kind}".` });
      }
    }
    return out;
  });
}

// ---------------------------------------------------------------------------------------------
// The derived architectural model

/**
 * The derived architectural model at a level. Memoised per model snapshot, level and coarsening.
 * @param {Model} model
 * @param {Parameters<typeof levelOf>[1]} ref
 * @param {{coarsen?: string[]|'all'|null}} [opts]
 */
export function deriveModel(model, ref, opts = {}) {
  const level = levelOf(model, ref);
  if (!level) return null;
  const coarsen = opts.coarsen ?? null;
  const key = `derive:${level.hierarchy}:${level.cut ?? ''}:${level.blocks.join('\u0001')}:${coarsen === null ? '' : coarsen === 'all' ? '*' : [...coarsen].sort().join(',')}`;
  return cached(model, key, () => assemble(model, level, coarsen, null));
}

/**
 * The derived model at a level the caller built itself (a candidate decomposition, src/core/decomposition.js, whose
 * hierarchy is not declared in the model). The same derivation as deriveModel, not memoised: the level is not a
 * key the model knows.
 * @param {Model} model @param {Level} level @param {{coarsen?: string[]|'all'|null}} [opts]
 */
export function deriveLevel(model, level, opts = {}) {
  return assemble(model, level, opts.coarsen ?? null, null);
}

/**
 * Build the derived model. `reuse` (from rederive) supplies interactions and fibres that are known to be unchanged
 * and the keys and blocks that must be computed again.
 * @param {Model} model @param {Level} level @param {string[]|'all'|null} coarsen
 * @param {{prev: ReturnType<typeof assemble>, dirtyKeys: Set<string>, dirtyFibres: Set<string>, dirtyBlocks: Set<string>}|null} reuse
 */
function assemble(model, level, coarsen, reuse) {
  const kindOf = kindCoarsening(model.meta, coarsen);
  const { facts, byId, unresolved } = baseFacts(model);
  const alpha = (/** @type {string} */ e) => blockAt(level, e);
  const cutTag = level.cut ?? '';

  /** @type {Map<string, {from: string, to: string, kind: string, witnesses: string[]}>} */
  let lifted;
  /** @type {Map<string, string[]>} */
  let fibreMap;
  /** @type {string[]} */
  let unplaced;
  if (!reuse) ({ interactions: lifted, fibres: fibreMap, unplaced } = lift(facts, alpha, kindOf));
  else {
    // Only the facts whose key is dirty are lifted again; the rest is carried over from the previous derivation.
    const { dirtyKeys, dirtyFibres } = reuse;
    const again = lift(facts.filter((f) => {
      const x = alpha(f.from), y = alpha(f.to);
      if (x === null || y === null) return true;
      return x === y ? dirtyFibres.has(x) : dirtyKeys.has(interactionKey(x, y, kindOf(f.kind)));
    }), alpha, kindOf);
    lifted = new Map();
    for (const i of reuse.prev.interactions) if (!dirtyKeys.has(i.key)) lifted.set(i.key, { from: i.from, to: i.to, kind: i.kind, witnesses: i.witnesses });
    for (const [k, i] of again.interactions) lifted.set(k, i);
    fibreMap = new Map();
    for (const [b, ws] of Object.entries(reuse.prev.fibres)) if (!dirtyFibres.has(b) && ws.length) fibreMap.set(b, ws);
    for (const [b, ws] of again.fibres) fibreMap.set(b, ws);
    unplaced = again.unplaced;
  }

  // Blocks: the cut's, then the implicit blocks facts are attached to.
  const blockSet = new Set(level.blocks);
  /** @type {Set<string>} */
  const implicit = new Set();
  for (const i of lifted.values()) for (const b of [i.from, i.to]) if (!blockSet.has(b)) implicit.add(b);
  for (const b of fibreMap.keys()) if (!blockSet.has(b)) implicit.add(b);
  /** @type {Map<string, number>} */
  const members = new Map();
  for (const b of level.map.values()) members.set(b, (members.get(b) ?? 0) + 1);
  const elements = elementsOf(model);
  const allBlocks = sortedUnique([...blockSet, ...implicit]);
  const blocks = allBlocks.map((id) => ({
    id, kind: elements.get(id)?.kind ?? null, implicit: implicit.has(id), knowledge: knowledgeOf(model, id)?.status ?? null,
    elements: implicit.has(id) ? 1 : members.get(id) ?? 0,
  }));

  /** @type {Interaction[]} */
  const interactions = [];
  const prevByKey = reuse ? new Map(reuse.prev.interactions.map((i) => [i.key, i])) : null;
  for (const [key, i] of [...lifted.entries()].sort((a, b) => byText(a[0], b[0]))) {
    const old = prevByKey && !reuse?.dirtyKeys.has(key) ? prevByKey.get(key) : undefined;
    if (old) { interactions.push(old); continue; }
    const lift1 = i.witnesses.some((w) => { const f = /** @type {BaseFact} */ (byId.get(w)); return f.from !== i.from || f.to !== i.to; });
    const summary = summarise(model, i.witnesses);
    interactions.push({
      key, from: i.from, to: i.to, kind: i.kind, class: kindInfo(model.meta, i.kind).class, lifted: lift1, witnesses: i.witnesses, summary,
      footprint: { witnesses: i.witnesses, reads: summary.carries, query: { from: i.from, to: i.to, kind: i.kind } },
    });
  }

  /** @type {Record<string, string[]>} */
  const fibres = {};
  for (const b of allBlocks) fibres[b] = fibreMap.get(b) ?? [];

  /** @type {Record<string, {out: string[], in: string[]}>} */
  const boundaries = {};
  for (const b of allBlocks) {
    if (reuse && !reuse.dirtyBlocks.has(b) && reuse.prev.boundaries[b]) { boundaries[b] = reuse.prev.boundaries[b]; continue; }
    boundaries[b] = { out: [], in: [] };
  }
  const touched = new Set(reuse ? allBlocks.filter((b) => reuse.dirtyBlocks.has(b) || !reuse.prev.boundaries[b]) : allBlocks);
  for (const i of interactions) {
    if (touched.has(i.from)) boundaries[i.from].out.push(...i.witnesses);
    if (touched.has(i.to)) boundaries[i.to].in.push(...i.witnesses);
  }
  for (const b of touched) { boundaries[b].out.sort(byText); boundaries[b].in.sort(byText); }

  // Interfaces: derived from the boundary; compared with the ports the block declares.
  /** @type {AbstractionDiagnostic[]} */
  const diagnostics = [];
  /** @type {Record<string, {authority: 'derived'|'declared', groups: (InterfaceGroup & {id: string, matchedBy: string[]})[], ports: {port: string, direction: string, contract: string|null, matches: string[]}[]}>} */
  const interfaces = {};
  for (const b of allBlocks) {
    const reused = reuse && !touched.has(b) ? reuse.prev.interfaces[b] : undefined;
    const ports = declaredPorts(model, b);
    const groups = reused ? reused.groups.map((g) => ({ ...g, matchedBy: [] })) : interfaceOf(model, boundaries[b], kindOf).map((g) => ({ ...g, id: groupId(g), matchedBy: /** @type {string[]} */ ([]) }));
    const portRows = ports.map((p) => {
      const matches = groups.filter((g) => portMatches(p, g)).map((g) => g.id);
      for (const g of groups) if (matches.includes(g.id)) g.matchedBy.push(p.id);
      return { port: p.id, direction: String(p.data.direction), contract: typeof p.data.contract === 'string' ? p.data.contract : null, matches };
    });
    const opaque = knowledgeOf(model, b)?.status === 'opaque' && ports.length > 0;
    interfaces[b] = { authority: opaque ? 'declared' : 'derived', groups, ports: portRows };
    for (const row of portRows) {
      if (!row.matches.length) diagnostics.push({ code: 'interface.unrealised-port', condition: 'V3', severity: 'warning', element: b, port: row.port, entities: [row.port, b],
        message: `Port "${row.port}" of "${b}" (${row.direction}${row.contract ? ` ${row.contract}` : ''}) is realised by nothing on the boundary of "${b}" at this level: no relationship ends at it${row.contract ? ` and none ${row.direction === 'requires' ? 'leaves' : 'enters'} it typed by "${row.contract}"` : ''}.` });
    }
    if (ports.length) {
      for (const g of groups) {
        if (g.matchedBy.length || (g.contract === null && !g.ports.length)) continue;
        diagnostics.push({ code: 'interface.undeclared-boundary', condition: 'V3', severity: 'warning', element: b, entities: [b, ...g.witnesses],
          message: `"${b}" declares ${ports.length === 1 ? 'a port' : `${ports.length} ports`}, but its boundary has ${g.direction === 'out' ? 'outgoing' : 'incoming'} ${g.kind}${g.contract ? ` typed by "${g.contract}"` : ''} (${g.witnesses.join(', ')}) that no declared port covers${opaque ? '; its declared interface is authoritative, so the boundary contradicts it' : ''}.` });
      }
    }
  }

  // Connectors: producer to consumer through a declared connector element, lifted to the blocks.
  const connectors = mediatedInteractions(model).map((m) => ({
    id: m.id, connector: m.connector, from: alpha(m.from), to: alpha(m.to), via: alpha(m.connector), witnesses: [...m.via].sort(byText), kind: m.kind,
  })).filter((c) => c.from !== null && c.to !== null && c.from !== c.to).sort((a, b) => byText(a.id, b.id));

  // Diagnostics: V1 from the cut and the hierarchy, V2 and V4 from declared coarse facts, ports, realisations.
  for (const p of level.problems) diagnostics.push({ code: `cut.${p.code}`, condition: 'V1', severity: 'error', element: p.element, entities: [p.element, ...(p.others ?? [])], message: p.message });
  for (const p of level.h.problems) diagnostics.push({ code: `hierarchy.${p.code}`, condition: 'V1', severity: level.hierarchy === LOGICAL && p.code === 'multiple-owners' ? 'warning' : 'error', element: p.element, entities: [p.element, ...(p.others ?? [])], message: p.message });
  if (level.hierarchy === LOGICAL) diagnostics.push(...declaredCoarseFacts(model));
  for (const p of portConnectionProblems(model)) diagnostics.push({ code: p.code, condition: 'port', severity: 'error', relationship: p.relationship, port: p.port, entities: [p.relationship, p.port], message: p.message });
  for (const r of checkRealisations(model)) for (const p of r.problems) diagnostics.push({ code: p.code, condition: 'realisation', severity: 'error', element: r.id, entities: [r.id], message: p.message });
  for (const id of [...unplaced, ...unresolved]) diagnostics.push({ code: 'abstraction.unplaced', condition: 'V1', severity: 'error', relationship: id, entities: [id], message: `Relationship "${id}" has an endpoint that is not an element of hierarchy "${level.hierarchy}", so it lies in no block.` });
  if (coarsen && coarsen !== 'all') for (const k of coarsen) if (!own(model.meta.relationshipKinds, k)) diagnostics.push({ code: 'abstraction.unknown-coarsening', condition: 'V4', severity: 'error', entities: [], message: `The coarsening names "${k}", which is not a relationship kind.` });
  diagnostics.sort((a, b) => byText(`${a.condition}|${a.code}|${a.entities.join(',')}`, `${b.condition}|${b.code}|${b.entities.join(',')}`));

  return {
    hierarchy: level.hierarchy, cut: level.cut, coarsening: coarsen, blocks, expanded: [...level.expanded].sort(byText),
    interactions, fibres, boundaries, interfaces, connectors, contracts: contractPaths(model), realisations: checkRealisations(model), diagnostics,
    footprint: { structure: { hierarchy: level.hierarchy, cut: cutTag || null } },
    /** alpha' of this level, for callers that place further elements (not serialised). */
    level,
  };
}

/** @typedef {NonNullable<ReturnType<typeof deriveModel>>} DerivedModel */

/**
 * The derived model as plain JSON (what the CLI prints and the goldens record): everything but the level.
 * @param {DerivedModel} d
 */
export function derivedJson(d) {
  const { level, ...rest } = d;
  return JSON.parse(JSON.stringify(rest));
}

/**
 * The derived interaction a relationship is a witness of at a derived model, or null when it is internal to a
 * block (then `fibre` names the block) or not placed.
 * @param {DerivedModel} d @param {string} relationshipId
 * @returns {{interaction: Interaction|null, fibre: string|null}}
 */
export function witnessOf(d, relationshipId) {
  let idx = witnessIndexes.get(d);
  if (!idx) {
    idx = new Map();
    for (const i of d.interactions) for (const w of i.witnesses) idx.set(w, i);
    witnessIndexes.set(d, idx);
  }
  const i = idx.get(relationshipId);
  if (i) return { interaction: i, fibre: null };
  for (const [b, ws] of Object.entries(d.fibres)) if (ws.includes(relationshipId)) return { interaction: null, fibre: b };
  return { interaction: null, fibre: null };
}
/** @type {WeakMap<object, Map<string, Interaction>>} */
const witnessIndexes = new WeakMap();

/**
 * An interaction restricted to the witnesses a filter keeps (a view's scope or kind filter): the witnesses that
 * pass and their summary, or null when none does. Because summaries are homomorphisms, this equals lifting the
 * filtered fact base.
 * @param {Model} model @param {Interaction} i @param {(fact: BaseFact) => boolean} keep
 * @returns {Interaction|null}
 */
export function restrictInteraction(model, i, keep) {
  const { byId } = baseFacts(model);
  const witnesses = i.witnesses.filter((w) => { const f = byId.get(w); return !!f && keep(f); });
  if (!witnesses.length) return null;
  if (witnesses.length === i.witnesses.length) return i;
  const summary = summarise(model, witnesses);
  const lifted = witnesses.some((w) => { const f = /** @type {BaseFact} */ (byId.get(w)); return f.from !== i.from || f.to !== i.to; });
  return { ...i, witnesses, summary, lifted, footprint: { ...i.footprint, witnesses } };
}

// ---------------------------------------------------------------------------------------------
// Change tracking (P13): which derived facts an edit can change, and incremental re-derivation

/** Component properties that place an element in a hierarchy or decide its knowledge status. */
const STRUCTURAL_COMPONENT_KEYS = ['parent', 'kind', 'implementation', 'knowledge', 'category'];

/**
 * Whether an edit changes the abstraction structure itself (so every derived fact at every level depends on it):
 * a component's placement, kind, modules, knowledge or category, any property a declared hierarchy groups by, a
 * port, a hierarchy, a cut, an element kind, or the relationship kinds of the vocabulary.
 * @param {Model} before @param {Model} after @param {Iterable<string>} affected
 */
export function structuralChange(before, after, affected) {
  if (JSON.stringify(before.meta.relationshipKinds) !== JSON.stringify(after.meta.relationshipKinds)) return true;
  const groupBy = new Set([...(before.byKind.hierarchy ?? []), ...(after.byKind.hierarchy ?? [])].map((h) => h.data.groupBy?.property).filter((p) => typeof p === 'string'));
  for (const id of affected) {
    const a = before.entities.get(id), b = after.entities.get(id);
    const kind = (b ?? a)?.kind;
    if (kind === undefined) continue;
    if (['port', 'hierarchy', 'cut', 'elementKind', 'system'].includes(kind)) return true;
    if (kind === 'component') {
      if (!a || !b) return true;
      for (const k of [...STRUCTURAL_COMPONENT_KEYS, ...groupBy]) if (JSON.stringify(a.data[k]) !== JSON.stringify(b.data[k])) return true;
    }
  }
  return false;
}

/**
 * The derived facts of a derived model whose footprint an edit touches: the interactions whose key the edited
 * relationships had before or have after the edit (or that carry an edited event), the fibres of the blocks they
 * were or are internal to, and the boundaries of the blocks those touch. `all` when the edit is structural.
 * @param {DerivedModel} d @param {Model} before @param {Model} after @param {Iterable<string>} affected
 */
export function dirtyFacts(d, before, after, affected) {
  const ids = [...affected];
  if (structuralChange(before, after, ids)) return { all: true, keys: new Set(), fibres: new Set(), blocks: new Set() };
  const kindOf = kindCoarsening(after.meta, d.coarsening);
  /** @type {Set<string>} */
  const keys = new Set();
  /** @type {Set<string>} */
  const fibres = new Set();
  const levels = [levelOf(before, levelRef(d)), levelOf(after, levelRef(d))];
  ids.forEach((id) => {
    [before, after].forEach((m, mi) => {
      const f = baseFacts(m).byId.get(id);
      const level = levels[mi];
      if (!f || !level) return;
      const x = blockAt(level, f.from), y = blockAt(level, f.to);
      if (x === null || y === null) return;
      if (x === y) fibres.add(x); else keys.add(interactionKey(x, y, kindOf(f.kind)));
    });
  });
  const edited = new Set(ids);
  for (const i of d.interactions) if (i.footprint.reads?.some((e) => edited.has(e))) keys.add(i.key);
  /** @type {Set<string>} */
  const blocks = new Set();
  for (const k of keys) { const [from, rest] = k.split('->'); blocks.add(from); blocks.add(rest.slice(0, rest.lastIndexOf(':'))); }
  return { all: false, keys, fibres, blocks };
}

/** The level reference a derived model was made at. @param {DerivedModel} d */
const levelRef = (d) => (d.cut ? { cut: d.cut } : { hierarchy: d.hierarchy, blocks: d.level.blocks });

/**
 * Re-derive after an edit, recomputing only the facts whose footprint the edit touches (dirtyFacts) and carrying
 * the rest over. The result equals deriveModel(after, ...) (P13; checked over randomised edit sequences by
 * tests/core/abstraction.test.js). Diagnostics are recomputed in full: they are cheap and model-wide.
 * @param {DerivedModel} prev @param {Model} before @param {Model} after @param {Iterable<string>} affected
 * @returns {{derived: DerivedModel, recomputed: {all: boolean, interactions: string[], fibres: string[], boundaries: string[]}}}
 */
export function rederive(prev, before, after, affected) {
  const dirty = dirtyFacts(prev, before, after, affected);
  const ref = levelRef(prev);
  if (dirty.all) {
    const full = /** @type {DerivedModel} */ (deriveModel(after, ref, { coarsen: prev.coarsening }));
    return { derived: full, recomputed: { all: true, interactions: full.interactions.map((i) => i.key), fibres: Object.keys(full.fibres), boundaries: Object.keys(full.boundaries) } };
  }
  const level = /** @type {Level} */ (levelOf(after, ref));
  const derived = assemble(after, level, prev.coarsening, { prev, dirtyKeys: dirty.keys, dirtyFibres: dirty.fibres, dirtyBlocks: dirty.blocks });
  return { derived, recomputed: { all: false, interactions: [...dirty.keys].sort(byText), fibres: [...dirty.fibres].sort(byText), boundaries: [...dirty.blocks].sort(byText) } };
}

/** Every hierarchy and declared cut of a model, for callers that derive at all of them. @param {Model} model */
export function declaredLevels(model) {
  return { hierarchies: hierarchyIds(model), cuts: (model.byKind.cut ?? []).map((c) => c.id) };
}

// ---------------------------------------------------------------------------------------------
// The invariants of an abstraction (WG-5694 I1-I7), checked on a model's own derived models

/** The invariants abstractionInvariants checks, by name. */
export const ABSTRACTION_INVARIANTS = /** @type {const} */ ({
  'witness-completeness': 'I1: every derived interaction has a non-empty witness set, and re-lifting each witness gives exactly that interaction.',
  'boundary-accounting': 'I2: every relationship whose ends lie in different blocks is a witness of exactly one derived interaction, of its kind or its coarsening.',
  recoverability: 'I3: the fibres together with all witness sets are exactly the relationships, each once.',
  'interfaces-from-boundaries': 'I4: the boundary of each block is the set of relationships with exactly one end in it, and its derived interface is the grouping of that boundary alone.',
  functoriality: 'I5: deriving straight to a cut equals deriving to any finer declared cut of the same hierarchy and lifting from there, on interactions, witness sets, every summary attribute and fibres.',
  'kind-preservation': 'I6: every derived kind is the kind of each of its witnesses or the declared coarsening of it.',
  determinism: 'I7: the derived model does not depend on the order relationships are declared in.',
});

/** @param {any} x */
const canon = (x) => JSON.stringify(x);

/**
 * Check the invariants on the derived models of the given cuts (every declared cut by default), without and with
 * the coarsening to the top kinds. Returns the faults per invariant (empty when it holds) and what was checked.
 * Each check recomputes its side from the base facts independently of how the derived model was assembled.
 * @param {Model} model @param {string[]} [cuts] @param {string[]} [which]
 * @returns {{faults: Record<string, string[]>, cuts: string[], pairs: [string, string][], interactions: number}}
 */
export function abstractionInvariants(model, cuts, which) {
  const ids = cuts ?? (model.byKind.cut ?? []).map((c) => c.id);
  const names = which ?? Object.keys(ABSTRACTION_INVARIANTS);
  /** @type {Record<string, string[]>} */
  const faults = Object.fromEntries(names.map((n) => [n, []]));
  const want = (/** @type {string} */ n) => names.includes(n);
  const { facts, byId } = baseFacts(model);
  let interactions = 0;
  /** @type {[string, string][]} */
  const pairs = [];
  for (const coarsen of [null, /** @type {'all'} */ ('all')]) {
    const kindOf = kindCoarsening(model.meta, coarsen);
    for (const cid of ids) {
      const d = deriveModel(model, cid, { coarsen });
      if (!d) { for (const n of names) faults[n].push(`"${cid}" is not a cut of a known hierarchy`); continue; }
      const tag = `cut "${cid}"${coarsen ? ' (coarsened)' : ''}`;
      const alpha = (/** @type {string} */ e) => blockAt(d.level, e);
      interactions += d.interactions.length;
      if (want('witness-completeness')) {
        for (const i of d.interactions) {
          if (!i.witnesses.length) faults['witness-completeness'].push(`${tag}: "${i.key}" has no witness`);
          for (const w of i.witnesses) {
            const f = byId.get(w);
            const back = f ? interactionKey(/** @type {string} */ (alpha(f.from)), /** @type {string} */ (alpha(f.to)), kindOf(f.kind)) : null;
            if (back !== i.key) faults['witness-completeness'].push(`${tag}: witness "${w}" of "${i.key}" lifts to ${back === null ? 'nothing' : `"${back}"`}`);
          }
        }
      }
      if (want('boundary-accounting')) {
        /** @type {Map<string, string[]>} */
        const holders = new Map();
        for (const i of d.interactions) for (const w of i.witnesses) { if (!holders.has(w)) holders.set(w, []); /** @type {string[]} */ (holders.get(w)).push(i.key); }
        for (const f of facts) {
          const x = alpha(f.from), y = alpha(f.to);
          if (x === null || y === null || x === y) continue;
          const h = holders.get(f.id) ?? [];
          if (h.length !== 1) faults['boundary-accounting'].push(`${tag}: "${f.id}" crosses "${x}" -> "${y}" but is a witness of ${h.length} derived interactions`);
          else if (!h[0].endsWith(`:${kindOf(f.kind)}`)) faults['boundary-accounting'].push(`${tag}: "${f.id}" (${f.kind}) is a witness of "${h[0]}", not of its kind or coarsening`);
        }
      }
      if (want('recoverability')) {
        const seen = [...Object.values(d.fibres).flat(), ...d.interactions.flatMap((i) => i.witnesses)];
        /** @type {Map<string, number>} */
        const counts = new Map();
        for (const w of seen) counts.set(w, (counts.get(w) ?? 0) + 1);
        for (const f of facts) if (counts.get(f.id) !== 1) faults.recoverability.push(`${tag}: "${f.id}" occurs ${counts.get(f.id) ?? 0} times among the fibres and witness sets`);
        for (const w of counts.keys()) if (!byId.has(w)) faults.recoverability.push(`${tag}: "${w}" is in a fibre or witness set but is no relationship`);
      }
      if (want('interfaces-from-boundaries')) {
        for (const b of d.blocks) {
          const out = facts.filter((f) => alpha(f.from) === b.id && alpha(f.to) !== b.id).map((f) => f.id).sort(byText);
          const inn = facts.filter((f) => alpha(f.to) === b.id && alpha(f.from) !== b.id).map((f) => f.id).sort(byText);
          if (canon(out) !== canon(d.boundaries[b.id].out) || canon(inn) !== canon(d.boundaries[b.id].in)) faults['interfaces-from-boundaries'].push(`${tag}: the boundary of "${b.id}" is not the relationships with exactly one end in it`);
          const derived = d.interfaces[b.id].groups.map(({ matchedBy, id, ...g }) => g);
          if (canon(derived) !== canon(interfaceOf(model, { out, in: inn }, kindOf))) faults['interfaces-from-boundaries'].push(`${tag}: the derived interface of "${b.id}" is not the grouping of its boundary`);
        }
      }
      if (want('kind-preservation')) {
        for (const i of d.interactions) for (const w of i.witnesses) {
          const f = byId.get(w);
          if (f && f.kind !== i.kind && !refines(model.meta, f.kind, i.kind)) faults['kind-preservation'].push(`${tag}: "${i.key}" has witness "${w}" of kind "${f.kind}", which does not coarsen to "${i.kind}"`);
        }
      }
    }
    if (want('functoriality')) {
      for (const fine of ids) for (const coarse of ids) {
        if (fine === coarse) continue;
        const a = deriveModel(model, fine, { coarsen: null }), b = deriveModel(model, coarse, { coarsen });
        if (!a || !b || a.hierarchy !== b.hierarchy) continue;
        // C refines C' when every block of C lies at or below a block of C'.
        if (!a.level.blocks.every((x) => b.level.map.has(x))) continue;
        if (!coarsen) pairs.push([fine, coarse]);
        const via = relift(a, (x) => blockAt(b.level, x), kindOf);
        const direct = { interactions: b.interactions.map((i) => ({ key: i.key, from: i.from, to: i.to, kind: i.kind, witnesses: i.witnesses, summary: i.summary })), fibres: Object.fromEntries(Object.entries(b.fibres).filter(([, ws]) => ws.length)) };
        if (canon(via.interactions) !== canon(direct.interactions)) faults.functoriality.push(`cut "${fine}" lifted to "${coarse}"${coarsen ? ' (coarsened)' : ''} differs from deriving "${coarse}" directly on interactions, witnesses or summaries`);
        if (canon(via.fibres) !== canon(direct.fibres)) faults.functoriality.push(`cut "${fine}" lifted to "${coarse}"${coarsen ? ' (coarsened)' : ''} differs from deriving "${coarse}" directly on fibres`);
      }
    }
  }
  if (want('determinism')) {
    const reversed = /** @type {Model} */ ({ ...model, byKind: { ...model.byKind, relationship: [...(model.byKind.relationship ?? [])].reverse() } });
    for (const cid of ids) {
      const a = deriveModel(model, cid), b = deriveModel(reversed, cid);
      if (!a || !b) continue;
      if (canon(derivedJson(a)) !== canon(derivedJson(b))) faults.determinism.push(`cut "${cid}": the derived model changes when the relationships are declared in reverse order`);
    }
  }
  return { faults, cuts: ids, pairs, interactions };
}
