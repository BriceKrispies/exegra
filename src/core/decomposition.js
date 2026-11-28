// Candidate decompositions, their validity, measurements and boundary evidence (WG-5731, the structural part of M7;
// docs/assessment/2026-11-27/multiscale.md, sections 3.9, 3.10 and 5.3).
//
// A candidate decomposition is a hierarchy over the same elements: a scope (an element), the grain of the scope that is
// regrouped (its children, its leaves or its module elements), and blocks, each a set of grain elements:
//
//   { id, name?, source?, scope, grain?: 'children'|'leaves'|'modules',
//     blocks: [{ id, name?, members: [element ids] }], rest?: <block id>, from?: {candidate, op} }
//
// `rest` names the block that takes every grain element no block lists (the audit's "plus the other components"); the
// elements it took are reported. A block whose members are exactly [its id] is that element itself.
//
// Evaluation is pure (invariant I1): the facts, the model and its hash are read and never written. A score never changes
// a fact. A candidate is checked against the validity conditions of ONE registry, VALIDITY_CONDITIONS, below; V1 to V4
// are registered here, and so are the behavioural conditions V5 to V7, which read the candidate's blocks as the composites of a
// cut (WG-5735: coherence.js decides V5 and V7, composition.js's refinement check decides V6). A condition that does not
// apply to a candidate (V6 where no block declares abstract behaviour) says so with its reason rather than passing. A valid candidate is measured by
// deterministic functions of the facts and the candidate (I3). Valid is not meaningful: no report ranks, scores or
// recommends, and nothing here accepts a candidate (I4; acceptance is a recorded transaction, `acceptanceOf` only
// describes it).
//
// Generation (generateCandidates) draws on the established semantics only: the declared hierarchy, module directories,
// strongly connected components of the dependency classes, regions bounded by contracts or by connectors, and split,
// merge and move refinements read off the measurements of a base candidate.

import { baseFacts, deriveLevel, contractPaths } from './abstraction.js';
import { LOGICAL, hierarchyOf, elementsOf, knowledgeOf, abstractionOf, ancestorsIn, moduleDeclarations } from './query.js';
import { kindInfo, refines, isConnector, provenanceOf } from './interactions.js';
import { reconcile } from './extraction.js';
import { coherenceAtLevel } from './coherence.js';
import { abstractionOf as declaredAbstraction, checkAbstraction, describeCounterexample } from './composition.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./abstraction.js').BaseFact} BaseFact */
/**
 * @typedef {{id: string, name?: string, members: string[]}} CandidateBlock
 * @typedef {{id: string, name?: string, source?: string, scope: string, grain?: 'children'|'leaves'|'modules', blocks: CandidateBlock[], rest?: string,
 *   note?: string, from?: {candidate: string, op: any}}} Candidate
 * @typedef {{code: string, message: string, witnesses: string[]}} Failure
 * @typedef {{failures: Failure[], notApplicable?: string, detail?: any}} ConditionOutcome
 * @typedef {{id: string, title: string, behavioural?: boolean, needs?: string[], check: (ctx: ConditionContext) => Failure[]|ConditionOutcome}} ValidityCondition
 */

const byText = (/** @type {string} */ a, /** @type {string} */ b) => (a < b ? -1 : a > b ? 1 : 0);
/** @param {Iterable<string>} xs */
const uniq = (xs) => [...new Set(xs)].sort(byText);
/** A ratio with its parts, rounded to six places so the report is the same text on every run. @param {number} n @param {number} d */
const fraction = (n, d) => ({ n, d, value: d > 0 ? Math.round((n / d) * 1e6) / 1e6 : null });

export const BEHAVIOURAL_CONDITIONS = Object.freeze(['V5', 'V6', 'V7']);
export const GRAINS = Object.freeze(['children', 'leaves', 'modules']);
export const SOURCES = Object.freeze(['declared', 'directory', 'cycles', 'contracts', 'connectors', 'refinement']);
export const NOT_MEANING = 'Measurements describe structure. Whether a decomposition is meaningful is a judgement they do not make, and no score here accepts, ranks or recommends a candidate.';

// ---------------------------------------------------------------------------------------------
// The fact base a candidate is evaluated against

/** @type {WeakMap<object, Map<string, Model>>} */
const views = new WeakMap();

/**
 * The model restricted to the relationships of the given provenances (a view; the model is untouched). Without a
 * restriction, the model itself.
 * @param {Model} model @param {string[]|null|undefined} provenance
 * @returns {Model}
 */
export function factView(model, provenance) {
  if (!provenance || !provenance.length) return model;
  const key = [...provenance].sort(byText).join(',');
  let m = views.get(model);
  if (!m) { m = new Map(); views.set(model, m); }
  const have = m.get(key);
  if (have) return have;
  const keep = new Set(provenance);
  const all = model.byKind.relationship ?? [];
  const kept = all.filter((r) => keep.has(provenanceOf(r)));
  const dropped = new Set(all.filter((r) => !keep.has(provenanceOf(r))).map((r) => r.id));
  const view = kept.length === all.length ? model : /** @type {Model} */ ({ ...model, entities: new Map([...model.entities].filter(([id]) => !dropped.has(id))), byKind: { ...model.byKind, relationship: kept } });
  m.set(key, view);
  return view;
}

/** The contract a fact is typed by: its own, or the one a port at either end declares. @param {Model} model @param {BaseFact} f */
export function factContract(model, f) {
  if (f.contract) return f.contract;
  for (const p of [f.fromPort, f.toPort]) {
    const c = p ? model.entities.get(p)?.data.contract : null;
    if (typeof c === 'string') return c;
  }
  return null;
}

// ---------------------------------------------------------------------------------------------
// Scope and grain

/**
 * The elements a candidate must place: the grain of its scope, sorted, and the map from every element at or below
 * the grain to its grain element. null when the scope is not an element.
 * @param {Model} model @param {string} scope @param {'children'|'leaves'|'modules'} grain
 */
export function grainOf(model, scope, grain) {
  const elements = elementsOf(model);
  const h = /** @type {import('./query.js').Hierarchy} */ (hierarchyOf(model, LOGICAL));
  if (!elements.has(scope)) return null;
  /** @type {string[]} */
  const out = [];
  const nonModuleKids = (/** @type {string} */ e) => (h.children.get(e) ?? []).filter((c) => elements.get(c)?.kind !== 'module');
  const walk = (/** @type {string} */ e) => {
    for (const c of h.children.get(e) ?? []) {
      if (grain === 'children') out.push(c);
      else if (grain === 'modules') { if (elements.get(c)?.kind === 'module') out.push(c); else walk(c); }
      else if (elements.get(c)?.kind === 'module') continue;
      else if (nonModuleKids(c).length) walk(c);
      else out.push(c);
    }
  };
  walk(scope);
  const universe = uniq(out);
  return { universe, map: abstractionOf(h, universe), h };
}

// ---------------------------------------------------------------------------------------------
// Resolving a candidate

/**
 * @typedef {{id: string, name: string, source: string, scope: string, grain: 'children'|'leaves'|'modules', universe: string[],
 *   blocks: {id: string, name: string, members: string[], existing: boolean, self: boolean}[], placedByRest: string[],
 *   problems: Failure[], from: any, note: string|null}} Resolved
 */

/**
 * The candidate with its defaults filled in and every way it is not a laminar covering partition of the grain, as
 * failures with witnesses (V1). Nothing is thrown for a malformed candidate.
 * @param {Model} model @param {any} raw @param {{scope?: string, grain?: 'children'|'leaves'|'modules'}} [defaults]
 * @returns {Resolved}
 */
export function resolveCandidate(model, raw, defaults = {}) {
  /** @type {Failure[]} */
  const problems = [];
  const fail = (/** @type {string} */ code, /** @type {string} */ message, /** @type {string[]} */ witnesses) => problems.push({ code, message, witnesses: uniq(witnesses) });
  const c = raw && typeof raw === 'object' ? raw : {};
  const id = typeof c.id === 'string' && c.id ? c.id : '(unnamed)';
  if (typeof c.id !== 'string' || !c.id) fail('shape.id', 'A candidate has an id.', []);
  const scope = typeof c.scope === 'string' ? c.scope : defaults.scope ?? model.system?.id ?? '';
  const grain = GRAINS.includes(c.grain) ? c.grain : defaults.grain ?? 'children';
  if (c.grain !== undefined && !GRAINS.includes(c.grain)) fail('shape.grain', `Grain "${String(c.grain)}" is none of ${GRAINS.join(', ')}.`, []);
  const g = grainOf(model, scope, grain);
  if (!g) fail('scope.unknown', `Scope "${scope}" is not an element.`, [scope]);
  const universe = g?.universe ?? [];
  if (g && !universe.length) fail('scope.empty-grain', `Scope "${scope}" has no ${grain} to place.`, [scope]);
  const elements = elementsOf(model);
  if (!Array.isArray(c.blocks)) fail('shape.blocks', 'A candidate has a list of blocks.', []);
  /** @type {Resolved['blocks']} */
  const blocks = [];
  /** @type {Map<string, string[]>} */
  const placed = new Map();
  /** @type {Set<string>} */
  const seenIds = new Set();
  const inScope = (/** @type {string} */ e) => e === scope || (g ? ancestorsIn(g.h, e).includes(scope) : false);
  for (const b of Array.isArray(c.blocks) ? c.blocks : []) {
    if (!b || typeof b.id !== 'string' || !b.id || !Array.isArray(b.members)) { fail('shape.block', `A block has an id and a list of members: ${JSON.stringify(b)?.slice(0, 80)}.`, []); continue; }
    if (seenIds.has(b.id)) { fail('duplicate-block', `Block "${b.id}" is listed twice.`, [b.id]); continue; }
    seenIds.add(b.id);
    const members = uniq(b.members.filter((/** @type {any} */ m) => typeof m === 'string'));
    if (!members.length) fail('empty-block', `Block "${b.id}" has no members.`, [b.id]);
    const self = members.length === 1 && members[0] === b.id;
    const existing = elements.has(b.id);
    if (b.id === scope) fail('block-is-scope', `Block "${b.id}" is the scope itself.`, [b.id]);
    else if (existing && !self) {
      if (universe.includes(b.id)) fail('block-id-collision', `Block "${b.id}" is named after a grain element it does not consist of alone.`, [b.id]);
      else if (g && !inScope(b.id)) fail('block-id-collision', `Block "${b.id}" is named after an element outside the scope "${scope}".`, [b.id]);
    }
    for (const m of members) {
      if (!placed.has(m)) placed.set(m, []);
      /** @type {string[]} */ (placed.get(m)).push(b.id);
      if (!universe.includes(m) && g) {
        if (!elements.has(m)) fail('unknown-member', `"${m}" (block "${b.id}") is not an element.`, [m, b.id]);
        else if (!inScope(m)) fail('outside-scope', `"${m}" (block "${b.id}") is not inside the scope "${scope}".`, [m, b.id]);
        else {
          const above = universe.find((u) => ancestorsIn(g.h, m).includes(u));
          if (above) fail('below-grain', `"${m}" (block "${b.id}") is inside "${above}", which is the grain element to place.`, [m, above, b.id]);
          else fail('above-grain', `"${m}" (block "${b.id}") is coarser than the grain "${grain}" of "${scope}"; place its members.`, [m, b.id]);
        }
      }
    }
    blocks.push({ id: b.id, name: typeof b.name === 'string' ? b.name : b.id, members, existing, self });
  }
  /** @type {string[]} */
  const placedByRest = [];
  if (c.rest !== undefined) {
    const rest = blocks.find((b) => b.id === c.rest);
    if (!rest) fail('rest-unknown', `rest names "${String(c.rest)}", which is not a block of the candidate.`, [String(c.rest)]);
    else for (const u of universe) if (!placed.has(u)) { rest.members = uniq([...rest.members, u]); placed.set(u, [rest.id]); placedByRest.push(u); }
  }
  for (const [m, ids] of placed) if (ids.length > 1) fail('overlap', `"${m}" is in ${ids.length} blocks (${ids.map((x) => `"${x}"`).join(', ')}); a hierarchy places an element once, so the blocks are not laminar.`, [m, ...ids]);
  const uncovered = universe.filter((u) => !placed.has(u));
  if (uncovered.length) fail('uncovered', `${uncovered.length} ${grain === 'children' ? 'children' : grain} of "${scope}" are in no block, so the blocks do not cover them: ${uncovered.slice(0, 8).join(', ')}${uncovered.length > 8 ? ', ...' : ''}.`, uncovered);
  for (const b of blocks) if (b.self && !universe.includes(b.id) && g) fail('unknown-member', `"${b.id}" (a block of itself) is not a ${grain} element of "${scope}".`, [b.id]);
  blocks.sort((a, b) => byText(a.id, b.id));
  return {
    id, name: typeof c.name === 'string' ? c.name : id, source: typeof c.source === 'string' ? c.source : 'data', scope, grain, universe, blocks, placedByRest: placedByRest.sort(byText),
    problems: problems.sort((a, b) => byText(`${a.code}|${a.witnesses.join(',')}`, `${b.code}|${b.witnesses.join(',')}`)), from: c.from ?? null, note: typeof c.note === 'string' ? c.note : null,
  };
}

/**
 * The candidate's hierarchy as a level the derivation reads: the logical hierarchy in which every block is a child of the
 * scope and holds its members. Only for a candidate with no problems.
 * @param {Model} model @param {Resolved} r
 */
function levelOfCandidate(model, r) {
  const h0 = /** @type {import('./query.js').Hierarchy} */ (hierarchyOf(model, LOGICAL));
  const parent = new Map(h0.parent);
  for (const b of r.blocks) {
    parent.set(b.id, r.scope);
    if (!b.self) for (const m of b.members) parent.set(m, b.id);
  }
  const order = [...h0.order];
  const have = new Set(order);
  for (const b of r.blocks) if (!have.has(b.id)) order.push(b.id);
  /** @type {Map<string, string[]>} */
  const children = new Map();
  /** @type {string[]} */
  const roots = [];
  for (const e of order) {
    const p = parent.get(e);
    if (p === undefined) roots.push(e);
    else { if (!children.has(p)) children.set(p, []); /** @type {string[]} */ (children.get(p)).push(e); }
  }
  /** @type {Map<string, number>} */
  const depth = new Map();
  const stack = roots.map((e) => /** @type {[string, number]} */ ([e, 0]));
  while (stack.length) { const [e, d] = /** @type {[string, number]} */ (stack.pop()); depth.set(e, d); for (const k of children.get(e) ?? []) stack.push([k, d + 1]); }
  const h = { id: r.id, parent, children, roots, depth, order, problems: [] };
  const blocks = r.blocks.map((b) => b.id);
  return { hierarchy: r.id, cut: null, blocks, expanded: [r.scope], problems: [], map: abstractionOf(h, blocks), h };
}

// ---------------------------------------------------------------------------------------------
// The registry of validity conditions

/**
 * @typedef {{model: Model, candidate: Resolved, level: ReturnType<typeof levelOfCandidate>|null, derived: import('./abstraction.js').DerivedModel|null,
 *   facts: BaseFact[], blockOf: (element: string) => string|null, results: Record<string, 'pass'|'fail'|'skipped'>}} ConditionContext
 */

/**
 * THE place validity conditions plug in. Each runs in order on a context holding the model (a fact view), the resolved
 * candidate, its level and derived model, the facts and the block of an element; it returns failures, each with a code, a
 * message and witnesses. A condition with `needs` is skipped when a needed one failed or was skipped. V1 to V4 are the
 * structural conditions of audit 3.10. The behavioural conditions V5 (structure-behaviour coherence), V6 (refinement) and V7
 * (contract conformance) are registered with registerValidityCondition by the modules that decide them; until they are, a
 * report says they were not evaluated and never calls a candidate valid.
 * @type {ValidityCondition[]}
 */
export const VALIDITY_CONDITIONS = [];

/**
 * Add a validity condition to the registry (replacing one of the same id), and return a function that removes it again.
 * @param {ValidityCondition} condition @returns {() => void}
 */
export function registerValidityCondition(condition) {
  const at = VALIDITY_CONDITIONS.findIndex((c) => c.id === condition.id);
  if (at >= 0) VALIDITY_CONDITIONS.splice(at, 1, condition); else VALIDITY_CONDITIONS.push(condition);
  return () => { const i = VALIDITY_CONDITIONS.indexOf(condition); if (i >= 0) VALIDITY_CONDITIONS.splice(i, 1); };
}

registerValidityCondition({
  id: 'V1', title: 'Well-formed partition: the blocks are a laminar hierarchy that places every element of the grain exactly once',
  check: (ctx) => {
    const failures = [...ctx.candidate.problems];
    // A module element two components declare lies in two blocks when those components do.
    const h0 = /** @type {import('./query.js').Hierarchy} */ (hierarchyOf(ctx.model, LOGICAL));
    if (!failures.length && ctx.level) for (const p of h0.problems) {
      if (p.code !== 'multiple-owners' || !p.others) continue;
      const bs = uniq(p.others.map((o) => ctx.blockOf(o)).filter((b) => b !== null).map(String));
      if (bs.length > 1) failures.push({ code: 'module-in-two-blocks', message: `Module element "${p.element}" is declared by ${p.others.join(' and ')}, which lie in blocks ${bs.join(' and ')}.`, witnesses: [p.element, ...p.others, ...bs] });
    }
    return failures;
  },
});

registerValidityCondition({
  id: 'V2', title: 'Witnessed coarse facts: every lifted interaction has a non-empty witness set whose facts run between its blocks, and every fact is accounted for once', needs: ['V1'],
  check: (ctx) => {
    const d = /** @type {NonNullable<ConditionContext['derived']>} */ (ctx.derived);
    /** @type {Failure[]} */
    const failures = [];
    const byId = new Map(ctx.facts.map((f) => [f.id, f]));
    const seen = new Set();
    for (const i of d.interactions) {
      if (!i.witnesses.length) failures.push({ code: 'unwitnessed-interaction', message: `Interaction ${i.key} has no witness.`, witnesses: [i.from, i.to] });
      for (const w of i.witnesses) {
        const f = byId.get(w);
        if (!f || (ctx.blockOf(f.from) ?? f.from) !== i.from || (ctx.blockOf(f.to) ?? f.to) !== i.to) failures.push({ code: 'witness-outside-interaction', message: `Fact "${w}" is a witness of ${i.key} but does not run between those blocks.`, witnesses: [w, i.from, i.to] });
        seen.add(w);
      }
    }
    for (const ids of Object.values(d.fibres)) for (const w of ids) seen.add(w);
    const lost = ctx.facts.filter((f) => !seen.has(f.id)).map((f) => f.id);
    if (lost.length) failures.push({ code: 'fact-unaccounted', message: `${lost.length} facts are in no block's fibre and no interaction's witnesses.`, witnesses: lost });
    return failures;
  },
});

function isBlockOrAbove(ctx, e, block) { return ctx.blockOf(e) === null && e === block; }

registerValidityCondition({
  id: 'V3', title: 'Interface agreement: for every block with a declared interface, the declared and the derived interface agree', needs: ['V1'],
  check: (ctx) => {
    const d = /** @type {NonNullable<ConditionContext['derived']>} */ (ctx.derived);
    const mine = new Set(ctx.candidate.blocks.map((b) => b.id));
    return d.diagnostics.filter((x) => x.condition === 'V3' && x.element !== undefined && mine.has(x.element)).map((x) => ({ code: x.code, message: x.message, witnesses: uniq(x.entities) }));
  },
});

registerValidityCondition({
  id: 'V4', title: 'Kind preservation: every lifted kind is a base kind or the declared coarsening of its witnesses\' kinds', needs: ['V1'],
  check: (ctx) => {
    const d = /** @type {NonNullable<ConditionContext['derived']>} */ (ctx.derived);
    const byId = new Map(ctx.facts.map((f) => [f.id, f]));
    /** @type {Failure[]} */
    const failures = [];
    for (const i of d.interactions) {
      const bad = i.witnesses.filter((w) => { const f = byId.get(w); return !f || !refines(ctx.model.meta, f.kind, i.kind); });
      if (bad.length) failures.push({ code: 'kind-not-coarsening', message: `Interaction ${i.key}: the kinds of ${bad.join(', ')} do not coarsen to "${i.kind}".`, witnesses: bad });
    }
    return failures;
  },
});

// The behavioural conditions read the candidate's blocks as the composites of a cut. They ask nothing of the blocks that the
// model's own cuts are not asked.

registerValidityCondition({
  id: 'V5', title: 'Structure-behaviour coherence: every message that crosses between two blocks is witnessed structurally, by a relationship of message class between the two elements themselves', behavioural: true, needs: ['V1'],
  check: (ctx) => {
    const level = /** @type {NonNullable<ConditionContext['level']>} */ (ctx.level);
    const r = coherenceAtLevel(ctx.model, level, ctx.derived, ctx.candidate.id);
    const failures = r.findings.map((f) => ({
      code: f.status === 'different-witness' ? 'message.different-witness' : 'message.unwitnessed', message: f.message,
      witnesses: [f.event, f.emitter, f.consumer, f.from, f.to, ...(f.fromBlock ? [f.fromBlock] : []), ...(f.toBlock ? [f.toBlock] : []), ...f.coarseWitnesses],
    }));
    return { failures, detail: { messages: r.messages, internal: r.internal, crossing: r.messages - r.internal - r.unplaced, unplaced: r.unplaced } };
  },
});

registerValidityCondition({
  id: 'V6', title: 'Refinement: where a block declares abstract behaviour, the abstraction refines the composition of its members', behavioural: true, needs: ['V1'],
  check: (ctx) => {
    /** @type {{block: string, abstraction: string}[]} */
    const declared = [];
    for (const b of ctx.candidate.blocks) {
      if (!b.existing) continue;
      for (const beh of ctx.model.byKind.behavior ?? []) if (beh.data.subject === b.id && declaredAbstraction(ctx.model, beh)) declared.push({ block: b.id, abstraction: beh.id });
    }
    if (!declared.length) {
      return { failures: [], notApplicable: 'No block declares abstract behaviour (a behavior with "abstracts" whose subject is the block), so there is no refinement to check. This is not a pass: the candidate is silent about behaviour.', detail: { checked: [] } };
    }
    /** @type {Failure[]} */
    const failures = [];
    const checked = declared.map(({ block, abstraction }) => {
      try {
        const r = checkAbstraction(ctx.model, abstraction);
        if (r.verdict === 'counterexample') {
          const cx = r.counterexample;
          failures.push({ code: 'refinement.counterexample', message: `Block "${block}": abstraction "${abstraction}" does not refine its members. ${describeCounterexample(cx)}`, witnesses: [abstraction, block, cx.scenario, cx.abstractStep?.event, cx.concreteStep?.event].filter((x) => typeof x === 'string') });
        } else if (r.verdict === 'unchecked') {
          failures.push({ code: 'refinement.unchecked', message: `Block "${block}": abstraction "${abstraction}" could not be checked (${r.notes[0] ?? 'no scenario runs it or its members'}), so refinement is not established.`, witnesses: [abstraction, block] });
        }
        return { block, abstraction, verdict: r.verdict, strength: r.strength, scenarios: r.runs.map((x) => x.scenario) };
      } catch (e) {
        failures.push({ code: 'refinement.unchecked', message: `Block "${block}": abstraction "${abstraction}" could not be checked: ${/** @type {Error} */ (e).message}`, witnesses: [abstraction, block] });
        return { block, abstraction, verdict: 'unchecked', strength: null, scenarios: [] };
      }
    });
    return { failures, detail: { checked } };
  },
});

registerValidityCondition({
  id: 'V7', title: 'Contract conformance: every boundary interaction that declares a contract has the events that cross it typed by that contract', behavioural: true, needs: ['V1'],
  check: (ctx) => {
    /** @type {Failure[]} */
    const failures = [];
    const seen = new Set();
    // The boundaries a candidate makes are the ones between its blocks. A hop from a block to an element outside the scope is
    // the scope's boundary: every candidate has it as it is, so it is counted in `outside` and decided by no candidate.
    const tally = { boundary: 0, typed: 0, untyped: 0, unmodelled: 0, outside: { hops: 0, untyped: /** @type {string[]} */ ([]) } };
    for (const { contract, paths } of contractPaths(ctx.model)) for (const p of paths) for (const h of p.hops) {
      if (seen.has(h.relationship)) continue;
      seen.add(h.relationship);
      const a = ctx.blockOf(h.from), b = ctx.blockOf(h.to);
      if (a === null && b === null) continue;
      if (a === null || b === null) { tally.outside.hops++; if (h.status === 'untyped') tally.outside.untyped.push(h.relationship); continue; }
      if (a === b) continue;
      tally.boundary++;
      tally[h.status]++;
      if (h.status !== 'untyped') continue;
      failures.push({ code: 'contract.untyped', message: `Boundary interaction "${h.relationship}" (block ${a} to block ${b}) declares contract "${contract}", but the events that pass between "${h.from}" and "${h.to}" (${h.events.join(', ')}) are not typed by it.`, witnesses: [h.relationship, contract, h.from, h.to, a, b, ...h.events] });
    }
    tally.outside.untyped.sort(byText);
    return { failures, detail: tally };
  },
});

// ---------------------------------------------------------------------------------------------
// Measurements

const CLASSES = /** @type {const} */ (['static', 'runtime', 'none']);
const DEPENDENCY = new Set(['static', 'runtime']);
const CYCLE_CLASSES = /** @type {const} */ ([['static', ['static']], ['runtime', ['runtime']], ['dependency', ['static', 'runtime']]]);

/**
 * Strongly connected components of size above one, canonically ordered (Tarjan over sorted nodes).
 * @param {string[]} nodes @param {Map<string, Set<string>>} adj @returns {string[][]}
 */
export function cyclicComponents(nodes, adj) {
  let idx = 0;
  /** @type {string[]} */ const stack = [];
  const on = new Set();
  /** @type {Map<string, number>} */ const index = new Map();
  /** @type {Map<string, number>} */ const low = new Map();
  /** @type {string[][]} */ const out = [];
  const visit = (/** @type {string} */ v) => {
    index.set(v, idx); low.set(v, idx); idx++; stack.push(v); on.add(v);
    for (const w of [...(adj.get(v) ?? [])].sort(byText)) {
      if (!index.has(w)) { visit(w); low.set(v, Math.min(/** @type {number} */ (low.get(v)), /** @type {number} */ (low.get(w)))); }
      else if (on.has(w)) low.set(v, Math.min(/** @type {number} */ (low.get(v)), /** @type {number} */ (index.get(w))));
    }
    if (low.get(v) === index.get(v)) {
      /** @type {string[]} */ const comp = [];
      let w;
      do { w = /** @type {string} */ (stack.pop()); on.delete(w); comp.push(w); } while (w !== v);
      if (comp.length > 1) out.push(comp.sort(byText));
    }
  };
  for (const n of [...nodes].sort(byText)) if (!index.has(n)) visit(n);
  return out.sort((a, b) => byText(a[0], b[0]));
}

/**
 * A top-to-bottom order of the blocks of a cycle that minimises the witnesses of the edges pointing upward (the back
 * edges): exact for up to 14 blocks, a degree heuristic beyond. Ties resolve to the smaller block id, so the order is
 * the same on every run. It names the edges to look at first; it does not say the dependency is wrong.
 * @param {string[]} blocks @param {Map<string, number>} weight key `from\0to` -> witnesses
 * @returns {string[]}
 */
export function layering(blocks, weight) {
  const n = blocks.length;
  const w = (/** @type {string} */ a, /** @type {string} */ b) => weight.get(`${a}\0${b}`) ?? 0;
  if (n > 14) {
    return [...blocks].sort((a, b) => {
      const score = (/** @type {string} */ x) => blocks.reduce((s, y) => s + w(x, y) - w(y, x), 0);
      return score(b) - score(a) || byText(a, b);
    });
  }
  const full = (1 << n) - 1;
  const cost = new Array(1 << n).fill(Infinity);
  const last = new Array(1 << n).fill(-1);
  cost[0] = 0;
  for (let mask = 0; mask < full; mask++) {
    if (cost[mask] === Infinity) continue;
    for (let v = 0; v < n; v++) {
      if (mask & (1 << v)) continue;
      let add = 0;
      for (let u = 0; u < n; u++) if (mask & (1 << u)) add += w(blocks[v], blocks[u]);
      const next = mask | (1 << v);
      if (cost[mask] + add < cost[next]) { cost[next] = cost[mask] + add; last[next] = v; }
    }
  }
  /** @type {string[]} */
  const order = [];
  for (let mask = full; mask; mask &= ~(1 << last[mask])) order.unshift(blocks[last[mask]]);
  return order;
}

/**
 * @param {ConditionContext} ctx @param {Model} source the model with every provenance, for the redundancy of declared facts
 */
function measure(ctx, source) {
  const model = ctx.model;
  const d = /** @type {NonNullable<ConditionContext['derived']>} */ (ctx.derived);
  const cand = ctx.candidate;
  const ids = cand.blocks.map((b) => b.id);
  const blockSet = new Set(ids);
  const h0 = /** @type {import('./query.js').Hierarchy} */ (hierarchyOf(model, LOGICAL));
  const inScope = (/** @type {string} */ e) => e === cand.scope || ancestorsIn(h0, e).includes(cand.scope);
  const classOf = (/** @type {BaseFact} */ f) => kindInfo(model.meta, f.kind).class;
  /** @type {BaseFact[]} */ const internal = [];
  /** @type {BaseFact[]} */ const crossing = [];
  /** @type {BaseFact[]} */ const external = [];
  /** @type {BaseFact[]} */ const above = [];
  for (const f of ctx.facts) {
    const a = ctx.blockOf(f.from), b = ctx.blockOf(f.to);
    if (a !== null && b !== null) (a === b ? internal : crossing).push(f);
    else if (a !== null || b !== null) external.push(f);
    else if (inScope(f.from) && inScope(f.to)) above.push(f);
  }
  const count = (/** @type {BaseFact[]} */ fs) => ({ all: fs.length, static: fs.filter((f) => classOf(f) === 'static').length, runtime: fs.filter((f) => classOf(f) === 'runtime').length, none: fs.filter((f) => classOf(f) === 'none').length, dependency: fs.filter((f) => DEPENDENCY.has(classOf(f))).length });
  const counts = { internal: count(internal), crossing: count(crossing), external: count(external), attachedAboveGrain: count(above) };

  // Block edges of the crossing facts.
  /** @type {Map<string, {from: string, to: string, witnesses: string[], kinds: Record<string, number>, classes: Record<string, number>, contracted: string[], uncovered: string[]}>} */
  const edges = new Map();
  for (const f of crossing) {
    const a = /** @type {string} */ (ctx.blockOf(f.from)), b = /** @type {string} */ (ctx.blockOf(f.to));
    const k = `${a}\0${b}`;
    let e = edges.get(k);
    if (!e) { e = { from: a, to: b, witnesses: [], kinds: {}, classes: {}, contracted: [], uncovered: [] }; edges.set(k, e); }
    e.witnesses.push(f.id);
    e.kinds[f.kind] = (e.kinds[f.kind] ?? 0) + 1;
    e.classes[classOf(f)] = (e.classes[classOf(f)] ?? 0) + 1;
    (factContract(model, f) ? e.contracted : e.uncovered).push(f.id);
  }
  const edgeList = [...edges.values()].map((e) => ({ ...e, witnesses: e.witnesses.sort(byText), contracted: e.contracted.sort(byText), uncovered: e.uncovered.sort(byText), kinds: sortKeys(e.kinds), classes: sortKeys(e.classes) })).sort((x, y) => byText(`${x.from}\0${x.to}`, `${y.from}\0${y.to}`));

  // Cycles by class, with the back edges of a minimal layering.
  const cycles = CYCLE_CLASSES.map(([id, classes]) => {
    /** @type {Map<string, Set<string>>} */ const adj = new Map(ids.map((b) => [b, new Set()]));
    /** @type {Map<string, number>} */ const weight = new Map();
    /** @type {Map<string, string[]>} */ const wit = new Map();
    for (const f of crossing) {
      if (!/** @type {readonly string[]} */ (classes).includes(classOf(f))) continue;
      const a = /** @type {string} */ (ctx.blockOf(f.from)), b = /** @type {string} */ (ctx.blockOf(f.to));
      /** @type {Set<string>} */ (adj.get(a)).add(b);
      weight.set(`${a}\0${b}`, (weight.get(`${a}\0${b}`) ?? 0) + 1);
      if (!wit.has(`${a}\0${b}`)) wit.set(`${a}\0${b}`, []);
      /** @type {string[]} */ (wit.get(`${a}\0${b}`)).push(f.id);
    }
    const components = cyclicComponents(ids, adj).map((blocks) => {
      const order = layering(blocks, weight);
      const pos = new Map(order.map((b, i) => [b, i]));
      const inside = blocks.flatMap((a) => blocks.filter((b) => a !== b && weight.has(`${a}\0${b}`)).map((b) => ({ from: a, to: b, witnesses: [.../** @type {string[]} */ (wit.get(`${a}\0${b}`))].sort(byText) })));
      return { blocks, layering: order, edges: inside, backEdges: inside.filter((e) => /** @type {number} */ (pos.get(e.from)) > /** @type {number} */ (pos.get(e.to))) };
    });
    return { class: id, cyclic: components.length > 0, blocksInCycles: components.reduce((s, c) => s + c.blocks.length, 0), backEdgeWitnesses: components.reduce((s, c) => s + c.backEdges.reduce((t, e) => t + e.witnesses.length, 0), 0), components };
  });

  // Per block.
  const perBlock = cand.blocks.map((b) => {
    const out = crossing.filter((f) => ctx.blockOf(f.from) === b.id), inn = crossing.filter((f) => ctx.blockOf(f.to) === b.id);
    const inner = internal.filter((f) => ctx.blockOf(f.from) === b.id);
    const ext = external.filter((f) => ctx.blockOf(f.from) === b.id || ctx.blockOf(f.to) === b.id);
    const groups = d.interfaces[b.id]?.groups ?? [];
    const statuses = { transparent: 0, opaque: 0, unknown: 0 };
    for (const m of b.members) { const s = knowledgeOf(model, m)?.status; if (s) statuses[s]++; }
    const boundary = out.length + inn.length;
    return {
      id: b.id, members: b.members.length, internal: inner.length, out: out.length, in: inn.length, boundary, external: ext.length, cohesion: fraction(inner.length, inner.length + boundary),
      interface: { groups: groups.length, witnesses: uniq(groups.flatMap((g) => g.witnesses)).length, contracted: groups.filter((g) => g.contract !== null).length }, knowledge: statuses,
    };
  });

  // Contract coverage of the boundary interactions.
  const interactions = edgeList.length;
  const coverage = {
    facts: fraction(crossing.filter((f) => factContract(model, f)).length, crossing.length),
    dependencyFacts: fraction(crossing.filter((f) => DEPENDENCY.has(classOf(f)) && factContract(model, f)).length, crossing.filter((f) => DEPENDENCY.has(classOf(f))).length),
    blockPairs: { total: interactions, covered: edgeList.filter((e) => e.uncovered.length === 0).length, partial: edgeList.filter((e) => e.contracted.length && e.uncovered.length).length, uncovered: edgeList.filter((e) => e.contracted.length === 0).length },
  };

  // Redundancy: declared facts the code or another declaration already gives.
  const redundantIds = new Set(reconcile(source).diagnostics.filter((x) => x.code === 'reconcile.static-declared-redundant' && x.relationship).map((x) => /** @type {string} */ (x.relationship)));
  /** @type {Map<string, string[]>} */ const same = new Map();
  for (const f of ctx.facts) if (f.provenance === 'declared') { const k = `${f.from}\0${f.to}\0${f.kind}`; if (!same.has(k)) same.set(k, []); /** @type {string[]} */ (same.get(k)).push(f.id); }
  const duplicates = [...same.values()].filter((v) => v.length > 1).flatMap((v) => v.sort(byText).slice(1)).sort(byText);
  const scoped = new Set([...internal, ...crossing].map((f) => f.id));
  const crossingIds = new Set(crossing.map((f) => f.id));
  const redundantDeclared = ctx.facts.filter((f) => redundantIds.has(f.id) && scoped.has(f.id)).map((f) => f.id).sort(byText);
  const redundancy = {
    basis: redundantIds.size || /** @type {any} */ (source).extraction ? 'extracted facts attached' : 'declared facts only',
    declaredDuplicatedByExtraction: redundantDeclared, declaredDuplicatedByDeclaration: duplicates.filter((x) => scoped.has(x)),
    onBoundary: redundantDeclared.filter((x) => crossingIds.has(x)).length + duplicates.filter((x) => crossingIds.has(x)).length,
  };

  // Knowledge and provenance mix.
  const statuses = { transparent: 0, opaque: 0, unknown: 0 };
  for (const u of cand.universe) { const s = knowledgeOf(model, u)?.status; if (s) statuses[s]++; }
  /** @type {Record<string, number>} */ const prov = {};
  for (const f of crossing) prov[f.provenance] = (prov[f.provenance] ?? 0) + 1;

  const sizes = cand.blocks.map((b) => b.members.length);
  const measurements = {
    blocks: { count: cand.blocks.length, grainElements: cand.universe.length, singletons: sizes.filter((s) => s === 1).length, largest: Math.max(0, ...sizes), smallest: sizes.length ? Math.min(...sizes) : 0 },
    facts: counts,
    boundarySize: { crossing: crossing.length, external: external.length },
    cohesion: { overall: fraction(internal.length, internal.length + crossing.length), dependency: fraction(counts.internal.dependency, counts.internal.dependency + counts.crossing.dependency), perBlock: perBlock.map((p) => ({ id: p.id, ...p.cohesion })) },
    coupling: { connectedBlockPairs: interactions, density: fraction(interactions, ids.length * (ids.length - 1)), perBlock: perBlock.map((p) => ({ id: p.id, out: p.out, in: p.in })) },
    cycles: cycles.map(({ class: c, cyclic, blocksInCycles, backEdgeWitnesses, components }) => ({ class: c, cyclic, components: components.length, blocksInCycles, backEdgeWitnesses })),
    interface: { groups: perBlock.reduce((s, p) => s + p.interface.groups, 0), largest: Math.max(0, ...perBlock.map((p) => p.interface.groups)), perBlock: perBlock.map((p) => ({ id: p.id, groups: p.interface.groups, witnesses: p.interface.witnesses })) },
    contractCoverage: coverage,
    redundancy,
    knowledge: { elements: statuses, boundaryFactProvenance: sortKeys(prov), perBlock: perBlock.map((p) => ({ id: p.id, ...p.knowledge })) },
  };
  const evidence = {
    boundaries: edgeList.map((e) => ({ from: e.from, to: e.to, witnesses: e.witnesses, kinds: e.kinds, classes: e.classes, uncoveredByContract: e.uncovered })),
    cycles: cycles.filter((c) => c.cyclic).map((c) => ({ class: c.class, components: c.components })),
    uncoveredContracts: edgeList.filter((e) => e.uncovered.length).map((e) => ({ from: e.from, to: e.to, facts: e.uncovered })),
    scopeBoundary: perBlock.filter((p) => p.external).map((p) => ({ block: p.id, facts: uniq(external.filter((f) => ctx.blockOf(f.from) === p.id || ctx.blockOf(f.to) === p.id).map((f) => f.id)) })),
  };
  return { measurements, evidence };
}

/** @param {Record<string, number>} o */
function sortKeys(o) { return Object.fromEntries(Object.keys(o).sort(byText).map((k) => [k, o[k]])); }

// ---------------------------------------------------------------------------------------------
// Evaluation

/**
 * Evaluate one candidate: resolve it, run the registered validity conditions, and measure it when it is valid. Pure; the
 * same inputs give the same report, key for key.
 * @param {Model} model @param {any} raw
 * @param {{scope?: string, grain?: 'children'|'leaves'|'modules', provenance?: string[]|null, conditions?: ValidityCondition[], evidence?: boolean}} [opts]
 */
export function evaluateCandidate(model, raw, opts = {}) {
  const view = factView(model, opts.provenance);
  const cand = resolveCandidate(view, raw, opts);
  const registry = opts.conditions ?? VALIDITY_CONDITIONS;
  const v1Failed = cand.problems.length > 0;
  const level = v1Failed ? null : levelOfCandidate(view, cand);
  const blockSet = new Set(cand.blocks.map((b) => b.id));
  const blockOf = (/** @type {string} */ e) => { const b = level?.map.get(e); return b !== undefined && blockSet.has(b) ? b : null; };
  /** @type {ConditionContext} */
  const ctx = { model: view, candidate: cand, level, derived: level ? deriveLevel(view, level) : null, facts: baseFacts(view).facts, blockOf, results: {} };
  const conditions = registry.map((c) => {
    const blocked = (c.needs ?? []).filter((n) => ctx.results[n] !== 'pass');
    if (blocked.length) { ctx.results[c.id] = 'skipped'; return { id: c.id, title: c.title, status: /** @type {'skipped'} */ ('skipped'), reason: `${blocked.join(', ')} did not pass.`, failures: /** @type {Failure[]} */ ([]), detail: /** @type {any} */ (null) }; }
    const out = c.check(ctx);
    const outcome = /** @type {ConditionOutcome} */ (Array.isArray(out) ? { failures: out } : out);
    const failures = outcome.failures.map((f) => ({ ...f, witnesses: uniq(f.witnesses) })).sort((a, b) => byText(`${a.code}|${a.witnesses.join(',')}`, `${b.code}|${b.witnesses.join(',')}`));
    // A condition that does not apply is not a pass: later conditions that need it are still free to run.
    const na = failures.length === 0 && typeof outcome.notApplicable === 'string';
    ctx.results[c.id] = failures.length ? 'fail' : 'pass';
    return { id: c.id, title: c.title, status: /** @type {'pass'|'fail'|'not-applicable'} */ (failures.length ? 'fail' : na ? 'not-applicable' : 'pass'), ...(na ? { reason: /** @type {string} */ (outcome.notApplicable) } : {}), failures, detail: outcome.detail ?? null };
  });
  const registered = new Set(registry.map((c) => c.id));
  const pending = BEHAVIOURAL_CONDITIONS.filter((id) => !registered.has(id));
  for (const id of pending) conditions.push({ id, title: 'Behavioural condition', status: /** @type {any} */ ('not-evaluated'), reason: 'No evaluator is registered for it (registerValidityCondition).', failures: [], detail: null });
  const failed = conditions.filter((c) => c.status === 'fail').map((c) => c.id);
  const status = failed.length ? 'invalid' : pending.length ? 'structurally-valid' : 'valid';
  const measured = status === 'invalid' || !ctx.derived ? null : measure(ctx, model);
  return {
    id: cand.id, name: cand.name, source: cand.source, scope: cand.scope, grain: cand.grain, from: cand.from, note: cand.note,
    status, failedConditions: failed, notEvaluated: pending, notApplicable: conditions.filter((c) => c.status === 'not-applicable').map((c) => c.id), conditions,
    blocks: cand.blocks.map((b) => ({ id: b.id, name: b.name, members: b.members, existing: b.existing })), placedByRest: cand.placedByRest,
    measurements: measured?.measurements ?? null,
    evidence: opts.evidence === false ? null : measured?.evidence ?? null,
    acceptance: status === 'invalid' ? null : acceptanceOf(model, cand),
    notes: [NOT_MEANING, ...(pending.length ? [`Not evaluated: ${pending.join(', ')}. The candidate is checked against the structural conditions only.`] : []),
      ...conditions.filter((c) => c.status === 'not-applicable').map((c) => `${c.id} does not apply: ${/** @type {any} */ (c).reason}`)],
  };
}

/** @typedef {ReturnType<typeof evaluateCandidate>} CandidateReport */

/**
 * What accepting a candidate records, described and never applied here (acceptance is a transaction a person decides
 * on, invariant I4): the components the blocks that are no element yet need, one named hierarchy and two cuts of it,
 * as the operations of that transaction.
 *
 * The hierarchy places every component where the logical hierarchy places it, except that the blocks sit under the
 * scope and hold their members: it is a complete alternative to the logical hierarchy, so the application can draw it
 * from its roots, and nothing the candidate does not regroup moves. Module elements follow their component in every
 * hierarchy: a candidate of the `modules` grain cannot be recorded this way and is refused (`refusal`), and the module
 * elements a candidate of another grain places in blocks (the scope's own modules, which are its children too) stay with
 * their component, are listed in `unrecorded`, and stand as blocks of their own at the cut; so do the elements between the
 * scope and the grain whose members all moved (`emptied`). The cuts are
 * `<id>-top`, the hierarchy opened down to the scope (the scope is one block), and `<id>-cut`, the scope opened into the
 * blocks of the candidate.
 * @param {Model} model @param {Resolved} cand
 */
export function acceptanceOf(model, cand) {
  const elements = elementsOf(model);
  const h0 = /** @type {import('./query.js').Hierarchy} */ (hierarchyOf(model, LOGICAL));
  const fresh = cand.blocks.filter((b) => !elements.has(b.id));
  const refusal = cand.grain === 'modules' ? 'A module element is a member of the component that declares it in every hierarchy, so blocks of module elements cannot be recorded as a hierarchy.'
    : cand.id === LOGICAL ? `"${LOGICAL}" is the logical hierarchy's id; give the candidate another id.` : null;
  /** @type {Map<string, string>} */
  const parent = new Map();
  for (const c of model.byKind.component ?? []) { const p = c.data.parent; if (typeof p === 'string' && p !== c.id && elements.has(p)) parent.set(c.id, p); }
  /** @type {{element: string, block: string}[]} */
  const unrecorded = [];
  for (const b of cand.blocks) {
    parent.set(b.id, cand.scope);
    if (b.self) continue;
    for (const m of b.members) {
      // A module element is a member of its declaring component in every hierarchy and no group can move it.
      if (elements.get(m)?.kind === 'module') unrecorded.push({ element: m, block: b.id });
      else parent.set(m, b.id);
    }
  }
  // Elements between the scope and the grain that the candidate leaves with nothing in them (their members now sit in blocks):
  // they stay where the logical hierarchy puts them, as empty blocks of the cut.
  const blockIds = new Set(cand.blocks.map((b) => b.id));
  const emptied = [...elements.keys()].filter((e) => !blockIds.has(e) && (h0.children.get(e) ?? []).some((k) => elements.get(k)?.kind !== 'module')
    && (h0.children.get(e) ?? []).every((k) => elements.get(k)?.kind === 'module' || parent.get(k) !== e) && parent.get(e) !== undefined).sort(byText);
  /** @type {Map<string, string[]>} */
  const byParent = new Map();
  for (const [m, p] of parent) { if (!byParent.has(p)) byParent.set(p, []); /** @type {string[]} */ (byParent.get(p)).push(m); }
  const groups = [...byParent].sort((x, y) => byText(x[0], y[0])).map(([p, members]) => ({ parent: p, members: members.sort(byText) }));
  const above = ancestorsIn(h0, cand.scope).reverse();
  const hierarchy = {
    id: cand.id, name: cand.name,
    description: `The candidate decomposition "${cand.id}" of "${cand.scope}", accepted: ${cand.blocks.length} blocks over the ${cand.grain} of the scope (source: ${cand.source}). Every other element is placed as the logical hierarchy places it.${unrecorded.length ? ` ${unrecorded.length} module elements the candidate placed in blocks stay with the component that declares them, as a module element does in every hierarchy.` : ''}`,
    groups,
  };
  const cuts = [
    { id: `${cand.id}-top`, name: `${cand.name}: scope as one block`, hierarchy: cand.id, expand: above },
    { id: `${cand.id}-cut`, name: `${cand.name}: blocks`, hierarchy: cand.id, expand: [...above, cand.scope] },
  ];
  const components = fresh.map((b) => ({
    id: b.id, name: b.name, category: 'logical', parent: cand.scope,
    purpose: `A block of the accepted decomposition "${cand.id}" of "${cand.scope}": it groups ${b.members.join(', ')}.`,
  }));
  /** @type {any[]} */
  const operations = refusal ? [] : [
    ...components.map((data) => ({ type: 'CreateEntity', kind: 'component', data })),
    { type: 'CreateEntity', kind: 'hierarchy', data: hierarchy },
    ...cuts.map((data) => ({ type: 'CreateEntity', kind: 'cut', data })),
  ];
  return {
    applied: false, refusal, hierarchy, cuts, components, unrecorded: unrecorded.sort((x, y) => byText(x.element, y.element)), emptied, operations,
    note: 'Described, not applied. A person accepts a candidate through a transaction (accept-decomposition, or these operations through apply) that records these components, this hierarchy and these cuts.',
  };
}

/**
 * Accept a candidate: evaluate it, refuse it unless every validity condition holds, and apply the operations of its
 * acceptance as one transaction of the project (so it is one entry of the undo history). The decision is the caller's: a
 * measurement never reaches this function (invariant I4).
 * @param {import('./project.js').Project} project @param {any} raw
 * @param {Parameters<typeof evaluateCandidate>[2] & {label?: string, origin?: string, dryRun?: boolean}} [opts]
 * @returns {{ok: boolean, code?: string, message?: string, report: CandidateReport, operations: any[], transaction: any}}
 */
export function acceptCandidate(project, raw, opts = {}) {
  const model = /** @type {Model} */ (project.model);
  const report = evaluateCandidate(model, raw, opts);
  const refuse = (/** @type {string} */ code, /** @type {string} */ message) => ({ ok: false, code, message, report, operations: /** @type {any[]} */ ([]), transaction: null });
  if (report.status !== 'valid') {
    const why = report.status === 'invalid' ? `${report.failedConditions.join(', ')} failed` : `${report.notEvaluated.join(', ')} not evaluated`;
    return refuse('accept.not-valid', `Candidate "${report.id}" is ${report.status} (${why}); only a candidate for which every validity condition holds can be accepted.`);
  }
  const acceptance = /** @type {NonNullable<CandidateReport['acceptance']>} */ (report.acceptance);
  if (acceptance.refusal) return refuse('accept.unrecordable', acceptance.refusal);
  const ops = acceptance.operations;
  if (opts.dryRun) return { ok: true, report, operations: ops, transaction: null };
  const tx = project.apply(ops, { label: opts.label ?? `Accept decomposition ${report.id}`, origin: opts.origin ?? 'cli' });
  if (!tx.ok) return { ok: false, code: tx.code ?? 'accept.rejected', message: tx.message, report, operations: ops, transaction: tx };
  return { ok: true, report, operations: ops, transaction: tx };
}

/**
 * Evaluate several candidates and put their measurements side by side. The columns are in the order given; no order
 * of merit exists here, and a candidate that is not valid has no measurements.
 * @param {Model} model @param {any[]} candidates @param {Parameters<typeof evaluateCandidate>[2]} [opts]
 */
export function compareCandidates(model, candidates, opts = {}) {
  const reports = candidates.map((c) => evaluateCandidate(model, c, opts));
  const m = (/** @type {CandidateReport} */ r) => r.measurements;
  /** @type {[string, string, (r: CandidateReport) => any][]} */
  const rows = [
    ['status', 'Validity', (r) => r.status],
    ['blocks', 'Blocks', (r) => m(r)?.blocks.count ?? null],
    ['largest-block', 'Members of the largest block', (r) => m(r)?.blocks.largest ?? null],
    ['internal', 'Facts internal to a block', (r) => m(r)?.facts.internal.all ?? null],
    ['crossing', 'Facts crossing blocks (boundary size)', (r) => m(r)?.facts.crossing.all ?? null],
    ['internal-dependency', 'Dependency-class facts internal to a block', (r) => m(r)?.facts.internal.dependency ?? null],
    ['crossing-dependency', 'Dependency-class facts crossing blocks', (r) => m(r)?.facts.crossing.dependency ?? null],
    ['cohesion', 'Cohesion (internal / (internal + crossing))', (r) => m(r)?.cohesion.overall.value ?? null],
    ['coupled-pairs', 'Ordered block pairs with a crossing fact', (r) => m(r)?.coupling.connectedBlockPairs ?? null],
    ['cycles-static', 'Cycles among blocks, static class', (r) => m(r)?.cycles.find((c) => c.class === 'static')?.components ?? null],
    ['cycles-runtime', 'Cycles among blocks, runtime class', (r) => m(r)?.cycles.find((c) => c.class === 'runtime')?.components ?? null],
    ['cycles-dependency', 'Cycles among blocks, static and runtime together', (r) => m(r)?.cycles.find((c) => c.class === 'dependency')?.components ?? null],
    ['back-edge-witnesses', 'Facts on the back edges of dependency cycles', (r) => m(r)?.cycles.find((c) => c.class === 'dependency')?.backEdgeWitnesses ?? null],
    ['interface-groups', 'Interface groups over all blocks', (r) => m(r)?.interface.groups ?? null],
    ['interface-largest', 'Interface groups of the largest interface', (r) => m(r)?.interface.largest ?? null],
    ['contract-coverage', 'Crossing facts typed by a contract', (r) => m(r)?.contractCoverage.facts.value ?? null],
    ['redundant-on-boundary', 'Redundant declared facts on the boundary', (r) => m(r)?.redundancy.onBoundary ?? null],
    ['opaque-elements', 'Opaque grain elements', (r) => m(r)?.knowledge.elements.opaque ?? null],
    ['unknown-elements', 'Grain elements of unknown knowledge', (r) => m(r)?.knowledge.elements.unknown ?? null],
  ];
  return {
    candidates: reports.map((r) => r.id),
    rows: rows.map(([id, label, f]) => ({ id, label, values: Object.fromEntries(reports.map((r) => [r.id, f(r)])) })),
    reports,
    note: NOT_MEANING,
  };
}

// ---------------------------------------------------------------------------------------------
// Generation

/** Pairs of grain elements joined by a fact, with the fact. @param {Model} model @param {NonNullable<ReturnType<typeof grainOf>>} g */
function grainEdges(model, g) {
  const { facts } = baseFacts(model);
  /** @type {{f: BaseFact, a: string, b: string}[]} */
  const out = [];
  for (const f of facts) {
    const a = g.map.get(f.from), b = g.map.get(f.to);
    if (a !== undefined && b !== undefined && g.universe.includes(a) && g.universe.includes(b) && a !== b) out.push({ f, a, b });
  }
  return out;
}

/** Connected components of the universe under undirected edges. @param {string[]} universe @param {{a: string, b: string}[]} edges */
function components(universe, edges) {
  const parent = new Map(universe.map((u) => [u, u]));
  const find = (/** @type {string} */ x) => { let r = x; while (parent.get(r) !== r) r = /** @type {string} */ (parent.get(r)); parent.set(x, r); return r; };
  for (const e of edges) { const x = find(e.a), y = find(e.b); if (x !== y) parent.set(byText(x, y) < 0 ? y : x, byText(x, y) < 0 ? x : y); }
  /** @type {Map<string, string[]>} */
  const groups = new Map();
  for (const u of universe) { const r = find(u); if (!groups.has(r)) groups.set(r, []); /** @type {string[]} */ (groups.get(r)).push(u); }
  return [...groups.values()].map((g) => g.sort(byText)).sort((x, y) => byText(x[0], y[0]));
}

/** @param {string} s */
const slug = (s) => s.toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-+|-+$/g, '') || 'block';

/**
 * Blocks from groups of grain elements; a group of one is that element.
 * @param {Model} model @param {string[][]} groups @param {(group: string[]) => string} name
 * @returns {CandidateBlock[]}
 */
function blocksOfGroups(model, groups, name) {
  const elements = elementsOf(model);
  const used = new Set();
  return groups.map((members) => {
    if (members.length === 1) return { id: members[0], members };
    let id = name(members);
    while (elements.has(id) || used.has(id)) id += '-block';
    used.add(id);
    return { id, members };
  });
}

/** The partition of a candidate, as text, to drop one that equals an earlier one. @param {{blocks: CandidateBlock[]}} c */
const partitionKey = (c) => c.blocks.map((b) => [...b.members].sort(byText).join('\u0001')).sort(byText).join('\u0002');

/**
 * Candidates for a scope drawn from the established semantics. `bases` are candidates given as data that refinements are
 * also read off. What a source could not produce is listed in `skipped` with the reason.
 * @param {Model} model
 * @param {{scope?: string, grain?: 'children'|'leaves'|'modules', sources?: string[], dirDepth?: number, provenance?: string[]|null, bases?: any[]}} [opts]
 */
export function generateCandidates(model, opts = {}) {
  const view = factView(model, opts.provenance);
  const scope = opts.scope ?? view.system?.id ?? '';
  const grain = opts.grain ?? 'children';
  const want = new Set(opts.sources?.length ? opts.sources : SOURCES);
  const g = grainOf(view, scope, grain);
  /** @type {{source: string, reason: string}[]} */
  const skipped = [];
  /** @type {Candidate[]} */
  const out = [];
  if (!g || !g.universe.length) return { scope, grain, universe: [], candidates: out, skipped: [{ source: 'all', reason: g ? `"${scope}" has no ${grain} to place.` : `"${scope}" is not an element.` }] };
  const elements = elementsOf(view);
  const edges = grainEdges(view, g);
  const mk = (/** @type {string} */ id, /** @type {string} */ name, /** @type {string} */ source, /** @type {CandidateBlock[]} */ blocks, /** @type {any} */ extra = {}) => ({ id, name, source, scope, grain, blocks, ...extra });
  const add = (/** @type {Candidate} */ c) => {
    const dup = out.find((o) => partitionKey(o) === partitionKey(c));
    if (dup) skipped.push({ source: c.source ?? '', reason: `"${c.id}" places the elements as "${dup.id}" does.` });
    else out.push(c);
  };

  // The declared hierarchy: each grain element in the child of the scope that holds it.
  const declaredOf = (/** @type {string} */ u) => ancestorsInclusive(g.h, u, scope);
  /** @type {Map<string, string[]>} */
  const byTop = new Map();
  for (const u of g.universe) { const t = declaredOf(u); if (!byTop.has(t)) byTop.set(t, []); /** @type {string[]} */ (byTop.get(t)).push(u); }
  const declared = mk(`${slug(scope)}-declared`, `The declared hierarchy of ${scope}`, 'declared', [...byTop].sort((a, b) => byText(a[0], b[0])).map(([id, members]) => ({ id, members: members.sort(byText) })));
  if (want.has('declared')) add(declared);

  // Module directories (extracted module paths, M5).
  if (want.has('directory')) {
    const depth = opts.dirDepth ?? 2;
    const decls = moduleDeclarations(view);
    const facts = /** @type {any} */ (view).extraction?.facts?.files;
    /** @type {Map<string, string[]>} */
    const dirsOf = new Map();
    for (const d of decls) {
      const owner = g.map.get(d.id) ?? g.map.get(d.component);
      if (owner === undefined) continue;
      const paths = d.path.endsWith('/') && Array.isArray(facts) ? facts.map((/** @type {any} */ f) => f.path).filter((/** @type {string} */ p) => p.startsWith(d.path)) : [d.path];
      for (const p of paths.length ? paths : [d.path]) {
        const segs = (p.endsWith('/') ? p.slice(0, -1) : p.split('/').slice(0, -1).join('/')).split('/').filter(Boolean).slice(0, depth);
        if (!dirsOf.has(owner)) dirsOf.set(owner, []);
        /** @type {string[]} */ (dirsOf.get(owner)).push(segs.join('/') || '(root)');
      }
    }
    /** @type {Map<string, string[]>} */
    const byDir = new Map();
    for (const u of g.universe) {
      const ds = dirsOf.get(u) ?? [];
      /** @type {Map<string, number>} */
      const n = new Map();
      for (const x of ds) n.set(x, (n.get(x) ?? 0) + 1);
      const best = [...n].sort((a, b) => b[1] - a[1] || byText(a[0], b[0]))[0]?.[0] ?? '(no modules)';
      if (!byDir.has(best)) byDir.set(best, []);
      /** @type {string[]} */ (byDir.get(best)).push(u);
    }
    if (byDir.size < 2) skipped.push({ source: 'directory', reason: `the ${grain} of "${scope}" lie in one directory (or have no module paths).` });
    else add(mk(`${slug(scope)}-directories`, `${scope} by the directory of its modules (depth ${depth})`, 'directory', blocksOfGroups(view, [...byDir.values()].map((m) => m.sort(byText)), (m) => `dir-${slug([...byDir].find(([, v]) => v.includes(m[0]))?.[0] ?? m[0])}`), { note: 'A component is placed in the directory most of its module paths lie in (the alphabetically first on a tie).' }));
  }

  // Condensation of the cycles of the dependency classes.
  if (want.has('cycles')) {
    const dep = edges.filter((e) => DEPENDENCY.has(kindInfo(view.meta, e.f.kind).class));
    /** @type {Map<string, Set<string>>} */ const adj = new Map(g.universe.map((u) => [u, new Set()]));
    for (const e of dep) /** @type {Set<string>} */ (adj.get(e.a)).add(e.b);
    const sccs = cyclicComponents(g.universe, adj);
    if (!sccs.length) skipped.push({ source: 'cycles', reason: `no dependency cycle among the ${grain} of "${scope}".` });
    else {
      const inScc = new Set(sccs.flat());
      add(mk(`${slug(scope)}-cycles-condensed`, `${scope} with each dependency cycle one block`, 'cycles', blocksOfGroups(view, [...sccs, ...g.universe.filter((u) => !inScc.has(u)).map((u) => [u])].sort((a, b) => byText(a[0], b[0])), (m) => `cycle-${slug(m[0])}`)));
    }
  }

  // Regions bounded by contracts: elements joined by facts no contract types lie together.
  if (want.has('contracts')) {
    if (!edges.some((e) => factContract(view, e.f))) skipped.push({ source: 'contracts', reason: `no fact inside "${scope}" is typed by a contract.` });
    else add(mk(`${slug(scope)}-contract-regions`, `${scope} in regions whose only mutual facts are contract-typed`, 'contracts', blocksOfGroups(view, components(g.universe, edges.filter((e) => !factContract(view, e.f))), (m) => `region-${slug(m[0])}`)));
  }

  // Regions bounded by connectors: elements joined without passing through a connector.
  if (want.has('connectors')) {
    const conn = g.universe.filter((u) => isConnector(elements.get(u)?.entity ?? undefined));
    const cs = new Set(conn);
    if (!conn.length) skipped.push({ source: 'connectors', reason: `no connector element among the ${grain} of "${scope}".` });
    else if (!edges.some((e) => cs.has(e.a) || cs.has(e.b))) skipped.push({ source: 'connectors', reason: `no fact inside "${scope}" passes through a connector, so connectors bound no region.` });
    else {
      const rest = g.universe.filter((u) => !cs.has(u));
      add(mk(`${slug(scope)}-connector-regions`, `${scope} in regions that meet only through connectors`, 'connectors', blocksOfGroups(view, [...conn.map((c) => [c]), ...components(rest, edges.filter((e) => !cs.has(e.a) && !cs.has(e.b)))].sort((a, b) => byText(a[0], b[0])), (m) => `connected-${slug(m[0])}`)));
    }
  }

  // Refinements: split, merge and move, read off the facts of each base.
  if (want.has('refinement')) {
    const bases = [declared, ...(opts.bases ?? []).filter((b) => b && typeof b === 'object')];
    for (const raw of bases) {
      const base = resolveCandidate(view, { scope, grain, ...raw }, { scope, grain });
      if (base.problems.length) { skipped.push({ source: 'refinement', reason: `base "${base.id}" is not a valid partition: ${base.problems[0].code}.` }); continue; }
      if (base.blocks.every((b) => b.members.length === 1)) { skipped.push({ source: 'refinement', reason: `base "${base.id}" has only single-element blocks, so there is no block to split, merge or move within.` }); continue; }
      const blockOf = new Map(base.blocks.flatMap((b) => b.members.map((m) => [m, b.id])));
      const members = (/** @type {string} */ id) => /** @type {any} */ (base.blocks.find((b) => b.id === id)).members;
      const asBlocks = (/** @type {Map<string, string[]>} */ m) => [...m].filter(([, v]) => v.length).sort((a, b) => byText(a[0], b[0])).map(([id, v]) => ({ id, members: v.sort(byText) }));
      const fresh = () => new Map(base.blocks.map((b) => [b.id, [...b.members]]));
      const dep = edges.filter((e) => DEPENDENCY.has(kindInfo(view.meta, e.f.kind).class));
      // move: an element with more dependency facts to one other block than to its own.
      for (const u of g.universe) {
        /** @type {Map<string, number>} */ const n = new Map();
        for (const e of dep) { const other = e.a === u ? e.b : e.b === u ? e.a : null; if (other === null) continue; const b = /** @type {string} */ (blockOf.get(other)); n.set(b, (n.get(b) ?? 0) + 1); }
        const own = /** @type {string} */ (blockOf.get(u));
        const best = [...n].filter(([b]) => b !== own).sort((a, b) => b[1] - a[1] || byText(a[0], b[0]))[0];
        if (!best || best[1] <= (n.get(own) ?? 0)) continue;
        const m = fresh();
        /** @type {string[]} */ (m.get(own)).splice(/** @type {string[]} */ (m.get(own)).indexOf(u), 1);
        /** @type {string[]} */ (m.get(best[0])).push(u);
        add(mk(`${base.id}~move-${slug(u)}-to-${slug(best[0])}`, `${base.name}, with ${u} moved to ${best[0]}`, 'refinement', asBlocks(m), { from: { candidate: base.id, op: { move: u, from: own, to: best[0] } } }));
      }
      // merge: the blocks of a dependency cycle between blocks become one.
      /** @type {Map<string, Set<string>>} */ const badj = new Map(base.blocks.map((b) => [b.id, new Set()]));
      for (const e of dep) { const x = /** @type {string} */ (blockOf.get(e.a)), y = /** @type {string} */ (blockOf.get(e.b)); if (x !== y) /** @type {Set<string>} */ (badj.get(x)).add(y); }
      for (const comp of cyclicComponents(base.blocks.map((b) => b.id), badj)) {
        const m = fresh();
        const into = comp.join('+');
        const all = comp.flatMap((id) => /** @type {string[]} */ (m.get(id)));
        for (const id of comp) m.delete(id);
        m.set(elements.has(into) ? `${into}-block` : into, all);
        add(mk(`${base.id}~merge-${slug(comp.join('-'))}`, `${base.name}, with ${comp.join(', ')} merged`, 'refinement', asBlocks(m), { from: { candidate: base.id, op: { merge: comp } } }));
      }
      // split: a block whose members fall apart into unconnected parts.
      for (const b of base.blocks) {
        if (b.members.length < 2) continue;
        const inner = edges.filter((e) => blockOf.get(e.a) === b.id && blockOf.get(e.b) === b.id);
        const parts = components(members(b.id), inner);
        if (parts.length < 2) continue;
        const m = fresh();
        m.delete(b.id);
        parts.forEach((p, i) => m.set(p.length === 1 && !elements.has(b.id) ? p[0] : `${b.id}-${i + 1}`, p));
        add(mk(`${base.id}~split-${slug(b.id)}`, `${base.name}, with ${b.id} split into its unconnected parts`, 'refinement', asBlocks(m), { from: { candidate: base.id, op: { split: b.id, into: parts } } }));
      }
    }
  }
  return { scope, grain, universe: g.universe, candidates: out.sort((a, b) => byText(a.id, b.id)), skipped: skipped.sort((a, b) => byText(a.source + a.reason, b.source + b.reason)) };
}

/** The ancestor-or-self of an element that is a child of the scope (the scope's declared block). @param {import('./query.js').Hierarchy} h @param {string} e @param {string} scope */
function ancestorsInclusive(h, e, scope) {
  let cur = e;
  while (h.parent.get(cur) !== undefined && h.parent.get(cur) !== scope) cur = /** @type {string} */ (h.parent.get(cur));
  return cur;
}

/**
 * Candidates given as data: a list, an object with `candidates`, or one candidate.
 * @param {any} doc @returns {any[]}
 */
export function candidatesOfData(doc) {
  if (Array.isArray(doc)) return doc;
  if (doc && Array.isArray(doc.candidates)) return doc.candidates.map((/** @type {any} */ c) => ({ scope: doc.scope, grain: doc.grain, rest: undefined, ...c }));
  return doc && typeof doc === 'object' ? [doc] : [];
}
