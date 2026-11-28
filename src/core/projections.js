// Projections: derive a SceneModel (flat nodes and edges) from the canonical
// semantic model. A view is never a separate dataset; every node and edge is
// backed by a real entity. Positions are decided elsewhere (layout.js).

import { ancestorsOf, entityLabel, componentsFor, elementsOf, hierarchyOf, ancestorsIn, cutBlocksOf, knowledgeOf, LOGICAL } from './query.js';
import {
  cutForCollapse, deriveModel, restrictInteraction, baseFacts, endpointElement, cutOfExpanded, expandedOfCut, declaredCutWithBlocks,
  pathSummaries, blocksWithoutPurpose,
} from './abstraction.js';
import { own } from './own.js';
import { kindInfo } from './interactions.js';
import { dataFindings, sourcesOf } from './data-model.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').SceneModel} SceneModel */
/** @typedef {import('./types.js').SceneNode} SceneNode */
/** @typedef {import('./types.js').SceneEdge} SceneEdge */
/** @typedef {import('./abstraction.js').DerivedModel} DerivedModel */

/**
 * @typedef {Object} ProjectionContext
 * @property {{hierarchy: string, expanded: string[]}|null} [cut]  a structural view's interactive cut: the hierarchy and the elements
 *   the viewer has expanded (src/core/abstraction.js, cutOfExpanded); without it the view's default cut
 * @property {Set<string>} [collapsed]  a legacy collapse set (cutForCollapse), used when no cut is given
 * @property {Set<string>} [hidden]
 * @property {{claimId: string, result: any}[]} [levelClaims]  claims stated at a cut, evaluated at this scene's cut
 * @property {string|null} [isolate]
 * @property {string|null} [focusClaim]
 * @property {string|null} [focusScenario]
 * @property {string|null} [focusEntity]
 * @property {any[]} [claimResults]
 * @property {any} [trace]
 * @property {number} [stepIndex]
 */

/** @type {Map<string, (model: Model, view: any, ctx: ProjectionContext) => SceneModel>} */
const registry = new Map();

const PRESENTATION_NOTE = 'Position and distance are presentation only; they carry no architectural meaning.';

const IMPLEMENTATION_COLORS = {
  manual: ['slate', 'Manual'],
  'model-configured': ['blue', 'Model-configured'],
  'partially-generated': ['violet', 'Partially generated'],
  generated: ['amber', 'Generated'],
  'not-implemented': ['red', 'Not implemented'],
};
const ZONE_PALETTE = ['blue', 'amber', 'teal', 'violet', 'rose', 'green', 'steel'];
const CLAIM_COLORS = { proved: 'blue', verified: 'green', supported: 'teal', violated: 'red', inconclusive: 'amber', 'not-evaluated': 'neutral' };
const CLAIM_STATUS_LABELS = { proved: 'proved', verified: 'verified', supported: 'supported', violated: 'violated', inconclusive: 'inconclusive', 'not-evaluated': 'not evaluated' };

/**
 * Register (or replace) a projection by name. `opts.available` limits its implicit view to models it returns true for.
 * @param {string} name @param {(model: Model, view: any, ctx: ProjectionContext) => SceneModel} fn
 * @param {{available?: (model: Model) => boolean}} [opts]
 */
export function registerProjection(name, fn, opts = {}) {
  registry.set(name, fn);
  if (opts.available) availability.set(name, opts.available);
  else availability.delete(name);
}

/** Projections whose implicit view is listed only when the model has something for them. @type {Map<string, (model: Model) => boolean>} */
const availability = new Map();

/**
 * Declared views in order, then an implicit view for each projection type
 * that has no declared view.
 * @param {Model} model
 * @returns {{id:string, name:string, projection:string, description:string, declared:boolean}[]}
 */
export function listViews(model) {
  const out = (model.byKind.view ?? []).map((v) => ({
    id: v.id,
    name: typeof v.data.name === 'string' ? v.data.name : v.id,
    projection: String(v.data.projection),
    description: typeof v.data.description === 'string' ? v.data.description : '',
    declared: true,
  }));
  const used = new Set(out.map((v) => v.projection));
  for (const name of registry.keys()) {
    if (used.has(name)) continue;
    if (availability.has(name) && !availability.get(name)?.(model)) continue;
    out.push({ id: name, name: name.charAt(0).toUpperCase() + name.slice(1), projection: name, description: '', declared: false });
  }
  return out;
}

/**
 * Project the model into a scene.
 * @param {Model} model @param {string} viewId @param {ProjectionContext} [ctx]
 * @returns {SceneModel}
 */
export function project(model, viewId, ctx = {}) {
  const views = listViews(model);
  const info = views.find((v) => v.id === viewId) ?? views[0];
  if (!info) return { viewId: String(viewId), projection: '', nodes: [], edges: [], legend: [], notes: ['No views are available.'] };
  const entity = model.entities.get(info.id);
  const view = info.declared && entity && entity.kind === 'view' ? { ...entity.data, id: info.id } : { id: info.id, name: info.name, projection: info.projection };
  const fn = registry.get(info.projection);
  if (!fn) return { viewId: info.id, projection: info.projection, nodes: [], edges: [], legend: [], notes: [`No projection named "${info.projection}" is registered.`] };
  const scene = fn(model, view, ctx ?? {});
  scene.viewId = info.id;
  scene.projection = info.projection;
  if (model.system?.data.illustrative === true) scene.notes.unshift('Illustrative example: this system is not a statement about real software.');
  return scene;
}

// ---------------------------------------------------------------- helpers

/**
 * The component a relationship endpoint stands for, from the core (abstraction.js, endpointElement).
 * @param {Model} model @param {any} id @returns {Entity|undefined}
 */
function endpointComponent(model, id) {
  const el = endpointElement(model, id);
  return el ? model.entities.get(el.element) : undefined;
}

/** @param {Model} model @param {string} cat */
function categoryOf(model, cat) {
  return own(model.meta.categories, cat) ?? { label: cat ?? 'component', shape: 'box', color: 'slate' };
}

/** @param {Model} model @param {string} kind */
function relKindOf(model, kind) {
  return own(model.meta.relationshipKinds, kind) ?? { label: kind, line: 'solid', color: 'neutral' };
}

/** @param {Map<string, any>} legend @param {string} id @param {any} entry */
function addLegend(legend, id, entry) {
  if (!legend.has(id)) legend.set(id, { id, ...entry });
}

/** @param {number} n @param {string} one @param {string} many */
function plural(n, one, many) {
  return n === 1 ? one : many;
}

/** @param {any} ctx */
function violatedIds(ctx) {
  /** @type {Set<string>} */
  const out = new Set();
  for (const r of ctx.claimResults ?? []) {
    if (r.status !== 'violated') continue;
    const ids = r.counterexample ? r.counterexample.entities ?? [] : r.involved ?? [];
    for (const id of ids) out.add(id);
  }
  return out;
}

// ------------------------------------------------------------- structural
//
// A structural view is a hierarchy, a cut, a kind coarsening and a filter (WG-5695). The scene is the derived
// model at the cut (src/core/abstraction.js, deriveModel): one node per block, a container for every element the cut
// opens, and one edge per derived interaction. The filter (view.filter, isolate, hidden elements) then removes
// blocks and witnesses, and everything it removes is reported: a connection through hidden blocks becomes a
// labelled path summary, every other lost connection is counted in the notes. Nothing here lifts, bundles or maps
// entities to elements; those are the core's (abstraction.js, query.js).

/** A large model's structural views open as an overview: top-level subsystems collapsed (a default cut). */
export const OVERVIEW_THRESHOLD = 30;

/**
 * The cut a structural view opens at, as the hierarchy and the elements it expands: the view's declared cut;
 * otherwise, in the logical hierarchy, the overview of a large model (top-level subsystems collapsed) or every
 * subsystem open; in another hierarchy, its first declared cut or its roots opened. A `within` filter opens the
 * path to its element.
 * @param {Model} model @param {any} view
 * @returns {{hierarchy: string, expanded: string[]}}
 */
export function defaultCut(model, view) {
  const cutEntity = typeof view.cut === 'string' ? model.entities.get(view.cut) : undefined;
  const declared = cutEntity?.kind === 'cut' ? expandedOfCut(model, cutEntity.id) : null;
  const hid = typeof view.hierarchy === 'string' && hierarchyOf(model, view.hierarchy) ? view.hierarchy : declared?.hierarchy ?? LOGICAL;
  const h = /** @type {import('./query.js').Hierarchy} */ (hierarchyOf(model, hid));
  /** @type {Set<string>} */
  let expanded;
  if (declared && declared.hierarchy === hid) expanded = new Set(declared.expanded);
  else if (hid !== LOGICAL) {
    const first = (model.byKind.cut ?? []).map((c) => expandedOfCut(model, c.id)).find((c) => c && c.hierarchy === hid);
    expanded = new Set(first ? first.expanded : h.roots.filter((r) => (h.children.get(r) ?? []).length));
  } else {
    const systemId = model.system?.id;
    const large = (model.byKind.component ?? []).length > OVERVIEW_THRESHOLD;
    const collapsed = new Set(large ? (model.byKind.component ?? []).filter((c) => c.data.kind === 'subsystem' && (!c.data.parent || c.data.parent === systemId)).map((c) => c.id) : []);
    expanded = new Set(cutBlocksOf(h, { blocks: cutForCollapse(model, collapsed).blocks }).expanded);
  }
  const within = view.filter?.within;
  if (typeof within === 'string' && h.depth.has(within)) { expanded.add(within); for (const a of ancestorsIn(h, within)) expanded.add(a); }
  return { hierarchy: hid, expanded: h.order.filter((e) => expanded.has(e)) };
}

/** The look of an element that is no component: the system, a module element. @type {Record<string, [string, string, string]>} shape, color, sublabel */
const ELEMENT_LOOK = { system: ['box', 'steel', 'System'], module: ['tablet', 'slate', 'Module'] };

/** The marks a block's knowledge status, realisation and coherence give, as short text and a sentence (WG-5695). */
const MARK_TEXT = {
  opaque: ['opaque', 'Opaque: its inside is not specified; its declared interface is all that is known.'],
  external: ['external', 'Outside the specified system: only how the system uses it is specified.'],
  planned: ['planned', 'Planned: not implemented; its declared interface is all there is.'],
  unknown: ['unknown', 'Unknown: a placeholder; nothing derived through it is asserted.'],
  'no-purpose': ['no purpose', 'States no purpose: the first coherence condition of a level is not met for this block.'],
  'interface-disagrees': ['interface disagrees', 'Its declared ports and its derived interface disagree at this cut (V3).'],
  unwitnessed: ['unwitnessed', 'Declared at a composite but witnessed by no relationship between its members (V2).'],
  'kind-not-coarsening': ['kind not coarsening', 'Declared with a kind none of its member facts refines (V4).'],
  'not-declared': ['not only declared', 'Witnessed by facts that are not declared in the specification: extracted from the code or observed in a recording.'],
  'hidden-inside': ['hidden inside', 'Some elements inside it are hidden; relationships touching them are not drawn.'],
};
/** @param {keyof typeof MARK_TEXT} kind @param {string} [text] */
const mark = (kind, text) => ({ kind, text: text ?? MARK_TEXT[kind][0], title: MARK_TEXT[kind][1] });

registerProjection('structural', (model, view, ctx) => {
  const filter = view.filter ?? {};
  const display = view.display ?? {};
  const notes = [PRESENTATION_NOTE];
  const elements = elementsOf(model);
  const compById = new Map((model.byKind.component ?? []).map((c) => [c.id, c]));

  // 1. The hierarchy: the viewer's (ctx.cut) or the view's default.
  const nav = ctx.cut && hierarchyOf(model, ctx.cut.hierarchy) ? ctx.cut : null;
  const fallback = nav ? null : defaultCut(model, view);
  const hid = nav ? nav.hierarchy : /** @type {{hierarchy: string}} */ (fallback).hierarchy;
  const h = /** @type {import('./query.js').Hierarchy} */ (hierarchyOf(model, hid));
  const within = (/** @type {string} */ e, /** @type {string} */ root) => e === root || ancestorsIn(h, e).includes(root);

  // 2. The filter, on elements: within and isolate (a subtree), categories and tags (matching elements and what
  // contains them), hidden elements (and what they contain). A module element is judged by the component declaring it.
  const dataOf = (/** @type {string} */ e) => { const el = elements.get(e); return el?.entity?.data ?? (el?.owners ? compById.get(el.owners[0])?.data : undefined) ?? {}; };
  /** @type {string[]} */
  const roots = [];
  if (typeof filter.within === 'string' && h.depth.has(filter.within)) { roots.push(filter.within); notes.push(`Limited to ${elementLabel(model, filter.within)} and what it contains.`); }
  if (typeof ctx.isolate === 'string' && ctx.isolate && h.depth.has(ctx.isolate)) { roots.push(ctx.isolate); notes.push(`Isolated to ${elementLabel(model, ctx.isolate)} and what it contains.`); }
  const cats = Array.isArray(filter.categories) && filter.categories.length ? filter.categories : null;
  const tags = Array.isArray(filter.tags) && filter.tags.length ? filter.tags : null;
  const kinds = Array.isArray(filter.relationshipKinds) && filter.relationshipKinds.length ? filter.relationshipKinds : null;
  if (cats) notes.push(`Filtered to categories: ${cats.join(', ')}.`);
  if (tags) notes.push(`Filtered to tags: ${tags.join(', ')}.`);
  if (kinds) notes.push(`Filtered to relationship kinds: ${kinds.join(', ')}.`);
  const hidden = ctx.hidden ?? new Set();
  const isHidden = (/** @type {string} */ e) => hidden.has(e) || ancestorsIn(h, e).some((a) => hidden.has(a));
  const matches = (/** @type {string} */ e) => {
    const d = dataOf(e);
    if (cats && !cats.includes(d.category)) return false;
    if (tags && !(Array.isArray(d.tags) && d.tags.some((/** @type {string} */ t) => tags.includes(t)))) return false;
    return true;
  };
  // In scope: what passes within, isolate, categories and tags, before hiding (a hidden element in scope is summarised).
  /** @type {Set<string>} */
  const scope = new Set();
  for (const e of h.order) {
    if (elements.get(e)?.kind === 'system' && !(h.children.get(e) ?? []).length) continue;
    if (roots.some((r) => !within(e, r))) continue;
    if ((cats || tags) && !matches(e)) continue;
    scope.add(e);
  }
  if (cats || tags) for (const e of [...scope]) for (const a of ancestorsIn(h, e)) if (roots.every((r) => within(a, r))) scope.add(a);
  // Shown: in scope and not hidden, and what contains such an element.
  const shownSet = new Set([...scope].filter((e) => !isHidden(e)));
  for (const e of [...shownSet]) for (const a of ancestorsIn(h, e)) if (!isHidden(a)) shownSet.add(a);
  const hiddenInScope = [...scope].filter((e) => hidden.has(e));

  // 3. The cut and its derived model.
  /** @type {{hierarchy: string, blocks: string[], expanded: string[]}} */
  let cut;
  if (nav) cut = /** @type {any} */ (cutOfExpanded(model, hid, nav.expanded));
  else if (ctx.collapsed && hid === LOGICAL) {
    const b = cutForCollapse(model, ctx.collapsed, (id) => shownSet.has(id) && scope.has(id)).blocks;
    cut = { hierarchy: LOGICAL, blocks: b, expanded: cutBlocksOf(h, { blocks: b }).expanded };
  } else cut = /** @type {any} */ (cutOfExpanded(model, hid, /** @type {{expanded: string[]}} */ (fallback ?? defaultCut(model, view)).expanded));
  const coarsen = Array.isArray(view.coarsen) && view.coarsen.length ? (view.coarsen.includes('all') ? 'all' : view.coarsen) : null;
  const d = /** @type {DerivedModel} */ (deriveModel(model, { hierarchy: hid, blocks: cut.blocks }, { coarsen }));
  const blockInfo = new Map(d.blocks.map((b) => [b.id, b]));
  const openedSet = new Set(cut.expanded);

  // 4. Which blocks are drawn. A block is removed by the filter when nothing in it is in scope, by the viewer when
  // it or a container of it is hidden.
  const visibleBlock = (/** @type {string} */ b) => shownSet.has(b) && !isHidden(b);
  /** @type {Set<string>} */
  const removedHidden = new Set();
  /** @type {Set<string>} */
  const removedFilter = new Set();
  for (const b of d.blocks) {
    if (visibleBlock(b.id)) continue;
    if (isHidden(b.id) && [...scope].some((e) => within(e, b.id))) removedHidden.add(b.id); else removedFilter.add(b.id);
  }
  const drawnBlocks = d.blocks.filter((b) => visibleBlock(b.id)).map((b) => b.id);
  /** Nodes: the drawn blocks and the opened elements that contain them. */
  const drawn = new Set(drawnBlocks);
  for (const b of drawnBlocks) for (const a of ancestorsIn(h, b)) if (openedSet.has(a)) drawn.add(a);
  if (!drawn.size) notes.push('No element matches this view at this cut.');

  // 5. Claims: verdicts of the whole model, and those of claims stated at a cut evaluated at this cut.
  const levelResults = /** @type {{claimId: string, result: any}[]} */ (ctx.levelClaims ?? []);
  const levelIds = new Set(levelResults.map((x) => x.claimId));
  const violated = violatedIds({ claimResults: (ctx.claimResults ?? []).filter((r) => !levelIds.has(r.claimId)) });
  /** @type {Set<string>} */
  const levelViolated = new Set();
  for (const { result } of levelResults) {
    if (result?.status !== 'violated' || !result.counterexample) continue;
    for (const id of [...(result.counterexample.entities ?? []), ...(result.counterexample.path ?? [])]) levelViolated.add(id);
  }

  // 6. Nodes.
  const colorBy = display.colorBy ?? 'category';
  const zones = colorBy === 'trustZone'
    ? [...new Set([...drawn].map((id) => compById.get(id)?.data.trustZone).filter((z) => typeof z === 'string' && z))].sort()
    : [];
  const portCounts = new Map();
  if (display.showPorts === true) for (const p of model.byKind.port ?? []) if (p.owner) portCounts.set(p.owner, (portCounts.get(p.owner) ?? 0) + 1);
  const purposeless = new Set(blocksWithoutPurpose(model, d).filter((b) => drawn.has(b)));
  const v3 = new Set(d.diagnostics.filter((x) => x.condition === 'V3' && x.element).map((x) => /** @type {string} */ (x.element)));
  /** @type {Map<string, any>} */
  const legend = new Map();
  /** @type {SceneNode[]} */
  const nodes = [];
  const nearestDrawn = (/** @type {string} */ id) => ancestorsIn(h, id).find((a) => drawn.has(a)) ?? null;
  for (const id of h.order) {
    if (!drawn.has(id)) continue;
    const el = /** @type {import('./query.js').Element} */ (elements.get(id));
    const entity = el.entity ?? (el.owners ? compById.get(el.owners[0]) : undefined);
    if (!entity) continue;
    const isContainer = openedSet.has(id);
    const members = (h.children.get(id) ?? []).length;
    const isBlock = blockInfo.has(id);
    const look = own(ELEMENT_LOOK, el.kind);
    const cat = entity.kind === 'component' && el.kind !== 'module' ? categoryOf(model, entity.data.category) : null;
    let color = cat ? cat.color : look ? look[1] : 'neutral';
    let legendId = cat ? String(entity.data.category) : `element:${el.kind}`;
    let legendLabel = cat ? cat.label : look ? look[2] : el.kind;
    if (cat && colorBy === 'implementation') {
      const st = entity.data.implementation?.status;
      const m = own(/** @type {any} */ (IMPLEMENTATION_COLORS), st);
      color = m ? m[0] : 'neutral';
      legendId = `implementation:${st ?? 'absent'}`;
      legendLabel = m ? `Implementation: ${m[1]}` : 'Implementation: not stated';
    } else if (cat && colorBy === 'trustZone') {
      const z = entity.data.trustZone;
      color = z ? ZONE_PALETTE[zones.indexOf(z) % ZONE_PALETTE.length] : 'neutral';
      legendId = `zone:${z ?? 'none'}`;
      legendLabel = z ? `Trust zone: ${z}` : 'Trust zone: none stated';
    }
    /** @type {string[]} */
    const badges = [];
    if (!isContainer && members) {
      // What the block stands for, counted after the filter: the elements inside it in scope and not hidden.
      const inside = [...shownSet].filter((e) => e !== id && within(e, id));
      const nonModule = inside.filter((e) => elements.get(e)?.kind !== 'module').length;
      badges.push(nonModule ? `${nonModule} inside` : `${inside.length} ${plural(inside.length, 'module', 'modules')}`);
    }
    if (portCounts.has(id)) { const n = portCounts.get(id); badges.push(`${n} ${plural(n, 'port', 'ports')}`); }
    // When the whole system is illustrative the scene notes say so once; per-node badges mark only exceptions.
    if (entity.data.illustrative === true && el.kind !== 'module' && model.system?.data.illustrative !== true) badges.push('illustrative');
    /** @type {{kind: string, text: string, title?: string}[]} */
    const marks = [];
    const knowledge = isBlock ? /** @type {any} */ (blockInfo.get(id)).knowledge : knowledgeOf(model, id)?.status ?? null;
    if (el.kind !== 'module') {
      const planned = entity.kind === 'component' && entity.data.implementation?.status === 'not-implemented';
      if (knowledge === 'unknown') marks.push(mark('unknown'));
      else if (planned) marks.push(mark('planned'));
      else if (knowledge === 'opaque') marks.push(el.kind === 'external' || el.kind === 'actor' || entity.data.category === 'external' ? mark('external', el.kind === 'actor' ? 'actor' : 'external') : mark('opaque'));
      if (purposeless.has(id)) marks.push(mark('no-purpose'));
      if (v3.has(id) && isBlock) marks.push(mark('interface-disagrees'));
    }
    const hiddenInside = hiddenInScope.filter((x) => x !== id && within(x, id)).length;
    if (hiddenInside) marks.push(mark('hidden-inside', `${hiddenInside} hidden`));
    const path = String(el.path ?? '');
    const label = el.kind === 'module' ? (path.endsWith('/') ? `${path.slice(0, -1).split('/').pop()}/` : path.split('/').pop() ?? path) : entityLabel(entity);
    /** @type {SceneNode} */
    const node = {
      id, entityId: entity.id, entityKind: entity.kind, label, sublabel: el.kind === 'module' ? path : cat ? cat.label : look ? look[2] : el.kind,
      shape: isContainer ? 'container' : cat ? cat.shape : look ? look[0] : 'box', color, parent: nearestDrawn(id), container: isContainer,
      element: id, elementKind: el.kind, block: isBlock,
    };
    if (knowledge) node.knowledge = knowledge;
    if (!isContainer && members) node.collapsed = true;
    if (badges.length) node.badges = badges;
    if (marks.length) node.marks = marks;
    if (violated.has(id) || levelViolated.has(id)) node.status = 'violated';
    nodes.push(node);
    if (isContainer) addLegend(legend, 'container', { kind: 'node', label: 'Opened element (contains the blocks drawn inside it)', shape: 'container', color: 'neutral' });
    else addLegend(legend, legendId, { kind: 'node', label: legendLabel, shape: colorBy === 'category' || !cat ? node.shape : 'box', color });
    for (const m of marks) addLegend(legend, `mark:${m.kind}`, { kind: 'mark', mark: m.kind, label: m.title ?? m.text, color: 'neutral' });
  }

  // 7. Edges: the derived interactions between drawn blocks, each restricted to the witnesses the filter keeps,
  // named by its first witness in declaration order and carrying all of them.
  const facts = baseFacts(model).byId;
  const factInScope = (/** @type {import('./abstraction.js').BaseFact} */ f) => scope.has(f.from) && scope.has(f.to);
  const kindKept = (/** @type {import('./abstraction.js').BaseFact} */ f) => !kinds || kinds.includes(f.kind);
  const keep = (/** @type {import('./abstraction.js').BaseFact} */ f) => factInScope(f) && !isHidden(f.from) && !isHidden(f.to) && kindKept(f);
  const declaredOrder = new Map((model.byKind.relationship ?? []).map((r, i) => [r.id, i]));
  const first = (/** @type {string[]} */ ws) => ws.reduce((a, b) => (/** @type {number} */ (declaredOrder.get(a)) <= /** @type {number} */ (declaredOrder.get(b)) ? a : b));
  const unwitnessed = new Set(d.diagnostics.filter((x) => x.code === 'abstraction.unwitnessed' && x.relationship).map((x) => /** @type {string} */ (x.relationship)));
  const notCoarsening = new Set(d.diagnostics.filter((x) => x.code === 'abstraction.kind-not-coarsening' && x.relationship).map((x) => /** @type {string} */ (x.relationship)));
  /** @type {{edge: SceneEdge, order: number}[]} */
  const drawnEdges = [];
  let lifted = 0, bundled = 0, internal = 0, droppedInteractions = 0, droppedWitnesses = 0, droppedByKind = 0, droppedHidden = 0, droppedScope = 0;
  for (const i of d.interactions) {
    if (!drawn.has(i.from) || !drawn.has(i.to)) {
      // Removed with a block: summarised below when the block is hidden, counted here otherwise.
      if (!removedHidden.has(i.from) && !removedHidden.has(i.to) && (drawn.has(i.from) || drawn.has(i.to))) {
        const kept = i.witnesses.filter((w) => { const f = facts.get(w); return !!f && kindKept(f); });
        if (kept.length) { droppedInteractions++; droppedWitnesses += kept.length; }
      }
      continue;
    }
    const r = restrictInteraction(model, i, keep);
    for (const w of i.witnesses) {
      if (r?.witnesses.includes(w)) continue;
      const f = facts.get(w);
      if (f && !kindKept(f)) droppedByKind++;
      else if (f && factInScope(f)) droppedHidden++;
      else if (f) droppedScope++;
    }
    if (!r) continue;
    const backing = /** @type {Entity} */ (model.entities.get(first(r.witnesses)));
    const rk = relKindOf(model, i.kind);
    const count = r.witnesses.length;
    /** @type {SceneEdge} */
    const e = {
      id: backing.id, entityId: backing.id, entityKind: 'relationship', from: i.from, to: i.to, line: rk.line, color: rk.color, dependencyClass: kindInfo(model.meta, i.kind).class,
      label: r.lifted || count > 1 ? (count > 1 ? `${rk.label} ×${count}` : rk.label) : typeof backing.data.label === 'string' && backing.data.label ? backing.data.label : rk.label,
      kind: i.kind, witnesses: r.witnesses, key: i.key,
    };
    /** @type {{kind: string, text: string, title?: string}[]} */
    const marks = [];
    if (r.witnesses.some((w) => unwitnessed.has(w))) marks.push(mark('unwitnessed'));
    if (r.witnesses.some((w) => notCoarsening.has(w))) marks.push(mark('kind-not-coarsening'));
    // Provenance: the witnesses that are not declared (extracted from the code, observed), named with their share.
    const other = Object.entries(r.summary.provenance).filter(([p]) => p !== 'declared');
    if (other.length) marks.push(mark('not-declared', other.map(([p, n]) => (n === count ? p : `${n} ${p}`)).join(', ')));
    if (marks.length) { e.marks = marks; e.label = `${e.label} (${marks.map((m) => m.text).join(', ')})`; e.line = 'dashed'; }
    if (r.lifted) { e.lifted = true; lifted += count; }
    if (count > 1) bundled += count - 1;
    if (r.witnesses.some((w) => violated.has(w) || levelViolated.has(w))) e.status = 'violated';
    drawnEdges.push({ edge: e, order: /** @type {number} */ (declaredOrder.get(backing.id)) });
    addLegend(legend, `rel:${i.kind}`, { kind: 'edge', label: rk.label, line: rk.line, color: rk.color });
    for (const m of marks) addLegend(legend, `mark:${m.kind}`, { kind: 'mark', mark: m.kind, label: m.title ?? m.text, color: 'neutral' });
  }
  for (const b of drawnBlocks) {
    if (openedSet.has(b) || !(h.children.get(b) ?? []).length) continue;
    for (const w of d.fibres[b] ?? []) { const f = facts.get(w); if (f && keep(f)) internal++; }
  }
  const edges = drawnEdges.sort((a, b) => a.order - b.order).map((x) => x.edge);

  // 8. Path summaries through hidden blocks; connections through blocks the filter removes are counted.
  const summaryKeep = (/** @type {import('./abstraction.js').BaseFact} */ f) => factInScope(f) && kindKept(f);
  const summaries = removedHidden.size ? pathSummaries(model, d, removedHidden, summaryKeep).filter((s) => drawn.has(s.from) && drawn.has(s.to)) : [];
  for (const s of summaries) {
    const backing = first(s.witnesses);
    edges.push({
      id: `summary:${s.from}->${s.to}`, entityId: backing, entityKind: 'relationship', from: s.from, to: s.to, line: 'dotted', color: 'neutral', dependencyClass: 'none',
      label: `may reach via ${s.via.length} hidden (${s.via.map((v) => elementLabel(model, v)).join(', ')})`, witnesses: s.witnesses, pathSummary: { via: s.via, kinds: s.kinds },
    });
    addLegend(legend, 'path-summary', { kind: 'edge', label: 'Derived path summary through hidden elements (a may-path)', line: 'dotted', color: 'neutral' });
  }
  const touchingHidden = d.interactions.filter((i) => removedHidden.has(i.from) || removedHidden.has(i.to)).length;
  const throughFiltered = removedFilter.size
    ? pathSummaries(model, d, new Set([...removedFilter, ...removedHidden]), kindKept).filter((s) => drawn.has(s.from) && drawn.has(s.to) && s.via.some((v) => removedFilter.has(v)))
    : [];

  // 9. Notes: what this scene shows, and everything the filter took away, counted.
  // A system with no members in this hierarchy (one that groups the elements under other roots, such as hosts) is a
  // block with nothing inside and no relationship: it is reported, not drawn as an empty box.
  for (const b of removedFilter) {
    if (elements.get(b)?.kind !== 'system' || (h.children.get(b) ?? []).length) continue;
    notes.push(`${elementLabel(model, b)} is a block of this cut with no members and no relationships in the ${hid} hierarchy, so it is not drawn.`);
  }
  const cutId = declaredCutWithBlocks(model, hid, cut.blocks);
  const cutEntity = cutId ? model.entities.get(cutId) : undefined;
  const cutBlocks = d.blocks.filter((b) => !b.implicit).length;
  notes.push(`Cut: ${cutEntity ? entityLabel(cutEntity) : 'an interactive cut'} of the ${hid} hierarchy, ${cutBlocks} ${plural(cutBlocks, 'block', 'blocks')}${cut.expanded.length ? `, opening ${cut.expanded.map((e) => elementLabel(model, e)).join(', ')}` : ''}.`);
  if (coarsen) notes.push(`Kinds are coarsened to ${coarsen === 'all' ? 'the kinds directly under interacts-with' : coarsen.join(', ')}.`);
  if (hiddenInScope.length) notes.push(`${hiddenInScope.length} ${plural(hiddenInScope.length, 'element is', 'elements are')} hidden (${hiddenInScope.map((x) => elementLabel(model, x)).join(', ')})${touchingHidden ? `; ${touchingHidden} derived ${plural(touchingHidden, 'interaction touches', 'interactions touch')} hidden blocks` : ''}${summaries.length ? `, and ${summaries.length} ${plural(summaries.length, 'connection', 'connections')} through them ${plural(summaries.length, 'is', 'are')} drawn as dotted path ${plural(summaries.length, 'summary', 'summaries')} (may-paths: a path through a block need not be a path through its members)` : ''}.`);
  if (droppedInteractions) notes.push(`${droppedInteractions} derived ${plural(droppedInteractions, 'interaction', 'interactions')} with a block outside this view's filter ${plural(droppedInteractions, 'is', 'are')} not drawn (${droppedWitnesses} ${plural(droppedWitnesses, 'relationship', 'relationships')}).`);
  if (throughFiltered.length) notes.push(`${throughFiltered.length} ${plural(throughFiltered.length, 'connection', 'connections')} between drawn blocks ${plural(throughFiltered.length, 'passes', 'pass')} through blocks the filter removes and ${plural(throughFiltered.length, 'is', 'are')} not drawn.`);
  if (droppedHidden) notes.push(`${droppedHidden} ${plural(droppedHidden, 'relationship touches', 'relationships touch')} hidden elements inside drawn blocks and ${plural(droppedHidden, 'is', 'are')} not drawn.`);
  if (droppedScope) notes.push(`${droppedScope} ${plural(droppedScope, 'relationship has', 'relationships have')} an end inside a drawn block that this view's filter removes and ${plural(droppedScope, 'is', 'are')} not drawn.`);
  if (droppedByKind) notes.push(`${droppedByKind} ${plural(droppedByKind, 'relationship', 'relationships')} of other kinds between drawn blocks ${plural(droppedByKind, 'is', 'are')} not drawn.`);
  if (lifted) notes.push(`${lifted} ${plural(lifted, 'relationship is', 'relationships are')} drawn to a collapsed block rather than to the element inside it.`);
  if (bundled) notes.push(`Relationships of one kind between the same two drawn blocks are one derived interaction, drawn as one line labelled with their number (${bundled} ${plural(bundled, 'line', 'lines')} saved); selecting it lists every relationship it stands for.`);
  if (internal) notes.push(`${internal} ${plural(internal, 'relationship', 'relationships')} inside collapsed blocks ${plural(internal, 'is', 'are')} not drawn; expanding a block shows them.`);
  const unknownBlocks = drawnBlocks.filter((b) => blockInfo.get(b)?.knowledge === 'unknown').length;
  if (unknownBlocks) notes.push(`${unknownBlocks} unknown ${plural(unknownBlocks, 'block asserts', 'blocks assert')} nothing about ${plural(unknownBlocks, 'its', 'their')} inside.`);
  if (purposeless.size) notes.push(`${purposeless.size} ${plural(purposeless.size, 'block states', 'blocks state')} no purpose (${[...purposeless].join(', ')}), so this level is not independently coherent.`);
  /** @type {NonNullable<SceneModel['levelClaims']>} */
  const levelClaims = [];
  const sceneIds = new Set([...nodes.map((n) => n.id), ...edges.filter((e) => !e.pathSummary).flatMap((e) => e.witnesses ?? [])]);
  for (const { claimId, result } of levelResults) {
    const expressible = !(result?.diagnostics ?? []).some((/** @type {any} */ x) => x.code === 'claim.not-expressible');
    const cx = result?.status === 'violated' ? [...new Set([...(result.counterexample?.entities ?? []), ...(result.counterexample?.path ?? [])])] : [];
    const drawnCx = cx.filter((x) => sceneIds.has(x));
    levelClaims.push({ claimId, status: result?.status ?? 'not-evaluated', expressible, explanation: result?.explanation ?? '', drawn: drawnCx, notDrawn: cx.filter((x) => !sceneIds.has(x)) });
    const label = /** @type {any} */ (CLAIM_STATUS_LABELS)[result?.status] ?? result?.status;
    notes.push(!expressible
      ? `Claim ${claimId} is stated at a cut and is not expressible at this level: ${String(result?.explanation ?? '').replace(/^Not expressible at this level: /, '')}`
      : `Claim ${claimId}, evaluated at this cut: ${label}${cx.length ? `; its counterexample is drawn in red${drawnCx.length < cx.length ? ` (${cx.length - drawnCx.length} of its ${cx.length} parts are not drawn here)` : ''}` : ''}.`);
  }
  if (colorBy === 'implementation') notes.push('Color shows how each component is realised; shape still shows its category.');
  if (colorBy === 'trustZone') notes.push('Color shows the declared trust zone; shape still shows its category.');
  if (display.showPorts === true) notes.push('Ports are not drawn as separate nodes; a badge counts them.');

  return {
    viewId: view.id, projection: 'structural', nodes, edges, legend: [...legend.values()], notes,
    abstraction: { hierarchy: hid, blocks: cut.blocks, expanded: cut.expanded, cut: cutId, coarsen },
    filterReport: {
      hidden: hiddenInScope, removedBlocks: [...removedHidden, ...removedFilter].sort(), droppedInteractions, droppedWitnesses: droppedWitnesses + droppedByKind + droppedHidden + droppedScope,
      pathSummaries: summaries.length, pathsThroughFiltered: throughFiltered.length,
    },
    levelClaims,
  };
});

/**
 * The semantic content of a structural scene, for comparison with the derived model the command line prints
 * (`exegra derive`): its cut, its blocks, its derived interactions with their witnesses, its path summaries, its
 * marks and its filter report. Presentation (positions, colours, labels) is left out.
 * @param {SceneModel} scene
 */
export function sceneSemantics(scene) {
  const byKey = (/** @type {{key: string}} */ a, /** @type {{key: string}} */ b) => (a.key < b.key ? -1 : a.key > b.key ? 1 : 0);
  return {
    view: scene.viewId,
    hierarchy: scene.abstraction?.hierarchy ?? null,
    cut: scene.abstraction?.cut ?? null,
    cutBlocks: [...(scene.abstraction?.blocks ?? [])],
    expanded: [...(scene.abstraction?.expanded ?? [])],
    blocks: scene.nodes.filter((n) => n.block).map((n) => n.id).sort(),
    containers: scene.nodes.filter((n) => n.container).map((n) => n.id).sort(),
    interactions: scene.edges.filter((e) => e.key).map((e) => ({ key: /** @type {string} */ (e.key), witnesses: [...(e.witnesses ?? [])] })).sort(byKey),
    pathSummaries: scene.edges.filter((e) => e.pathSummary).map((e) => ({ from: e.from, to: e.to, via: e.pathSummary?.via ?? [], witnesses: [...(e.witnesses ?? [])] })),
    marks: Object.fromEntries(scene.nodes.filter((n) => n.marks?.length).map((n) => [n.id, (n.marks ?? []).map((m) => m.kind)])),
    filterReport: scene.filterReport ?? null,
    levelClaims: (scene.levelClaims ?? []).map((c) => ({ claimId: c.claimId, status: c.status, expressible: c.expressible, drawn: c.drawn, notDrawn: c.notDrawn })),
  };
}

/** The label of an element: its entity's, or a module element's path. @param {Model} model @param {string} id */
function elementLabel(model, id) {
  const e = model.entities.get(id);
  return e ? entityLabel(e) : id.startsWith('module:') ? id.slice('module:'.length) : id;
}

// ----------------------------------------------------------------- claims

/** @param {any} status */
function claimColor(status) {
  return /** @type {any} */ (CLAIM_COLORS)[status] ?? 'neutral';
}

registerProjection('claims', (model, view, ctx) => {
  const notes = [PRESENTATION_NOTE];
  const results = new Map((ctx.claimResults ?? []).map((r) => [r.claimId, r]));
  const allClaims = model.byKind.claim ?? [];
  const focus = ctx.focusClaim ? allClaims.find((c) => c.id === ctx.focusClaim) : undefined;
  const claims = focus ? [focus] : allClaims;
  /** @type {Map<string, any>} */
  const legend = new Map();
  const violated = violatedIds(ctx);

  /** @type {Map<string, Set<string>>} */
  const skipped = new Map();
  const skip = (/** @type {Entity|undefined} */ e) => {
    if (!e || ['assumption', 'evidence', 'claim', 'fault'].includes(e.kind)) return;
    if (!skipped.has(e.kind)) skipped.set(e.kind, new Set());
    /** @type {Set<string>} */ (skipped.get(e.kind)).add(e.id);
  };
  /** Resolve an entity id to the drawable components (and relationships) it stands for. */
  const resolve = (/** @type {string} */ id, /** @type {Set<string>} */ compsOut, /** @type {Set<string>} */ relsOut) => {
    const e = model.entities.get(id);
    if (!e) return;
    if (!['component', 'port', 'relationship', 'behavior'].includes(e.kind)) { skip(e); return; }
    const stands = componentsFor(model, id);
    if (e.kind === 'relationship') {
      if (stands.length && endpointElement(model, e.data.from) && endpointElement(model, e.data.to)) { for (const c of stands) compsOut.add(c); relsOut.add(e.id); } else skip(e);
    } else for (const c of stands) compsOut.add(c);
  };

  /** @type {Set<string>} */ const compIds = new Set();
  /** @type {Set<string>} */ const relIds = new Set();
  /** @type {Map<string, Set<string>>} claim -> subject components */
  const aboutOf = new Map();
  for (const claim of claims) {
    const res = results.get(claim.id);
    const subjects = Array.isArray(claim.data.subjects) ? claim.data.subjects : [];
    const aboutC = new Set();
    const aboutR = new Set();
    for (const s of subjects) resolve(s, aboutC, aboutR);
    const involvedC = new Set();
    const involvedR = new Set();
    if (focus) for (const id of res?.involved?.length ? res.involved : subjects) resolve(id, involvedC, involvedR);
    const target = focus && aboutC.size === 0 ? involvedC : aboutC;
    aboutOf.set(claim.id, target);
    for (const c of aboutC) compIds.add(c);
    for (const r of aboutR) relIds.add(r);
    for (const c of involvedC) compIds.add(c);
    for (const r of involvedR) relIds.add(r);
  }

  // Containers survive only where more than one shown component sits inside.
  const comps = (model.byKind.component ?? []).filter((c) => compIds.has(c.id));
  /** @type {Map<string, number>} */
  const inside = new Map();
  for (const c of comps) for (const a of ancestorsOf(model, c.id)) inside.set(a, (inside.get(a) ?? 0) + 1);
  /** @type {Set<string>} */
  const containers = new Set([...inside].filter(([, n]) => n > 1).map(([id]) => id));
  const compNodeIds = new Set([...compIds, ...containers]);

  /** @type {SceneNode[]} */
  const nodes = [];
  /** @type {SceneEdge[]} */
  const edges = [];
  /** @type {Set<string>} */
  const emitted = new Set();
  const compById = new Map((model.byKind.component ?? []).map((c) => [c.id, c]));
  const nearestContainer = (/** @type {string} */ id) => ancestorsOf(model, id).find((a) => containers.has(a)) ?? null;
  /** @param {Entity} c */
  const emitComp = (c) => {
    if (emitted.has(c.id) || !compNodeIds.has(c.id)) return;
    const parent = nearestContainer(c.id);
    if (parent) emitComp(/** @type {Entity} */ (compById.get(parent)));
    emitted.add(c.id);
    const cat = categoryOf(model, c.data.category);
    const isContainer = containers.has(c.id);
    /** @type {SceneNode} */
    const node = {
      id: c.id, entityId: c.id, entityKind: 'component', label: entityLabel(c), sublabel: cat.label,
      shape: isContainer ? 'container' : cat.shape, color: cat.color, parent, container: isContainer,
    };
    if (c.data.illustrative === true && model.system?.data.illustrative !== true) node.badges = ['illustrative'];
    if (violated.has(c.id)) node.status = 'violated';
    nodes.push(node);
    if (isContainer) addLegend(legend, 'container', { kind: 'node', label: 'Subsystem (contains components)', shape: 'container', color: 'neutral' });
    else addLegend(legend, String(c.data.category), { kind: 'node', label: cat.label, shape: cat.shape, color: cat.color });
  };
  // Containers are emitted through their children; also emit any that are shown themselves.
  for (const c of model.byKind.component ?? []) emitComp(c);

  // Claim nodes (declaration order), then their assumptions and evidence.
  /** @type {Set<string>} */ const assumptionIds = new Set();
  /** @type {Set<string>} */ const evidenceIds = new Set();
  for (const claim of claims) {
    const res = results.get(claim.id);
    const status = res?.status ?? 'not-evaluated';
    nodes.push({
      id: claim.id, entityId: claim.id, entityKind: 'claim', label: entityLabel(claim), sublabel: String(claim.data.kind),
      shape: 'diamond', color: claimColor(status), parent: null, container: false, status,
    });
    addLegend(legend, `claim:${status}`, { kind: 'node', label: `Claim: ${/** @type {any} */ (CLAIM_STATUS_LABELS)[status] ?? status}`, shape: 'diamond', color: claimColor(status) });
  }
  if (focus) {
    const res = results.get(focus.id);
    for (const a of [...(focus.data.assumptions ?? []), ...(res?.assumptions ?? [])]) if (model.entities.get(a)?.kind === 'assumption') assumptionIds.add(a);
    for (const ev of model.byKind.evidence ?? []) if (ev.data.claim === focus.id) evidenceIds.add(ev.id);
    for (const a of model.byKind.assumption ?? []) {
      if (!assumptionIds.has(a.id)) continue;
      nodes.push({
        id: a.id, entityId: a.id, entityKind: 'assumption', label: entityLabel(a), sublabel: undefined,
        shape: 'hex', color: 'violet', parent: null, container: false, ...(a.data.illustrative === true ? { badges: ['illustrative'] } : {}),
      });
      addLegend(legend, 'assumption', { kind: 'node', label: 'Assumption', shape: 'hex', color: 'violet' });
    }
    for (const ev of model.byKind.evidence ?? []) {
      if (!evidenceIds.has(ev.id)) continue;
      nodes.push({
        id: ev.id, entityId: ev.id, entityKind: 'evidence', label: typeof ev.data.ref === 'string' ? ev.data.ref : ev.id, sublabel: String(ev.data.kind),
        shape: 'tablet', color: 'steel', parent: null, container: false,
      });
      addLegend(legend, 'evidence', { kind: 'node', label: 'Evidence', shape: 'tablet', color: 'steel' });
    }
  }
  for (const n of nodes) if (n.sublabel === undefined) delete n.sublabel;

  // Edges: relationships among the shown components, then claim edges.
  const shownRels = new Set(relIds);
  if (focus) {
    for (const r of model.byKind.relationship ?? []) {
      const f = endpointComponent(model, r.data.from);
      const t = endpointComponent(model, r.data.to);
      if (f && t && compIds.has(f.id) && compIds.has(t.id)) shownRels.add(r.id);
    }
  }
  for (const r of model.byKind.relationship ?? []) {
    if (!shownRels.has(r.id)) continue;
    const f = endpointComponent(model, r.data.from);
    const t = endpointComponent(model, r.data.to);
    if (!f || !t || !compNodeIds.has(f.id) || !compNodeIds.has(t.id)) continue;
    const rk = relKindOf(model, r.data.kind);
    /** @type {SceneEdge} */
    const e = { id: r.id, entityId: r.id, entityKind: 'relationship', from: f.id, to: t.id, line: rk.line, color: rk.color, dependencyClass: kindInfo(model.meta, r.data.kind).class, label: typeof r.data.label === 'string' && r.data.label ? r.data.label : rk.label };
    if (violated.has(r.id)) e.status = 'violated';
    edges.push(e);
    addLegend(legend, `rel:${r.data.kind}`, { kind: 'edge', label: rk.label, line: rk.line, color: rk.color });
  }
  for (const claim of claims) {
    for (const c of aboutOf.get(claim.id) ?? []) {
      edges.push({ id: `${claim.id}~about~${c}`, entityId: claim.id, entityKind: 'claim', from: claim.id, to: c, line: 'dotted', color: 'neutral' });
      addLegend(legend, 'about', { kind: 'edge', label: 'Claim is about', line: 'dotted', color: 'neutral' });
    }
  }
  if (focus) {
    for (const a of assumptionIds) {
      edges.push({ id: `${focus.id}~assumes~${a}`, entityId: focus.id, entityKind: 'claim', from: focus.id, to: a, line: 'dashed', color: 'violet' });
      addLegend(legend, 'assumes', { kind: 'edge', label: 'Claim assumes', line: 'dashed', color: 'violet' });
    }
    for (const ev of model.byKind.evidence ?? []) {
      if (!evidenceIds.has(ev.id)) continue;
      const supports = ev.data.supports !== false;
      edges.push({ id: `${ev.id}~${supports ? 'supports' : 'contradicts'}~${focus.id}`, entityId: ev.id, entityKind: 'evidence', from: ev.id, to: focus.id, line: 'solid', color: supports ? 'steel' : 'red' });
      addLegend(legend, supports ? 'supports' : 'contradicts', { kind: 'edge', label: supports ? 'Evidence offered in support (author-entered)' : 'Evidence offered against (author-entered)', line: 'solid', color: supports ? 'steel' : 'red' });
    }
  }

  // Notes.
  notes.push(focus ? `Showing claim ${focus.id}, its subjects, assumptions and evidence, and the relationships among the involved components.` : 'Showing every claim with its subjects. Focus a claim to see its assumptions, evidence and the components involved in its evaluation.');
  notes.push('Claim status comes only from evaluation results; a claim without a result is shown as not evaluated.');
  for (const [kind, ids] of skipped) notes.push(`${ids.size} ${plural(ids.size, kind, kind + 's')} involved in the claims ${plural(ids.size, 'is', 'are')} not drawn here (${[...ids].sort().join(', ')}).`);
  if (!claims.length) notes.push('The model declares no claims.');

  return { viewId: view.id, projection: 'claims', nodes, edges, legend: [...legend.values()], notes };
});

// --------------------------------------------------------------- behavior

registerProjection('behavior', (model, view, ctx) => {
  const notes = [PRESENTATION_NOTE];
  const allBehaviors = model.byKind.behavior ?? [];
  const scenario = ctx.focusScenario ? (model.byKind.scenario ?? []).find((s) => s.id === ctx.focusScenario) : undefined;
  const behaviors = scenario
    ? (scenario.data.behaviors ?? []).map((/** @type {string} */ id) => model.entities.get(id)).filter((/** @type {Entity|undefined} */ e) => e && e.kind === 'behavior')
    : allBehaviors;
  /** @type {Map<string, any>} */
  const legend = new Map();
  /** @type {SceneNode[]} */
  const nodes = [];
  /** @type {SceneEdge[]} */
  const edges = [];
  const eventName = (/** @type {string} */ id) => { const e = model.entities.get(id); return e ? entityLabel(e) : id; };

  // Trace overlay.
  /** @type {any} */ let config = null;
  /** @type {any} */ let step = null;
  const trace = ctx.trace;
  const traceApplies = trace && (!scenario || trace.scenarioId === scenario.id);
  if (traceApplies) {
    const si = typeof ctx.stepIndex === 'number' ? ctx.stepIndex : -1;
    if (si < 0) config = trace.initial;
    else { step = trace.steps[si] ?? null; config = step ? step.config : trace.final; }
  }
  const activeStates = new Set();
  if (config) for (const m of Object.values(config.machines ?? {})) activeStates.add(/** @type {any} */ (m).state);
  const firedTransitions = new Set();
  if (step) for (const f of step.fired ?? []) firedTransitions.add(f.transition);

  /** @type {Set<string>} */ const eventIds = new Set();
  /** @type {Set<string>} */ const injected = new Set();
  const edgeIds = new Set();
  /** @type {SceneEdge[]} */ const flowEdges = [];
  let faultOnly = 0;

  for (const b of behaviors) {
    const subject = model.entities.get(b.data.subject);
    nodes.push({
      id: b.id, entityId: b.id, entityKind: 'behavior', label: entityLabel(b), ...(subject ? { sublabel: entityLabel(subject) } : {}),
      shape: 'container', color: 'neutral', parent: null, container: true,
    });
    addLegend(legend, 'behavior', { kind: 'node', label: 'Behavior (state machine)', shape: 'container', color: 'neutral' });
    for (const s of (model.byKind.state ?? []).filter((x) => x.owner === b.id)) {
      /** @type {string[]} */
      const badges = [];
      if (b.data.initial === s.id) badges.push('initial');
      if (s.data.terminal === true) badges.push('terminal');
      /** @type {SceneNode} */
      const n = { id: s.id, entityId: s.id, entityKind: 'state', label: entityLabel(s), shape: 'capsule', color: 'slate', parent: b.id, container: false };
      if (badges.length) n.badges = badges;
      if (activeStates.has(s.id)) n.status = 'active';
      nodes.push(n);
      addLegend(legend, 'state', { kind: 'node', label: 'State', shape: 'capsule', color: 'slate' });
    }
    for (const t of (model.byKind.transition ?? []).filter((x) => x.owner === b.id)) {
      const guard = typeof t.data.guard === 'string' && t.data.guard ? ` [${t.data.guard}]` : '';
      const fo = t.data.faultOnly === true;
      if (fo) faultOnly++;
      /** @type {SceneEdge} */
      const e = {
        id: t.id, entityId: t.id, entityKind: 'transition', from: t.data.from, to: t.data.to,
        line: fo ? 'dashed' : 'solid', color: fo ? 'red' : 'slate',
        label: `${eventName(t.data.on)}${guard}${fo ? ' (fault only)' : ''}`,
      };
      if (firedTransitions.has(t.id)) e.status = 'active';
      edges.push(e);
      addLegend(legend, fo ? 'transition:fault' : 'transition', { kind: 'edge', label: fo ? 'Fault-only transition' : 'Transition (event [guard])', line: e.line, color: e.color });
      if (typeof t.data.on === 'string') {
        eventIds.add(t.data.on);
        const id = `${t.data.on}~triggers~${t.id}`;
        if (!edgeIds.has(id)) { edgeIds.add(id); flowEdges.push({ id, entityId: t.id, entityKind: 'transition', from: t.data.on, to: t.data.from, line: 'dotted', color: 'rose' }); }
      }
      for (const eff of Array.isArray(t.data.effects) ? t.data.effects : []) {
        if (!eff || typeof eff.emit !== 'string') continue;
        eventIds.add(eff.emit);
        const id = `${t.id}~emits~${eff.emit}`;
        if (!edgeIds.has(id)) { edgeIds.add(id); flowEdges.push({ id, entityId: t.id, entityKind: 'transition', from: t.data.to, to: eff.emit, line: 'dotted', color: 'rose' }); }
      }
    }
  }
  if (scenario) for (const s of scenario.data.steps ?? []) if (typeof s.event === 'string') { eventIds.add(s.event); injected.add(s.event); }

  const deliveredId = step?.event?.id;
  for (const ev of model.byKind.event ?? []) {
    if (!eventIds.has(ev.id)) continue;
    /** @type {SceneNode} */
    const n = { id: ev.id, entityId: ev.id, entityKind: 'event', label: entityLabel(ev), shape: 'sphere', color: 'rose', parent: null, container: false };
    if (injected.has(ev.id)) n.badges = ['injected'];
    if (deliveredId === ev.id) n.status = 'active';
    nodes.push(n);
    addLegend(legend, 'event', { kind: 'node', label: 'Event', shape: 'sphere', color: 'rose' });
  }
  for (const e of flowEdges) {
    edges.push(e);
    const emits = e.id.includes('~emits~');
    addLegend(legend, emits ? 'flow:emits' : 'flow:triggers', { kind: 'edge', label: emits ? 'Transition emits event' : 'Event triggers transition', line: 'dotted', color: 'rose' });
  }

  notes.push('Arrows between states are transitions, labelled with the triggering event and guard. Events are drawn outside the state machines.');
  notes.push(scenario ? `Showing the behaviors run by scenario ${scenario.id}.` : 'Showing every behavior. Focus a scenario to restrict the view to the behaviors it runs.');
  if (faultOnly) notes.push(`${faultOnly} fault-only ${plural(faultOnly, 'transition is', 'transitions are')} drawn dashed; ${plural(faultOnly, 'it can', 'they can')} fire only while a fault enables ${plural(faultOnly, 'it', 'them')}.`);
  if (injected.size) notes.push('Events marked "injected" are inputs of the scenario.');
  if (config) notes.push(step ? `Active markers show the configuration after step ${step.index} of scenario ${trace.scenarioId}.` : `Active markers show the initial configuration of scenario ${trace.scenarioId}.`);
  if (!behaviors.length) notes.push('There are no behaviors to show.');

  return { viewId: view.id, projection: 'behavior', nodes, edges, legend: [...legend.values()], notes };
});

// ------------------------------------------------------------- references

const REFERENCE_NODE_CAP = 150;
const REFERENCE_KIND_FILTER_CAP = 300;

/** Fixed look of built-in kinds that are neither components nor claims: [shape, color]. */
const BUILTIN_KIND_LOOK = {
  contract: ['hex', 'steel'], event: ['sphere', 'rose'], behavior: ['box', 'neutral'], state: ['capsule', 'slate'],
  transition: ['capsule', 'slate'], scenario: ['box', 'violet'], fault: ['octa', 'red'], assumption: ['hex', 'violet'],
  evidence: ['tablet', 'steel'], view: ['box', 'neutral'], port: ['box', 'teal'], system: ['box', 'neutral'],
  record: ['cylinder', 'amber'], copy: ['tablet', 'teal'],
};

/**
 * Text of at most `max` characters, ending in an ellipsis when it was cut.
 * @param {string} text @param {number} max
 */
export function truncateText(text, max) {
  return text.length > max ? text.slice(0, max - 1) + '…' : text;
}

/**
 * Label that leads with the entity's original identifier (`data.ref`, e.g.
 * "KRN-002") when it has one.
 * @param {Entity} e
 */
export function refLabel(e) {
  const text = entityLabel(e);
  return typeof e.data.ref === 'string' && e.data.ref && e.data.ref !== text ? `${e.data.ref} ${text}` : text;
}

/** Human label of an entity kind. @param {Model} model @param {string} kind */
export function kindLabelOf(model, kind) {
  return model.meta.entities?.[kind]?.label ?? kind;
}

/** Property path of a reference relative to its referring entity, without list indices. @param {Entity} from @param {{path:(string|number)[]}} ref */
function referenceProperty(from, ref) {
  const rel = ref.path.slice(from.path?.length ?? 0).filter((s) => typeof s === 'string');
  if (rel.length) return rel.join('.');
  const all = ref.path.filter((s) => typeof s === 'string');
  return all.length ? String(all[all.length - 1]) : 'ref';
}

registerProjection('references', (model, view, ctx) => {
  const display = view.display ?? {};
  const filter = view.filter ?? {};
  const depth = Math.min(3, Math.max(1, Number.isFinite(Number(display.depth)) ? Math.floor(Number(display.depth)) : 1));
  const kindFilter = Array.isArray(filter.entityKinds) && filter.entityKinds.length ? new Set(filter.entityKinds) : null;
  /** @type {string[]} */
  const notes = [];
  const results = new Map((ctx.claimResults ?? []).map((r) => [r.claimId, r]));
  const violated = violatedIds(ctx);
  const focus = typeof ctx.focusEntity === 'string' && ctx.focusEntity ? model.entities.get(ctx.focusEntity) : undefined;
  /** @type {Map<string, number>} */
  const order = new Map();
  let idx = 0;
  for (const id of model.entities.keys()) order.set(id, idx++);
  const byOrder = (/** @type {string} */ a, /** @type {string} */ b) => (order.get(a) ?? 0) - (order.get(b) ?? 0);

  // 1. Which entities are drawn.
  /** @type {string[]} drawn entity ids, nearest first */
  let drawn = [];
  if (focus) {
    /** @type {Map<string, string[]>} */
    const adj = new Map();
    const link = (/** @type {string} */ a, /** @type {string} */ b) => {
      if (!adj.has(a)) adj.set(a, []);
      /** @type {string[]} */ (adj.get(a)).push(b);
    };
    for (const r of model.refs) {
      if (r.from === r.target || !model.entities.has(r.from) || !model.entities.has(r.target)) continue;
      link(r.from, r.target);
      link(r.target, r.from);
    }
    const seen = new Set([focus.id]);
    drawn = [focus.id];
    let frontier = [focus.id];
    for (let hop = 0; hop < depth && frontier.length; hop++) {
      /** @type {Set<string>} */
      const next = new Set();
      for (const id of frontier) for (const n of adj.get(id) ?? []) if (!seen.has(n)) { seen.add(n); next.add(n); }
      frontier = [...next].sort(byOrder);
      drawn.push(...frontier);
    }
    if (kindFilter) drawn = drawn.filter((id) => id === focus.id || kindFilter.has(/** @type {Entity} */ (model.entities.get(id)).kind));
    /** @type {string|null} */
    let capNote = null;
    if (drawn.length > REFERENCE_NODE_CAP) {
      const left = drawn.slice(REFERENCE_NODE_CAP);
      drawn = drawn.slice(0, REFERENCE_NODE_CAP);
      /** @type {Map<string, number>} */
      const byKind = new Map();
      for (const id of left) { const k = /** @type {Entity} */ (model.entities.get(id)).kind; byKind.set(k, (byKind.get(k) ?? 0) + 1); }
      capNote = `${left.length} more ${plural(left.length, 'entity was', 'entities were')} left out to keep the view readable (${[...byKind].map(([k, n]) => `${n} ${kindLabelOf(model, k)}`).join(', ')}); narrow the kinds or lower the depth.`;
    }
    notes.push(`Showing ${entityLabel(focus)} and everything within ${depth} ${plural(depth, 'reference', 'references')} of it, in either direction.`);
    if (kindFilter) notes.push(`Filtered to kinds: ${[...kindFilter].join(', ')}.`);
    if (capNote) notes.push(capNote);
  } else {
    const counts = Object.entries(model.byKind).filter(([, list]) => list.length).map(([k, list]) => `${kindLabelOf(model, k)} ${list.length}`);
    let total = 0;
    if (kindFilter) for (const k of kindFilter) total += (model.byKind[k] ?? []).length;
    if (kindFilter && total > 0 && total <= REFERENCE_KIND_FILTER_CAP) {
      for (const k of kindFilter) for (const e of model.byKind[k] ?? []) drawn.push(e.id);
      drawn.sort(byOrder);
      notes.push(`Showing every ${[...kindFilter].map((k) => kindLabelOf(model, k)).join(', ')} entity (${total}) and the references among them.`);
    } else {
      notes.push('Select an entity to see what it refers to and what refers to it.');
      if (kindFilter && total > REFERENCE_KIND_FILTER_CAP) notes.push(`The selected kinds have ${total} entities; more than ${REFERENCE_KIND_FILTER_CAP} are not drawn without a focus.`);
    }
    notes.push(`Entities in the model: ${counts.join(', ') || 'none'}.`);
  }
  notes.unshift(PRESENTATION_NOTE);

  // 2. Relationships between two drawn components become edges, not nodes.
  const drawnSet = new Set(drawn);
  const isDrawnComponent = (/** @type {string} */ id) => drawnSet.has(id) && model.entities.get(id)?.kind === 'component';
  /** @type {Map<string, {from: string, to: string}>} */
  const converted = new Map();
  for (const id of drawn) {
    const e = /** @type {Entity} */ (model.entities.get(id));
    if (e.kind !== 'relationship' || (focus && focus.id === id)) continue;
    const f = endpointComponent(model, e.data.from);
    const t = endpointComponent(model, e.data.to);
    if (f && t && isDrawnComponent(f.id) && isDrawnComponent(t.id)) converted.set(id, { from: f.id, to: t.id });
  }

  // 3. Nodes.
  /** @type {Map<string, any>} */
  const legend = new Map();
  /** @type {SceneNode[]} */
  const nodes = [];
  /** @type {Set<string>} */
  const nodeIds = new Set();
  for (const id of drawn) {
    if (converted.has(id)) continue;
    const e = /** @type {Entity} */ (model.entities.get(id));
    let shape = 'box';
    let color = 'neutral';
    /** @type {string|undefined} */
    let status;
    if (e.kind === 'component') { const cat = categoryOf(model, e.data.category); shape = cat.shape; color = cat.color; }
    else if (e.kind === 'claim') { status = results.get(e.id)?.status ?? 'not-evaluated'; shape = 'diamond'; color = claimColor(status); }
    else if (model.meta.entities?.[e.kind]?.declared) { shape = model.meta.entities[e.kind].shape ?? 'box'; color = model.meta.entities[e.kind].color ?? 'neutral'; }
    else { const look = /** @type {any} */ (BUILTIN_KIND_LOOK)[e.kind]; if (look) { shape = look[0]; color = look[1]; } }
    /** @type {SceneNode} */
    const node = {
      id: e.id, entityId: e.id, entityKind: e.kind,
      label: truncateText(typeof e.data.ref === 'string' && e.data.ref ? e.data.ref : entityLabel(e), 48),
      sublabel: kindLabelOf(model, e.kind), shape, color, parent: null, container: false,
    };
    if (status) node.status = status;
    if (focus && focus.id === e.id) node.badges = ['focus'];
    if (violated.has(e.id)) node.status = 'violated';
    nodes.push(node);
    nodeIds.add(e.id);
    addLegend(legend, `node:${e.kind}`, { kind: 'node', label: kindLabelOf(model, e.kind), shape, color });
  }

  // 4. Edges.
  /** @type {SceneEdge[]} */
  const edges = [];
  /** @type {Set<string>} */
  const edgeIds = new Set();
  const pushEdge = (/** @type {SceneEdge} */ e) => {
    if (edgeIds.has(e.id)) return;
    edgeIds.add(e.id);
    edges.push(e);
    addLegend(legend, `edge:${e.label}`, { kind: 'edge', label: e.label, line: e.line, color: e.color });
  };
  for (const [id, ends] of converted) {
    const r = /** @type {Entity} */ (model.entities.get(id));
    const rk = relKindOf(model, r.data.kind);
    /** @type {SceneEdge} */
    const e = {
      id, entityId: id, entityKind: 'relationship', from: ends.from, to: ends.to, line: rk.line, color: rk.color, dependencyClass: kindInfo(model.meta, r.data.kind).class,
      label: typeof r.data.label === 'string' && r.data.label ? r.data.label : rk.label,
    };
    if (violated.has(id)) e.status = 'violated';
    pushEdge(e);
  }
  for (const r of model.refs) {
    if (r.from === r.target || !nodeIds.has(r.from) || !nodeIds.has(r.target)) continue;
    const from = /** @type {Entity} */ (model.entities.get(r.from));
    const prop = referenceProperty(from, r);
    const defs = model.meta.entities?.[from.kind]?.properties ?? {};
    const label = prop === 'parent' ? 'inside' : (defs[prop]?.label ?? prop);
    pushEdge({ id: `${r.from}~${prop}~${r.target}`, entityId: from.id, entityKind: from.kind, from: r.from, to: r.target, line: 'solid', color: 'neutral', label });
  }

  return { viewId: view.id, projection: 'references', nodes, edges, legend: [...legend.values()], notes };
});

// ------------------------------------------------------------------- data

const DATA_SCOPE_COLORS = { shared: 'rose', 'per-session': 'teal', 'per-principal': 'blue', internal: 'slate' };

registerProjection('data', (model, view, ctx) => {
  void ctx;
  const records = model.byKind.record ?? [];
  const copies = model.byKind.copy ?? [];
  /** @type {string[]} */
  const notes = [PRESENTATION_NOTE];
  /** @type {Map<string, any>} */
  const legend = new Map();
  /** @type {SceneNode[]} */
  const nodes = [];
  /** @type {SceneEdge[]} */
  const edges = [];
  const { findings } = dataFindings(model);
  /** @type {Map<string, string[]>} */
  const findingsBy = new Map();
  for (const f of findings) findingsBy.set(f.entityId, [...(findingsBy.get(f.entityId) ?? []), f.rule]);
  /** @type {Set<string>} */
  const components = new Set();
  for (const r of records) if (typeof r.data.owner === 'string') components.add(r.data.owner);
  for (const c of copies) if (typeof c.data.heldBy === 'string') components.add(c.data.heldBy);
  for (const id of components) {
    const e = model.entities.get(id);
    if (!e || e.kind !== 'component') continue;
    const cat = categoryOf(model, e.data.category);
    nodes.push({ id, entityId: id, entityKind: 'component', label: entityLabel(e), sublabel: cat.label, shape: cat.shape, color: cat.color, parent: null, container: false });
    addLegend(legend, `cat:${e.data.category}`, { kind: 'node', label: cat.label, shape: cat.shape, color: cat.color });
  }
  const present = new Set(nodes.map((n) => n.id));
  for (const r of records) {
    const fields = Array.isArray(r.data.fields) ? r.data.fields.length : 0;
    /** @type {SceneNode} */
    const node = { id: r.id, entityId: r.id, entityKind: 'record', label: entityLabel(r), sublabel: `Record, ${fields} ${plural(fields, 'field', 'fields')}`, shape: 'cylinder', color: 'amber', parent: null, container: false };
    if (findingsBy.has(r.id)) { node.status = 'violated'; node.badges = /** @type {string[]} */ (findingsBy.get(r.id)); }
    nodes.push(node);
    present.add(r.id);
    addLegend(legend, 'node:record', { kind: 'node', label: 'Record', shape: 'cylinder', color: 'amber' });
    if (present.has(r.data.owner)) {
      edges.push({ id: `${r.id}~owner~${r.data.owner}`, entityId: r.id, entityKind: 'record', from: r.id, to: r.data.owner, line: 'solid', color: 'amber', label: 'owned by' });
      addLegend(legend, 'edge:owner', { kind: 'edge', label: 'Owned by', line: 'solid', color: 'amber' });
    }
  }
  for (const c of copies) {
    const scope = String(c.data.scope);
    const color = /** @type {any} */ (DATA_SCOPE_COLORS)[scope] ?? 'neutral';
    /** @type {SceneNode} */
    const node = { id: c.id, entityId: c.id, entityKind: 'copy', label: entityLabel(c), sublabel: `Copy, ${scope}`, shape: 'tablet', color, parent: null, container: false };
    if (findingsBy.has(c.id)) { node.status = 'violated'; node.badges = /** @type {string[]} */ (findingsBy.get(c.id)); }
    nodes.push(node);
    present.add(c.id);
    addLegend(legend, `node:copy:${scope}`, { kind: 'node', label: `Copy (${scope})`, shape: 'tablet', color });
    for (const r of sourcesOf(model, c)) {
      edges.push({ id: `${c.id}~of~${r.id}`, entityId: c.id, entityKind: 'copy', from: c.id, to: r.id, line: 'dashed', color: 'teal', label: 'copy of' });
      addLegend(legend, 'edge:of', { kind: 'edge', label: 'Copy of', line: 'dashed', color: 'teal' });
    }
    if (present.has(c.data.heldBy)) {
      edges.push({ id: `${c.id}~heldBy~${c.data.heldBy}`, entityId: c.id, entityKind: 'copy', from: c.id, to: c.data.heldBy, line: 'dotted', color: 'neutral', label: 'held by' });
      addLegend(legend, 'edge:heldBy', { kind: 'edge', label: 'Held by', line: 'dotted', color: 'neutral' });
    }
  }
  notes.push(`${records.length} ${plural(records.length, 'record', 'records')} and ${copies.length} ${plural(copies.length, 'copy', 'copies')}, with the components that own or hold them.`);
  notes.push(findings.length ? `${findings.length} data-rule ${plural(findings.length, 'finding marks', 'findings mark')} ${plural(findingsBy.size, 'its entity', 'their entities')} as violated; the badge names the rule.` : 'The data rules report no finding.');
  if (!records.length && !copies.length) notes.push('The model declares no records or copies.');
  return { viewId: view.id, projection: 'data', nodes, edges, legend: [...legend.values()], notes };
}, { available: (model) => (model.byKind.record ?? []).length + (model.byKind.copy ?? []).length > 0 });

// The reader projection draws no scene: the application shows a reading surface in its
// place, built from the view's reader blocks by src/core/reader.js.
registerProjection('reader', (model, view, ctx) => {
  void model; void ctx;
  return { viewId: view.id, projection: 'reader', nodes: [], edges: [], legend: [], notes: ['A reading view: the page replaces the scene.'] };
});
