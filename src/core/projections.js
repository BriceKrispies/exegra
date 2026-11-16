// Projections: derive a SceneModel (flat nodes and edges) from the canonical
// semantic model. A view is never a separate dataset; every node and edge is
// backed by a real entity. Positions are decided elsewhere (layout.js).

import { componentOf, ancestorsOf, descendantsOf, entityLabel } from './query.js';
import { own } from './own.js';
import { dataFindings, sourcesOf } from './data-model.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').SceneModel} SceneModel */
/** @typedef {import('./types.js').SceneNode} SceneNode */
/** @typedef {import('./types.js').SceneEdge} SceneEdge */

/**
 * @typedef {Object} ProjectionContext
 * @property {Set<string>} [collapsed]
 * @property {Set<string>} [hidden]
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
const CLAIM_COLORS = { verified: 'green', supported: 'teal', violated: 'red', inconclusive: 'amber', 'not-evaluated': 'neutral' };
const CLAIM_STATUS_LABELS = { verified: 'verified', supported: 'supported', violated: 'violated', inconclusive: 'inconclusive', 'not-evaluated': 'not evaluated' };

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

registerProjection('structural', (model, view, ctx) => {
  const filter = view.filter ?? {};
  const display = view.display ?? {};
  const comps = model.byKind.component ?? [];
  const compById = new Map(comps.map((c) => [c.id, c]));
  const notes = [PRESENTATION_NOTE];

  // 1. Which components pass the scope and filters.
  /** @type {Set<string>} */
  let inScope = new Set(comps.map((c) => c.id));
  const restrictTo = (/** @type {string} */ rootId, /** @type {string} */ label) => {
    if (!compById.has(rootId)) return;
    const keep = new Set([rootId, ...descendantsOf(model, rootId).map((c) => c.id)]);
    inScope = new Set([...inScope].filter((id) => keep.has(id)));
    notes.push(`${label} ${entityLabel(/** @type {Entity} */ (compById.get(rootId)))} and what it contains.`);
  };
  if (typeof filter.within === 'string') restrictTo(filter.within, 'Limited to the subsystem');
  if (typeof ctx.isolate === 'string' && ctx.isolate) restrictTo(ctx.isolate, 'Isolated to');

  const cats = Array.isArray(filter.categories) && filter.categories.length ? filter.categories : null;
  const tags = Array.isArray(filter.tags) && filter.tags.length ? filter.tags : null;
  if (cats || tags) {
    /** @type {Set<string>} */
    const matching = new Set();
    for (const id of inScope) {
      const c = /** @type {Entity} */ (compById.get(id));
      if (cats && !cats.includes(c.data.category)) continue;
      if (tags && !(Array.isArray(c.data.tags) && c.data.tags.some((/** @type {string} */ t) => tags.includes(t)))) continue;
      matching.add(id);
    }
    const keep = new Set(matching);
    for (const id of matching) for (const a of ancestorsOf(model, id)) if (inScope.has(a)) keep.add(a);
    inScope = keep;
    if (cats) notes.push(`Filtered to categories: ${cats.join(', ')}.`);
    if (tags) notes.push(`Filtered to tags: ${tags.join(', ')}.`);
  }
  const kinds = Array.isArray(filter.relationshipKinds) && filter.relationshipKinds.length ? filter.relationshipKinds : null;
  if (kinds) notes.push(`Filtered to relationship kinds: ${kinds.join(', ')}.`);

  // 2. Hidden components (and everything inside them).
  let hiddenCount = 0;
  if (ctx.hidden && ctx.hidden.size) {
    for (const id of [...inScope]) {
      if (ctx.hidden.has(id) || ancestorsOf(model, id).some((a) => /** @type {Set<string>} */ (ctx.hidden).has(a))) { inScope.delete(id); hiddenCount++; }
    }
    if (hiddenCount) notes.push(`${hiddenCount} ${plural(hiddenCount, 'component is', 'components are')} hidden; relationships touching ${plural(hiddenCount, 'it are', 'them are')} not drawn.`);
  }
  if (inScope.size === 0) notes.push('No components match this view.');

  // 3. Collapse: the outermost collapsed visible subsystem stands for its subtree.
  /** @type {Map<string, string>} component id -> id of the node that represents it */
  const rep = new Map();
  /** @type {Set<string>} */
  const shown = new Set();
  /** @type {Set<string>} */
  const collapsedShown = new Set();
  const collapsed = ctx.collapsed ?? new Set();
  for (const c of comps) {
    if (!inScope.has(c.id)) continue;
    const chain = [...ancestorsOf(model, c.id).reverse(), c.id];
    const hit = chain.find((id) => collapsed.has(id) && inScope.has(id) && compById.get(id)?.data.kind === 'subsystem' && hasChildren(model, id));
    const r = hit ?? c.id;
    rep.set(c.id, r);
    if (r === c.id) shown.add(c.id);
    if (hit) collapsedShown.add(hit);
  }
  for (const id of collapsedShown) shown.add(id);

  // 4. Nodes.
  const violated = violatedIds(ctx);
  const colorBy = display.colorBy ?? 'category';
  const zones = colorBy === 'trustZone'
    ? [...new Set(comps.filter((c) => shown.has(c.id) && typeof c.data.trustZone === 'string' && c.data.trustZone).map((c) => c.data.trustZone))].sort()
    : [];
  const portCounts = new Map();
  if (display.showPorts === true) for (const p of model.byKind.port ?? []) if (p.owner) portCounts.set(p.owner, (portCounts.get(p.owner) ?? 0) + 1);

  /** @type {Map<string, any>} */
  const legend = new Map();
  /** @type {SceneNode[]} */
  const nodes = [];
  /** @type {Set<string>} */
  const emitted = new Set();
  const nearestShownParent = (/** @type {string} */ id) => {
    for (const a of ancestorsOf(model, id)) if (shown.has(a)) return a;
    return null;
  };
  /** @param {Entity} c */
  const emit = (c) => {
    if (emitted.has(c.id) || !shown.has(c.id)) return;
    const parent = nearestShownParent(c.id);
    if (parent) emit(/** @type {Entity} */ (compById.get(parent)));
    emitted.add(c.id);
    const cat = categoryOf(model, c.data.category);
    const isCollapsed = collapsedShown.has(c.id);
    const childShown = !isCollapsed && c.data.kind === 'subsystem' && comps.some((x) => shown.has(x.id) && nearestShownParent(x.id) === c.id);
    /** @type {string} */
    let color = cat.color;
    /** @type {string} */
    let legendId = String(c.data.category);
    let legendLabel = cat.label;
    if (colorBy === 'implementation') {
      const st = c.data.implementation?.status;
      const m = own(/** @type {any} */ (IMPLEMENTATION_COLORS), st);
      color = m ? m[0] : 'neutral';
      legendId = `implementation:${st ?? 'absent'}`;
      legendLabel = m ? `Implementation: ${m[1]}` : 'Implementation: not stated';
    } else if (colorBy === 'trustZone') {
      const z = c.data.trustZone;
      color = z ? ZONE_PALETTE[zones.indexOf(z) % ZONE_PALETTE.length] : 'neutral';
      legendId = `zone:${z ?? 'none'}`;
      legendLabel = z ? `Trust zone: ${z}` : 'Trust zone: none stated';
    }
    /** @type {string[]} */
    const badges = [];
    if (isCollapsed) badges.push(`${descendantsOf(model, c.id).length} inside`);
    if (portCounts.has(c.id)) { const n = portCounts.get(c.id); badges.push(`${n} ${plural(n, 'port', 'ports')}`); }
    // When the whole system is illustrative the scene notes say so once; per-node badges mark only exceptions.
    if (c.data.illustrative === true && model.system?.data.illustrative !== true) badges.push('illustrative');
    /** @type {SceneNode} */
    const node = {
      id: c.id, entityId: c.id, entityKind: 'component', label: entityLabel(c), sublabel: cat.label,
      shape: childShown ? 'container' : cat.shape, color, parent, container: childShown,
    };
    if (isCollapsed) node.collapsed = true;
    if (badges.length) node.badges = badges;
    if (violated.has(c.id)) node.status = 'violated';
    nodes.push(node);
    if (childShown) addLegend(legend, 'container', { kind: 'node', label: 'Subsystem (contains components)', shape: 'container', color: 'neutral' });
    else addLegend(legend, legendId, { kind: 'node', label: legendLabel, shape: colorBy === 'category' ? cat.shape : 'box', color });
  };
  for (const c of comps) emit(c);

  // 5. Edges.
  /** @type {SceneEdge[]} */
  const edges = [];
  let lifted = 0;
  let internal = 0;
  let bundled = 0;
  /** @type {Map<string, {edge: SceneEdge, count: number}>} */
  const bundles = new Map();
  for (const r of model.byKind.relationship ?? []) {
    if (kinds && !kinds.includes(r.data.kind)) continue;
    const fc = componentOf(model, r.data.from);
    const tc = componentOf(model, r.data.to);
    if (!fc || !tc) continue;
    const from = rep.get(fc.id);
    const to = rep.get(tc.id);
    if (!from || !to) continue;
    const isLifted = from !== fc.id || to !== tc.id;
    if (isLifted && from === to) { internal++; continue; }
    if (isLifted) lifted++;
    const rk = relKindOf(model, r.data.kind);
    /** @type {SceneEdge} */
    const e = {
      id: r.id, entityId: r.id, entityKind: 'relationship', from, to, line: rk.line, color: rk.color,
      label: typeof r.data.label === 'string' && r.data.label ? r.data.label : rk.label,
    };
    if (isLifted) e.lifted = true;
    if (violated.has(r.id)) e.status = 'violated';
    if (isLifted) {
      // Several relationships of one kind between the same two drawn nodes become
      // one line that says how many it stands for (it is backed by the first of them).
      const key = `${from} ${to} ${r.data.kind}`;
      const first = bundles.get(key);
      if (first) {
        first.count++;
        first.edge.label = `${rk.label} ×${first.count}`;
        if (e.status === 'violated') first.edge.status = 'violated';
        bundled++;
        continue;
      }
      bundles.set(key, { edge: e, count: 1 });
      e.label = rk.label;
    }
    edges.push(e);
    addLegend(legend, `rel:${r.data.kind}`, { kind: 'edge', label: rk.label, line: rk.line, color: rk.color });
  }
  if (lifted) notes.push(`${lifted} ${plural(lifted, 'relationship is', 'relationships are')} drawn to a collapsed subsystem rather than to the component inside it.`);
  if (bundled) notes.push(`Relationships of one kind between the same two drawn nodes are bundled into one line labelled with their number (${bundled} ${plural(bundled, 'line', 'lines')} saved); expand the subsystem to see each.`);
  if (internal) notes.push(`${internal} ${plural(internal, 'relationship', 'relationships')} inside collapsed subsystems ${plural(internal, 'is', 'are')} not drawn.`);
  if (colorBy === 'implementation') notes.push('Color shows how each component is realised; shape still shows its category.');
  if (colorBy === 'trustZone') notes.push('Color shows the declared trust zone; shape still shows its category.');
  if (display.showPorts === true) notes.push('Ports are not drawn as separate nodes; a badge counts them.');

  return { viewId: view.id, projection: 'structural', nodes, edges, legend: [...legend.values()], notes };
});

/** @param {Model} model @param {string} id */
function hasChildren(model, id) {
  return (model.byKind.component ?? []).some((c) => c.data.parent === id);
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
    if (e.kind === 'component') compsOut.add(e.id);
    else if (e.kind === 'port') { if (e.owner) compsOut.add(e.owner); }
    else if (e.kind === 'relationship') {
      const f = componentOf(model, e.data.from);
      const t = componentOf(model, e.data.to);
      if (f && t) { compsOut.add(f.id); compsOut.add(t.id); relsOut.add(e.id); } else skip(e);
    } else if (e.kind === 'behavior') {
      if (typeof e.data.subject === 'string' && model.entities.get(e.data.subject)?.kind === 'component') compsOut.add(e.data.subject);
    } else skip(e);
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
      const f = componentOf(model, r.data.from);
      const t = componentOf(model, r.data.to);
      if (f && t && compIds.has(f.id) && compIds.has(t.id)) shownRels.add(r.id);
    }
  }
  for (const r of model.byKind.relationship ?? []) {
    if (!shownRels.has(r.id)) continue;
    const f = componentOf(model, r.data.from);
    const t = componentOf(model, r.data.to);
    if (!f || !t || !compNodeIds.has(f.id) || !compNodeIds.has(t.id)) continue;
    const rk = relKindOf(model, r.data.kind);
    /** @type {SceneEdge} */
    const e = { id: r.id, entityId: r.id, entityKind: 'relationship', from: f.id, to: t.id, line: rk.line, color: rk.color, label: typeof r.data.label === 'string' && r.data.label ? r.data.label : rk.label };
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
    const f = componentOf(model, e.data.from);
    const t = componentOf(model, e.data.to);
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
      id, entityId: id, entityKind: 'relationship', from: ends.from, to: ends.to, line: rk.line, color: rk.color,
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
