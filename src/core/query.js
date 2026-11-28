// Read-only queries over the semantic model. Shared by projections, claims,
// generators, the inspector and the agent CLI so that every consumer answers
// "what depends on what" the same way.

import { own } from './own.js';
import { kindInfo, mediatedInteractions, isConnector, provenanceOf } from './interactions.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Ref} Ref */

/**
 * Human label of an entity: its name, else its statement, else its id.
 * @param {Entity} e
 */
export function entityLabel(e) {
  if (typeof e.data.name === 'string' && e.data.name) return e.data.name;
  if (typeof e.data.statement === 'string') return e.data.statement.length > 72 ? e.data.statement.slice(0, 69) + '...' : e.data.statement;
  if (typeof e.data.label === 'string' && e.data.label) return e.data.label;
  return e.id;
}

/**
 * The component an id stands for: the component itself, or the owner of a port.
 * @param {Model} model @param {string} id
 * @returns {Entity|undefined}
 */
export function componentOf(model, id) {
  const e = model.entities.get(id);
  if (!e) {
    // A module element stands for the component that declares it.
    const m = typeof id === 'string' && id.startsWith(MODULE_PREFIX) ? elementsOf(model).get(id) : undefined;
    return m?.kind === 'module' && m.owners?.length ? model.entities.get(m.owners[0]) : undefined;
  }
  if (e.kind === 'component') return e;
  if (e.kind === 'port' && e.owner) return model.entities.get(e.owner);
  return undefined;
}

/**
 * The components an entity stands for when it has no node of its own in a structural picture: a component
 * itself; a port's owner; a behavior's subject (or the owner of its subject port); a state's or transition's
 * behavior's subject; the subjects of a scenario's behaviors; a relationship's two endpoints. Empty for anything
 * else. The one place this mapping lives: projections, flows and the session's highlighting all ask it.
 * @param {Model} model @param {string} id
 * @returns {string[]}
 */
export function componentsFor(model, id) {
  const e = model.entities.get(id);
  if (!e) return [];
  /** @param {any} x */
  const comp = (x) => (typeof x === 'string' ? componentOf(model, x)?.id : undefined);
  /** @param {Entity|undefined} b */
  const subjectOf = (b) => (b && b.kind === 'behavior' ? comp(b.data.subject) : undefined);
  /** @type {(string|undefined)[]} */
  let out = [];
  if (e.kind === 'component' || e.kind === 'port') out = [comp(e.id)];
  else if (e.kind === 'behavior') out = [subjectOf(e)];
  else if ((e.kind === 'state' || e.kind === 'transition') && e.owner) out = [subjectOf(model.entities.get(e.owner))];
  else if (e.kind === 'scenario') out = (Array.isArray(e.data.behaviors) ? e.data.behaviors : []).map((/** @type {any} */ b) => subjectOf(typeof b === 'string' ? model.entities.get(b) : undefined));
  else if (e.kind === 'relationship') out = [comp(e.data.from), comp(e.data.to)];
  return [...new Set(out.filter((x) => typeof x === 'string'))];
}

/**
 * The components whose logical parent is `parentId`. null gives the top-level components: those with no
 * parent and those whose parent is the system (the root element).
 * @param {Model} model @param {string|null} parentId
 */
export function childrenOf(model, parentId) {
  const systemId = model.system?.id ?? null;
  return (model.byKind.component ?? []).filter((c) => {
    const p = c.data.parent ?? null;
    return p === parentId || (parentId === null && p !== null && p === systemId);
  });
}

/**
 * Ancestor component ids in the logical hierarchy, nearest first. The system, when it is the parent of a
 * top-level component, is not a component and is not listed (hierarchyOf includes it).
 * @param {Model} model @param {string} id
 */
export function ancestorsOf(model, id) {
  const out = [];
  const seen = new Set([id]);
  let cur = model.entities.get(id);
  while (cur && typeof cur.data.parent === 'string' && !seen.has(cur.data.parent)) {
    const next = model.entities.get(cur.data.parent);
    if (next && next.kind !== 'component') break;
    out.push(cur.data.parent);
    seen.add(cur.data.parent);
    cur = next;
  }
  return out;
}

/** All components nested inside a subsystem, at any depth. @param {Model} model @param {string} id */
export function descendantsOf(model, id) {
  /** @type {Entity[]} */
  const out = [];
  const walk = (/** @type {string} */ pid) => {
    for (const c of childrenOf(model, pid)) { out.push(c); walk(c.id); }
  };
  walk(id);
  return out;
}

/** Entities nested in `id` through ownership (ports, states, transitions), any depth. @param {Model} model @param {string} id */
export function ownedBy(model, id) {
  /** @type {Entity[]} */
  const out = [];
  for (const e of model.entities.values()) {
    let o = e.owner;
    while (o) {
      if (o === id) { out.push(e); break; }
      o = model.entities.get(o)?.owner ?? null;
    }
  }
  return out;
}

/**
 * References pointing at `id` from other entities.
 * @param {Model} model @param {string} id
 * @returns {Ref[]}
 */
export function inboundRefs(model, id) {
  return model.refs.filter((r) => r.target === id && r.from !== id);
}

/**
 * Relationships touching a component (directly or through one of its ports).
 * @param {Model} model @param {string} componentId
 * @returns {{relationship: Entity, direction: 'out'|'in', other: Entity|undefined, viaPort?: string}[]}
 */
export function relationshipsOf(model, componentId) {
  const out = [];
  for (const r of model.byKind.relationship ?? []) {
    const from = componentOf(model, r.data.from);
    const to = componentOf(model, r.data.to);
    if (from?.id === componentId) out.push({ relationship: r, direction: /** @type {'out'} */ ('out'), other: to, viaPort: r.data.from !== componentId ? r.data.from : undefined });
    if (to?.id === componentId) out.push({ relationship: r, direction: /** @type {'in'} */ ('in'), other: from, viaPort: r.data.to !== componentId ? r.data.to : undefined });
  }
  return out;
}

/**
 * Directed component graph. Edges are relationships resolved to components. Each edge states its relationship
 * `rel`, its `kind`, the dependency `class` of that kind (a legacy kind has the class of the kind it behaves as)
 * and the relationship's `provenance`.
 *
 * Filters, all of which must hold: `kinds` (relationship kinds), `classes` (dependency classes `static`,
 * `runtime`, `none`), `dependencyOnly` (class not `none`, the `dependency` flag) and `where`.
 * `contractConnectors` removes every relationship that touches a connector element (a component of kind
 * `connector`) and adds, for each producer and consumer paired through one, a `notifies` edge from the
 * producer to the consumer that names the connector (`connector`); the kind and class filters then apply to
 * that `notifies` edge.
 * @param {Model} model
 * @param {{kinds?: string[]|null, classes?: string[]|null, dependencyOnly?: boolean, where?: {property: string, values: string[]}|null, contractConnectors?: boolean}} [opts]
 * @returns {Map<string, {to: string, rel: string, kind: string, class: string, provenance: string, connector?: string}[]>}
 */
export function componentGraph(model, opts = {}) {
  /** @type {Map<string, {to: string, rel: string, kind: string, class: string, provenance: string, connector?: string}[]>} */
  const g = new Map();
  for (const c of model.byKind.component ?? []) g.set(c.id, []);
  /** @param {string} kind */
  const passes = (kind) => {
    if (opts.kinds && !opts.kinds.includes(kind)) return null;
    const cls = kindInfo(model.meta, kind).class;
    if (opts.classes && !opts.classes.includes(cls)) return null;
    if (opts.dependencyOnly && !own(model.meta.relationshipKinds, kind)?.dependency) return null;
    return cls;
  };
  for (const r of model.byKind.relationship ?? []) {
    const cls = passes(r.data.kind);
    if (cls === null) continue;
    if (opts.where && !opts.where.values.includes(r.data[opts.where.property])) continue;
    const from = componentOf(model, r.data.from);
    const to = componentOf(model, r.data.to);
    if (!from || !to) continue;
    // An import between two modules of one component is internal to it, not an edge of the component graph.
    if (from.id === to.id && provenanceOf(r) !== 'declared') continue;
    if (opts.contractConnectors && (isConnector(from) || isConnector(to))) continue;
    g.get(from.id)?.push({ to: to.id, rel: r.id, kind: r.data.kind, class: cls, provenance: provenanceOf(r) });
  }
  if (opts.contractConnectors) {
    const cls = passes('notifies');
    if (cls !== null && !opts.where) {
      for (const m of mediatedInteractions(model)) g.get(m.from)?.push({ to: m.to, rel: m.id, kind: m.kind, class: cls, provenance: m.provenance, connector: m.connector });
    }
  }
  return g;
}

/**
 * Dependency traversal from one component.
 * direction 'out' = what it depends on; 'in' = what depends on it.
 * By default follows only relationship kinds flagged `dependency` in the meta-model.
 * @param {Model} model @param {string} id
 * @param {{direction?: 'out'|'in', transitive?: boolean, kinds?: string[], classes?: string[]}} [opts]
 * @returns {{id: string, via: string, depth: number}[]}
 */
export function dependencies(model, id, opts = {}) {
  const direction = opts.direction ?? 'out';
  const g = componentGraph(model, opts.kinds || opts.classes ? { kinds: opts.kinds, classes: opts.classes } : { dependencyOnly: true });
  /** @type {Map<string, {to: string, rel: string}[]>} */
  let adj = g;
  if (direction === 'in') {
    adj = new Map([...g.keys()].map((k) => [k, []]));
    for (const [from, edges] of g) for (const e of edges) adj.get(e.to)?.push({ to: from, rel: e.rel });
  }
  const out = [];
  const seen = new Set([id]);
  let frontier = [id];
  let depth = 0;
  while (frontier.length) {
    depth++;
    const next = [];
    for (const cur of frontier) for (const e of adj.get(cur) ?? []) {
      if (seen.has(e.to)) continue;
      seen.add(e.to);
      out.push({ id: e.to, via: e.rel, depth });
      next.push(e.to);
    }
    if (!opts.transitive) break;
    frontier = next;
  }
  return out;
}

/**
 * Components picked by a selector (see claim-methods.js). A component nested
 * inside a selected subsystem is selected too, unless `exact` is set. `facet`
 * selects the members of a facet (facetMembers): a declared facet or a tag.
 * `outside` selects the complement of an element (isOutside), and `except` removes
 * the listed elements (and what they contain, unless `exact`) from the selection.
 * @param {Model} model @param {any} selector @param {{exact?: boolean}} [opts]
 * @returns {Entity[]}
 */
/**
 * The subjects of a claim: those it declares, or, when it declares none, the entities its evaluation's parameters
 * name (WG-5705): every component a selector parameter selects and every id of an id-list parameter other than a cut,
 * in the order the parameters are written. A structural claim that checks named components names its subjects there,
 * so declaring them again is redundant.
 * @param {Model} model @param {Entity} claim @param {Record<string, {type: string}>} [params] the method's parameter
 *   types (src/core/claim-methods.js), passed in by callers that know the registry
 * @returns {string[]}
 */
export function claimSubjects(model, claim, params) {
  const declared = Array.isArray(claim.data.subjects) ? claim.data.subjects.filter((/** @type {any} */ s) => typeof s === 'string') : null;
  if (declared && declared.length) return declared;
  const ev = claim.data.evaluate;
  if (!params || !ev || typeof ev !== 'object') return declared ?? [];
  /** @type {string[]} */
  const out = [];
  for (const [name, value] of Object.entries(ev)) {
    const type = params[name]?.type;
    if (!type) continue;
    if (type === 'selector') out.push(...selectComponents(model, value).map((c) => c.id));
    else if (type.startsWith('ids:') && type !== 'ids:cut') out.push(...[].concat(value).filter((x) => typeof x === 'string'));
  }
  return [...new Set(out)];
}

export function selectComponents(model, selector, opts = {}) {
  const all = model.byKind.component ?? [];
  /** @type {(c: Entity) => boolean} */
  let match;
  if (typeof selector === 'string') match = (c) => c.id === selector;
  else if (Array.isArray(selector)) match = (c) => selector.includes(c.id);
  else if (selector && typeof selector === 'object') {
    if (selector.all === false || !Object.keys(selector).length) return [];
    const cats = selector.category === undefined ? null : [].concat(selector.category);
    const ids = selector.ids === undefined ? null : [].concat(selector.ids);
    const facet = typeof selector.facet === 'string' ? facetMembers(model, selector.facet) : null;
    match = (c) =>
      (!ids || ids.includes(/** @type {never} */ (c.id))) &&
      (!cats || cats.includes(/** @type {never} */ (c.data.category))) &&
      (selector.kind === undefined || (c.data.kind ?? 'component') === selector.kind) &&
      (selector.tag === undefined || (Array.isArray(c.data.tags) && c.data.tags.includes(selector.tag))) &&
      (selector.trustZone === undefined || c.data.trustZone === selector.trustZone) &&
      (facet === null || facet.has(c.id)) &&
      (selector.within === undefined || ancestorsOf(model, c.id).includes(selector.within)) &&
      (selector.outside === undefined || isOutside(model, c.id, selector.outside));
  } else return [];
  const direct = all.filter(match);
  const removed = exceptedIds(model, selector, opts.exact === true);
  if (opts.exact) return direct.filter((c) => !removed.has(c.id));
  const picked = new Set(direct.map((c) => c.id));
  for (const c of direct) for (const d of descendantsOf(model, c.id)) picked.add(d.id);
  return all.filter((c) => picked.has(c.id) && !removed.has(c.id));
}

/**
 * Whether a component lies outside an element: it is not the element, not inside it and not one of its ancestors
 * (an ancestor contains it). The complement selector {outside: X} picks exactly these.
 * @param {Model} model @param {string} id @param {any} element
 */
export function isOutside(model, id, element) {
  if (typeof element !== 'string') return false;
  if (id === element) return false;
  if (ancestorsOf(model, id).includes(element)) return false;
  return !ancestorsOf(model, element).includes(id);
}

/**
 * The ids a selector's `except` removes: each listed id ({id, reason} or a bare id) and, unless exact, what it
 * contains.
 * @param {Model} model @param {any} selector @param {boolean} exact
 * @returns {Set<string>}
 */
export function exceptedIds(model, selector, exact) {
  /** @type {Set<string>} */
  const out = new Set();
  if (!selector || typeof selector !== 'object' || Array.isArray(selector) || !Array.isArray(selector.except)) return out;
  for (const x of selector.except) {
    const id = typeof x === 'string' ? x : x && typeof x === 'object' && typeof x.id === 'string' ? x.id : null;
    if (id === null) continue;
    out.add(id);
    if (!exact) for (const d of descendantsOf(model, id)) out.add(d.id);
  }
  return out;
}

/**
 * Every element id a selector names explicitly (a string, the ids of an array or of `ids`, `within`, `outside`
 * and the ids in `except`): what a claim stated at a cut must not name below the cut.
 * @param {any} selector @returns {string[]}
 */
export function selectorNames(selector) {
  if (typeof selector === 'string') return [selector];
  if (Array.isArray(selector)) return selector.filter((x) => typeof x === 'string');
  if (!selector || typeof selector !== 'object') return [];
  /** @type {string[]} */
  const out = [];
  for (const x of [].concat(selector.ids ?? [])) if (typeof x === 'string') out.push(x);
  for (const k of ['within', 'outside']) if (typeof selector[k] === 'string') out.push(selector[k]);
  for (const x of Array.isArray(selector.except) ? selector.except : []) {
    const id = typeof x === 'string' ? x : x && typeof x === 'object' ? x.id : null;
    if (typeof id === 'string') out.push(id);
  }
  return out;
}

/**
 * Contracts a component is bound to through its ports and relationships.
 * @param {Model} model @param {string} componentId
 * @returns {{contract: Entity, via: string, role: string}[]}
 */
export function contractsOf(model, componentId) {
  const out = [];
  for (const p of model.byKind.port ?? []) {
    if (p.owner !== componentId || typeof p.data.contract !== 'string') continue;
    const c = model.entities.get(p.data.contract);
    if (c) out.push({ contract: c, via: p.id, role: p.data.direction });
  }
  for (const { relationship, direction } of relationshipsOf(model, componentId)) {
    if (typeof relationship.data.contract !== 'string') continue;
    const c = model.entities.get(relationship.data.contract);
    if (c) out.push({ contract: c, via: relationship.id, role: direction === 'out' ? 'consumer' : 'provider' });
  }
  return out;
}

/**
 * The top-level section (or owner property) entities of a kind are declared in.
 * @param {Model} model @param {string} kind
 * @returns {{section?: string, ownerKind?: string, property?: string}|null}
 */
export function declarationSite(model, kind) {
  for (const [section, def] of Object.entries(model.meta.sections)) {
    if (/** @type {any} */ (def).entity === kind && !(/** @type {any} */ (def).single)) return { section };
  }
  for (const [ownerKind, def] of Object.entries(model.meta.entities)) {
    for (const [property, p] of Object.entries(/** @type {any} */ (def).properties)) {
      if (/** @type {any} */ (p).type === 'entities' && /** @type {any} */ (p).entity === kind) return { ownerKind, property };
    }
  }
  return null;
}

// ---------------------------------------------------------------------------
// Elements, hierarchies, facets and cuts (docs/model-and-format.md, "Elements, hierarchies, facets and cuts")
//
// The elements are the system, every component, and the module elements derived from each component's
// implementation.modules. A hierarchy is a forest over all of them: `logical` from component.parent (the
// system may be a parent) with each module element under the component that declares it, and every
// declared hierarchy from its groups and groupBy. A cut of a hierarchy is an antichain that every
// root-to-leaf path meets once; its abstraction map sends each element at or below it to its unique
// ancestor-or-self on it. Everything here is derived from the model and cached per model (models are
// immutable snapshots). Problems are reported, never thrown; validate.js turns them into diagnostics.
// ---------------------------------------------------------------------------

/** The default hierarchy, declared by component.parent. */
export const LOGICAL = 'logical';
/** Module element ids are this prefix and the module path; no entity id can take this form. */
export const MODULE_PREFIX = 'module:';
/** The element kinds every specification has; elementKinds adds more. */
export const BUILTIN_ELEMENT_KINDS = Object.freeze(['system', 'subsystem', 'component', 'module', 'actor', 'store', 'connector', 'external']);

/**
 * @typedef {{id: string, kind: string, entity: Entity|null, path?: string, owners?: string[]}} Element
 * entity is null for a module element; path and owners (the components that declare it, in declaration
 * order) are set only on module elements.
 * @typedef {{code: string, element: string, others?: string[], message: string, at?: {entity: string, path: (string|number)[]}}} HierarchyProblem
 * @typedef {{id: string, parent: Map<string, string>, children: Map<string, string[]>, roots: string[], depth: Map<string, number>, order: string[], problems: HierarchyProblem[]}} Hierarchy
 * @typedef {{expand?: string[], depth?: number, finest?: boolean, blocks?: string[]}} CutSpec
 * @typedef {{blocks: string[], expanded: string[], problems: HierarchyProblem[]}} CutBlocks
 */

/** @type {WeakMap<object, Map<string, any>>} */
const derivedCache = new WeakMap();
/**
 * @template T @param {Model} model @param {string} key @param {() => T} make @returns {T}
 */
function cached(model, key, make) {
  let m = derivedCache.get(model);
  if (!m) { m = new Map(); derivedCache.set(model, m); }
  if (!m.has(key)) m.set(key, make());
  return m.get(key);
}

/** The id of the module element for a module path. @param {string} path */
export function moduleId(path) {
  return MODULE_PREFIX + path.replace(/\\/g, '/');
}

/**
 * The source of module elements: one declaration per path in a component's implementation.modules, in
 * declaration order, duplicates kept. This is the one place module elements come from. The declaration places
 * a module element under a component; when extracted facts are attached to the model (src/core/extraction.js), each
 * element says whether the facts found files for it (`extracted`), and a declaration the facts do not find stays
 * what it is declared. With no facts it falls back to implementation.modules alone.
 * @param {Model} model
 * @returns {{id: string, path: string, component: string, index: number, extracted?: boolean}[]}
 */
export function moduleDeclarations(model) {
  return cached(model, 'moduleDeclarations', () => {
    /** @type {{id: string, path: string, component: string, index: number}[]} */
    const out = [];
    for (const c of model.byKind.component ?? []) {
      const modules = c.data.implementation?.modules;
      if (!Array.isArray(modules)) continue;
      modules.forEach((/** @type {any} */ m, /** @type {number} */ index) => {
        if (typeof m === 'string' && m !== '') out.push({ id: moduleId(m), path: m.replace(/\\/g, '/'), component: c.id, index });
      });
    }
    const files = /** @type {any} */ (model).extraction?.facts?.files;
    if (Array.isArray(files)) {
      const paths = files.map((/** @type {any} */ f) => f.path);
      const have = new Set(paths);
      for (const d of /** @type {any[]} */ (out)) d.extracted = d.path.endsWith('/') ? paths.some((/** @type {string} */ f) => f.startsWith(d.path)) : have.has(d.path);
    }
    return out;
  });
}

/**
 * Every element by id: the system, the components (in declaration order), then the module elements.
 * @param {Model} model @returns {Map<string, Element>}
 */
export function elementsOf(model) {
  return cached(model, 'elements', () => {
    /** @type {Map<string, Element>} */
    const out = new Map();
    if (model.system) out.set(model.system.id, { id: model.system.id, kind: 'system', entity: model.system });
    for (const c of model.byKind.component ?? []) out.set(c.id, { id: c.id, kind: typeof c.data.kind === 'string' ? c.data.kind : 'component', entity: c });
    for (const d of moduleDeclarations(model)) {
      const e = out.get(d.id);
      if (e) { if (e.owners && !e.owners.includes(d.component)) e.owners.push(d.component); continue; }
      out.set(d.id, { id: d.id, kind: 'module', entity: null, path: d.path, owners: [d.component] });
    }
    return out;
  });
}

/** The element kind of an element id, or null. @param {Model} model @param {string} id */
export function elementKindOf(model, id) {
  return elementsOf(model).get(id)?.kind ?? null;
}

/** The hierarchy ids of a model: logical first, then the declared ones. @param {Model} model */
export function hierarchyIds(model) {
  return [LOGICAL, ...(model.byKind.hierarchy ?? []).map((h) => h.id).filter((id) => id !== LOGICAL)];
}

/**
 * A hierarchy as a forest over every element, or null when no hierarchy has that id.
 * @param {Model} model @param {string} [id] default logical
 * @returns {Hierarchy|null}
 */
export function hierarchyOf(model, id = LOGICAL) {
  return cached(model, `hierarchy:${id}`, () => {
    const elements = elementsOf(model);
    /** @type {Map<string, string>} */
    const parent = new Map();
    /** @type {HierarchyProblem[]} */
    const problems = [];
    const isElement = (/** @type {any} */ x) => typeof x === 'string' && elements.has(x);
    if (id === LOGICAL) {
      for (const c of model.byKind.component ?? []) if (isElement(c.data.parent) && c.data.parent !== c.id) parent.set(c.id, c.data.parent);
    } else {
      const h = model.entities.get(id);
      if (!h || h.kind !== 'hierarchy') return null;
      /** @type {Map<string, string>} */
      const placed = new Map();
      const groups = Array.isArray(h.data.groups) ? h.data.groups : [];
      groups.forEach((/** @type {any} */ g, /** @type {number} */ gi) => {
        if (!g || typeof g !== 'object') return;
        const p = g.parent;
        (Array.isArray(g.members) ? g.members : []).forEach((/** @type {any} */ m, /** @type {number} */ mi) => {
          if (!isElement(m)) return;
          const first = placed.get(m);
          if (first !== undefined && first !== p) {
            problems.push({ code: 'multiple-parents', element: m, others: [first, p], message: `"${m}" is placed under "${first}" and under "${p}" in hierarchy "${id}"; an element has at most one parent in a hierarchy.`, at: { entity: id, path: ['groups', gi, 'members', mi] } });
            return;
          }
          if (first !== undefined) return;
          placed.set(m, p);
          if (isElement(p) && p !== m) parent.set(m, p);
        });
      });
      const by = h.data.groupBy;
      if (by && typeof by === 'object' && typeof by.property === 'string' && by.parents && typeof by.parents === 'object') {
        /** @type {Set<string>} */
        const reported = new Set();
        for (const c of model.byKind.component ?? []) {
          if (placed.has(c.id)) continue;
          const v = c.data[by.property];
          if (typeof v !== 'string' || !Object.hasOwn(by.parents, v)) continue;
          const p = by.parents[v];
          if (p === c.id) continue;
          if (!isElement(p)) {
            if (!reported.has(v)) problems.push({ code: 'unknown-parent', element: c.id, others: [String(p)], message: `groupBy places the elements whose "${by.property}" is "${v}" under "${p}", which is not an element.`, at: { entity: id, path: ['groupBy', 'parents', v] } });
            reported.add(v);
            continue;
          }
          parent.set(c.id, p);
        }
      }
    }
    // Module elements are members of the component that declares them, in every hierarchy.
    for (const e of elements.values()) {
      if (e.kind !== 'module' || !e.owners) continue;
      parent.set(e.id, e.owners[0]);
      if (id === LOGICAL && e.owners.length > 1) {
        problems.push({ code: 'multiple-owners', element: e.id, others: [...e.owners], message: `Module "${e.path}" is declared by ${e.owners.map((o) => `"${o}"`).join(' and ')}; a module element belongs to exactly one element (a file several elements share belongs to one shared element at their lowest common ancestor).` });
      }
    }
    // Cycles: every element on one loses its parent here, so the forest stays total; the problem is reported.
    /** @type {Set<string>} */
    const onCycle = new Set();
    for (const start of parent.keys()) {
      const seen = [start];
      let cur = parent.get(start);
      while (cur !== undefined && !onCycle.has(cur)) {
        const at = seen.indexOf(cur);
        if (at >= 0) {
          const loop = seen.slice(at);
          for (const x of loop) onCycle.add(x);
          problems.push({ code: 'cycle', element: loop[0], others: loop, message: `Hierarchy "${id}" has a containment cycle: ${[...loop, loop[0]].map((e) => `"${e}"`).join(' -> ')}.` });
          break;
        }
        seen.push(cur);
        cur = parent.get(cur);
      }
    }
    for (const x of onCycle) parent.delete(x);
    const order = [...elements.keys()];
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
    const stack = roots.map((r) => /** @type {[string, number]} */ ([r, 0]));
    while (stack.length) {
      const [e, d] = /** @type {[string, number]} */ (stack.pop());
      depth.set(e, d);
      for (const c of children.get(e) ?? []) stack.push([c, d + 1]);
    }
    return { id, parent, children, roots, depth, order, problems };
  });
}

/** The members of an element in a hierarchy (its children). @param {Hierarchy} h @param {string} id */
export function membersIn(h, id) {
  return h.children.get(id) ?? [];
}

/** Whether an element has members in a hierarchy. @param {Hierarchy} h @param {string} id */
export function isCompositeIn(h, id) {
  return (h.children.get(id)?.length ?? 0) > 0;
}

/** Ancestors of an element in a hierarchy, nearest first. @param {Hierarchy} h @param {string} id */
export function ancestorsIn(h, id) {
  const out = [];
  let cur = h.parent.get(id);
  while (cur !== undefined) { out.push(cur); cur = h.parent.get(cur); }
  return out;
}

/**
 * The blocks of a cut of a hierarchy, the elements it opens (strictly above it), and what is wrong with the
 * declaration. Pure over the hierarchy, so property checks can run it on generated hierarchies.
 * @param {Hierarchy} h @param {CutSpec} spec
 * @returns {CutBlocks}
 */
export function cutBlocksOf(h, spec) {
  /** @type {HierarchyProblem[]} */
  const problems = [];
  const known = (/** @type {any} */ x) => typeof x === 'string' && h.depth.has(x);
  const pos = new Map(h.order.map((e, i) => [e, i]));
  const byOrder = (/** @type {string} */ a, /** @type {string} */ b) => /** @type {number} */ (pos.get(a)) - /** @type {number} */ (pos.get(b));
  if (Array.isArray(spec.blocks)) {
    const blocks = [...new Set(spec.blocks.filter(known))];
    const set = new Set(blocks);
    for (const b of blocks) {
      const a = ancestorsIn(h, b).find((x) => set.has(x));
      if (a !== undefined) problems.push({ code: 'not-antichain', element: b, others: [a], message: `The cut contains "${b}" and its ancestor "${a}"; a cut holds no element together with its ancestor.` });
    }
    /** @type {Set<string>} */
    const expanded = new Set();
    for (const b of blocks) for (const a of ancestorsIn(h, b)) if (!set.has(a)) expanded.add(a);
    // Omitted: an element with no block at, above or below it. Reported at the topmost such element.
    /** @type {string[]} */
    const omitted = [];
    const walk = (/** @type {string} */ e) => {
      if (set.has(e)) return;
      if (!expanded.has(e)) { omitted.push(e); return; }
      for (const c of h.children.get(e) ?? []) walk(c);
    };
    for (const r of h.roots) walk(r);
    if (omitted.length) problems.push({ code: 'uncovered', element: omitted[0], others: omitted, message: `The cut omits ${omitted.map((x) => `"${x}"`).join(', ')}: no block is at, above or below ${omitted.length === 1 ? 'it' : 'them'}, so the cut does not cover every element.` });
    return { blocks: blocks.sort(byOrder), expanded: [...expanded].sort(byOrder), problems };
  }
  const explicit = Array.isArray(spec.expand) ? spec.expand.filter(known) : [];
  /** @type {Set<string>} */
  const open = new Set(explicit);
  const depth = typeof spec.depth === 'number' && Number.isFinite(spec.depth) ? spec.depth : 0;
  for (const e of h.order) {
    if (!isCompositeIn(h, e)) continue;
    if (spec.finest === true || /** @type {number} */ (h.depth.get(e)) < depth) open.add(e);
  }
  for (const e of explicit) {
    if (!isCompositeIn(h, e)) problems.push({ code: 'not-composite', element: e, message: `"${e}" has no members in hierarchy "${h.id}", so it cannot be expanded.` });
    for (const a of ancestorsIn(h, e)) {
      if (!open.has(a)) problems.push({ code: 'ancestor-not-expanded', element: e, others: [a], message: `"${e}" is expanded but its ancestor "${a}" is not; a cut expands an element only inside expanded ancestors.` });
    }
  }
  /** @type {string[]} */
  const blocks = [];
  /** @type {string[]} */
  const expanded = [];
  const walk = (/** @type {string} */ e) => {
    if (open.has(e) && isCompositeIn(h, e)) { expanded.push(e); for (const c of /** @type {string[]} */ (h.children.get(e))) walk(c); }
    else blocks.push(e);
  };
  for (const r of h.roots) walk(r);
  return { blocks: blocks.sort(byOrder), expanded: expanded.sort(byOrder), problems };
}

/**
 * The abstraction map of a cut: each element at or below it -> its unique ancestor-or-self on it.
 * Elements strictly above the cut (opened by it) are not in the map.
 * @param {Hierarchy} h @param {string[]} blocks
 * @returns {Map<string, string>}
 */
export function abstractionOf(h, blocks) {
  const set = new Set(blocks);
  /** @type {Map<string, string>} */
  const out = new Map();
  for (const e of h.order) {
    if (set.has(e)) { out.set(e, e); continue; }
    const a = ancestorsIn(h, e).find((x) => set.has(x));
    if (a !== undefined) out.set(e, a);
  }
  return out;
}

/**
 * The map between two cuts of one hierarchy, alpha_{C->C'}: each block of the finer cut C -> the block of
 * the coarser cut C' that contains it. null when C does not refine C' (some block of C has no
 * ancestor-or-self in C').
 * @param {Hierarchy} h @param {string[]} finer @param {string[]} coarser
 * @returns {Map<string, string>|null}
 */
export function refinementOf(h, finer, coarser) {
  const alpha = abstractionOf(h, coarser);
  /** @type {Map<string, string>} */
  const out = new Map();
  for (const b of finer) {
    const t = alpha.get(b);
    if (t === undefined) return null;
    out.set(b, t);
  }
  return out;
}

/** The cut spec a cut entity declares. @param {Entity} cut @returns {CutSpec} */
function cutSpecOf(cut) {
  const d = cut.data;
  return Array.isArray(d.blocks) ? { blocks: d.blocks } : { expand: Array.isArray(d.expand) ? d.expand : [], depth: d.depth, finest: d.finest === true };
}

/** The hierarchy id a cut entity is of. @param {Entity} cut */
export function cutHierarchyId(cut) {
  return typeof cut.data.hierarchy === 'string' ? cut.data.hierarchy : LOGICAL;
}

/**
 * A declared cut: its hierarchy, blocks, the elements it opens and its abstraction map alpha_C, which is
 * total on every element at or below the cut. null when no cut has that id or its hierarchy is unknown.
 * @param {Model} model @param {string} cutId
 * @returns {{cut: string, hierarchy: string, blocks: string[], expanded: string[], map: Map<string, string>, problems: HierarchyProblem[]}|null}
 */
export function cutMap(model, cutId) {
  return cached(model, `cut:${cutId}`, () => {
    const cut = model.entities.get(cutId);
    if (!cut || cut.kind !== 'cut') return null;
    const h = hierarchyOf(model, cutHierarchyId(cut));
    if (!h) return null;
    const { blocks, expanded, problems } = cutBlocksOf(h, cutSpecOf(cut));
    return { cut: cut.id, hierarchy: h.id, blocks, expanded, map: abstractionOf(h, blocks), problems };
  });
}

/** The block of a declared cut an element maps to, or null. @param {Model} model @param {string} cutId @param {string} elementId */
export function blockOf(model, cutId, elementId) {
  return cutMap(model, cutId)?.map.get(elementId) ?? null;
}

/**
 * alpha_{C->C'} between two declared cuts of one hierarchy, or null when they are of different hierarchies
 * or the first does not refine the second.
 * @param {Model} model @param {string} finerId @param {string} coarserId
 * @returns {Map<string, string>|null}
 */
export function cutToCut(model, finerId, coarserId) {
  const a = cutMap(model, finerId);
  const b = cutMap(model, coarserId);
  if (!a || !b || a.hierarchy !== b.hierarchy) return null;
  const h = /** @type {Hierarchy} */ (hierarchyOf(model, a.hierarchy));
  return refinementOf(h, a.blocks, b.blocks);
}

/**
 * The members of a facet: a declared facet's members and the components carrying its tag, or, for an id
 * no facet declares, the components carrying that tag (a tag is an implicit facet). Overlap is allowed.
 * @param {Model} model @param {string} id
 * @returns {Set<string>}
 */
export function facetMembers(model, id) {
  const f = model.entities.get(id);
  const declared = f && f.kind === 'facet' ? f : null;
  const tag = declared ? (typeof declared.data.tag === 'string' ? declared.data.tag : null) : id;
  /** @type {Set<string>} */
  const out = new Set(declared && Array.isArray(declared.data.members) ? declared.data.members.filter((/** @type {any} */ m) => typeof m === 'string') : []);
  if (tag !== null) for (const c of model.byKind.component ?? []) if (Array.isArray(c.data.tags) && c.data.tags.includes(tag)) out.add(c.id);
  return out;
}

/** Whether an id names a facet: a declared one, or a tag some component carries that no entity id takes. @param {Model} model @param {string} id */
export function isFacet(model, id) {
  const e = model.entities.get(id);
  if (e) return e.kind === 'facet';
  return (model.byKind.component ?? []).some((c) => Array.isArray(c.data.tags) && c.data.tags.includes(id));
}

/**
 * What is known about an element's inside, derived in this order: unknown when it declares knowledge
 * unknown; transparent when it has members in the logical hierarchy; opaque when it declares knowledge
 * opaque, is not implemented, or is external (kind external or actor, or category external); otherwise a
 * transparent leaf. null for an id that is not an element.
 * @param {Model} model @param {string} id
 * @returns {{status: 'transparent'|'opaque'|'unknown', leaf: boolean, reason: string}|null}
 */
export function knowledgeOf(model, id) {
  const e = elementsOf(model).get(id);
  if (!e) return null;
  const d = e.entity?.data ?? {};
  const h = /** @type {Hierarchy} */ (hierarchyOf(model, LOGICAL));
  const members = membersIn(h, id).length;
  if (d.knowledge === 'unknown') return { status: 'unknown', leaf: members === 0, reason: 'It declares knowledge "unknown".' };
  if (members) return { status: 'transparent', leaf: false, reason: `It has ${members} member${members === 1 ? '' : 's'} in the logical hierarchy.` };
  if (d.knowledge === 'opaque') return { status: 'opaque', leaf: true, reason: 'It declares knowledge "opaque" and has no members.' };
  if (e.entity?.kind === 'component' && d.implementation?.status === 'not-implemented') return { status: 'opaque', leaf: true, reason: 'It is not implemented and has no members: its declared interface is all there is.' };
  if (e.kind === 'external' || e.kind === 'actor' || d.category === 'external') return { status: 'opaque', leaf: true, reason: 'It is outside the specified system and has no members.' };
  return { status: 'transparent', leaf: true, reason: 'A leaf: nothing finer is declared inside it.' };
}

/** The knowledge status of every element. @param {Model} model @returns {Map<string, 'transparent'|'opaque'|'unknown'>} */
export function knowledgeStatus(model) {
  /** @type {Map<string, 'transparent'|'opaque'|'unknown'>} */
  const out = new Map();
  for (const id of elementsOf(model).keys()) out.set(id, /** @type {any} */ (knowledgeOf(model, id)).status);
  return out;
}
