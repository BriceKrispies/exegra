// Read-only queries over the semantic model. Shared by projections, claims,
// generators, the inspector and the agent CLI so that every consumer answers
// "what depends on what" the same way.

import { own } from './own.js';

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
  if (!e) return undefined;
  if (e.kind === 'component') return e;
  if (e.kind === 'port' && e.owner) return model.entities.get(e.owner);
  return undefined;
}

/** @param {Model} model @param {string|null} parentId null for root components */
export function childrenOf(model, parentId) {
  return (model.byKind.component ?? []).filter((c) => (c.data.parent ?? null) === parentId);
}

/** Ancestor subsystem ids, nearest first. @param {Model} model @param {string} id */
export function ancestorsOf(model, id) {
  const out = [];
  const seen = new Set([id]);
  let cur = model.entities.get(id);
  while (cur && typeof cur.data.parent === 'string' && !seen.has(cur.data.parent)) {
    out.push(cur.data.parent);
    seen.add(cur.data.parent);
    cur = model.entities.get(cur.data.parent);
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
 * Directed component graph. Edges are relationships resolved to components.
 * @param {Model} model
 * @param {{kinds?: string[]|null, dependencyOnly?: boolean}} [opts]
 * @returns {Map<string, {to: string, rel: string, kind: string}[]>}
 */
export function componentGraph(model, opts = {}) {
  /** @type {Map<string, {to: string, rel: string, kind: string}[]>} */
  const g = new Map();
  for (const c of model.byKind.component ?? []) g.set(c.id, []);
  for (const r of model.byKind.relationship ?? []) {
    if (opts.kinds && !opts.kinds.includes(r.data.kind)) continue;
    if (opts.dependencyOnly && !own(model.meta.relationshipKinds, r.data.kind)?.dependency) continue;
    const from = componentOf(model, r.data.from);
    const to = componentOf(model, r.data.to);
    if (!from || !to) continue;
    g.get(from.id)?.push({ to: to.id, rel: r.id, kind: r.data.kind });
  }
  return g;
}

/**
 * Dependency traversal from one component.
 * direction 'out' = what it depends on; 'in' = what depends on it.
 * By default follows only relationship kinds flagged `dependency` in the meta-model.
 * @param {Model} model @param {string} id
 * @param {{direction?: 'out'|'in', transitive?: boolean, kinds?: string[]}} [opts]
 * @returns {{id: string, via: string, depth: number}[]}
 */
export function dependencies(model, id, opts = {}) {
  const direction = opts.direction ?? 'out';
  const g = componentGraph(model, opts.kinds ? { kinds: opts.kinds } : { dependencyOnly: true });
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
 * inside a selected subsystem is selected too, unless `exact` is set.
 * @param {Model} model @param {any} selector @param {{exact?: boolean}} [opts]
 * @returns {Entity[]}
 */
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
    match = (c) =>
      (!ids || ids.includes(/** @type {never} */ (c.id))) &&
      (!cats || cats.includes(/** @type {never} */ (c.data.category))) &&
      (selector.kind === undefined || (c.data.kind ?? 'component') === selector.kind) &&
      (selector.tag === undefined || (Array.isArray(c.data.tags) && c.data.tags.includes(selector.tag))) &&
      (selector.trustZone === undefined || c.data.trustZone === selector.trustZone) &&
      (selector.within === undefined || ancestorsOf(model, c.id).includes(selector.within));
  } else return [];
  const direct = all.filter(match);
  if (opts.exact) return direct;
  const picked = new Set(direct.map((c) => c.id));
  for (const c of direct) for (const d of descendantsOf(model, c.id)) picked.add(d.id);
  return all.filter((c) => picked.has(c.id));
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
