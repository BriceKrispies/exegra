// The interaction taxonomy (WG-5693). Every relationship kind, built in (metamodel.json) or declared
// in a specification's vocabulary, states
//   class      what the kind is as a dependency: `static` (the source names the target in its own
//              code), `runtime` (the source uses the target while it runs) or `none` (not a dependency);
//   direction  { control, data }: whether control, and data, flow `with` the edge, `against` it,
//              `both` ways, or `none`;
//   parent     the kind this one coarsens to, in a tree rooted at `interacts-with`.
// The class and the direction are functions of the kind (never of the relationship), so a coarsening
// that relabels a kind never changes an interaction's endpoints, direction, contract, carried data or
// provenance. The legacy `dependency` flag is derived: true exactly when the class is not `none`.
//
// Pure functions of the effective meta-model (`model.meta.relationshipKinds`), plus the query that
// contracts a connector-mediated pair into a producer to consumer `notifies`.

import { own } from './own.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */

export const DEPENDENCY_CLASSES = /** @type {const} */ (['static', 'runtime', 'none']);
export const FLOW_DIRECTIONS = /** @type {const} */ (['with', 'against', 'both', 'none']);
export const PROVENANCES = /** @type {const} */ (['declared', 'extracted', 'observed', 'derived', 'assumed']);
/** The one kind with no parent. */
export const ROOT_KIND = 'interacts-with';
/** The element kind (component `kind`) that mediates publishes and subscribes. */
export const CONNECTOR_KIND = 'connector';

/**
 * What the meta-model says of a relationship kind, with the defaults an unclassified vocabulary kind
 * gets: its class follows its `dependency` flag (`runtime` or `none`), its direction is none, its
 * parent is the root. `classified` tells whether the kind stated the taxonomy itself.
 * @param {any} meta effective meta-model @param {string} kind
 * @returns {{kind: string, known: boolean, classified: boolean, class: 'static'|'runtime'|'none', direction: {control: string, data: string}, parent: string|null, dependency: boolean, legacy: boolean, replacedBy: string|null}}
 */
export function kindInfo(meta, kind) {
  const k = /** @type {any} */ (own(meta?.relationshipKinds, kind));
  if (!k) return { kind, known: false, classified: false, class: 'none', direction: { control: 'none', data: 'none' }, parent: ROOT_KIND, dependency: false, legacy: false, replacedBy: null };
  const stated = typeof k.class === 'string' && typeof k.parent !== 'undefined' && k.direction && typeof k.direction === 'object';
  const cls = DEPENDENCY_CLASSES.includes(k.class) ? k.class : (k.dependency === true ? 'runtime' : 'none');
  const dir = k.direction && typeof k.direction === 'object' ? k.direction : {};
  return {
    kind, known: true, classified: !!stated, class: cls,
    direction: { control: FLOW_DIRECTIONS.includes(dir.control) ? dir.control : 'none', data: FLOW_DIRECTIONS.includes(dir.data) ? dir.data : 'none' },
    parent: typeof k.parent === 'string' ? k.parent : (kind === ROOT_KIND ? null : ROOT_KIND),
    dependency: cls !== 'none',
    legacy: k.legacy === true,
    replacedBy: typeof k.replacedBy === 'string' ? k.replacedBy : null,
  };
}

/** The dependency class of a kind. @param {any} meta @param {string} kind */
export const kindClass = (meta, kind) => kindInfo(meta, kind).class;

/**
 * The kinds a kind coarsens to, nearest first, ending at the root. Stops at an unknown kind or a cycle.
 * @param {any} meta @param {string} kind
 */
export function kindAncestors(meta, kind) {
  /** @type {string[]} */
  const out = [];
  const seen = new Set([kind]);
  let cur = kindInfo(meta, kind).parent;
  while (cur !== null && !seen.has(cur) && own(meta?.relationshipKinds, cur)) {
    out.push(cur);
    seen.add(cur);
    cur = kindInfo(meta, cur).parent;
  }
  return out;
}

/**
 * Whether `kind` is `ancestor` or refines it (coarsens to it).
 * @param {any} meta @param {string} kind @param {string} ancestor
 */
export const refines = (meta, kind, ancestor) => kind === ancestor || kindAncestors(meta, kind).includes(ancestor);

/**
 * Coarsen a kind to an ancestor kind: the ancestor when the kind refines it, else the kind itself.
 * Only the label changes; the class and direction that analyses read stay those of the original kind.
 * @param {any} meta @param {string} kind @param {string} to
 */
export const coarsen = (meta, kind, to) => (refines(meta, kind, to) ? to : kind);

/**
 * The kind an analysis treats a relationship kind as: a legacy kind behaves as the kind that replaces it
 * (`calls` as `invokes`). Any other kind is its own.
 * @param {any} meta @param {string} kind
 */
export function effectiveKind(meta, kind) {
  const seen = new Set();
  let cur = kind;
  while (!seen.has(cur)) {
    seen.add(cur);
    const info = kindInfo(meta, cur);
    if (!info.legacy || !info.replacedBy) return cur;
    cur = info.replacedBy;
  }
  return cur;
}

/** The provenance of a relationship: `declared` when it states none. @param {Entity|{data: any}} r */
export const provenanceOf = (r) => (typeof r.data.provenance === 'string' ? r.data.provenance : 'declared');

/**
 * Diagnostics of the taxonomy: kinds without it, cycles in the kind tree, dependency flags that
 * contradict the class, and legacy kinds in use.
 * `at` finds the entity a diagnostic is anchored on (the first relationship of the kind, else the system).
 * @param {Model} model
 * @param {(severity: 'error'|'warning'|'info', code: string, entity: Entity, message: string, sub?: (string|number)[]) => void} report
 */
export function checkTaxonomy(model, report) {
  const kinds = /** @type {Record<string, any>} */ (model.meta.relationshipKinds ?? {});
  const rels = model.byKind.relationship ?? [];
  const system = model.system;
  /** @param {string} kind @returns {Entity|undefined} */
  const anchor = (kind) => rels.find((r) => r.data.kind === kind) ?? system ?? undefined;
  /** @type {(entity: Entity|undefined, severity: 'error'|'warning', code: string, message: string) => void} */
  const say = (entity, severity, code, message) => { if (entity) report(severity, code, entity, message); };

  for (const [id, k] of Object.entries(kinds)) {
    const isRoot = id === ROOT_KIND;
    const declared = k.declared === true;
    const hasClass = k.class !== undefined, hasDirection = k.direction !== undefined, hasParent = k.parent !== undefined;
    const where = anchor(id);
    if (declared && !hasClass && !hasDirection && !hasParent) {
      // A vocabulary kind written before the taxonomy: it still works (class from its dependency flag, direction
      // none, parent the root), and the author is told what to add.
      say(where, 'warning', 'vocabulary.kind-unclassified', `Relationship kind "${id}" declares no class, direction or coarsening parent; it is treated as class ${kindClass(model.meta, id)}, direction none and parent "${ROOT_KIND}". Declare "class" (${DEPENDENCY_CLASSES.join(', ')}), "direction" {control, data} and "parent" in vocabulary.relationshipKinds.`);
      continue;
    }
    /** @param {string} what */
    const bad = (what) => say(where, 'error', 'vocabulary.kind-taxonomy', `Relationship kind "${id}" ${what}`);
    if (!DEPENDENCY_CLASSES.includes(k.class)) bad(`needs "class" to be one of: ${DEPENDENCY_CLASSES.join(', ')}.`);
    if (!k.direction || typeof k.direction !== 'object' || Array.isArray(k.direction)) bad(`needs "direction" {"control": ..., "data": ...}, each one of: ${FLOW_DIRECTIONS.join(', ')}.`);
    else for (const f of ['control', 'data']) if (!FLOW_DIRECTIONS.includes(k.direction[f])) bad(`needs direction.${f} to be one of: ${FLOW_DIRECTIONS.join(', ')}.`);
    if (isRoot) { if (k.parent !== null) bad('is the root of the kind tree and has no parent (parent null).'); }
    else if (typeof k.parent !== 'string') bad('needs a "parent": the kind it coarsens to.');
    else if (!own(kinds, k.parent)) bad(`names the unknown parent kind "${k.parent}".`);
    else if (k.parent === id) bad('is its own parent.');
    // The kernel derives the flag from the class, so the flag the author wrote is read from the raw vocabulary.
    const written = /** @type {any} */ (own(own(model.vocabulary, 'relationshipKinds'), id))?.dependency;
    if (declared && DEPENDENCY_CLASSES.includes(k.class) && typeof written === 'boolean' && written !== (k.class !== 'none')) {
      bad(`has dependency ${written} but class ${k.class}; the flag is derived from the class (true unless the class is none).`);
    }
    if (k.legacy === true && (typeof k.replacedBy !== 'string' || !own(kinds, k.replacedBy))) bad('is legacy and names no known kind in "replacedBy".');
  }

  // The kind tree is acyclic and every kind reaches the root. Report each cycle once, anchored on its smallest kind.
  const reported = new Set();
  for (const id of Object.keys(kinds)) {
    const path = [id];
    let cur = typeof kinds[id].parent === 'string' ? kinds[id].parent : null;
    while (cur !== null && own(kinds, cur)) {
      const at = path.indexOf(cur);
      if (at >= 0) {
        const cycle = path.slice(at);
        const key = [...cycle].sort().join('|');
        if (!reported.has(key)) {
          reported.add(key);
          say(anchor(cycle.slice().sort()[0]), 'error', 'vocabulary.kind-cycle', `The relationship kind tree has a cycle: ${[...cycle, cur].join(' -> ')}. Every kind has one coarsening parent and the tree ends at "${ROOT_KIND}".`);
        }
        break;
      }
      path.push(cur);
      cur = typeof kinds[cur].parent === 'string' ? kinds[cur].parent : null;
    }
  }

  // Legacy kinds in use: one warning per kind, naming it and how many relationships use it.
  for (const [id, k] of Object.entries(kinds)) {
    if (k.legacy !== true) continue;
    const users = rels.filter((r) => r.data.kind === id);
    if (!users.length) continue;
    const ids = users.slice(0, 3).map((r) => `"${r.id}"`).join(', ');
    report('warning', 'relationship.legacy-kind', users[0], `Relationship kind "${id}" is a legacy, unclassified kind (treated as "${k.replacedBy}"); ${users.length} ${users.length === 1 ? 'relationship uses' : 'relationships use'} it, such as ${ids}. State what each one is: imports, invokes, notifies or composes.`, ['kind']);
  }
}

/** Whether a component is a connector element (kind `connector`). @param {Entity|undefined} e */
export const isConnector = (e) => !!e && e.kind === 'component' && e.data.kind === CONNECTOR_KIND;

/**
 * Connector-mediated interactions, contracted. For each connector element C, every `publishes` relationship
 * from a producer P to C and every `subscribes` relationship from a consumer S to C give one interaction
 * P -> S of kind `notifies`, naming the connector and the two relationships it stands for. A pair is
 * contracted only through a declared connector element: a publishes with no matching subscribes through
 * the same connector yields nothing, and no direct edge is ever invented between components that share no
 * connector. A component that publishes and subscribes through one connector is not paired with itself.
 * @param {Model} model
 * @param {{connectors?: string[]}} [opts] only these connectors
 * @returns {{id: string, kind: 'notifies', from: string, to: string, connector: string, via: [string, string], carries: string[], provenance: 'derived'}[]}
 */
export function mediatedInteractions(model, opts = {}) {
  const comp = (/** @type {string} */ id) => {
    const e = model.entities.get(id);
    if (!e) return undefined;
    return e.kind === 'port' && e.owner ? model.entities.get(e.owner) : e;
  };
  /** @type {Map<string, {pubs: Entity[], subs: Entity[]}>} */
  const byConnector = new Map();
  for (const c of model.byKind.component ?? []) if (isConnector(c) && (!opts.connectors || opts.connectors.includes(c.id))) byConnector.set(c.id, { pubs: [], subs: [] });
  for (const r of model.byKind.relationship ?? []) {
    const to = comp(r.data.to);
    const slot = to ? byConnector.get(to.id) : undefined;
    if (!slot) continue;
    if (r.data.kind === 'publishes') slot.pubs.push(r);
    else if (r.data.kind === 'subscribes') slot.subs.push(r);
  }
  /** @type {ReturnType<typeof mediatedInteractions>} */
  const out = [];
  for (const [connector, { pubs, subs }] of byConnector) {
    for (const p of pubs) for (const s of subs) {
      const from = comp(p.data.from), to = comp(s.data.from);
      if (!from || !to || from.id === to.id || from.kind !== 'component' || to.kind !== 'component') continue;
      const carries = [...new Set([...(Array.isArray(p.data.carries) ? p.data.carries : []), ...(Array.isArray(s.data.carries) ? s.data.carries : [])])];
      out.push({ id: `${connector}~${p.id}~${s.id}`, kind: 'notifies', from: from.id, to: to.id, connector, via: [p.id, s.id], carries, provenance: 'derived' });
    }
  }
  return out;
}
