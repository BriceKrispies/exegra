// Residency (WG-5277): regions, the classes of tenants that are provisioned in them, where each
// component holds and processes data, and the records a class confines to a tenant's home region.
// The rules follow the bound records to every place their data is: the owner of the record, the
// holder of each copy of it, and both ends of each relationship that carries it, and report a
// place that can be outside the permitted regions, unless an active residency exception names
// that copy or flow. Pure and deterministic; run from validate.js. See
// docs/model-and-format.md#residency.

import { durationNs } from './constructs.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */

/** @param {any} v @returns {any[]} */
const list = (v) => (Array.isArray(v) ? v : []);
/** @param {any} v @returns {string[]} */
const ids = (v) => list(v).filter((x) => typeof x === 'string');

/** The confinement of a tenant class: home unless stated. @param {Entity} t */
export const confinementOf = (t) => (typeof t.data.confinement === 'string' ? t.data.confinement : 'home');

/** The status of a residency exception: active unless stated. @param {Entity} e */
export const exceptionActive = (e) => (e.data.status ?? 'active') === 'active';

/**
 * The component an endpoint is: the component itself, or the owner of a port.
 * @param {Model} model @param {any} id @returns {Entity|undefined}
 */
function componentOf(model, id) {
  const e = typeof id === 'string' ? model.entities.get(id) : undefined;
  if (!e) return undefined;
  if (e.kind === 'component') return e;
  if (e.kind === 'port' && typeof e.owner === 'string') return componentOf(model, e.owner);
  return undefined;
}

/**
 * Whether a component keeps the data of a tenant of a class inside the regions the class permits.
 * `ok` true, or the reason it does not: `missing` (no placement stated), `uncovered` (a per-region
 * component with no instance in some region the class provisions in) or `outside` (a fixed
 * component outside the permitted regions, or a global one).
 * @param {Entity} c @param {Entity} t
 * @returns {{ok: true} | {ok: false, reason: 'missing'|'uncovered'|'outside', regions: string[]}}
 */
export function placementFits(c, t) {
  const provisioned = ids(t.data.provisionedIn);
  const placement = c.data.placement;
  const regions = ids(c.data.regions);
  if (placement === undefined) return { ok: false, reason: 'missing', regions: [] };
  if (placement === 'per-region') {
    if (!regions.length) return { ok: true };
    const absent = provisioned.filter((r) => !regions.includes(r));
    return absent.length ? { ok: false, reason: 'uncovered', regions: absent } : { ok: true };
  }
  if (placement === 'fixed') {
    if (confinementOf(t) === 'provisioned-regions') {
      const outside = regions.filter((r) => !provisioned.includes(r));
      return outside.length || !regions.length ? { ok: false, reason: 'outside', regions: outside } : { ok: true };
    }
    // home: a fixed place keeps every tenant's data in its home only when the class has one region and the
    // component runs there alone.
    const home = provisioned.length === 1 ? provisioned[0] : undefined;
    return home !== undefined && regions.length === 1 && regions[0] === home ? { ok: true } : { ok: false, reason: 'outside', regions: regions.filter((r) => r !== home) };
  }
  return { ok: false, reason: 'outside', regions: [] };
}

/**
 * Every place the data of a record bound by a tenant class is: the record's owner, the holder of each copy
 * of it, and both ends of each relationship that carries it.
 * @param {Model} model @param {Entity} t
 * @returns {{via: 'record'|'copy'|'flow', entity: Entity, component: Entity, records: string[], sub: (string|number)[]}[]}
 */
export function boundPlaces(model, t) {
  const bound = new Set(ids(t.data.binds));
  /** @type {{via: 'record'|'copy'|'flow', entity: Entity, component: Entity, records: string[], sub: (string|number)[]}[]} */
  const out = [];
  for (const r of model.byKind.record ?? []) {
    if (!bound.has(r.id)) continue;
    const c = componentOf(model, r.data.owner);
    if (c) out.push({ via: 'record', entity: r, component: c, records: [r.id], sub: ['owner'] });
  }
  for (const cp of model.byKind.copy ?? []) {
    const records = ids(cp.data.of).filter((r) => bound.has(r));
    const c = componentOf(model, cp.data.heldBy);
    if (records.length && c) out.push({ via: 'copy', entity: cp, component: c, records, sub: ['heldBy'] });
  }
  for (const rel of model.byKind.relationship ?? []) {
    const records = ids(rel.data.carries).filter((r) => bound.has(r));
    if (!records.length) continue;
    for (const end of /** @type {const} */ (['from', 'to'])) {
      const c = componentOf(model, rel.data[end]);
      if (c) out.push({ via: 'flow', entity: rel, component: c, records, sub: [end] });
    }
  }
  return out;
}

/**
 * The active exception of a tenant class that covers a copy or flow placed in a component, if any; or why the
 * exceptions that name it do not cover it.
 * @param {Model} model @param {Entity} t @param {'copy'|'flow'} via @param {Entity} target @param {Entity} component
 * @returns {{covered: Entity|null, notes: string[]}}
 */
export function coveringException(model, t, via, target, component) {
  /** @type {string[]} */
  const notes = [];
  for (const e of model.byKind.residencyException ?? []) {
    if (e.data.tenantClass !== t.id || e.data[via] !== target.id) continue;
    if (!exceptionActive(e)) { notes.push(`exception "${e.id}" is ${e.data.status}`); continue; }
    const allowed = ids(e.data.regions);
    if (allowed.length) {
      const regions = ids(component.data.regions);
      const inside = component.data.placement === 'fixed' && regions.length > 0 && regions.every((r) => allowed.includes(r));
      if (!inside) { notes.push(`exception "${e.id}" allows only ${allowed.map((r) => `"${r}"`).join(', ')}, and component "${component.id}" is ${component.data.placement === 'fixed' ? `fixed in ${regions.map((r) => `"${r}"`).join(', ') || 'no region'}` : component.data.placement ?? 'without a placement'}`); continue; }
    }
    return { covered: e, notes };
  }
  return { covered: null, notes };
}

/**
 * The rules of regions, tenant classes, component placement, carried records and residency exceptions.
 * @param {Model} model @returns {Diagnostic[]}
 */
export function checkResidency(model) {
  /** @type {Diagnostic[]} */
  const out = [];
  /** @param {string} code @param {Entity} e @param {string} message @param {(string|number)[]} [sub] */
  const err = (code, e, message, sub = []) => out.push({ code, severity: 'error', message, entityId: e.id, loc: e.loc, path: [...e.path, ...sub] });
  const kind = (/** @type {string} */ k) => model.byKind[k] ?? [];

  // Placement is stated whole: a fixed component names where it runs, a global one names nowhere, and regions
  // come only with a placement.
  for (const c of kind('component')) {
    const p = c.data.placement;
    const regions = ids(c.data.regions);
    if (p === 'fixed' && !regions.length) err('component.placement-regions', c, `Component "${c.id}" is fixed and names no region it runs in.`, ['regions']);
    else if (p === 'global' && regions.length) err('component.placement-regions', c, `Component "${c.id}" is global and names regions; a global component runs anywhere, so it lists none (use fixed to name where it runs).`, ['regions']);
    else if (p === undefined && c.data.regions !== undefined) err('component.placement-regions', c, `Component "${c.id}" names regions but no placement; say whether it is per-region or fixed in them.`, ['regions']);
  }

  for (const t of kind('tenantClass')) {
    if (t.data.flag !== undefined && t.data.plan !== undefined) err('tenant-class.selector', t, `Tenant class "${t.id}" names both a flag and a plan; a class is the tenants with one flag on, or on one plan, or every tenant.`, ['plan']);
    const prov = ids(t.data.provisionedIn);
    if (!prov.length) err('tenant-class.provisioned-in', t, `Tenant class "${t.id}" names no region its tenants are provisioned in.`, ['provisionedIn']);
    else if (new Set(prov).size !== prov.length) err('tenant-class.provisioned-in', t, `Tenant class "${t.id}" names a region twice in provisionedIn.`, ['provisionedIn']);
  }

  // Every place of bound data is inside the permitted regions, or its copy or flow is covered by an active
  // exception. A component with no placement that receives bound data is reported once, on the component.
  /** @type {Set<string>} */
  const missingReported = new Set();
  /** @type {Set<string>} */
  const uncoveredReported = new Set();
  for (const t of kind('tenantClass')) {
    if (confinementOf(t) === 'none' || !ids(t.data.provisionedIn).length) continue;
    for (const place of boundPlaces(model, t)) {
      const fit = placementFits(place.component, t);
      if (fit.ok) continue;
      const c = place.component;
      const what = place.via === 'record' ? `record "${place.entity.id}" is owned by` : place.via === 'copy' ? `copy "${place.entity.id}" of ${place.records.map((r) => `"${r}"`).join(', ')} is held by` : `relationship "${place.entity.id}" carries ${place.records.map((r) => `"${r}"`).join(', ')} ${place.sub[0] === 'to' ? 'to' : 'from'}`;
      if (fit.reason === 'missing') {
        if (!missingReported.has(c.id)) {
          missingReported.add(c.id);
          err('residency.placement-missing', c, `Component "${c.id}" holds or receives data that tenant class "${t.id}" confines (${what} it) and states no placement; say whether it is per-region, fixed in some regions or global.`, ['placement']);
        }
        continue;
      }
      if (fit.reason === 'uncovered') {
        const key = `${c.id}|${t.id}`;
        if (!uncoveredReported.has(key)) {
          uncoveredReported.add(key);
          err('residency.region-uncovered', c, `Component "${c.id}" is per-region but has no instance in ${fit.regions.map((r) => `"${r}"`).join(', ')}, where tenant class "${t.id}" provisions tenants, and ${what} it; the data of those tenants would leave their home region.`, ['regions']);
        }
        continue;
      }
      /** @type {string[]} */
      let notes = [];
      if (place.via !== 'record') {
        const cov = coveringException(model, t, place.via, place.entity, c);
        if (cov.covered) continue;
        notes = cov.notes;
      }
      const where = c.data.placement === 'global' ? 'global (anywhere)' : `fixed in ${ids(c.data.regions).map((r) => `"${r}"`).join(', ')}`;
      const permitted = confinementOf(t) === 'home' ? 'the home region of each tenant' : `the regions ${ids(t.data.provisionedIn).map((r) => `"${r}"`).join(', ')}`;
      const code = place.via === 'record' ? 'residency.record-outside' : place.via === 'copy' ? 'residency.copy-outside' : 'residency.flow-outside';
      err(code, place.entity, `Tenant class "${t.id}" confines its data to ${permitted}, but ${what} component "${c.id}", which is ${where}${notes.length ? `; ${notes.join('; ')}` : place.via === 'record' ? '' : ', and no active residency exception names it'}.`, place.sub);
    }
  }

  // An exception names one copy or flow that holds or carries a record its class binds, is approved by a role,
  // and when it is bounded says how soon what it let out is purged.
  for (const e of kind('residencyException')) {
    const t = typeof e.data.tenantClass === 'string' ? model.entities.get(e.data.tenantClass) : undefined;
    const hasCopy = e.data.copy !== undefined;
    const hasFlow = e.data.flow !== undefined;
    if (hasCopy === hasFlow) err('residency.exception-target', e, `Residency exception "${e.id}" names ${hasCopy ? 'both a copy and a flow' : 'neither a copy nor a flow'}; it names exactly one.`, []);
    else if (t?.kind === 'tenantClass') {
      const bound = new Set(ids(t.data.binds));
      const target = model.entities.get(hasCopy ? e.data.copy : e.data.flow);
      const held = target ? ids(hasCopy ? target.data.of : target.data.carries) : [];
      if (target && !held.some((r) => bound.has(r))) err('residency.exception-target', e, `Residency exception "${e.id}" names ${hasCopy ? 'copy' : 'flow'} "${target.id}", which ${hasCopy ? 'holds' : 'carries'} no record tenant class "${t.id}" binds; there is nothing for it to except.`, [hasCopy ? 'copy' : 'flow']);
    }
    for (const key of ['maxDuration', 'renewalWindow', 'purgeWithin']) {
      if (e.data[key] !== undefined && durationNs(e.data[key]) === null) err('residency.exception-duration', e, `The ${key} of residency exception "${e.id}" must be a positive duration such as "90 d".`, [key]);
    }
    if (e.data.maxDuration !== undefined && e.data.purgeWithin === undefined) err('residency.exception-purge', e, `Residency exception "${e.id}" expires after ${e.data.maxDuration} and does not say how soon what it let outside the region is purged (purgeWithin).`, []);
    if (e.data.renewalWindow !== undefined) {
      const max = durationNs(e.data.maxDuration);
      const win = durationNs(e.data.renewalWindow);
      if (e.data.maxDuration === undefined) err('residency.exception-renewal', e, `Residency exception "${e.id}" has a renewal window but no longest duration; a renewal continues an approval that expires.`, ['renewalWindow']);
      else if (max !== null && win !== null && win >= max) err('residency.exception-renewal', e, `The renewal window of residency exception "${e.id}" (${e.data.renewalWindow}) is not shorter than its longest duration (${e.data.maxDuration}).`, ['renewalWindow']);
    }
  }
  return out;
}
