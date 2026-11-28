// Pooled quotas (WG-5278): limits shared by a group of tenants, such as the clients of one reseller.
// Each member contributes its fair share (the limit of a per-tenant quota, or a stated amount per
// member) and the pool's capacity is the sum. A member may go over its share while the pool has
// headroom; a member over its share at the end of N consecutive windows is throttled even with
// headroom, unless an exemption a named role set applies from that window; a throttle lifts after R
// consecutive windows at or under the share, or never.
//
// The meaning is executable: the lowering (formal/Exegra/Lower/Input.lean, Exegra.Lower.poolMachines,
// WG-5683) derives, for each pooled limit and each modelled member, a state machine of the engine input,
// and a scenario that lists the pool runs them next to its behaviors. Claims read their variables as
// `<pool>-<limit>-m<k>.<variable>`, so simulation and exhaustive exploration decide them like any other
// machine. This module holds the rules of the construct (`checkPools`) and the machine ids and variables
// validation and the claim methods resolve. Pure and deterministic. See
// docs/model-and-format.md#pooled-quotas.

import { durationNs } from './constructs.js';
import { listedCapabilities } from './capabilities.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */

/** @param {any} v @returns {any[]} */
const list = (v) => (Array.isArray(v) ? v : []);
/** @param {any} v */
const isObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);
/** @param {any} v */
const posInt = (v) => Number.isInteger(v) && v >= 1;

const LIMIT_NAME = /^[a-z][a-z0-9]*$/;
export const DEFAULT_MODEL_MEMBERS = 2;
export const MAX_MODEL_MEMBERS = 4;

/** The variables of every pool machine, in order. */
export const POOL_VARIABLES = Object.freeze(['usage', 'day', 'overDays', 'underDays', 'throttledOn', 'burstSetOn', 'burstFrom', 'admitted', 'refused']);
/** The states of every pool machine. */
export const POOL_STATES = Object.freeze(['normal', 'throttled']);

/** The number of members the model of a pool runs. @param {Entity} pool */
export function modelMembers(pool) {
  const n = pool.data.modelMembers;
  return posInt(n) && n <= MAX_MODEL_MEMBERS ? n : DEFAULT_MODEL_MEMBERS;
}

/** The id of the machine of one limit and one member. @param {string} poolId @param {string} limit @param {number} k */
export const poolMachineId = (poolId, limit, k) => `${poolId}-${limit}-m${k}`;

/** The pooled limits of a pool that have a usable name. @param {Entity} pool */
const limitsOf = (pool) => list(pool.data.limits).filter((l) => isObj(l) && typeof l.name === 'string' && LIMIT_NAME.test(l.name));

/** The ids of every machine a pool runs as. @param {Entity} pool @returns {string[]} */
export function poolMachineIds(pool) {
  const n = modelMembers(pool);
  const out = [];
  for (const l of limitsOf(pool)) for (let k = 1; k <= n; k++) out.push(poolMachineId(pool.id, l.name, k));
  return out;
}

/**
 * The machine ids a scenario runs: its behaviors and the machines of its pools.
 * @param {Model} model @param {Entity|undefined} scenario @returns {Set<string>}
 */
export function scenarioMachineIds(model, scenario) {
  const out = new Set(list(scenario?.data.behaviors).filter((b) => typeof b === 'string'));
  for (const pid of list(scenario?.data.pools)) {
    const pool = typeof pid === 'string' ? model.entities.get(pid) : undefined;
    if (pool?.kind === 'quotaPool') for (const id of poolMachineIds(pool)) out.add(id);
  }
  return out;
}

/** Every pool machine id of the model, with its pool. @param {Model} model @returns {Map<string, Entity>} */
export function allPoolMachines(model) {
  const out = new Map();
  for (const p of model.byKind.quotaPool ?? []) for (const id of poolMachineIds(p)) out.set(id, p);
  return out;
}

/**
 * What one member contributes to a pooled limit (its fair share), or undefined when the limit does not say.
 * @param {Model} model @param {any} limit
 */
export function contributionOf(model, limit) {
  if (typeof limit.perMember === 'number' && limit.perMember > 0) return limit.perMember;
  const q = typeof limit.quota === 'string' ? model.entities.get(limit.quota) : undefined;
  return q?.kind === 'quota' && typeof q.data.limit === 'number' && q.data.limit > 0 ? q.data.limit : undefined;
}

/** The event that uses a pooled limit: its own, or the event its quota counts. @param {Model} model @param {any} limit */
export function usageEventOf(model, limit) {
  if (typeof limit.usage === 'string') return limit.usage;
  const q = typeof limit.quota === 'string' ? model.entities.get(limit.quota) : undefined;
  return q?.kind === 'quota' && typeof q.data.event === 'string' ? q.data.event : undefined;
}

/**
 * The rules of quota pools and of the scenarios that run them.
 * @param {Model} model @returns {Diagnostic[]}
 */
export function checkPools(model) {
  /** @type {Diagnostic[]} */
  const out = [];
  /** @param {string} code @param {Entity} e @param {string} message @param {(string|number)[]} [sub] */
  const err = (code, e, message, sub = []) => out.push({ code, severity: 'error', message, entityId: e.id, loc: e.loc, path: [...e.path, ...sub] });
  const get = (/** @type {any} */ id) => (typeof id === 'string' ? model.entities.get(id) : undefined);
  /** @param {Entity} p @param {any} evId @param {string[]} fields @param {(string|number)[]} at @param {string} what */
  const payload = (p, evId, fields, at, what) => {
    const ev = get(evId);
    if (ev?.kind !== 'event') return;
    const names = list(ev.data.payload).map((f) => f?.name);
    const missing = fields.filter((f) => !names.includes(f));
    if (missing.length) err('pool.event-payload', p, `Event "${ev.id}", the ${what} of quota pool "${p.id}", declares no payload field ${missing.map((f) => `"${f}"`).join(' or ')}; the pool reads ${fields.map((f) => `event.${f}`).join(' and ')}.`, at);
  };

  for (const p of model.byKind.quotaPool ?? []) {
    const d = p.data;
    const window = durationNs(d.window);
    if (window === null) err('pool.window', p, `The window of quota pool "${p.id}" must be a positive duration such as "1 d".`, ['window']);
    const limits = list(d.limits);
    if (!limits.length) err('pool.limits', p, `Quota pool "${p.id}" pools no limit.`, ['limits']);
    /** @type {Set<string>} */
    const names = new Set();
    limits.forEach((l, i) => {
      if (!isObj(l)) return;
      const at = ['limits', i];
      if (typeof l.name !== 'string' || !LIMIT_NAME.test(l.name)) err('pool.limits', p, `Pooled limit ${i} of "${p.id}" needs a name of lower-case letters and digits, starting with a letter; it is part of the machine ids.`, [...at, 'name']);
      else if (names.has(l.name)) err('pool.limits', p, `Quota pool "${p.id}" pools two limits named "${l.name}".`, [...at, 'name']);
      else names.add(l.name);
      const hasQuota = l.quota !== undefined;
      const hasShare = l.perMember !== undefined;
      if (hasQuota === hasShare) err('pool.limit-contribution', p, `Pooled limit "${l.name}" of "${p.id}" names ${hasQuota ? 'both a quota and perMember' : 'neither a quota nor perMember'}; what a member contributes comes from exactly one.`, at);
      else if (hasShare && !(typeof l.perMember === 'number' && l.perMember > 0)) err('pool.limit-contribution', p, `What each member contributes to pooled limit "${l.name}" of "${p.id}" must be a positive number.`, [...at, 'perMember']);
      const q = get(l.quota);
      if (hasQuota && q?.kind === 'quota') {
        if (q.data.scope !== 'tenant') err('pool.quota-scope', p, `Pooled limit "${l.name}" of "${p.id}" pools quota "${q.id}", which is counted per ${q.data.scope}; a pooled quota is counted per tenant, so each member contributes its limit.`, [...at, 'quota']);
        if (window !== null && durationNs(q.data.window) !== null && durationNs(q.data.window) !== window) err('pool.quota-window', p, `Pooled limit "${l.name}" of "${p.id}" pools quota "${q.id}", whose window (${q.data.window}) is not the pool's (${d.window}).`, [...at, 'quota']);
        if (l.kind !== 'rate') err('pool.limit-kind', p, `Pooled limit "${l.name}" of "${p.id}" pools quota "${q.id}", a count per window, so it is a rate.`, [...at, 'kind']);
        if (typeof d.heldBy === 'string' && typeof q.data.heldBy === 'string' && q.data.heldBy !== d.heldBy) err('pool.held-by', p, `Quota pool "${p.id}" is held by "${d.heldBy}" and pools quota "${q.id}", whose counters "${q.data.heldBy}" holds; one component keeps both.`, ['heldBy']);
      }
      const usage = usageEventOf(model, l);
      if (usage === undefined) err('pool.usage-event', p, `Pooled limit "${l.name}" of "${p.id}" names no usage event, and ${hasQuota ? 'its quota counts a contract, not an event' : 'it has no quota whose event could stand in'}.`, at);
      else payload(p, usage, ['member', 'amount'], l.usage !== undefined ? [...at, 'usage'] : [...at, 'quota'], `usage event of limit "${l.name}"`);
    });
    if (!posInt(d.overShare?.consecutive)) err('pool.over-share', p, `The over-share rule of quota pool "${p.id}" counts a positive whole number of consecutive windows.`, ['overShare', 'consecutive']);
    const release = d.throttle?.release;
    if (!(posInt(release) || release === 'never')) err('pool.release', p, `Quota pool "${p.id}" must say when a throttle is released: after a positive whole number of consecutive windows at or under the fair share, or "never".`, ['throttle', 'release']);
    const n = d.modelMembers;
    if (n !== undefined && !(posInt(n) && n <= MAX_MODEL_MEMBERS)) err('pool.model-members', p, `Quota pool "${p.id}" models ${JSON.stringify(n)} members; the model runs 1 to ${MAX_MODEL_MEMBERS}.`, ['modelMembers']);
    if (isObj(d.exemption)) {
      payload(p, d.exemption.event, ['member'], ['exemption', 'event'], 'exemption event');
      const role = get(d.exemption.setBy);
      const cap = get(d.exemption.capability);
      if (role?.kind === 'role' && cap?.kind === 'capability' && !listedCapabilities(role).has(cap.id)) err('pool.exemption-capability', p, `The exemption of quota pool "${p.id}" is set by role "${role.id}", which does not confer capability "${cap.id}" that setting it needs.`, ['exemption', 'capability']);
    }
    for (const id of poolMachineIds(p)) if (model.entities.has(id)) err('pool.machine-id', p, `Quota pool "${p.id}" runs as a machine "${id}", which is already the id of an entity (a ${model.entities.get(id)?.kind}).`, ['limits']);
  }
  return out;
}
