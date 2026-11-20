// Pooled quotas (WG-5278): limits shared by a group of tenants, such as the clients of one reseller.
// Each member contributes its fair share (the limit of a per-tenant quota, or a stated amount per
// member) and the pool's capacity is the sum. A member may go over its share while the pool has
// headroom; a member over its share at the end of N consecutive windows is throttled even with
// headroom, unless an exemption a named role set applies from that window; a throttle lifts after R
// consecutive windows at or under the share, or never.
//
// The meaning is executable: `poolMachines` derives, for each pooled limit and each modelled member,
// a state machine of the engine input, and a scenario that lists the pool runs them next to its
// behaviors. Claims read their variables as `<pool>-<limit>-m<k>.<variable>`, so simulation and
// exhaustive exploration decide them like any other machine. `checkPools` holds the rules of the
// construct. Pure and deterministic. See docs/model-and-format.md#pooled-quotas.

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
 * The machines a pool runs as, in the engine input's behavior form (src/core/sim-input.js), one per pooled
 * limit and modelled member. Throws when the pool is not complete enough to run (validation reports why).
 *
 * Each machine keeps, for its member and limit: `usage` (this window's use for a rate, the standing amount
 * for a level), `day` (the index of the current window), `overDays` and `underDays` (consecutive windows that
 * ended over, and at or under, the fair share), `throttledOn` (the window the throttle in force began, -1
 * none), `burstSetOn` and `burstFrom` (the window the exemption was set in and the first window it applies
 * to, -1 none), and the counts `admitted` and `refused`. Its states are `normal` and `throttled`.
 *
 * - Usage (`event.member == "m<k>"`, `event.amount`): in `normal`, admitted when it lowers the amount or the
 *   pool's total use plus it is within the capacity (headroom); in `throttled`, admitted only within the fair
 *   share and the capacity (`to: fair-share`) or only when it lowers the amount (`to: refuse`). Otherwise
 *   refused, with no change but the count.
 * - Window end: the window ended over the share when `usage` exceeds it. In `normal`, a member whose over
 *   count reaches N is throttled (throttledOn = this window) unless exempt, `burstFrom` set and not after
 *   this window; in `throttled`, the throttle lifts when the under count reaches R. A rate's usage resets,
 *   and the window index advances.
 * - Exemption set (`event.member == "m<k>"`), first time only: `burstSetOn` is this window and `burstFrom`
 *   it or the next (effective). Retroactive, it also lifts a throttle in force; otherwise a throttle in
 *   force stays until its release.
 * @param {Model} model @param {string} poolId
 * @returns {{id: string, subject: string, initial: string, variables: {name: string, initial: any}[], states: string[], transitions: any[]}[]}
 */
export function poolMachines(model, poolId) {
  const pool = model.entities.get(poolId);
  if (!pool || pool.kind !== 'quotaPool') throw new Error(`"${poolId}" is not a quota pool in this model.`);
  const d = pool.data;
  const n = modelMembers(pool);
  const N = d.overShare?.consecutive;
  const release = d.throttle?.release;
  const to = d.throttle?.to;
  const windowEnd = d.windowEnd;
  if (!posInt(N)) throw new Error(`Quota pool "${poolId}" has no over-share window count.`);
  if (!(posInt(release) || release === 'never')) throw new Error(`Quota pool "${poolId}" does not say when a throttle is released.`);
  const ex = isObj(d.exemption) && typeof d.exemption.event === 'string' ? d.exemption : null;
  const offset = ex?.effective === 'next-window' ? 1 : 0;
  const subject = typeof d.heldBy === 'string' ? d.heldBy : poolId;
  const out = [];
  for (const l of limitsOf(pool)) {
    const share = contributionOf(model, l);
    const usageEvent = usageEventOf(model, l);
    if (share === undefined) throw new Error(`Pooled limit "${l.name}" of "${poolId}" states no contribution.`);
    if (usageEvent === undefined) throw new Error(`Pooled limit "${l.name}" of "${poolId}" has no usage event.`);
    const capacity = share * n;
    const ids = Array.from({ length: n }, (_, i) => poolMachineId(poolId, l.name, i + 1));
    const total = `(${ids.map((id) => `${id}.usage`).join(' + ')})`;
    const rate = l.kind !== 'level';
    for (let k = 1; k <= n; k++) {
      const id = ids[k - 1];
      const me = `event.member == '${'m' + k}'`;
      const over = `usage > ${share}`;
      const exempt = ex ? `(burstFrom >= 0 && burstFrom <= day)` : 'false';
      /** @param {string} v @param {any} value */
      const set = (v, value) => ({ set: v, to: value });
      const tail = [...(rate ? [set('usage', 0)] : []), set('day', 'day + 1')];
      /** @param {string} name @param {string} from @param {string} toState @param {string} on @param {string|null} guard @param {any[]} effects */
      const t = (name, from, toState, on, guard, effects) => ({ id: `${id}-${name}`, from, to: toState, on, guard, effects, faultOnly: false });
      const admit = [set('usage', 'usage + event.amount'), set('admitted', 'admitted + 1')];
      const refuse = [set('refused', 'refused + 1')];
      const transitions = [
        t('use', 'normal', 'normal', usageEvent, `${me} && (event.amount <= 0 || ${total} + event.amount <= ${capacity})`, admit),
        t('refuse', 'normal', 'normal', usageEvent, me, refuse),
        t('use-throttled', 'throttled', 'throttled', usageEvent, to === 'refuse' ? `${me} && event.amount <= 0` : `${me} && (event.amount <= 0 || (usage + event.amount <= ${share} && ${total} + event.amount <= ${capacity}))`, admit),
        t('refuse-throttled', 'throttled', 'throttled', usageEvent, me, refuse),
        t('throttle', 'normal', 'throttled', windowEnd, `${over} && overDays + 1 >= ${N} && !${exempt}`, [set('overDays', 'overDays + 1'), set('underDays', 0), set('throttledOn', 'day'), ...tail]),
        t('over', 'normal', 'normal', windowEnd, over, [set('overDays', 'overDays + 1'), set('underDays', 0), ...tail]),
        t('under', 'normal', 'normal', windowEnd, null, [set('overDays', 0), set('underDays', 'underDays + 1'), ...tail]),
        ...(posInt(release) ? [t('release', 'throttled', 'normal', windowEnd, `!(${over}) && underDays + 1 >= ${release}`, [set('overDays', 0), set('underDays', 0), set('throttledOn', -1), ...tail])] : []),
        t('over-throttled', 'throttled', 'throttled', windowEnd, over, [set('overDays', 'overDays + 1'), set('underDays', 0), ...tail]),
        t('under-throttled', 'throttled', 'throttled', windowEnd, null, [set('overDays', 0), set('underDays', 'underDays + 1'), ...tail]),
      ];
      if (ex) {
        const mark = [set('burstSetOn', 'day'), set('burstFrom', offset ? 'day + 1' : 'day')];
        transitions.push(t('exempt', 'normal', 'normal', ex.event, `${me} && burstSetOn < 0`, mark));
        transitions.push(ex.retroactive === true
          ? t('exempt-lifts', 'throttled', 'normal', ex.event, `${me} && burstSetOn < 0`, [...mark, set('overDays', 0), set('throttledOn', -1)])
          : t('exempt-throttled', 'throttled', 'throttled', ex.event, `${me} && burstSetOn < 0`, mark));
      }
      out.push({
        id,
        subject,
        initial: 'normal',
        variables: POOL_VARIABLES.map((name) => ({ name, initial: ['throttledOn', 'burstSetOn', 'burstFrom'].includes(name) ? -1 : 0 })),
        states: [...POOL_STATES],
        transitions,
      });
    }
  }
  return out;
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
