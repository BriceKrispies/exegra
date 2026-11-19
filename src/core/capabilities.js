// Capabilities: the named things a principal may do. A contract's structured auth names the capabilities a
// call requires (auth.requires); a plan names the capabilities it entitles, unless a capability is core; roles
// and grants confer capabilities, delegations and token scopes pass them on, and feature flags gate them per
// tenant. The rules make the model closed: every non-local contract of a specification to generate from
// requires a capability, every capability can be held and is entitled, every name resolves, and nothing passes
// on more than its source holds. Pure and deterministic; run from validate.js. See
// docs/model-and-format.md#capabilities-plans-and-roles.

import { durationNs } from './constructs.js';
import { structuredAuth } from './access.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */

/** The entity kinds that name capabilities, with the property each names them in. */
export const CAPABILITY_LISTS = Object.freeze({ plan: 'capabilities', role: 'capabilities', grant: 'capabilities', delegation: 'capabilities', tokenScope: 'capabilities', featureFlag: 'gates' });

/** @param {any} v @returns {any[]} */
const list = (v) => (Array.isArray(v) ? v : []);
/** @param {any} v */
const isObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);

/**
 * The capabilities an entity holds or passes on, as the specification lists them: a role's, a grant's, a
 * delegation's or a token scope's.
 * @param {Entity|undefined} e @returns {Set<string>}
 */
export function listedCapabilities(e) {
  if (!e) return new Set();
  const key = /** @type {Record<string, string>} */ (CAPABILITY_LISTS)[e.kind];
  return new Set(key ? list(e.data[key]).filter((c) => typeof c === 'string') : []);
}

/**
 * The capabilities a contract requires (auth.requires), or an empty list.
 * @param {Entity} c @returns {string[]}
 */
export function requiredCapabilities(c) {
  const a = structuredAuth(c);
  return a ? list(a.requires).filter((x) => typeof x === 'string') : [];
}

/**
 * The rules of capabilities, plans, roles, grants, delegations, token scopes and feature flags.
 * @param {Model} model @returns {Diagnostic[]}
 */
export function checkCapabilityConsistency(model) {
  /** @type {Diagnostic[]} */
  const out = [];
  /** @param {string} code @param {Entity} e @param {string} message @param {(string|number)[]} [sub] */
  const err = (code, e, message, sub = []) => out.push({ code, severity: 'error', message, entityId: e.id, loc: e.loc, path: [...e.path, ...sub] });
  const kind = (/** @type {string} */ k) => model.byKind[k] ?? [];
  const generating = isObj(model.system.data.generation);
  const capabilities = new Set(kind('capability').map((c) => c.id));

  /** @param {Entity} e @param {any} id @param {(string|number)[]} at @param {string} what */
  const known = (e, id, at, what) => {
    if (typeof id !== 'string') return;
    if (capabilities.has(id)) return;
    const other = model.entities.get(id);
    err('capability.unknown', e, `${what} names capability "${id}", which ${other ? `is a ${other.kind}, not a capability` : 'does not exist'}.`, at);
  };

  // Every name resolves: what contracts require, plans entitle, roles and grants confer, delegations and token
  // scopes pass on, and flags gate.
  for (const c of kind('contract')) {
    const a = structuredAuth(c);
    list(a?.requires).forEach((id, i) => known(c, id, ['auth', 'requires', i], `The auth of contract "${c.id}"`));
  }
  for (const [k, key] of Object.entries(CAPABILITY_LISTS)) {
    for (const e of kind(k)) list(e.data[key]).forEach((id, i) => known(e, id, [key, i], `${e.kind[0].toUpperCase()}${e.kind.slice(1)} "${e.id}"`));
  }

  // Every contract reachable from outside its process requires a capability, so the generated authorizer has
  // something to check against the plan, the flags and the principal.
  if (generating) {
    for (const c of kind('contract')) {
      if (c.data.exposure === undefined || c.data.exposure === 'local') continue;
      const a = structuredAuth(c);
      if (!a) continue;
      // A requires that is there but malformed is contract.auth-structured.
      if (a.requires === undefined) {
        err('capability.required', c, `Contract "${c.id}" is ${c.data.exposure} and requires no capability; a contract reachable from outside its process names in auth.requires the capabilities a call needs, so the authorizer checks the tenant's plan, its flags and the principal against them.`, ['auth']);
      }
    }
  }

  // Every capability can be held (a role or a grant confers it) and is entitled (it is core, or a plan
  // entitles it).
  /** @type {Set<string>} */
  const conferred = new Set();
  for (const e of [...kind('role'), ...kind('grant')]) for (const id of listedCapabilities(e)) conferred.add(id);
  /** @type {Set<string>} */
  const entitled = new Set();
  for (const p of kind('plan')) for (const id of list(p.data.capabilities)) if (typeof id === 'string') entitled.add(id);
  for (const cap of kind('capability')) {
    const missing = [];
    if (!conferred.has(cap.id)) missing.push('no role or grant confers it');
    if (cap.data.core !== true && !entitled.has(cap.id)) missing.push('it is not core and no plan entitles it');
    if (missing.length) err('capability.unreachable', cap, `Capability "${cap.id}" can never be used: ${missing.join(', and ')}.`);
  }

  // Nothing passes on more than its source holds: a delegation's capabilities are within what it is issued
  // from, and a grant's within what its issuer's role confers.
  for (const d of kind('delegation')) {
    const from = typeof d.data.from === 'string' ? model.entities.get(d.data.from) : undefined;
    if (!from || !Object.hasOwn(CAPABILITY_LISTS, from.kind)) continue;
    const held = listedCapabilities(from);
    list(d.data.capabilities).forEach((id, i) => {
      if (typeof id === 'string' && capabilities.has(id) && !held.has(id)) err('delegation.exceeds', d, `Delegation "${d.id}" passes on capability "${id}", which ${from.kind} "${from.id}" it is issued from does not hold; a delegation passes on at most what its source holds.`, ['capabilities', i]);
    });
    if (d.data.maxDuration !== undefined && durationNs(d.data.maxDuration) === null) err('capability.duration', d, `The longest duration of delegation "${d.id}" must be a positive duration such as "1 h".`, ['maxDuration']);
  }
  for (const g of kind('grant')) {
    const issuer = typeof g.data.issuer === 'string' ? model.entities.get(g.data.issuer) : undefined;
    if (issuer?.kind === 'role') {
      const held = listedCapabilities(issuer);
      list(g.data.capabilities).forEach((id, i) => {
        if (typeof id === 'string' && capabilities.has(id) && !held.has(id)) err('delegation.exceeds', g, `Grant "${g.id}" confers capability "${id}", which its issuer role "${issuer.id}" does not hold; a grant passes on at most what its issuer holds.`, ['capabilities', i]);
      });
    }
    if (g.data.maxDuration !== undefined && durationNs(g.data.maxDuration) === null) err('capability.duration', g, `The longest duration of grant "${g.id}" must be a positive duration such as "72 h".`, ['maxDuration']);
  }
  return out;
}
