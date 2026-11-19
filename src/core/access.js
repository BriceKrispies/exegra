// Who may call a contract and from where: its exposure (public, internal, local) and its structured auth (a
// scheme with roles, policies, CSRF and origin, step-up, a named secret). The rules make the security posture
// checkable data: a free-text auth is refused once the specification sets system.generation, a public
// state-changing contract needs a browser session with CSRF and origin or a verified credential, an anonymous
// caller is admitted only where the specification says why and limits it with a quota, a service credential is
// never accepted on a public contract, and an internal or local contract is never routable through the gateway.
// Pure and deterministic; run from validate.js. See docs/model-and-format.md#contract-exposure-and-auth.

import { durationNs } from './constructs.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */

/** Where a contract can be reached from. */
export const EXPOSURES = Object.freeze(['public', 'internal', 'local']);

/** How a caller proves who it is. */
export const AUTH_SCHEMES = Object.freeze(['anonymous', 'session', 'service', 'provisioning-token', 'signature', 'signed-address', 'delegation', 'in-process']);

/** What a contract may return of tenant data. */
export const TENANT_SCOPES = Object.freeze(['request', 'none', 'platform']);

/**
 * The members of a structured auth and the schemes each is allowed on (null: every scheme).
 * @type {Record<string, string[]|null>}
 */
const MEMBERS = {
  scheme: null,
  description: null,
  requires: null,
  roles: ['session', 'delegation', 'in-process'],
  policies: ['session', 'delegation', 'in-process'],
  tenantPolicies: ['session', 'delegation', 'in-process'],
  csrf: ['session', 'anonymous'],
  origin: ['session', 'anonymous'],
  stepUp: ['session', 'delegation'],
  secret: ['signature', 'signed-address'],
  justification: ['anonymous'],
};

/** Schemes whose credential a browser never attaches by itself, so a write needs no CSRF token: it is verified. */
const VERIFIED_WRITE = ['signature', 'signed-address', 'provisioning-token', 'delegation'];

/** @param {any} v */
const isObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);
/** @param {any} v */
const nonEmpty = (v) => typeof v === 'string' && v.trim() !== '';

/**
 * The structured auth of a contract, or undefined when it states none or states it as prose.
 * @param {Entity} c @returns {any}
 */
export function structuredAuth(c) {
  return isObj(c.data.auth) ? c.data.auth : undefined;
}

/**
 * The rules of contract exposure and auth.
 * @param {Model} model @returns {Diagnostic[]}
 */
export function checkAccessConsistency(model) {
  /** @type {Diagnostic[]} */
  const out = [];
  /** @param {string} code @param {Entity} e @param {string} message @param {(string|number)[]} [sub] */
  const err = (code, e, message, sub = []) => out.push({ code, severity: 'error', message, entityId: e.id, loc: e.loc, path: [...e.path, ...sub] });
  const sys = model.system;
  const g = isObj(sys.data.generation) ? sys.data.generation : undefined;
  const generating = g !== undefined;

  // The gateway and the development conditions are stated once, on system.generation.
  const gateway = g && isObj(g.gateway) ? g.gateway : undefined;
  if (g && g.gateway !== undefined && !(gateway && typeof gateway.prefix === 'string' && /^\/[A-Za-z0-9._~/-]*$/.test(gateway.prefix) && !gateway.prefix.endsWith('/'))) {
    err('exposure.gateway', sys, 'system.generation.gateway.prefix must be the path every public route is served under through the gateway, such as "/api": "/" and plain segments, without a trailing "/".', ['generation', 'gateway']);
  }
  /** @type {string[]} */
  const conditions = g && Array.isArray(g.developmentConditions) ? g.developmentConditions.filter(nonEmpty) : [];
  if (g && g.developmentConditions !== undefined && !(Array.isArray(g.developmentConditions) && g.developmentConditions.every(nonEmpty))) {
    err('auth.dev-only', sys, 'system.generation.developmentConditions must list the names of the deployment conditions under which development contracts exist, such as "STRATA_DEV".', ['generation', 'developmentConditions']);
  }
  const prefix = gateway && typeof gateway.prefix === 'string' ? gateway.prefix : undefined;
  /** @param {string} path */
  const underGateway = (path) => prefix !== undefined && (path === prefix || path.startsWith(`${prefix}/`));

  /** The contracts each quota limits. */
  /** @type {Set<string>} */
  const quoted = new Set();
  for (const q of model.byKind.quota ?? []) if (typeof q.data.contract === 'string') quoted.add(q.data.contract);

  for (const c of model.byKind.contract ?? []) {
    const d = c.data;
    const exposure = typeof d.exposure === 'string' ? d.exposure : undefined;

    // Presence: under generation every contract states where it is reachable from and who may call it.
    if (generating && exposure === undefined) err('contract.exposure', c, `Contract "${c.id}" states no exposure: public (reachable from browsers and the internet through the gateway), internal (the service network only) or local (an in-process call).`, ['exposure']);
    if (typeof d.auth === 'string') {
      if (generating) err('contract.auth-structured', c, `The auth of contract "${c.id}" is prose ("${d.auth}"); a specification to generate from states it as {scheme, ...} so the authorizer is generated from it, not read from words.`, ['auth']);
    } else if (d.auth === undefined) {
      if (generating) err('contract.auth-structured', c, `Contract "${c.id}" states no auth; a specification to generate from states who may call every contract as {scheme, ...}, and nothing unstated is admitted.`, []);
    } else if (!isObj(d.auth)) {
      err('contract.auth-structured', c, `The auth of contract "${c.id}" must be an object {scheme, ...} (or, without system.generation, a sentence).`, ['auth']);
    }
    const a = structuredAuth(c);
    if (a) checkShape(c, a, err);
    const scheme = a && AUTH_SCHEMES.includes(a.scheme) ? a.scheme : undefined;

    // Exposure and scheme together.
    if (scheme && exposure) {
      if (scheme === 'in-process' && exposure !== 'local') err('contract.exposure', c, `Contract "${c.id}" is ${exposure} but its auth scheme is in-process; only a local contract is called in-process.`, ['auth', 'scheme']);
      if (exposure === 'local' && scheme !== 'in-process') err('contract.exposure', c, `Contract "${c.id}" is local, so it is called in-process and its auth scheme is in-process, not ${scheme}.`, ['auth', 'scheme']);
      if (scheme === 'service' && exposure === 'public') err('auth.service-public', c, `Contract "${c.id}" is public and accepts the service credential; a service credential is accepted only on internal contracts, never on a route a browser or the internet reaches.`, ['auth', 'scheme']);
    }

    // Never routable through the gateway: a local contract has no route at all, an internal one none under the
    // gateway's prefix.
    const path = isObj(d.binding) && typeof d.binding.path === 'string' ? d.binding.path : undefined;
    if (exposure === 'local' && isObj(d.binding) && (d.binding.path !== undefined || d.binding.method !== undefined)) {
      err('exposure.gateway', c, `Contract "${c.id}" is local (an in-process call) but states an HTTP binding; a local contract is never served on a route.`, ['binding']);
    } else if (exposure !== undefined && exposure !== 'public' && path !== undefined && underGateway(path)) {
      err('exposure.gateway', c, `Contract "${c.id}" is ${exposure} but is bound to "${path}", under the gateway's prefix "${prefix}"; only public contracts are routed through the gateway.`, ['binding', 'path']);
    }

    // A public state-changing contract needs a browser session (or visitor) with CSRF and origin checked, or a
    // verified credential that no browser attaches by itself.
    const readOnly = d.readOnly === true;
    if (exposure === 'public' && scheme && !readOnly) {
      const browserChecked = (scheme === 'session' || scheme === 'anonymous') && a.csrf === true && a.origin === true;
      if (!browserChecked && !VERIFIED_WRITE.includes(scheme)) {
        err('auth.public-write', c, `Contract "${c.id}" is public and changes state (it is not marked readOnly), so its auth must be a session with csrf and origin checked, or a verified credential (signature, signed-address, provisioning-token, delegation); it is ${scheme}${scheme === 'session' || scheme === 'anonymous' ? ` without ${[a.csrf === true ? '' : 'csrf', a.origin === true ? '' : 'origin'].filter(Boolean).join(' and ')}` : ''}.`, ['auth']);
      }
    }

    // Anonymous callers: only where the specification says why, and limited by a quota.
    if (scheme === 'anonymous') {
      const justified = nonEmpty(a.justification);
      if (exposure === 'public') {
        if (!readOnly && !justified) err('auth.anonymous', c, `Contract "${c.id}" admits anonymous callers and changes state; an anonymous public contract is marked readOnly or states a justification.`, ['auth']);
        if (!quoted.has(c.id)) err('auth.anonymous', c, `Contract "${c.id}" admits anonymous callers from the internet but no quota limits it; state a quota whose contract is "${c.id}".`, ['auth']);
      } else if (exposure === 'internal') {
        if (!readOnly || !justified) err('auth.anonymous', c, `Contract "${c.id}" is internal and admits callers without the service credential; that is only for a readOnly contract with a justification (such as a health check).`, ['auth']);
      }
    }

    // Policies named by the auth exist and govern this contract.
    if (a && Array.isArray(a.policies)) {
      a.policies.forEach((/** @type {any} */ id, /** @type {number} */ i) => {
        if (typeof id !== 'string') return;
        const p = model.entities.get(id);
        if (p?.kind !== 'policy') err('auth.policy-unknown', c, `The auth of contract "${c.id}" names policy "${id}", which ${p ? `is a ${p.kind}, not a policy` : 'does not exist'}.`, ['auth', 'policies', i]);
        else if (p.data.contract !== c.id) err('auth.policy-unknown', c, `The auth of contract "${c.id}" names policy "${id}", which governs ${typeof p.data.contract === 'string' ? `contract "${p.data.contract}"` : 'no contract'}, not this one.`, ['auth', 'policies', i]);
      });
    }

    // Development and fixture contracts exist only under a declared development condition, and never for
    // anonymous callers.
    if (d.development !== undefined) {
      if (!nonEmpty(d.development)) err('auth.dev-only', c, `The development condition of contract "${c.id}" must name a deployment condition, such as "STRATA_DEV".`, ['development']);
      else if (!conditions.includes(d.development)) err('auth.dev-only', c, `Contract "${c.id}" exists under the development condition "${d.development}", which system.generation.developmentConditions does not declare (${conditions.join(', ') || 'none declared'}).`, ['development']);
      if (scheme === 'anonymous') err('auth.dev-only', c, `Contract "${c.id}" is a development contract open to anonymous callers; a development fixture names who may use it (a session with roles).`, ['auth', 'scheme']);
      if (exposure === 'public' && scheme === 'session' && !(Array.isArray(a.roles) && a.roles.length)) err('auth.dev-only', c, `Contract "${c.id}" is a public development contract open to any session; name the roles that may use it.`, ['auth']);
    }

    // Tenant scope: a public contract says what tenant data it returns, and never crosses tenants.
    const scope = d.tenantScope;
    if (exposure === 'public') {
      if (scope === undefined) { if (generating) err('contract.tenant-scope', c, `Contract "${c.id}" is public and does not state its tenantScope: request (only the data of the tenant the request is made in, which a principal's own tenant must match) or none.`, ['tenantScope']); }
      else if (scope === 'platform') err('contract.tenant-scope', c, `Contract "${c.id}" is public and returns data across tenants (tenantScope platform); a public contract returns only the data of the request's own tenant, or none.`, ['tenantScope']);
    }
  }
  return out;
}

/**
 * The shape of a structured auth: a known scheme, known members on the schemes they belong to, and their values.
 * @param {Entity} c @param {any} a @param {(code: string, e: Entity, message: string, sub?: (string|number)[]) => void} err
 */
function checkShape(c, a, err) {
  const bad = (/** @type {string} */ message, /** @type {(string|number)[]} */ sub) => err('contract.auth-structured', c, `The auth of contract "${c.id}": ${message}`, ['auth', ...sub]);
  if (!AUTH_SCHEMES.includes(a.scheme)) {
    bad(`"scheme" is ${a.scheme === undefined ? 'missing' : JSON.stringify(a.scheme)}; it is one of ${AUTH_SCHEMES.join(', ')}.`, a.scheme === undefined ? [] : ['scheme']);
    return;
  }
  for (const [key, v] of Object.entries(a)) {
    if (!Object.hasOwn(MEMBERS, key)) { bad(`"${key}" is not a member of an auth; they are ${Object.keys(MEMBERS).join(', ')}.`, [key]); continue; }
    const on = MEMBERS[key];
    if (on && !on.includes(a.scheme)) { bad(`"${key}" does not apply to the ${a.scheme} scheme (only to ${on.join(', ')}).`, [key]); continue; }
    if (key === 'roles' && !(Array.isArray(v) && v.length && v.every(nonEmpty))) bad('"roles" is a non-empty list of role names, any one of which admits the caller.', [key]);
    if (key === 'policies' && !(Array.isArray(v) && v.length && v.every(nonEmpty))) bad('"policies" is a non-empty list of policy ids.', [key]);
    if (key === 'requires' && !(Array.isArray(v) && v.length && v.every(nonEmpty))) bad('"requires" is a non-empty list of capability ids, every one of which a call needs.', [key]);
    if (['tenantPolicies', 'csrf', 'origin'].includes(key) && typeof v !== 'boolean') bad(`"${key}" is true or false.`, [key]);
    if (key === 'stepUp' && durationNs(v) === null) bad('"stepUp" is how recently the caller must have proved who it is, a positive duration such as "5 min".', [key]);
    if (['secret', 'justification', 'description'].includes(key) && !nonEmpty(v)) bad(`"${key}" is a non-empty text.`, [key]);
  }
  if ((a.scheme === 'signature' || a.scheme === 'signed-address') && !nonEmpty(a.secret)) bad(`the ${a.scheme} scheme names the secret it is verified with ("secret").`, []);
}
