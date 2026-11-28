import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { analyzeSpec } from '../../src/core/analyze.js';
import { readinessGaps } from '../../src/core/readiness.js';
import { AUTH_SCHEMES, EXPOSURES, TENANT_SCOPES } from '../../src/core/access.js';

const metamodel = JSON.parse(fs.readFileSync(new URL('../../src/core/metamodel.json', import.meta.url), 'utf8'));

// Contract exposure and structured auth (WG-4908): each rule with a negative fixture, a specification that
// breaks exactly that rule once, and a passing case, the base specification below.

/**
 * A specification ready to generate from whose eight contracts cover every exposure and the schemes a web
 * platform uses. `generation: false` leaves the switch out.
 */
function spec(mutate = (/** @type {any} */ _d) => {}, { generation = true } = {}) {
  const d = {
    exegra: '0.1',
    system: {
      id: 'site', name: 'Site',
      ...(generation ? { generation: { target: 'rust', gateway: { prefix: '/api' }, developmentConditions: ['DEV'] } } : {}),
    },
    components: [
      { id: 'gw', name: 'Gateway', category: 'computational' },
      { id: 'svc', name: 'Service', category: 'computational' },
    ],
    contracts: [
      { id: 'read-page', name: 'Read a page', realisation: 'generated', exposure: 'public', readOnly: true, tenantScope: 'request', auth: { scheme: 'anonymous' } },
      { id: 'sign-in', name: 'Sign in', realisation: 'generated', exposure: 'public', tenantScope: 'request', auth: { scheme: 'anonymous', csrf: true, origin: true, justification: 'Signing in is how a visitor gets a session.' } },
      { id: 'save-post', name: 'Save a post', realisation: 'generated', exposure: 'public', tenantScope: 'request', policyDefault: 'deny', auth: { scheme: 'session', roles: ['author'], policies: ['p-save'], csrf: true, origin: true, stepUp: '15 min' } },
      { id: 'receive-hook', name: 'Receive a webhook', realisation: 'generated', exposure: 'public', tenantScope: 'request', binding: { protocol: 'http', method: 'POST', path: '/api/hooks/in' }, auth: { scheme: 'signature', secret: 'endpoint-secret' } },
      { id: 'look-up-session', name: 'Look up a session', realisation: 'generated', exposure: 'internal', readOnly: true, binding: { protocol: 'http', method: 'POST', path: '/internal/session' }, auth: { scheme: 'service' } },
      { id: 'health', name: 'Health', realisation: 'generated', exposure: 'internal', readOnly: true, auth: { scheme: 'anonymous', justification: 'Probes reach it before any credential exists.' } },
      { id: 'hash', name: 'Hash a password', realisation: 'generated', exposure: 'local', auth: { scheme: 'in-process' } },
      { id: 'reset', name: 'Reset fixtures', realisation: 'generated', exposure: 'public', tenantScope: 'request', development: 'DEV', policyDefault: 'deny', auth: { scheme: 'session', roles: ['owner'], csrf: true, origin: true } },
    ],
    policies: [
      { id: 'p-save', subject: { principal: 'member', role: 'author' }, contract: 'save-post', effect: 'allow' },
      { id: 'p-reset', subject: { principal: 'member', role: 'owner' }, contract: 'reset', effect: 'allow' },
    ],
    quotas: [
      { id: 'q-read', scope: 'source-address', contract: 'read-page', limit: 600, window: '1 min', onExceed: 'throttle', heldBy: 'gw' },
      { id: 'q-sign-in', scope: 'source-address', contract: 'sign-in', limit: 10, window: '1 min', onExceed: 'throttle', heldBy: 'gw' },
    ],
  };
  mutate(d);
  // Every contract reachable from outside its process requires a capability (capability.required, WG-4954); one
  // whose test does not name one requires "use", which every principal holds and every plan has.
  requireUse(d);
  return JSON.stringify(d, null, 2);
}

/**
 * Give every non-local contract with a structured auth and no requires the capability "use", core and held
 * through the platform role "everyone", which the specification gains unless it states its own capabilities.
 * @param {any} d
 */
function requireUse(d) {
  let used = false;
  for (const c of /** @type {any[]} */ (d.contracts ?? [])) {
    if (c.exposure === 'local' || c.auth === null || typeof c.auth !== 'object' || 'requires' in c.auth) continue;
    c.auth.requires = ['use'];
    used = true;
  }
  if (!used || d.capabilities) return;
  d.capabilities = [{ id: 'use', name: 'Use the system', core: true }];
  d.roles = [...(d.roles ?? []), { id: 'everyone', name: 'Everyone', level: 'platform', holders: ['person', 'service', 'agent', 'anonymous', 'external'], capabilities: ['use'] }];
}

/** @param {any[]} list @param {string} id */
const entity = (list, id) => list.find((e) => e.id === id);
const errors = (/** @type {any} */ r) => r.diagnostics.filter((/** @type {any} */ d) => d.severity === 'error');

test('the exposures, schemes and tenant scopes are the ones the metamodel and the docs name', () => {
  assert.deepEqual([...EXPOSURES], ['public', 'internal', 'local']);
  assert.deepEqual([...AUTH_SCHEMES], ['anonymous', 'session', 'service', 'provisioning-token', 'signature', 'signed-address', 'delegation', 'in-process']);
  assert.deepEqual(metamodel.entities.contract.properties.exposure.values, [...EXPOSURES]);
  assert.deepEqual(metamodel.entities.contract.properties.tenantScope.values, [...TENANT_SCOPES]);
});

// Eight contracts covering every exposure and the anonymous, session, signature, service and in-process schemes validate with no errors and no readiness gaps.
// @evidence contract-exposure-and-auth
test('a specification stating exposure and structured auth on every contract validates with no errors and no readiness gaps', () => {
  const r = analyzeSpec(spec());
  assert.deepEqual(errors(r).map((/** @type {any} */ d) => `${d.code} ${d.message}`), []);
  assert.deepEqual(readinessGaps(/** @type {any} */ (r.model)), []);
});

// Without the switch prose auth and a missing exposure are accepted.
// @evidence contract-exposure-and-auth
test('without system.generation a contract may state its auth as a sentence and leave its exposure out', () => {
  const r = analyzeSpec(spec((/** @type {any} */ d) => {
    for (const c of d.contracts) { c.auth = 'Anyone.'; delete c.exposure; delete c.tenantScope; delete c.development; delete c.binding; }
    d.quotas = [];
  }, { generation: false }));
  assert.deepEqual(errors(r).map((/** @type {any} */ d) => `${d.code} ${d.message}`), []);
});

/** Each rule, a mutation that breaks it once, the code it reports and the path it reports at. */
const RULES = [
  ['prose auth under generation', 'contract.auth-structured', 'contracts.2.auth', (/** @type {any} */ d) => { entity(d.contracts, 'save-post').auth = 'An author of the site.'; delete entity(d.contracts, 'save-post').policyDefault; d.policies.shift(); }],
  ['a contract with no auth under generation', 'contract.auth-structured', 'contracts.6', (/** @type {any} */ d) => { delete entity(d.contracts, 'hash').auth; }],
  ['an auth with an unknown scheme', 'contract.auth-structured', 'contracts.4.auth.scheme', (/** @type {any} */ d) => { entity(d.contracts, 'look-up-session').auth.scheme = 'token'; }],
  ['csrf on a service credential', 'contract.auth-structured', 'contracts.4.auth.csrf', (/** @type {any} */ d) => { entity(d.contracts, 'look-up-session').auth.csrf = true; }],
  ['a member an auth does not have', 'contract.auth-structured', 'contracts.4.auth.when', (/** @type {any} */ d) => { entity(d.contracts, 'look-up-session').auth.when = 'always'; }],
  ['a signature without its secret', 'contract.auth-structured', 'contracts.3.auth', (/** @type {any} */ d) => { delete entity(d.contracts, 'receive-hook').auth.secret; }],
  ['a step-up that is not a duration', 'contract.auth-structured', 'contracts.2.auth.stepUp', (/** @type {any} */ d) => { entity(d.contracts, 'save-post').auth.stepUp = 'soon'; }],
  ['a contract with no exposure under generation', 'contract.exposure', 'contracts.4.exposure', (/** @type {any} */ d) => { delete entity(d.contracts, 'look-up-session').exposure; }],
  ['an internal contract called in-process', 'contract.exposure', 'contracts.4.auth.scheme', (/** @type {any} */ d) => { entity(d.contracts, 'look-up-session').auth = { scheme: 'in-process' }; }],
  ['a local contract taking the service credential', 'contract.exposure', 'contracts.6.auth.scheme', (/** @type {any} */ d) => { entity(d.contracts, 'hash').auth = { scheme: 'service' }; }],
  ['a public write by session without csrf', 'auth.public-write', 'contracts.2.auth', (/** @type {any} */ d) => { delete entity(d.contracts, 'save-post').auth.csrf; }],
  ['a public write by session without origin', 'auth.public-write', 'contracts.2.auth', (/** @type {any} */ d) => { entity(d.contracts, 'save-post').auth.origin = false; }],
  ['an anonymous public write without csrf and origin', 'auth.public-write', 'contracts.1.auth', (/** @type {any} */ d) => { const a = entity(d.contracts, 'sign-in').auth; delete a.csrf; delete a.origin; }],
  ['an anonymous public write without a justification', 'auth.anonymous', 'contracts.1.auth', (/** @type {any} */ d) => { delete entity(d.contracts, 'sign-in').auth.justification; }],
  ['an anonymous public contract without a quota', 'auth.anonymous', 'contracts.0.auth', (/** @type {any} */ d) => { d.quotas.shift(); }],
  ['an anonymous internal contract without a justification', 'auth.anonymous', 'contracts.5.auth', (/** @type {any} */ d) => { delete entity(d.contracts, 'health').auth.justification; }],
  ['an internal contract bound under the gateway', 'exposure.gateway', 'contracts.4.binding.path', (/** @type {any} */ d) => { entity(d.contracts, 'look-up-session').binding.path = '/api/session'; }],
  ['a local contract with an HTTP binding', 'exposure.gateway', 'contracts.6.binding', (/** @type {any} */ d) => { entity(d.contracts, 'hash').binding = { protocol: 'http', method: 'POST', path: '/internal/hash' }; }],
  ['a gateway prefix with a trailing slash', 'exposure.gateway', 'system.generation.gateway', (/** @type {any} */ d) => { d.system.generation.gateway.prefix = '/api/'; entity(d.contracts, 'receive-hook').binding.path = '/api//hooks'; }],
  ['an auth naming a policy that does not exist', 'auth.policy-unknown', 'contracts.2.auth.policies.0', (/** @type {any} */ d) => { entity(d.contracts, 'save-post').auth.policies = ['p-missing']; }],
  ['an auth naming the policy of another contract', 'auth.policy-unknown', 'contracts.2.auth.policies.1', (/** @type {any} */ d) => { entity(d.contracts, 'save-post').auth.policies.push('p-reset'); }],
  ['a public contract taking the service credential', 'auth.service-public', 'contracts.0.auth.scheme', (/** @type {any} */ d) => { entity(d.contracts, 'read-page').auth = { scheme: 'service' }; }],
  ['a development contract under an undeclared condition', 'auth.dev-only', 'contracts.7.development', (/** @type {any} */ d) => { entity(d.contracts, 'reset').development = 'PROD'; }],
  ['a development contract open to anonymous callers', 'auth.dev-only', 'contracts.7.auth.scheme', (/** @type {any} */ d) => {
    entity(d.contracts, 'reset').auth = { scheme: 'anonymous', csrf: true, origin: true, justification: 'Fixtures.' };
    d.quotas.push({ id: 'q-reset', scope: 'source-address', contract: 'reset', limit: 1, window: '1 min', onExceed: 'throttle', heldBy: 'gw' });
  }],
  ['a public development contract open to any session', 'auth.dev-only', 'contracts.7.auth', (/** @type {any} */ d) => { delete entity(d.contracts, 'reset').auth.roles; }],
  ['a public contract that does not state its tenant scope', 'contract.tenant-scope', 'contracts.0.tenantScope', (/** @type {any} */ d) => { delete entity(d.contracts, 'read-page').tenantScope; }],
  ['a public contract returning data across tenants', 'contract.tenant-scope', 'contracts.2.tenantScope', (/** @type {any} */ d) => { entity(d.contracts, 'save-post').tenantScope = 'platform'; }],
];

for (const [title, code, at, mutate] of RULES) {
  // Prose auth under generation is exactly contract.auth-structured.
  // @evidence contract-exposure-and-auth # access: prose auth under generation is reported once as contract.auth-structured at contracts.2.auth
  // A contract with no auth under generation is exactly contract.auth-structured.
  // @evidence contract-exposure-and-auth # access: a contract with no auth under generation is reported once as contract.auth-structured at contracts.6
  // A member on a scheme it does not apply to is exactly contract.auth-structured.
  // @evidence contract-exposure-and-auth # access: csrf on a service credential is reported once as contract.auth-structured at contracts.4.auth.csrf
  // A contract with no exposure under generation is exactly contract.exposure.
  // @evidence contract-exposure-and-auth # access: a contract with no exposure under generation is reported once as contract.exposure at contracts.4.exposure
  // The in-process scheme on an internal contract is exactly contract.exposure.
  // @evidence contract-exposure-and-auth # access: an internal contract called in-process is reported once as contract.exposure at contracts.4.auth.scheme
  // A public state-changing session contract without csrf is exactly auth.public-write.
  // @evidence contract-exposure-and-auth # access: a public write by session without csrf is reported once as auth.public-write at contracts.2.auth
  // An anonymous public write without csrf and origin is exactly auth.public-write.
  // @evidence contract-exposure-and-auth # access: an anonymous public write without csrf and origin is reported once as auth.public-write at contracts.1.auth
  // An anonymous public write without a justification is exactly auth.anonymous.
  // @evidence contract-exposure-and-auth # access: an anonymous public write without a justification is reported once as auth.anonymous at contracts.1.auth
  // An anonymous public contract no quota limits is exactly auth.anonymous.
  // @evidence contract-exposure-and-auth # access: an anonymous public contract without a quota is reported once as auth.anonymous at contracts.0.auth
  // An internal contract bound under the gateway prefix is exactly exposure.gateway.
  // @evidence contract-exposure-and-auth # access: an internal contract bound under the gateway is reported once as exposure.gateway at contracts.4.binding.path
  // A local contract with an HTTP binding is exactly exposure.gateway.
  // @evidence contract-exposure-and-auth # access: a local contract with an HTTP binding is reported once as exposure.gateway at contracts.6.binding
  // An auth naming a missing policy is exactly auth.policy-unknown.
  // @evidence contract-exposure-and-auth # access: an auth naming a policy that does not exist is reported once as auth.policy-unknown at contracts.2.auth.policies.0
  // The service scheme on a public contract is exactly auth.service-public.
  // @evidence contract-exposure-and-auth # access: a public contract taking the service credential is reported once as auth.service-public at contracts.0.auth.scheme
  // A development contract open to anonymous callers is exactly auth.dev-only.
  // @evidence contract-exposure-and-auth # access: a development contract open to anonymous callers is reported once as auth.dev-only at contracts.7.auth.scheme
  // A public contract with tenantScope platform is exactly contract.tenant-scope.
  // @evidence contract-exposure-and-auth # access: a public contract returning data across tenants is reported once as contract.tenant-scope at contracts.2.tenantScope
  test(`access: ${title} is reported once as ${code} at ${at}`, () => {
    const r = analyzeSpec(spec(/** @type {any} */ (mutate)));
    assert.deepEqual(errors(r).map((/** @type {any} */ d) => [d.code, d.path.join('.')]), [[code, at]], r.diagnostics.map((/** @type {any} */ d) => `${d.code} ${d.message}`).join('\n'));
  });
}

test('the shape and the cross rules of a structured auth hold with or without system.generation', () => {
  const r = analyzeSpec(spec((/** @type {any} */ d) => { delete entity(d.contracts, 'save-post').auth.csrf; entity(d.contracts, 'look-up-session').auth.csrf = true; delete entity(d.contracts, 'reset').development; }, { generation: false }));
  assert.deepEqual(errors(r).map((/** @type {any} */ d) => d.code).sort(), ['auth.public-write', 'contract.auth-structured']);
});
