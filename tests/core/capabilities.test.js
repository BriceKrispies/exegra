import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { analyzeSpec } from '../../src/core/analyze.js';
import { readinessGaps } from '../../src/core/readiness.js';
import { CAPABILITY_LISTS } from '../../src/core/capabilities.js';

const metamodel = JSON.parse(fs.readFileSync(new URL('../../src/core/metamodel.json', import.meta.url), 'utf8'));

// Capabilities, plans, roles, grants, delegations, token scopes and feature flags (WG-4954): each rule with a
// negative fixture, a specification that breaks exactly that rule once, and a passing case, the base
// specification below.

/**
 * A specification ready to generate from: four contracts reachable from outside their process, each requiring a
 * capability; two plans; a platform role for operators and services, a tenant role and the anonymous visitor's
 * role; a support grant, an assistant delegation from a token scope, and a flag. `generation: false` leaves the
 * switch out.
 */
function spec(mutate = (/** @type {any} */ _d) => {}, { generation = true } = {}) {
  const d = {
    exegra: '0.1',
    system: {
      id: 'site', name: 'Site',
      ...(generation ? { generation: { target: 'rust', gateway: { prefix: '/api' } } } : {}),
    },
    components: [{ id: 'gw', name: 'Gateway', category: 'computational' }],
    contracts: [
      { id: 'read-page', name: 'Read a page', realisation: 'generated', exposure: 'public', readOnly: true, tenantScope: 'request', auth: { scheme: 'anonymous', requires: ['content-read'] } },
      { id: 'publish', name: 'Publish', realisation: 'generated', exposure: 'public', tenantScope: 'request', auth: { scheme: 'session', requires: ['content-publish'], csrf: true, origin: true } },
      { id: 'schedule', name: 'Schedule a publication', realisation: 'generated', exposure: 'public', tenantScope: 'request', auth: { scheme: 'delegation', requires: ['content-schedule'] } },
      { id: 'look-up', name: 'Look up a tenant', realisation: 'generated', exposure: 'internal', readOnly: true, auth: { scheme: 'service', requires: ['tenant-resolve'] } },
      { id: 'hash', name: 'Hash a password', realisation: 'generated', exposure: 'local', auth: { scheme: 'in-process' } },
    ],
    quotas: [{ id: 'q-read', scope: 'source-address', contract: 'read-page', limit: 600, window: '1 min', onExceed: 'throttle', heldBy: 'gw' }],
    capabilities: [
      { id: 'content-read', name: 'Read published content', core: true },
      { id: 'content-publish', name: 'Publish content', core: true },
      { id: 'content-schedule', name: 'Schedule publications' },
      { id: 'tenant-resolve', name: 'Resolve a tenant', core: true },
      { id: 'support-read', name: 'Read a tenant for support', core: true },
    ],
    plans: [
      { id: 'starter', name: 'Starter', capabilities: [] },
      { id: 'business', name: 'Business', capabilities: ['content-schedule'] },
    ],
    roles: [
      { id: 'visitor', name: 'Visitor', level: 'platform', holders: ['anonymous'], capabilities: ['content-read'] },
      { id: 'platform-service', name: 'Platform service', level: 'platform', holders: ['service'], capabilities: ['tenant-resolve'] },
      { id: 'support', name: 'Support', level: 'platform', holders: ['person'], capabilities: [] },
      { id: 'owner', name: 'Owner', level: 'tenant', holders: ['person', 'team'], capabilities: ['content-read', 'content-publish', 'content-schedule', 'support-read'] },
    ],
    grants: [{ id: 'support-grant', name: 'Support grant', issuer: 'owner', grantee: 'support', capabilities: ['support-read'], perTenant: true, maxDuration: '72 h' }],
    tokenScopes: [{ id: 'content-write', name: 'content:write', capabilities: ['content-publish', 'content-schedule'] }],
    delegations: [{ id: 'assistant', name: 'Assistant', from: 'content-write', to: 'agent', capabilities: ['content-schedule'], maxDuration: '1 h' }],
    featureFlags: [{ id: 'scheduling', name: 'Scheduling', gates: ['content-schedule'], default: 'off' }],
  };
  mutate(d);
  return JSON.stringify(d, null, 2);
}

/** @param {any[]} list @param {string} id */
const entity = (list, id) => list.find((e) => e.id === id);
const errors = (/** @type {any} */ r) => r.diagnostics.filter((/** @type {any} */ d) => d.severity === 'error');

test('the kinds that name capabilities are entities of the metamodel, each with its own section', () => {
  for (const [kind, key] of Object.entries(CAPABILITY_LISTS)) {
    assert.ok(metamodel.entities[kind]?.properties?.[key], `${kind}.${key}`);
    assert.ok(Object.values(metamodel.sections).some((/** @type {any} */ s) => s.entity === kind), kind);
  }
  assert.ok(metamodel.entities.capability.properties.core);
  assert.deepEqual(metamodel.entities.role.properties.level.values, ['platform', 'tenant']);
});

// Contracts on every exposure requiring capabilities that platform and tenant roles confer, plans entitle, a grant, a delegation from a token scope and a flag validate with no errors and no readiness gaps.
// @evidence capability-model-closed
test('a specification whose contracts require capabilities that roles confer and plans entitle validates with no errors and no readiness gaps', () => {
  const r = analyzeSpec(spec());
  assert.deepEqual(errors(r).map((/** @type {any} */ d) => `${d.code} ${d.message}`), []);
  assert.deepEqual(readinessGaps(/** @type {any} */ (r.model)), []);
});

// Without the switch a contract with no requires is accepted.
// @evidence capability-model-closed
test('without system.generation a contract need not require a capability', () => {
  const r = analyzeSpec(spec((/** @type {any} */ d) => { for (const c of d.contracts) delete c.auth.requires; }, { generation: false }));
  assert.deepEqual(errors(r).map((/** @type {any} */ d) => `${d.code} ${d.message}`), []);
});

test('a local contract need not require a capability', () => {
  const r = analyzeSpec(spec());
  assert.equal(entity(JSON.parse(spec()).contracts, 'hash').auth.requires, undefined);
  assert.deepEqual(errors(r), []);
});

/** Each rule, a mutation that breaks it once, the code it reports and the path it reports at. */
const RULES = [
  ['a public contract that requires no capability', 'capability.required', 'contracts.1.auth', (/** @type {any} */ d) => { delete entity(d.contracts, 'publish').auth.requires; }],
  ['an internal contract that requires no capability', 'capability.required', 'contracts.3.auth', (/** @type {any} */ d) => { delete entity(d.contracts, 'look-up').auth.requires; }],
  ['an empty list of required capabilities', 'contract.auth-structured', 'contracts.2.auth.requires', (/** @type {any} */ d) => { entity(d.contracts, 'schedule').auth.requires = []; }],
  ['a contract requiring a capability that does not exist', 'capability.unknown', 'contracts.1.auth.requires.0', (/** @type {any} */ d) => { entity(d.contracts, 'publish').auth.requires = ['content-write']; }],
  ['a plan entitling a capability that does not exist', 'capability.unknown', 'plans.1.capabilities.1', (/** @type {any} */ d) => { entity(d.plans, 'business').capabilities.push('content-translate'); }],
  ['a role conferring a capability that does not exist', 'capability.unknown', 'roles.0.capabilities.1', (/** @type {any} */ d) => { entity(d.roles, 'visitor').capabilities.push('comments-write'); }],
  ['a token scope naming a role as a capability', 'capability.unknown', 'tokenScopes.0.capabilities.2', (/** @type {any} */ d) => { entity(d.tokenScopes, 'content-write').capabilities.push('owner'); }],
  ['a flag gating a capability that does not exist', 'capability.unknown', 'featureFlags.0.gates.0', (/** @type {any} */ d) => { entity(d.featureFlags, 'scheduling').gates = ['scheduling']; }],
  ['a capability no role or grant confers', 'capability.unreachable', 'capabilities.3', (/** @type {any} */ d) => { entity(d.roles, 'platform-service').capabilities = []; entity(d.contracts, 'look-up').auth.requires = ['content-read']; }],
  ['a capability that is not core and no plan entitles', 'capability.unreachable', 'capabilities.2', (/** @type {any} */ d) => { entity(d.plans, 'business').capabilities = []; }],
  ['a delegation passing on a capability its token scope does not hold', 'delegation.exceeds', 'delegations.0.capabilities.1', (/** @type {any} */ d) => { entity(d.delegations, 'assistant').capabilities.push('content-read'); }],
  ['a delegation passing on a capability its role does not hold', 'delegation.exceeds', 'delegations.0.capabilities.0', (/** @type {any} */ d) => { entity(d.delegations, 'assistant').from = 'visitor'; }],
  ['a grant conferring a capability its issuer does not hold', 'delegation.exceeds', 'grants.0.capabilities.1', (/** @type {any} */ d) => { entity(d.grants, 'support-grant').capabilities.push('tenant-resolve'); }],
  ['a grant whose longest duration is not a duration', 'capability.duration', 'grants.0.maxDuration', (/** @type {any} */ d) => { entity(d.grants, 'support-grant').maxDuration = 'a while'; }],
];

for (const [title, code, at, mutate] of RULES) {
  // A public contract with no requires under generation is exactly capability.required.
  // @evidence capability-model-closed # capabilities: a public contract that requires no capability is reported once as capability.required at contracts.1.auth
  // An internal contract with no requires under generation is exactly capability.required.
  // @evidence capability-model-closed # capabilities: an internal contract that requires no capability is reported once as capability.required at contracts.3.auth
  // An empty requires is exactly contract.auth-structured.
  // @evidence capability-model-closed # capabilities: an empty list of required capabilities is reported once as contract.auth-structured at contracts.2.auth.requires
  // A contract requiring a missing capability is exactly capability.unknown.
  // @evidence capability-model-closed # capabilities: a contract requiring a capability that does not exist is reported once as capability.unknown at contracts.1.auth.requires.0
  // A plan entitling a missing capability is exactly capability.unknown.
  // @evidence capability-model-closed # capabilities: a plan entitling a capability that does not exist is reported once as capability.unknown at plans.1.capabilities.1
  // A token scope naming a role as a capability is exactly capability.unknown.
  // @evidence capability-model-closed # capabilities: a token scope naming a role as a capability is reported once as capability.unknown at tokenScopes.0.capabilities.2
  // A flag gating a missing capability is exactly capability.unknown.
  // @evidence capability-model-closed # capabilities: a flag gating a capability that does not exist is reported once as capability.unknown at featureFlags.0.gates.0
  // A capability no role or grant confers is exactly capability.unreachable.
  // @evidence capability-model-closed # capabilities: a capability no role or grant confers is reported once as capability.unreachable at capabilities.3
  // A capability that is not core and that no plan entitles is exactly capability.unreachable.
  // @evidence capability-model-closed # capabilities: a capability that is not core and no plan entitles is reported once as capability.unreachable at capabilities.2
  // A delegation passing on more than its token scope holds is exactly delegation.exceeds.
  // @evidence capability-model-closed # capabilities: a delegation passing on a capability its token scope does not hold is reported once as delegation.exceeds at delegations.0.capabilities.1
  // A delegation passing on more than its role holds is exactly delegation.exceeds.
  // @evidence capability-model-closed # capabilities: a delegation passing on a capability its role does not hold is reported once as delegation.exceeds at delegations.0.capabilities.0
  // A grant conferring more than its issuer role holds is exactly delegation.exceeds.
  // @evidence capability-model-closed # capabilities: a grant conferring a capability its issuer does not hold is reported once as delegation.exceeds at grants.0.capabilities.1
  // A grant maxDuration that is not a duration is exactly capability.duration.
  // @evidence capability-model-closed # capabilities: a grant whose longest duration is not a duration is reported once as capability.duration at grants.0.maxDuration
  test(`capabilities: ${title} is reported once as ${code} at ${at}`, () => {
    const r = analyzeSpec(spec(/** @type {any} */ (mutate)));
    assert.deepEqual(errors(r).map((/** @type {any} */ d) => [d.code, d.path.join('.')]), [[code, at]], r.diagnostics.map((/** @type {any} */ d) => `${d.code} ${d.message}`).join('\n'));
  });
}

test('the name, reachability and delegation rules hold with or without system.generation', () => {
  const r = analyzeSpec(spec((/** @type {any} */ d) => {
    entity(d.contracts, 'publish').auth.requires = ['content-write'];
    entity(d.plans, 'business').capabilities = [];
    entity(d.delegations, 'assistant').capabilities.push('content-read');
  }, { generation: false }));
  assert.deepEqual(errors(r).map((/** @type {any} */ d) => d.code).sort(), ['capability.unknown', 'capability.unreachable', 'delegation.exceeds']);
});
