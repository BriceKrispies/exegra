// Residency (WG-5277; docs/model-and-format.md, Residency): regions, tenant classes, component placement,
// carried records and residency exceptions. The fixture tests/fixtures/residency/harbourline.jsonc states
// Harbourline BR-04 and BR-05 on the structure and validates clean; each rule has a mutation of it that
// breaks exactly that rule once, and the integrity rules of the fixture read regions and placements
// through a recursive relation that follows data flows.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { parse } from 'jsonc-parser';
import { analyzeSpec } from '../../src/core/analyze.js';
import { evaluateIntegrity } from '../../src/core/integrity.js';

const metamodel = JSON.parse(fs.readFileSync(new URL('../../src/core/metamodel.json', import.meta.url), 'utf8'));
const FIXTURE = fs.readFileSync(new URL('../fixtures/residency/harbourline.jsonc', import.meta.url), 'utf8');

/** The fixture as an object, changed by `mutate`, as JSON text. */
function spec(mutate = (/** @type {any} */ _d) => {}) {
  const d = parse(FIXTURE);
  mutate(d);
  return JSON.stringify(d, null, 2);
}

/** @param {any[]} list @param {string} id */
const entity = (list, id) => list.find((e) => e.id === id);
const errors = (/** @type {any} */ r) => r.diagnostics.filter((/** @type {any} */ d) => d.severity === 'error');
const show = (/** @type {any} */ r) => r.diagnostics.map((/** @type {any} */ d) => `${d.severity} ${d.code} ${d.message}`).join('\n');

test('regions tenant classes and residency exceptions are entities of the metamodel with sections of their own', () => {
  for (const [kind, section] of [['region', 'regions'], ['tenantClass', 'tenantClasses'], ['residencyException', 'residencyExceptions']]) {
    assert.ok(metamodel.entities[kind], kind);
    assert.equal(metamodel.sections[section]?.entity, kind);
  }
  assert.deepEqual(metamodel.entities.component.properties.placement.values, ['per-region', 'fixed', 'global']);
  assert.deepEqual(metamodel.entities.component.properties.regions.items.ref, ['region']);
  assert.deepEqual(metamodel.entities.relationship.properties.carries.items.ref, ['record', 'type', 'event']);
  assert.deepEqual(metamodel.entities.tenantClass.properties.binds.items.ref, ['record']);
});

test('the Harbourline fixture states BR-04 and BR-05 on the structure and validates with no errors and no warnings', () => {
  const r = analyzeSpec(spec());
  assert.deepEqual(r.diagnostics.filter((/** @type {any} */ d) => d.severity !== 'info').map((/** @type {any} */ d) => `${d.code} ${d.message}`), []);
  const d = parse(FIXTURE);
  assert.equal(d.scenarios, undefined, 'no scenario says which tenant is a Harbour tenant or where it lives');
  const ex = entity(d.residencyExceptions, 'edge-acceleration-exception');
  assert.deepEqual([ex.maxDuration, ex.renewalWindow, ex.purgeWithin, ex.approvedBy], ['90 d', '14 d', '72 h', 'compliance']);
  assert.deepEqual(entity(d.copies, 'edge-page-accelerated').erasure.bound, 5, 'the excepted edge copy keeps its 5 s erasure bound');
});

/** Each rule, a mutation that breaks it once, the code it reports and the path it reports at. */
const RULES = [
  ['a copy on a global holder with no exception', 'residency.copy-outside', 'copies.3.heldBy', (/** @type {any} */ d) => { d.residencyExceptions = []; }],
  ['a copy whose exception has expired', 'residency.copy-outside', 'copies.3.heldBy', (/** @type {any} */ d) => { d.residencyExceptions[0].status = 'expired'; }],
  ['a copy whose exception allows only a region its global holder is not confined to', 'residency.copy-outside', 'copies.3.heldBy', (/** @type {any} */ d) => { d.residencyExceptions[0].regions = ['eu-central']; }],
  ['a bound record owned by a global component', 'residency.record-outside', 'records.2.owner', (/** @type {any} */ d) => {
    d.records.push({ id: 'page-draft', name: 'Page draft', owner: 'delivery-network', key: ['draft-id'], fields: [{ name: 'draft-id', type: 'draft-id' }] });
    d.tenantClasses[0].binds.push('page-draft');
  }],
  ['a flow of attachments to a sandbox fixed in one region', 'residency.flow-outside', 'relationships.0.to', (/** @type {any} */ d) => { Object.assign(entity(d.components, 'rendition-sandbox'), { placement: 'fixed', regions: ['eu-central'] }); }],
  ['a holder of bound data with no placement', 'residency.placement-missing', 'components.2.placement', (/** @type {any} */ d) => { delete entity(d.components, 'search-index').placement; }],
  ['a per-region holder with no instance in a provisioned region', 'residency.region-uncovered', 'components.6.regions', (/** @type {any} */ d) => { entity(d.components, 'mail-dispatch').regions = ['eu-central']; }],
  ['a global component that names regions', 'component.placement-regions', 'components.5.regions', (/** @type {any} */ d) => { entity(d.components, 'delivery-network').regions = ['eu-central']; }],
  ['a tenant class selected by both a flag and a plan', 'tenant-class.selector', 'tenantClasses.0.plan', (/** @type {any} */ d) => { d.tenantClasses[0].plan = 'standard'; }],
  ['a tenant class provisioned in no region', 'tenant-class.provisioned-in', 'tenantClasses.0.provisionedIn', (/** @type {any} */ d) => { d.tenantClasses[0].provisionedIn = []; }],
  ['an exception naming both a copy and a flow', 'residency.exception-target', 'residencyExceptions.0', (/** @type {any} */ d) => { d.residencyExceptions[0].flow = 'db-to-search'; }],
  ['an exception for a copy of no bound record', 'residency.exception-target', 'residencyExceptions.0.copy', (/** @type {any} */ d) => { d.tenantClasses[0].binds = ['attachment']; }],
  ['a bounded exception with no purge obligation', 'residency.exception-purge', 'residencyExceptions.0', (/** @type {any} */ d) => { delete d.residencyExceptions[0].purgeWithin; }],
  ['an exception whose longest duration is not a duration', 'residency.exception-duration', 'residencyExceptions.0.maxDuration', (/** @type {any} */ d) => { d.residencyExceptions[0].maxDuration = 'ninety days'; }],
  ['a renewal window not shorter than the longest duration', 'residency.exception-renewal', 'residencyExceptions.0.renewalWindow', (/** @type {any} */ d) => { d.residencyExceptions[0].renewalWindow = '120 d'; }],
];

for (const [title, code, at, mutate] of RULES) {
  test(`residency: ${title} is reported once as ${code} at ${at}`, () => {
    const r = analyzeSpec(spec(/** @type {any} */ (mutate)));
    assert.deepEqual(errors(r).map((/** @type {any} */ d) => [d.code, d.path.join('.')]), [[code, at]], show(r));
  });
}

test('a fixed holder inside the provisioned regions is accepted for provisioned-regions confinement and refused for home', () => {
  const fixed = (/** @type {any} */ d) => { Object.assign(entity(d.components, 'rendition-sandbox'), { placement: 'fixed', regions: ['eu-central', 'ca-central'] }); };
  const regional = analyzeSpec(spec((/** @type {any} */ d) => { fixed(d); d.tenantClasses[0].confinement = 'provisioned-regions'; }));
  assert.deepEqual(errors(regional), [], show(regional));
  const home = analyzeSpec(spec(fixed));
  assert.deepEqual(errors(home).map((/** @type {any} */ d) => d.code), ['residency.flow-outside'], show(home));
});

test('a tenant class with confinement none confines nothing', () => {
  const r = analyzeSpec(spec((/** @type {any} */ d) => { d.residencyExceptions = []; d.tenantClasses[0].confinement = 'none'; entity(d.components, 'search-index').placement = 'global'; }));
  assert.deepEqual(errors(r), [], show(r));
});

test('integrity rules read regions and placements and follow carried data through a recursive relation', () => {
  const clean = analyzeSpec(spec());
  const before = evaluateIntegrity(/** @type {any} */ (clean.model));
  assert.deepEqual(before.map((r) => [r.ruleId, r.status, r.vacuous]), [['notification-payload-reference-only', 'holds', false], ['confined-data-in-region', 'holds', false]]);

  const broken = analyzeSpec(spec((/** @type {any} */ d) => {
    entity(d.components, 'rendition-sandbox').placement = 'global';
    entity(d.copies, 'notification-payload').fields.push('content');
  }));
  const after = evaluateIntegrity(/** @type {any} */ (broken.model));
  const region = after.find((r) => r.ruleId === 'confined-data-in-region');
  assert.equal(region?.status, 'violated');
  assert.deepEqual(region?.counterexamples.map((c) => c.values), [['s:harbour', 's:rendition-sandbox']], 'the sandbox is reached only through the flow that carries attachments');
  assert.equal(after.find((r) => r.ruleId === 'notification-payload-reference-only')?.status, 'violated');
});
