import { test } from 'node:test';
import assert from 'node:assert/strict';
import { analyzeSpec } from '../../src/core/analyze.js';
import { readinessGaps } from '../../src/core/readiness.js';
import { durationNs } from '../../src/core/constructs.js';
import { dataFindings } from '../../src/core/data-model.js';

// Cross-cutting constructs (WG-4856): policy, validation, retention, quota, retry and audit; their consistency
// rules (always errors), their readiness rules (errors when system.generation is set), and requirements
// realised by construction through them.

/** A specification using every construct, ready to generate from. `generation: false` leaves the switch out. */
function spec(mutate = (/** @type {any} */ _d) => {}, { generation = true } = {}) {
  const d = {
    exegra: '0.1',
    system: { id: 'shop', name: 'Shop', ...(generation ? { generation: { target: 'rust' } } : {}) },
    vocabulary: { verificationMethods: { review: { label: 'Review', description: 'Checked by a person.' } } },
    components: [
      { id: 'svc', name: 'Service', category: 'computational' },
      { id: 'archive', name: 'Archive', category: 'storage' },
      { id: 'limiter', name: 'Limiter', category: 'storage' },
    ],
    types: [
      { id: 'order-id', name: 'Order id', kind: 'id', repr: 'uuid' },
      { id: 'order-status', name: 'Order status', kind: 'enum', values: ['open', 'paid'] },
      { id: 'money', name: 'Money', kind: 'scalar', repr: 'i64' },
    ],
    records: [
      {
        id: 'order', name: 'Order', owner: 'svc', key: ['id'], schemaVersion: 1,
        fields: [
          { name: 'id', type: 'order-id' },
          { name: 'tenant', type: 'string' },
          { name: 'status', type: 'order-status' },
          { name: 'total', type: 'money' },
          { name: 'note', type: 'option<string>', optional: true },
        ],
      },
      {
        id: 'member', name: 'Member', owner: 'svc', key: ['id'], schemaVersion: 1,
        fields: [{ name: 'id', type: 'uuid' }, { name: 'email', type: 'string', personal: 'contact' }],
      },
      {
        id: 'audit-entry', name: 'Audit entry', owner: 'svc', key: ['seq'], schemaVersion: 1,
        fields: [
          { name: 'seq', type: 'u64' },
          { name: 'actor', type: 'string' },
          { name: 'order', type: 'order-id' },
          { name: 'at', type: 'timestamp' },
          { name: 'prev', type: 'bytes' },
          { name: 'detail', type: 'option<string>', optional: true },
        ],
      },
    ],
    contracts: [
      {
        id: 'ct-place', name: 'Place an order', realisation: 'generated', policyDefault: 'deny',
        inputs: [{ name: 'order', type: 'order-id' }, { name: 'tenant', type: 'string' }, { name: 'amount', type: 'money' }, { name: 'note', type: 'string', optional: true }],
        outputs: [{ name: 'accepted', type: 'bool' }],
        errors: [{ name: 'rate-limited' }, { name: 'invalid' }],
      },
    ],
    events: [
      { id: 'placed', name: 'Placed', payload: [{ name: 'order', type: 'order-id' }, { name: 'tenant', type: 'string' }] },
      { id: 'member-left', name: 'Member left', payload: [{ name: 'member', type: 'uuid' }] },
    ],
    behaviors: [
      {
        id: 'order-flow', name: 'Order flow', subject: 'svc', level: 'implementation', initial: 'open',
        storage: { record: 'order', key: 'id', state: 'status', stateValues: { done: 'paid' } },
        transaction: { scope: 'transition', isolation: 'serializable' },
        states: [{ id: 'open', name: 'Open' }, { id: 'done', name: 'Done', terminal: true }],
        transitions: [{ id: 't-place', from: 'open', to: 'done', on: 'placed', otherwise: true }],
      },
    ],
    policies: [
      { id: 'p-place', subject: { principal: 'member', role: 'buyer' }, contract: 'ct-place', resource: 'order', condition: "request.tenant == principal.tenant && record.status == 'open'", effect: 'allow' },
      { id: 'p-flow', subject: { principal: 'service' }, transition: 't-place', condition: 'event.tenant == principal.tenant', effect: 'allow' },
    ],
    validations: [
      { id: 'v-order', contract: 'ct-place', input: 'order', rule: 'required', message: 'An order is required.' },
      { id: 'v-note', contract: 'ct-place', input: 'note', rule: 'maxLength', maxLength: 200, unit: 'characters', message: 'A note is at most 200 characters.' },
      { id: 'v-tenant', contract: 'ct-place', input: 'tenant', rule: 'pattern', pattern: '^[a-z]+$', message: 'A tenant is lower-case letters.' },
      { id: 'v-amount', contract: 'ct-place', input: 'amount', rule: 'range', min: 1, max: 1000000, message: 'An amount is 1 to 1000000.' },
      { id: 'v-status', record: 'order', field: 'status', rule: 'oneOf', values: ['open', 'paid'], message: 'A status is open or paid.' },
      { id: 'v-total', record: 'order', field: 'total', rule: 'custom', expr: "value >= 0 || record.status == 'open'", message: 'A paid order has a total.' },
    ],
    retentions: [
      { id: 'r-member', record: 'member', until: 'member-left', then: 'anonymise', fields: ['email'] },
      { id: 'r-order', record: 'order', keepFor: '400 d', then: 'archive', archiveTo: 'archive' },
    ],
    quotas: [
      { id: 'q-place', scope: 'tenant', contract: 'ct-place', limit: 100, window: '1 min', onExceed: 'refuse', error: 'rate-limited', heldBy: 'limiter' },
    ],
    retries: [
      { id: 'y-place', contract: 'ct-place', attempts: 3, backoff: { kind: 'exponential', base: '100 ms', cap: '2 s' }, idempotencyKey: 'order', timeout: '5 s' },
    ],
    audits: [
      {
        id: 'a-place', contract: 'ct-place', record: 'audit-entry', immutability: 'chained-hash', chainField: 'prev',
        capture: [{ field: 'actor', from: 'principal.id' }, { field: 'order', from: 'request.order' }, { field: 'at', from: 'time' }],
      },
    ],
    claims: [
      { id: 'r-limit', kind: 'requirement', statement: 'A tenant places at most 100 orders a minute.', realisation: 'construction', realisedBy: ['q-place'], evaluate: { method: 'review' } },
      { id: 'r-audit', kind: 'requirement', statement: 'Every order placed leaves a chained audit entry.', realisation: 'construction', realisedBy: ['a-place', 'p-place'], evaluate: { method: 'review' } },
      { id: 'c-struct', kind: 'structural', statement: 'Orders are kept.', evaluate: { method: 'review' } },
    ],
  };
  mutate(d);
  // Every contract states its exposure and a structured auth (contract.exposure, contract.auth-structured); a
  // contract whose test leaves them out is a local, in-process one.
  for (const c of /** @type {any[]} */ (d.contracts ?? [])) {
    if (!('exposure' in c)) c.exposure = 'local';
    if (!('auth' in c)) c.auth = { scheme: 'in-process' };
  }
  return JSON.stringify(d, null, 2);
}

/** @param {any[]} list @param {string} id */
const entity = (list, id) => list.find((e) => e.id === id);
const errors = (/** @type {any} */ r) => r.diagnostics.filter((/** @type {any} */ d) => d.severity === 'error');
const codes = (/** @type {any} */ ds) => ds.map((/** @type {any} */ d) => d.code);
/** @param {any} r */
const explain = (r) => r.diagnostics.map((/** @type {any} */ d) => `${d.severity} ${d.code} ${d.message}`).join('\n');

test('a specification with every construct validates with no errors, no warnings and no readiness gaps', () => {
  const r = analyzeSpec(spec());
  assert.deepEqual(r.diagnostics.filter((/** @type {any} */ d) => d.severity !== 'info').map((/** @type {any} */ d) => `${d.code} ${d.message}`), []);
  assert.deepEqual(readinessGaps(/** @type {any} */ (r.model)), []);
});

/** Each consistency rule, a mutation that breaks it once, and the code it reports. */
const CONSISTENCY = [
  ['a policy naming both a contract and a transition', 'policy.target', (/** @type {any} */ d) => { entity(d.policies, 'p-place').transition = 't-place'; }],
  ['a policy condition that does not parse', 'policy.expr-syntax', (/** @type {any} */ d) => { entity(d.policies, 'p-place').condition = 'request.tenant =='; }],
  ['a policy condition reading an undeclared input', 'policy.expr-reference', (/** @type {any} */ d) => { entity(d.policies, 'p-place').condition = 'request.region == principal.tenant'; }],
  ['a policy condition comparing a number with a string', 'policy.expr-type', (/** @type {any} */ d) => { entity(d.policies, 'p-flow').condition = 'event.tenant == 3'; }],
  ['a contract validation naming a field', 'validation.target', (/** @type {any} */ d) => { entity(d.validations, 'v-order').field = 'order'; }],
  ['a validation of an undeclared input', 'validation.target-unknown', (/** @type {any} */ d) => { entity(d.validations, 'v-order').input = 'basket'; }],
  ['a maxLength that is not a positive integer', 'validation.param', (/** @type {any} */ d) => { entity(d.validations, 'v-note').maxLength = 0; }],
  ['a range over a string input', 'validation.target-type', (/** @type {any} */ d) => { entity(d.validations, 'v-amount').input = 'tenant'; }],
  ['a pattern that is not a regular expression', 'validation.pattern', (/** @type {any} */ d) => { entity(d.validations, 'v-tenant').pattern = '([a-z'; }],
  ['an empty range', 'validation.range', (/** @type {any} */ d) => { Object.assign(entity(d.validations, 'v-amount'), { min: 10, max: 1 }); }],
  ['a custom rule comparing a number with a string', 'validation.expr-type', (/** @type {any} */ d) => { entity(d.validations, 'v-total').expr = "value >= 'a'"; }],
  ['a retention with both keepFor and until', 'retention.period', (/** @type {any} */ d) => { entity(d.retentions, 'r-order').until = 'member-left'; }],
  ['a retention period that is not a duration', 'retention.duration', (/** @type {any} */ d) => { entity(d.retentions, 'r-order').keepFor = '400 days'; }],
  ['fields on a retention that does not anonymise', 'retention.fields', (/** @type {any} */ d) => { entity(d.retentions, 'r-order').fields = ['note']; }],
  ['an anonymised field the record does not have', 'retention.field-unknown', (/** @type {any} */ d) => { entity(d.retentions, 'r-member').fields.push('phone'); }],
  ['two retentions of one record', 'retention.duplicate', (/** @type {any} */ d) => { d.retentions.push({ id: 'r-order-2', record: 'order', keepFor: '1 d', then: 'delete' }); }],
  ['an archive target on a retention that does not archive', 'retention.archive-target', (/** @type {any} */ d) => { entity(d.retentions, 'r-member').archiveTo = 'archive'; }],
  ['a quota naming both a contract and an event', 'quota.target', (/** @type {any} */ d) => { entity(d.quotas, 'q-place').event = 'placed'; }],
  ['a quota limit of zero', 'quota.limit', (/** @type {any} */ d) => { entity(d.quotas, 'q-place').limit = 0; }],
  ['a quota window that is not a duration', 'quota.window', (/** @type {any} */ d) => { entity(d.quotas, 'q-place').window = '1 minute'; }],
  ['a refusing quota without an error', 'quota.error-missing', (/** @type {any} */ d) => { delete entity(d.quotas, 'q-place').error; }],
  ['a quota error the contract does not declare', 'quota.error-unknown', (/** @type {any} */ d) => { entity(d.quotas, 'q-place').error = 'too-many'; }],
  ['an error on a quota that queues', 'quota.error-misplaced', (/** @type {any} */ d) => { entity(d.quotas, 'q-place').onExceed = 'queue'; }],
  ['a retry naming both a contract and an event', 'retry.target', (/** @type {any} */ d) => { entity(d.retries, 'y-place').event = 'placed'; }],
  ['a retry of zero attempts', 'retry.attempts', (/** @type {any} */ d) => { entity(d.retries, 'y-place').attempts = 0; }],
  ['a retry timeout that is not a duration', 'retry.duration', (/** @type {any} */ d) => { entity(d.retries, 'y-place').timeout = '5 sec'; }],
  ['a cap on a fixed backoff', 'retry.backoff', (/** @type {any} */ d) => { entity(d.retries, 'y-place').backoff.kind = 'fixed'; }],
  ['an idempotency key that is not an input', 'retry.idempotency-key-unknown', (/** @type {any} */ d) => { entity(d.retries, 'y-place').idempotencyKey = 'request-id'; }],
  ['an audit naming both a contract and an event', 'audit.target', (/** @type {any} */ d) => { entity(d.audits, 'a-place').event = 'placed'; }],
  ['an audit capturing one field twice', 'audit.capture', (/** @type {any} */ d) => { entity(d.audits, 'a-place').capture.push({ field: 'actor', from: 'principal.tenant' }); }],
  ['an audit capturing a field the record does not have', 'audit.field-unknown', (/** @type {any} */ d) => { entity(d.audits, 'a-place').capture.push({ field: 'who', from: 'principal.id' }); }],
  ['an audit capture reading an undeclared output', 'audit.expr-reference', (/** @type {any} */ d) => { entity(d.audits, 'a-place').capture.push({ field: 'detail', from: 'response.reason' }); }],
  ['an audit capture of the wrong class', 'audit.expr-type', (/** @type {any} */ d) => { entity(d.audits, 'a-place').capture[2].from = 'principal.id'; }],
  ['a chain field on an append-only audit', 'audit.chain-field', (/** @type {any} */ d) => { entity(d.audits, 'a-place').immutability = 'append-only'; }],
  ['realisedBy on a claim that is not a requirement', 'claim.realised-by-not-requirement', (/** @type {any} */ d) => { entity(d.claims, 'c-struct').realisedBy = ['q-place']; }],
  ['a construction requirement with neither models nor realisedBy', 'requirement.construction-unmodelled', (/** @type {any} */ d) => { delete entity(d.claims, 'r-limit').realisedBy; }],
];

const generationChecked = new Set();
for (const [title, code, mutate] of CONSISTENCY) {
  // The generation switch is checked once per family of reported codes (the part before the dot); the other cases run without it.
  const modes = generationChecked.has(code.split(".")[0]) ? [false] : [false, true];
  generationChecked.add(code.split(".")[0]);
  for (const generation of modes) {
    test(`construct consistency: ${title} is reported once as ${code}${generation ? ' (generation set)' : ''}`, () => {
      const r = analyzeSpec(spec(/** @type {any} */ (mutate), { generation }));
      assert.deepEqual(codes(errors(r)), [code], explain(r));
      assert.ok(errors(r)[0].loc && errors(r)[0].loc.line > 1);
    });
  }
}

/** Each readiness rule, a mutation that breaks it once, and the code it reports. */
const READINESS = [
  ['a contract governed by policies without a policyDefault', 'ready.policy-default-missing', (/** @type {any} */ d) => { delete entity(d.contracts, 'ct-place').policyDefault; }],
  ['a policy on a transition of a model-level machine', 'ready.policy-transition-model-level', (/** @type {any} */ d) => { delete entity(d.behaviors, 'order-flow').level; }],
  ['a maxLength validation without a unit', 'ready.validation-unit-missing', (/** @type {any} */ d) => { delete entity(d.validations, 'v-note').unit; }],
  ['a record with personal fields and no retention', 'ready.retention-missing', (/** @type {any} */ d) => { d.retentions = d.retentions.filter((/** @type {any} */ t) => t.id !== 'r-member'); }],
  ['an archiving retention without a target', 'ready.retention-archive-target-missing', (/** @type {any} */ d) => { delete entity(d.retentions, 'r-order').archiveTo; }],
  ['a quota that does not say who keeps its counters', 'ready.quota-held-by-missing', (/** @type {any} */ d) => { delete entity(d.quotas, 'q-place').heldBy; }],
  ['a retry of a call that is not idempotent without a key', 'ready.retry-idempotency-missing', (/** @type {any} */ d) => { delete entity(d.retries, 'y-place').idempotencyKey; }],
  ['a retry without a timeout', 'ready.retry-timeout-missing', (/** @type {any} */ d) => { delete entity(d.retries, 'y-place').timeout; }],
  ['an audit leaving a required field unfilled', 'ready.audit-field-unfilled', (/** @type {any} */ d) => { entity(d.audits, 'a-place').capture.shift(); }],
];

for (const [title, code, mutate] of READINESS) {
  test(`construct readiness: ${title} is exactly one ${code} error when generation is set`, () => {
    const r = analyzeSpec(spec(/** @type {any} */ (mutate)));
    assert.deepEqual(codes(errors(r)), [code], explain(r));
    assert.ok(errors(r)[0].loc && errors(r)[0].loc.line > 1);
  });

  test(`construct readiness: ${title} is no validation diagnostic without the switch and readinessGaps lists ${code}`, () => {
    const r = analyzeSpec(spec(/** @type {any} */ (mutate), { generation: false }));
    assert.deepEqual(r.diagnostics.filter((/** @type {any} */ d) => d.code.startsWith('ready.')), []);
    assert.equal(r.errorCount, 0);
    assert.deepEqual(codes(readinessGaps(/** @type {any} */ (r.model))), [code]);
  });
}

test('construct durations are a positive decimal with a unit from ns to d', () => {
  assert.equal(durationNs('100 ms'), 1e8);
  assert.equal(durationNs('1.5 s'), 1.5e9);
  assert.equal(durationNs('400 d'), 400 * 8.64e13);
  assert.equal(durationNs('2min'), 1.2e11);
  for (const bad of ['0 s', '5 sec', '1 week', '-1 s', 5, undefined]) assert.equal(durationNs(bad), null, String(bad));
});

test('a retention that deletes a record, or anonymises its personal fields, satisfies the record erasure rule', () => {
  const rule = (/** @type {any} */ r) => dataFindings(r.model).findings.filter((/** @type {any} */ f) => f.rule === 'record-erasure-point').map((/** @type {any} */ f) => f.entityId);
  assert.deepEqual(rule(analyzeSpec(spec())), []);
  const partly = analyzeSpec(spec((/** @type {any} */ d) => { entity(d.records, 'member').fields.push({ name: 'phone', type: 'string', personal: 'contact' }); }));
  assert.deepEqual(rule(partly), ['member']);
  const deleted = analyzeSpec(spec((/** @type {any} */ d) => { Object.assign(entity(d.retentions, 'r-member'), { then: 'delete' }); delete entity(d.retentions, 'r-member').fields; }));
  assert.deepEqual(rule(deleted), []);
});
