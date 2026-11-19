import { test } from 'node:test';
import assert from 'node:assert/strict';
import { analyzeSpec } from '../../src/core/analyze.js';
import { readinessGaps } from '../../src/core/readiness.js';
import { RECORD_FIELDS, eventLogging, typeSensitivity } from '../../src/core/telemetry.js';

// Telemetry (WG-4896): system.telemetry declares the services that write structured logs; each event states
// its logging (an allowlist of payload fields, or not logged with a reason); sensitive fields and types are
// never logged; with system.generation every domain event states its logging; a journey's expectLog step
// reads a logged event's line.

/** A specification with telemetry, ready to generate from. */
function spec(mutate = (/** @type {any} */ _d) => {}, { generation = true } = {}) {
  const d = {
    exegra: '0.1',
    system: {
      id: 'notes', name: 'Notes',
      ...(generation ? { generation: { target: 'rust' } } : {}),
      telemetry: { format: 'json-lines', services: [{ id: 'backend', component: 'backend', log: 'var/logs/backend.jsonl' }, { id: 'bff', log: 'var/logs/bff.jsonl' }] },
    },
    components: [{ id: 'backend', name: 'Backend', category: 'computational' }],
    types: [
      { id: 'tenant-id', name: 'Tenant', kind: 'id', repr: 'string' },
      { id: 'session-token', name: 'Session token', kind: 'scalar', repr: 'string', sensitive: 'token' },
      { id: 'credentials', name: 'Credentials', kind: 'struct', fields: [{ name: 'login', type: 'string' }, { name: 'password', type: 'string', sensitive: 'password' }] },
      { id: 'summary', name: 'Summary', kind: 'struct', fields: [{ name: 'title', type: 'string' }] },
    ],
    events: [
      {
        id: 'record-updated', name: 'Record updated', domain: true,
        payload: [
          { name: 'tenant', type: 'tenant-id' }, { name: 'object', type: 'string' }, { name: 'record', type: 'u64' },
          { name: 'transition', type: 'option<string>', optional: true }, { name: 'body', type: 'string', sensitive: 'personal' },
          { name: 'token', type: 'session-token' }, { name: 'login', type: 'credentials' }, { name: 'tags', type: 'list<string>' },
          { name: 'summary', type: 'summary' },
        ],
        logging: { logged: true, service: 'backend', level: 'info', name: 'record.updated', tenant: 'tenant', fields: [{ field: 'object' }, { field: 'record', as: 'id' }, { field: 'transition' }] },
      },
      {
        id: 'session-started', name: 'Signed in', domain: true,
        payload: [{ name: 'tenant', type: 'tenant-id' }, { name: 'principal', type: 'string' }],
        logging: { logged: true, service: 'backend', level: 'info', name: 'session.started', tenant: 'tenant', fields: [{ field: 'principal' }] },
      },
      { id: 'page-pinged', name: 'Page pinged', domain: true, logging: { logged: false, reason: 'A heartbeat; it says nothing about the domain.' } },
      { id: 'tick', name: 'Tick' },
    ],
    uiScenarios: [
      {
        id: 'j-log', name: 'Publishing is logged',
        steps: [
          { gotoPath: { path: '/' } },
          { expectLog: { service: 'backend', event: 'record-updated', fields: { object: 'post', transition: 'publish', tenant: 'fieldnotes', id: 3 } } },
          { expectLog: { service: 'backend', event: 'session-started', timeoutMs: 5000 } },
        ],
      },
    ],
  };
  mutate(d);
  return analyzeSpec(JSON.stringify(d, null, 2));
}

/** @param {ReturnType<typeof spec>} a @param {string} prefix */
const codes = (a, prefix) => a.diagnostics.filter((x) => x.code.startsWith(prefix) && x.severity === 'error').map((x) => x.code);
/** @param {ReturnType<typeof spec>} a */
const errors = (a) => a.diagnostics.filter((x) => x.severity === 'error');

test('a specification with telemetry validates with no errors with and without the switch', () => {
  for (const generation of [true, false]) {
    const a = spec(undefined, { generation });
    assert.deepEqual(errors(a).map((x) => `${x.code}: ${x.message}`), []);
  }
  assert.deepEqual(readinessGaps(spec().model).filter((g) => g.code === 'ready.event-logging-missing'), []);
});

test('eventLogging gives the service level log name tenant and the names fields are written under', () => {
  const a = spec();
  const e = a.model.entities.get('record-updated');
  assert.deepEqual(eventLogging(e), { service: 'backend', level: 'info', name: 'record.updated', tenant: 'tenant', fields: [{ field: 'object', as: 'object' }, { field: 'record', as: 'id' }, { field: 'transition', as: 'transition' }] });
  assert.equal(eventLogging(a.model.entities.get('page-pinged')), null);
  assert.equal(eventLogging(a.model.entities.get('tick')), null);
  assert.deepEqual(RECORD_FIELDS, ['ts', 'level', 'service', 'event', 'correlation', 'tenant']);
});

test('a type is sensitive when marked or through a struct field or through list and option', () => {
  const m = spec().model;
  assert.equal(typeSensitivity(m, 'session-token'), 'token');
  assert.equal(typeSensitivity(m, 'credentials'), 'password');
  assert.equal(typeSensitivity(m, 'option<list<credentials>>'), 'password');
  assert.equal(typeSensitivity(m, 'summary'), undefined);
  assert.equal(typeSensitivity(m, 'string'), undefined);
});

/** One rule broken once: [title, mutation, expected codes]. */
const BROKEN = /** @type {[string, (d: any) => void, string[]][]} */ ([
  ['a logged field the payload does not have', (d) => { d.events[0].logging.fields.push({ field: 'missing' }); }, ['event.logging-field-unknown']],
  ['a tenant field the payload does not have', (d) => { d.events[1].logging.tenant = 'site'; }, ['event.logging-field-unknown']],
  ['a logged field marked sensitive', (d) => { d.events[0].logging.fields.push({ field: 'body' }); }, ['event.logging-field-sensitive']],
  ['a logged field of a sensitive type', (d) => { d.events[0].logging.fields.push({ field: 'token' }); }, ['event.logging-field-sensitive']],
  ['a logged field of a struct with a sensitive field', (d) => { d.events[0].logging.fields.push({ field: 'login' }); }, ['event.logging-field-sensitive', 'event.logging-field-type']],
  ['a logged list', (d) => { d.events[0].logging.fields.push({ field: 'tags' }); }, ['event.logging-field-type']],
  ['a logged struct', (d) => { d.events[0].logging.fields.push({ field: 'summary' }); }, ['event.logging-field-type']],
  ['a field written under a name every line holds', (d) => { d.events[0].logging.fields.push({ field: 'object', as: 'level' }); }, ['event.logging-field-reserved']],
  ['two fields written under one name', (d) => { d.events[0].logging.fields.push({ field: 'transition', as: 'id' }); }, ['event.logging-field-reserved']],
  ['the tenant field logged again', (d) => { d.events[0].logging.fields.push({ field: 'tenant', as: 'site' }); }, ['event.logging-field-reserved']],
  ['a field written under a name that is not lower case', (d) => { d.events[0].logging.fields[0].as = 'Object'; }, ['event.logging-field-reserved']],
  ['a service system.telemetry does not declare', (d) => { d.events[0].logging.service = 'worker'; }, ['event.logging-service']],
  ['a logged event without a level', (d) => { delete d.events[0].logging.level; }, ['event.logging-shape']],
  ['a logged event without fields', (d) => { delete d.events[0].logging.fields; }, ['event.logging-shape']],
  ['a logged event with a reason', (d) => { d.events[0].logging.reason = 'Because.'; }, ['event.logging-shape']],
  ['an event not logged without a reason', (d) => { delete d.events[2].logging.reason; }, ['event.logging-shape']],
  ['an event not logged with an allowlist', (d) => { d.events[2].logging.fields = []; }, ['event.logging-shape']],
  ['a log name that is not dotted lower-case words', (d) => { d.events[0].logging.name = 'Record Updated'; }, ['event.logging-name']],
  ['two events logged under one name by one service', (d) => { d.events[1].logging.name = 'record.updated'; }, ['event.logging-name']],
  ['a service declared twice', (d) => { d.system.telemetry.services.push({ id: 'bff', log: 'var/logs/other.jsonl' }); }, ['telemetry.service']],
  ['a service log outside the working directory', (d) => { d.system.telemetry.services[1].log = '../bff.jsonl'; }, ['telemetry.service']],
]);

for (const [title, mutate, expected] of BROKEN) {
  test(`telemetry consistency: ${title}`, () => {
    for (const generation of [true, false]) {
      // Without the journey, whose expectLog steps would also report a broken logging.
      const a = spec((d) => { mutate(d); d.uiScenarios = []; }, { generation });
      assert.deepEqual(errors(a).map((x) => x.code), expected, `${title} (generation ${generation}): ${errors(a).map((x) => x.message).join(' | ')}`);
    }
  });
}

test('a logging level outside debug, info, warn and error is refused by the metamodel', () => {
  const a = spec((d) => { d.events[0].logging.level = 'notice'; });
  assert.ok(errors(a).some((x) => x.code === 'property.enum'), errors(a).map((x) => x.code).join(', '));
});

test('telemetry readiness: a domain event that does not state its logging is a gap and an error only with the switch', () => {
  const drop = (/** @type {any} */ d) => { delete d.events[1].logging; d.uiScenarios[0].steps.pop(); };
  assert.deepEqual(codes(spec(drop), 'ready.'), ['ready.event-logging-missing']);
  assert.deepEqual(codes(spec(drop, { generation: false }), 'ready.'), []);
  assert.deepEqual(readinessGaps(spec(drop, { generation: false }).model).filter((g) => g.code === 'ready.event-logging-missing').map((g) => g.entityId), ['session-started']);
  // An event that is not a domain event needs no logging.
  assert.deepEqual(readinessGaps(spec().model).filter((g) => g.entityId === 'tick'), []);
});

/** A broken expectLog step: [title, step, expected codes]. */
const BROKEN_STEPS = /** @type {[string, any, string[]][]} */ ([
  ['an expectLog of an event that is not logged', { expectLog: { service: 'backend', event: 'page-pinged' } }, ['uiScenario.log-event']],
  ['an expectLog of an event that states no logging', { expectLog: { service: 'backend', event: 'tick' } }, ['uiScenario.log-event']],
  ['an expectLog in the log of another service', { expectLog: { service: 'bff', event: 'record-updated' } }, ['uiScenario.log-event']],
  ['an expectLog of a field outside the allowlist', { expectLog: { service: 'backend', event: 'record-updated', fields: { body: 'x' } } }, ['uiScenario.log-field']],
  ['an expectLog of a field under its payload name instead of the name it is written as', { expectLog: { service: 'backend', event: 'record-updated', fields: { record: 3 } } }, ['uiScenario.log-field']],
  ['an expectLog of an event that does not exist', { expectLog: { service: 'backend', event: 'nothing' } }, ['uiScenario.step-reference']],
  ['an expectLog without a service', { expectLog: { event: 'record-updated' } }, ['uiScenario.step']],
  ['an expectLog with a selector key', { expectLog: { service: 'backend', event: 'record-updated', role: 'status' } }, ['uiScenario.step']],
  ['an expectLog with a timeout that is not a positive integer', { expectLog: { service: 'backend', event: 'record-updated', timeoutMs: 0 } }, ['uiScenario.timeout']],
]);

for (const [title, step, expected] of BROKEN_STEPS) {
  test(`ui consistency: ${title}`, () => {
    const a = spec((d) => { d.uiScenarios[0].steps.push(step); });
    assert.deepEqual(errors(a).map((x) => x.code).filter((c) => c !== 'ref.unresolved'), expected, errors(a).map((x) => x.message).join(' | '));
  });
}

test('a logged domain event is emitted by the running system so it is not an unused event', () => {
  const unused = (/** @type {ReturnType<typeof spec>} */ a) => a.diagnostics.filter((x) => x.code === 'gap.unused-event').map((x) => x.entityId).sort();
  // record-updated and session-started are logged domain events; page-pinged is a domain event that is not logged.
  assert.deepEqual(unused(spec()), ['page-pinged', 'tick']);
  assert.deepEqual(unused(spec((d) => { d.events[0].domain = false; })), ['page-pinged', 'record-updated', 'tick']);
});
