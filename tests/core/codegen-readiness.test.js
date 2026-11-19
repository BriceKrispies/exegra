import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { analyzeSpec } from '../../src/core/analyze.js';
import { readinessGaps } from '../../src/core/readiness.js';
import { BUILTIN_TYPES, WIRE_CASES, isBuiltinType } from '../../src/core/builtin-types.js';
import { RUNTIME_FAILURES, errorStatus, exprClass, typeClass } from '../../src/core/codegen-model.js';
import { parseExpr } from '../../src/core/expr.js';
const metamodel = JSON.parse(fs.readFileSync(new URL('../../src/core/metamodel.json', import.meta.url), 'utf8'));
import { runCommand, exitCodeOf } from '../../cli/commands.js';

// Declared types, record constraints, contract details, holes and requirement realisation (WG-4840): the
// consistency rules that always apply, and the readiness rules that apply when system.generation is set.

/** A specification that is ready to generate from. `generation: false` leaves the switch out. */
function spec(mutate = (/** @type {any} */ _d) => {}, { generation = true } = {}) {
  const d = {
    exegra: '0.1',
    system: { id: 'shop', name: 'Shop', ...(generation ? { generation: { target: 'rust' } } : {}) },
    vocabulary: {
      properties: [{ entity: 'claim', name: 'models', type: 'ref', ref: ['claim'], label: 'Checks requirement' }],
      verificationMethods: { review: { label: 'Review', description: 'Checked by a person.' } },
    },
    components: [
      { id: 'svc', name: 'Service', category: 'computational' },
      { id: 'impl', name: 'Hand-written part', category: 'computational' },
    ],
    types: [
      { id: 'order-id', name: 'Order id', kind: 'id', repr: 'uuid' },
      { id: 'order-status', name: 'Order status', kind: 'enum', values: ['open', 'paid'] },
      { id: 'money', name: 'Money', kind: 'scalar', repr: 'i64' },
      { id: 'address', name: 'Address', kind: 'struct', fields: [{ name: 'street', type: 'string' }, { name: 'zip', type: 'option<string>', optional: true }] },
    ],
    records: [
      {
        id: 'customer', name: 'Customer', owner: 'svc', key: ['id'], schemaVersion: 1, changes: [{ version: 1, description: 'First shape.' }],
        fields: [{ name: 'id', type: 'order-id' }, { name: 'home', type: 'address' }],
      },
      {
        id: 'order', name: 'Order', owner: 'svc', key: ['id'], schemaVersion: 2,
        changes: [{ version: 1, description: 'First shape.' }, { version: 2, description: 'Added the customer.' }],
        unique: [['id'], ['customer', 'status']],
        indexes: [{ name: 'by-status', fields: ['status'] }],
        fields: [
          { name: 'id', type: 'order-id' },
          { name: 'status', type: 'order-status' },
          { name: 'total', type: 'money', constraints: { min: 0 } },
          { name: 'tags', type: 'list<string>' },
          { name: 'note', type: 'option<string>', optional: true, constraints: { maxLength: 200 } },
          { name: 'customer', type: 'order-id', refersTo: 'customer', optional: true, onDelete: 'set-null' },
        ],
      },
    ],
    contracts: [
      {
        id: 'ct-place', name: 'Place an order', ref: 'CT-001', realisation: 'generated', exposure: 'internal', auth: { scheme: 'service' }, idempotent: true, timeoutMs: 2000,
        inputs: [{ name: 'order', type: 'order-id' }], outputs: [{ name: 'accepted', type: 'bool' }],
        errors: [{ name: 'rejected', condition: 'The order is not open.', type: 'string' }],
      },
      {
        id: 'ct-price', name: 'Price an order', ref: 'H-001', realisation: 'hand', implementedBy: 'impl',
        inputs: [{ name: 'order', type: 'order-id' }], outputs: [{ name: 'total', type: 'money' }],
        postconditions: ['The total is the sum of the line totals.'],
      },
    ],
    events: [{ id: 'placed', name: 'Placed', payload: [{ name: 'order', type: 'order-id' }, { name: 'lines', type: 'list<money>' }] }],
    claims: [
      { id: 'r-construction', kind: 'requirement', statement: 'Every order has a status.', realisation: 'construction', evaluate: { method: 'review' } },
      { id: 'r-checked', kind: 'requirement', statement: 'Prices are exact.', realisation: 'checked', evaluate: { method: 'review' } },
      { id: 'r-operational', kind: 'requirement', statement: 'A place call answers in two seconds.', realisation: 'operational', evaluate: { method: 'review' } },
      { id: 'c-status', kind: 'structural', statement: 'The order record has a status.', models: 'r-construction', evaluate: { method: 'external-evidence' } },
    ],
  };
  mutate(d);
  // Every contract states its exposure and a structured auth (contract.exposure, contract.auth-structured); a
  // contract whose test leaves them out is a local, in-process one.
  for (const c of /** @type {any[]} */ (d.contracts ?? [])) {
    if (!('exposure' in c)) c.exposure = 'local';
    if (!('auth' in c)) c.auth = { scheme: 'in-process' };
  }
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

/** @param {string} id @param {(d: any) => any} f */
const entity = (list, id) => list.find((/** @type {any} */ e) => e.id === id);
const errors = (/** @type {any} */ r) => r.diagnostics.filter((/** @type {any} */ d) => d.severity === 'error');
const codes = (/** @type {any} */ ds) => ds.map((/** @type {any} */ d) => d.code);

test('the built-in representation types are the ones the format names', () => {
  assert.deepEqual([...BUILTIN_TYPES], ['bool', 'u8', 'u16', 'u32', 'u64', 'i32', 'i64', 'f64', 'string', 'bytes', 'timestamp', 'duration', 'uuid', 'json', 'unit']);
  assert.ok(isBuiltinType('uuid'));
  assert.ok(!isBuiltinType('order-id'));
});

test('a ready specification validates with no errors and no readiness gaps', () => {
  const r = analyzeSpec(spec());
  assert.deepEqual(errors(r).map((/** @type {any} */ d) => `${d.code} ${d.message}`), []);
  assert.deepEqual(readinessGaps(/** @type {any} */ (r.model)), []);
});

/** Each consistency rule, a mutation that breaks it once, and the code it reports. They hold with or without the switch. */
const CONSISTENCY = [
  ['set-null without optional', 'record.set-null-required', (/** @type {any} */ d) => { entity(d.records, 'order').fields[5].optional = false; }],
  ['onDelete without refersTo', 'record.on-delete-without-refers-to', (/** @type {any} */ d) => { entity(d.records, 'order').fields[1].onDelete = 'restrict'; }],
  ['a unique set naming an undeclared field', 'record.unique-field', (/** @type {any} */ d) => { entity(d.records, 'order').unique.push(['missing']); }],
  ['an index naming an undeclared field', 'record.index-field', (/** @type {any} */ d) => { entity(d.records, 'order').indexes[0].fields.push('missing'); }],
  ['changes with a gap in the versions', 'record.changes-version', (/** @type {any} */ d) => { entity(d.records, 'order').changes[1].version = 3; }],
  ['changes that stop before the schema version', 'record.changes-version', (/** @type {any} */ d) => { entity(d.records, 'order').changes.pop(); }],
  ['an id type without a representation', 'type.repr-missing', (/** @type {any} */ d) => { delete entity(d.types, 'order-id').repr; }],
  ['a scalar over a type that is not built in', 'type.repr-not-builtin', (/** @type {any} */ d) => { entity(d.types, 'money').repr = 'decimal'; }],
  ['an enum without values', 'type.values-missing', (/** @type {any} */ d) => { entity(d.types, 'order-status').values = []; }],
  ['a struct field whose type does not resolve', 'type.field-unresolved', (/** @type {any} */ d) => { entity(d.types, 'address').fields[0].type = 'street-name'; }],
  ['an id represented as json', 'type.repr-json', (/** @type {any} */ d) => { entity(d.types, 'order-id').repr = 'json'; }],
  ['a type with the name of a built-in', 'type.shadows-builtin', (/** @type {any} */ d) => { d.types.push({ id: 'uuid', name: 'Uuid', kind: 'scalar', repr: 'string' }); }],
  ['a construction requirement no claim models', 'requirement.construction-unmodelled', (/** @type {any} */ d) => { delete entity(d.claims, 'c-status').models; }],
];

for (const [title, code, mutate] of CONSISTENCY) {
  for (const generation of [false, true]) {
    test(`${title} is reported once as ${code}${generation ? ' (generation set)' : ''}`, () => {
      const r = analyzeSpec(spec(/** @type {any} */ (mutate), { generation }));
      assert.deepEqual(codes(errors(r)), [code], r.diagnostics.map((/** @type {any} */ d) => d.message).join('\n'));
      assert.ok(errors(r)[0].loc && errors(r)[0].loc.line > 1);
    });
  }
}

/** Each readiness rule, a mutation that breaks it once, and the code it reports. */
const READINESS = [
  ['a record field whose type is not declared', 'ready.field-type-undeclared', (/** @type {any} */ d) => { entity(d.records, 'order').fields[1].type = 'order-state'; }],
  ['a contract input whose type is not declared', 'ready.contract-input-type-undeclared', (/** @type {any} */ d) => { entity(d.contracts, 'ct-place').inputs[0].type = 'basket'; }],
  ['a contract output whose type is not declared', 'ready.contract-output-type-undeclared', (/** @type {any} */ d) => { entity(d.contracts, 'ct-place').outputs[0].type = 'receipt'; }],
  ['a contract error whose type is not declared', 'ready.contract-error-type-undeclared', (/** @type {any} */ d) => { entity(d.contracts, 'ct-place').errors[0].type = 'rejection'; }],
  ['an event payload field whose type is not declared', 'ready.event-payload-type-undeclared', (/** @type {any} */ d) => { entity(d.events, 'placed').payload[1].type = 'list<line>'; }],
  ['a reference without onDelete', 'ready.on-delete-missing', (/** @type {any} */ d) => { delete entity(d.records, 'order').fields[5].onDelete; }],
  ['a record without a schema version', 'ready.schema-version-missing', (/** @type {any} */ d) => { const r = entity(d.records, 'customer'); delete r.schemaVersion; delete r.changes; }],
  ['a contract without a realisation', 'ready.contract-realisation-missing', (/** @type {any} */ d) => { delete entity(d.contracts, 'ct-place').realisation; }],
  ['a hole without an H- ref', 'ready.hole-ref-invalid', (/** @type {any} */ d) => { entity(d.contracts, 'ct-price').ref = 'CT-002'; }],
  ['a hole without implementedBy', 'ready.hole-implemented-by-missing', (/** @type {any} */ d) => { delete entity(d.contracts, 'ct-price').implementedBy; }],
  ['a hole without a postcondition', 'ready.hole-postcondition-missing', (/** @type {any} */ d) => { delete entity(d.contracts, 'ct-price').postconditions; }],
  ['a requirement without a realisation', 'ready.requirement-realisation-missing', (/** @type {any} */ d) => { delete entity(d.claims, 'r-operational').realisation; }],
];

for (const [title, code, mutate] of READINESS) {
  test(`${title} is exactly one ${code} error when generation is set`, () => {
    const r = analyzeSpec(spec(/** @type {any} */ (mutate)));
    assert.deepEqual(codes(errors(r)), [code], r.diagnostics.map((/** @type {any} */ d) => d.message).join('\n'));
    assert.equal(errors(r)[0].severity, 'error');
    assert.ok(errors(r)[0].loc && errors(r)[0].loc.line > 1);
  });

  test(`${title} is no validation diagnostic without the switch and readinessGaps lists ${code}`, () => {
    const r = analyzeSpec(spec(/** @type {any} */ (mutate), { generation: false }));
    assert.deepEqual(r.diagnostics.filter((/** @type {any} */ d) => d.code.startsWith('ready.')), []);
    assert.equal(r.errorCount, 0);
    const gaps = readinessGaps(/** @type {any} */ (r.model));
    assert.deepEqual(codes(gaps), [code]);
    assert.ok(typeof gaps[0].entityId === 'string' && gaps[0].message.length > 0);
  });
}

test('a type name resolves when it is built in or declared or list/option of one that resolves', () => {
  const r = analyzeSpec(spec((/** @type {any} */ d) => {
    const f = entity(d.records, 'order').fields;
    f[1].type = 'list<option<order-status>>';
    f[2].type = 'option<money>';
  }));
  assert.deepEqual(errors(r), []);
  const bad = analyzeSpec(spec((/** @type {any} */ d) => { entity(d.records, 'order').fields[1].type = 'list<option<nothing>>'; }));
  assert.deepEqual(codes(errors(bad)), ['ready.field-type-undeclared']);
});

test('the readiness command lists the gaps of a specification and exits 0 either way', async () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-readiness-'));
  try {
    for (const [name, text] of [['broken', spec((/** @type {any} */ d) => { delete entity(d.claims, 'r-operational').realisation; }, { generation: false })], ['ready', spec()]]) {
      fs.mkdirSync(path.join(dir, name));
      fs.writeFileSync(path.join(dir, name, 'spec.jsonc'), text);
    }
    const broken = await runCommand('readiness', [], { specs: dir, project: 'broken' });
    assert.equal(broken.ok, true);
    assert.equal(broken.command, 'readiness');
    assert.equal(broken.project, 'broken');
    assert.deepEqual(broken.result.gaps.map((/** @type {any} */ g) => g.code), ['ready.requirement-realisation-missing']);
    assert.equal(exitCodeOf(broken), 0);
    const ready = await runCommand('readiness', [], { specs: dir, project: 'ready' });
    assert.deepEqual(ready.result.gaps, []);
    assert.equal(exitCodeOf(ready), 0);
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
});

test('the exegra and strata specifications that do not set the switch validate with no errors and no warnings', async () => {
  const projects = ['exegra'];
  if (fs.existsSync(fileURLToPath(new URL('../../../strata/specifications/spec.jsonc', import.meta.url)))) projects.push('strata');
  for (const project of projects) {
    const env = await runCommand('validate', [], { project });
    assert.equal(env.ok, true, project);
    assert.equal(env.result.errors, 0, project);
    assert.equal(env.result.warnings, 0, project);
    assert.ok(!env.result.diagnostics.some((/** @type {any} */ d) => d.code.startsWith('ready.')), project);
  }
});

// Wire naming and the json type (WG-4881).

test('the wire case is set on the system and overridden per contract with the cases WIRE_CASES lists', () => {
  assert.deepEqual(metamodel.entities.system.properties.generation.fields.wireCase.values, [...WIRE_CASES]);
  assert.deepEqual(metamodel.entities.contract.properties.binding.fields.case.values, [...WIRE_CASES]);
  for (const wc of WIRE_CASES) {
    const r = analyzeSpec(spec((/** @type {any} */ d) => {
      d.system.generation.wireCase = wc;
      entity(d.contracts, 'ct-place').binding = { protocol: 'http', method: 'POST', path: '/orders', case: wc };
    }));
    assert.deepEqual(errors(r), [], wc);
  }
});

test('a wire case that is not one of the cases is a property.enum error at its position', () => {
  const r = analyzeSpec(spec((/** @type {any} */ d) => {
    d.system.generation.wireCase = 'SCREAMING_CASE';
    entity(d.contracts, 'ct-place').binding = { case: 'PascalCase' };
  }));
  assert.deepEqual(errors(r).map((/** @type {any} */ e) => [e.code, e.path.join('.')]), [
    ['property.enum', 'system.generation.wireCase'],
    ['property.enum', 'contracts.0.binding.case'],
  ]);
});

test('json is a built-in that resolves anywhere a type is named and is its own class', () => {
  const r = analyzeSpec(spec((/** @type {any} */ d) => {
    entity(d.contracts, 'ct-place').inputs.push({ name: 'params', type: 'json' });
    entity(d.contracts, 'ct-place').outputs.push({ name: 'blocks', type: 'list<json>' });
    entity(d.types, 'address').fields.push({ name: 'refs', type: 'option<json>', optional: true });
    entity(d.events, 'placed').payload.push({ name: 'extra', type: 'json' });
  }));
  assert.deepEqual(errors(r), []);
  assert.equal(typeClass(/** @type {any} */ (r.model), 'json'), 'json');
  assert.equal(typeClass(/** @type {any} */ (r.model), 'option<json>'), 'json');
  assert.equal(typeClass(/** @type {any} */ (r.model), 'list<json>'), 'list');
});

test('a json value is compared only by equality with json or null and takes no ordering arithmetic or text', () => {
  /** @param {string} src */
  const check = (src) => {
    const parsed = parseExpr(src);
    assert.ok(parsed.ok, src);
    return exprClass(/** @type {any} */ (parsed).ast, (path) => (path[1] === 'j' || path[1] === 'k' ? 'json' : path[1] === 's' ? 'string' : path[1] === 'n' ? 'number' : 'any'));
  };
  for (const ok of ['a.j == a.k', 'a.j != null', 'null == a.j', 'a.j == a.x']) assert.deepEqual(check(ok), { cls: 'bool' }, ok);
  for (const bad of ['a.j < a.k', 'a.j + 1', 'a.j + a.s', '-a.j', '!a.j', 'a.j && true', 'a.j == a.s', 'a.n != a.j']) assert.ok(check(bad).error, bad);
});

// Contract errors on the wire (WG-4893): statuses, kinds and the error body.

/** The ready specification with error kinds, an error body and a served contract whose errors name kinds. */
function wired(mutate = (/** @type {any} */ _d) => {}, { generation = true } = {}) {
  return spec((/** @type {any} */ d) => {
    d.system.generation = {
      ...(d.system.generation ?? {}),
      errorKinds: { unauthenticated: 401, forbidden: 403, not_found: 404, conflict: 409, invalid: 422, unavailable: 503, internal: 500 },
      errorBody: {
        type: 'api-error', code: 'code', message: 'message', correlation: 'correlation',
        runtime: { unauthenticated: 'unauthenticated', forbidden: 'forbidden', 'invalid-request': 'invalid', timeout: 'unavailable', unavailable: 'unavailable', internal: 'internal' },
      },
    };
    d.types.push(
      { id: 'error-code', name: 'Error code', kind: 'enum', values: ['unauthenticated', 'forbidden', 'not_found', 'conflict', 'invalid', 'unavailable', 'internal'] },
      { id: 'api-error', name: 'Api error', kind: 'struct', fields: [{ name: 'code', type: 'error-code' }, { name: 'message', type: 'string' }, { name: 'kind', type: 'string', optional: true }, { name: 'correlation', type: 'string' }] },
    );
    d.contracts.push({
      id: 'ct-cancel', name: 'Cancel an order', ref: 'CT-002', realisation: 'generated', implementedBy: 'svc', idempotent: true,
      inputs: [{ name: 'order', type: 'order-id' }], outputs: [],
      errors: [
        { name: 'not-found', condition: 'No order has the id.', type: 'api-error', kind: 'not_found' },
        { name: 'paid', condition: 'The order is paid.', kind: 'conflict' },
      ],
    });
    mutate(d);
  }, { generation });
}

test('error kinds and an error body and errors naming kinds validate with no errors and no readiness gaps', () => {
  const r = analyzeSpec(wired());
  assert.deepEqual(errors(r).map((/** @type {any} */ d) => `${d.code} ${d.message}`), []);
  assert.deepEqual(readinessGaps(/** @type {any} */ (r.model)), []);
  assert.deepEqual([...RUNTIME_FAILURES], ['unauthenticated', 'forbidden', 'invalid-request', 'timeout', 'unavailable', 'internal']);
});

test('the status of an error is its own or else the status of its kind or else the default kind or else the default status', () => {
  const r = analyzeSpec(wired((/** @type {any} */ d) => { delete d.system.generation.errorBody; d.system.generation.errorStatus = 422; }));
  const model = /** @type {any} */ (r.model);
  assert.equal(errorStatus(model, { name: 'a', status: 418 }), 418);
  assert.equal(errorStatus(model, { name: 'a', kind: 'conflict' }), 409);
  assert.equal(errorStatus(model, { name: 'a' }), 422);
  const k = analyzeSpec(wired((/** @type {any} */ d) => { d.system.generation.errorKind = 'invalid'; }));
  assert.equal(errorStatus(/** @type {any} */ (k.model), { name: 'a' }), 422);
  const none = analyzeSpec(spec());
  assert.equal(errorStatus(/** @type {any} */ (none.model), { name: 'a' }), undefined);
  assert.equal(errorStatus(/** @type {any} */ (none.model), { name: 'a', kind: 'constructor' }), undefined);
});

/** Each wire rule, a mutation that breaks it once, the code it reports and the path it reports at. */
const WIRE = [
  ['an error status outside 400 to 599', 'contract.error-status', 'contracts.2.errors.1.status', (/** @type {any} */ d) => { const e = entity(d.contracts, 'ct-cancel').errors[1]; delete e.kind; e.status = 302; d.system.generation.errorKind = 'conflict'; }],
  ['an error kind that is not declared', 'contract.error-kind-unknown', 'contracts.2.errors.1.kind', (/** @type {any} */ d) => { entity(d.contracts, 'ct-cancel').errors[1].kind = 'gone'; }],
  ['an error with both a status and a kind', 'contract.error-status-kind', 'contracts.2.errors.1', (/** @type {any} */ d) => { entity(d.contracts, 'ct-cancel').errors[1].status = 409; }],
  ['an error kind whose status is not one', 'generation.error-kinds', 'system.generation.errorKinds.internal', (/** @type {any} */ d) => { d.system.generation.errorKinds.internal = '500'; d.system.generation.errorBody.runtime.internal = 'unavailable'; d.types.find((/** @type {any} */ t) => t.id === 'error-code').values.pop(); }],
  ['a default status outside 400 to 599', 'generation.error-status', 'system.generation.errorStatus', (/** @type {any} */ d) => { delete d.system.generation.errorBody; d.system.generation.errorStatus = 200; }],
  ['a default kind that is not declared', 'generation.error-status', 'system.generation.errorKind', (/** @type {any} */ d) => { d.system.generation.errorKind = 'gone'; }],
  ['an error body type that is not a struct', 'generation.error-body-type', 'system.generation.errorBody.type', (/** @type {any} */ d) => { d.system.generation.errorBody.type = 'error-code'; }],
  ['an error body type with a required field it does not fill', 'generation.error-body-type', 'system.generation.errorBody.type', (/** @type {any} */ d) => { entity(d.types, 'api-error').fields[2].optional = false; }],
  ['an error body naming a field its type does not have', 'generation.error-body-field', 'system.generation.errorBody.message', (/** @type {any} */ d) => { d.system.generation.errorBody.message = 'text'; entity(d.types, 'api-error').fields[1].optional = true; }],
  ['an error body code that is not an enum', 'generation.error-body-field', 'system.generation.errorBody.code', (/** @type {any} */ d) => { entity(d.types, 'api-error').fields[0].type = 'string'; }],
  ['an error body message that is not a string', 'generation.error-body-field', 'system.generation.errorBody.message', (/** @type {any} */ d) => { entity(d.types, 'api-error').fields[1].type = 'u32'; }],
  ['an error body code whose enum lacks a kind', 'generation.error-body-code', 'system.generation.errorBody.code', (/** @type {any} */ d) => { entity(d.types, 'error-code').values.pop(); }],
  ['an error body that maps a runtime failure to no kind', 'generation.error-body-runtime', 'system.generation.errorBody.runtime.timeout', (/** @type {any} */ d) => { d.system.generation.errorBody.runtime.timeout = 'gateway-timeout'; }],
  ['an error body that leaves a runtime failure out', 'generation.error-body-runtime', 'system.generation.errorBody.runtime', (/** @type {any} */ d) => { delete d.system.generation.errorBody.runtime.internal; }],
  ['an error body that maps something that is no runtime failure', 'generation.error-body-runtime', 'system.generation.errorBody.runtime.teapot', (/** @type {any} */ d) => { d.system.generation.errorBody.runtime.teapot = 'internal'; }],
];

for (const [title, code, at, mutate] of WIRE) {
  test(`${title} is reported once as ${code} at ${at}`, () => {
    const r = analyzeSpec(wired(/** @type {any} */ (mutate)));
    const found = errors(r).filter((/** @type {any} */ d) => !d.code.startsWith('ready.'));
    assert.deepEqual(found.map((/** @type {any} */ d) => [d.code, d.path.join('.')]), [[code, at]], r.diagnostics.map((/** @type {any} */ d) => d.message).join('\n'));
  });
}

test('an error body without error kinds is reported as generation.error-body-kinds', () => {
  const r = analyzeSpec(wired((/** @type {any} */ d) => { delete d.system.generation.errorKinds; for (const e of entity(d.contracts, 'ct-cancel').errors) delete e.kind; }));
  assert.ok(codes(errors(r)).includes('generation.error-body-kinds'), r.diagnostics.map((/** @type {any} */ d) => d.message).join('\n'));
});

test('a served error with no status or kind or default is exactly one ready.error-status-missing when generation is set', () => {
  const unstated = (/** @type {any} */ d) => { delete d.system.generation.errorBody; delete entity(d.contracts, 'ct-cancel').errors[1].kind; };
  const r = analyzeSpec(wired(unstated));
  assert.deepEqual(codes(errors(r)), ['ready.error-status-missing'], r.diagnostics.map((/** @type {any} */ d) => d.message).join('\n'));
  const fixed = analyzeSpec(wired((/** @type {any} */ d) => { unstated(d); d.system.generation.errorStatus = 422; }));
  assert.deepEqual(codes(errors(fixed)), []);
  const off = analyzeSpec(wired(unstated, { generation: false }));
  assert.deepEqual(codes(readinessGaps(/** @type {any} */ (off.model))), ['ready.error-status-missing']);
});

test('under an error body a served error with no kind and no default kind is exactly one ready.error-kind-missing', () => {
  const r = analyzeSpec(wired((/** @type {any} */ d) => { const e = entity(d.contracts, 'ct-cancel').errors[1]; delete e.kind; e.status = 409; }));
  assert.deepEqual(codes(errors(r)), ['ready.error-kind-missing'], r.diagnostics.map((/** @type {any} */ d) => d.message).join('\n'));
  const fixed = analyzeSpec(wired((/** @type {any} */ d) => { delete entity(d.contracts, 'ct-cancel').errors[1].kind; d.system.generation.errorKind = 'conflict'; }));
  assert.deepEqual(codes(errors(fixed)), []);
});

test('an error of a contract no component serves needs no status', () => {
  const r = analyzeSpec(wired((/** @type {any} */ d) => { delete d.system.generation.errorBody; delete entity(d.contracts, 'ct-cancel').implementedBy; delete entity(d.contracts, 'ct-cancel').errors[1].kind; }));
  assert.deepEqual(codes(errors(r)), []);
});
