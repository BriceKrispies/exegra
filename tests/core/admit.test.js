// `exegra admit` (cli/commands.js, cli/admit.js): a change set is folded in only when the specification
// still holds what it held and the change's own claims hold. Each test works in a temporary specs/ directory.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { runCommand, exitCodeOf } from '../../cli/commands.js';

const SPEC = `{
  "exegra": "0.1",
  "system": { "id": "shop", "name": "Shop" },
  "components": [
    { "id": "web", "name": "Web", "category": "client", "purpose": "Front end." },
    { "id": "api", "name": "API", "category": "computational", "purpose": "Serves requests." },
    { "id": "db", "name": "DB", "category": "storage", "purpose": "Stores data." }
  ],
  "relationships": [
    { "id": "r-web-api", "kind": "calls", "from": "web", "to": "api" },
    { "id": "r-api-db", "kind": "writes", "from": "api", "to": "db" }
  ],
  "integrityRules": [
    { "id": "has-purpose", "severity": "warning", "statement": "Every component has a purpose.", "rule": "forall c : component, nonempty c.purpose" }
  ],
  "claims": [
    { "id": "c-no-direct", "kind": "structural", "statement": "Web never touches the db directly.",
      "evaluate": { "method": "no-relationship", "from": "web", "to": "db" } }
  ]
}
`;

/** @param {(ctx: {specs: string, file: string}) => Promise<void>} body */
async function withProject(body) {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-admit-'));
  try {
    const specs = path.join(dir, 'specs');
    fs.mkdirSync(path.join(specs, 'shop'), { recursive: true });
    const file = path.join(specs, 'shop', 'spec.jsonc');
    fs.writeFileSync(file, SPEC);
    await body({ specs, file });
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
}

/** @param {string} specs @param {any[]} ops @param {string[]} [extra] */
const admit = (specs, ops, extra = []) => runCommand('admit', ['--project', 'shop', '--ops', JSON.stringify(ops), ...extra], { specs });

const DIRECT = { type: 'CreateRelationship', id: 'r-web-db', kind: 'calls', from: 'web', to: 'db' };
const REACHES = { id: 'c-web-reaches-db', kind: 'structural', statement: 'Web reaches the db.', evaluate: { method: 'reachable', from: 'web', to: 'db' } };

// A change that worsens a claim is rejected, naming the claim with its status before and after.
// @evidence admit-never-writes-a-rejected-change
test('a change that worsens a claim is rejected naming the claim with both statuses', () =>
  withProject(async ({ specs }) => {
    const r = await admit(specs, [DIRECT]);
    assert.equal(r.ok, false);
    assert.equal(r.error?.code, 'admit.rejected');
    assert.equal(exitCodeOf(r), 1);
    assert.equal(r.result.verdict, 'rejected');
    const reason = r.result.reasons.find((/** @type {any} */ x) => x.code === 'admit.claim-regressed');
    assert.deepEqual([reason.id, reason.before, reason.after], ['c-no-direct', 'verified', 'violated']);
    assert.deepEqual(r.result.diff.claims.changed.map((/** @type {any} */ c) => [c.id, c.before, c.after]), [['c-no-direct', 'verified', 'violated']]);
    assert.match(r.result.diff.claims.changed[0].explanation, /r-web-db/);
  }));

// A change that adds an integrity violation is rejected with the rule and the counterexample.
// @evidence admit-never-writes-a-rejected-change
test('a change that adds an integrity violation is rejected with the rule and its counterexample', () =>
  withProject(async ({ specs }) => {
    const r = await admit(specs, [{ type: 'CreateEntity', kind: 'component', data: { id: 'queue', name: 'Queue', category: 'storage' } }]);
    assert.equal(r.ok, false);
    const reasons = r.result.reasons.filter((/** @type {any} */ x) => x.code === 'admit.new-violation');
    assert.equal(reasons.length, 1);
    assert.equal(reasons[0].id, 'has-purpose');
    assert.equal(reasons[0].counterexample[0].entity, 'queue');
    assert.equal(r.result.diff.integrity.new.length, 1);
  }));

// A new claim that is only inconclusive is a reason to reject.
// @evidence admit-never-writes-a-rejected-change
test('a new claim that is not verified or proved is a reason to reject', () =>
  withProject(async ({ specs }) => {
    const weak = { id: 'c-nobody', kind: 'structural', statement: 'Nothing tagged nope reaches the db.', evaluate: { method: 'no-relationship', from: { tag: 'nope' }, to: 'db' } };
    const r = await admit(specs, [{ type: 'AddClaim', data: weak }]);
    assert.equal(r.ok, false);
    assert.deepEqual(r.result.reasons.map((/** @type {any} */ x) => [x.code, x.id]), [['admit.new-claim-weak', 'c-nobody']]);
    assert.equal(r.result.diff.claims.added[0].id, 'c-nobody');
    assert.notEqual(r.result.diff.claims.added[0].status, 'verified');
  }));

// A refused transaction is a rejected verdict carrying the transaction code and message, and writes nothing.
// @evidence admit-never-writes-a-rejected-change
test('a refused transaction is rejected with the transaction code and message', () =>
  withProject(async ({ specs, file }) => {
    const r = await admit(specs, [{ type: 'DeleteEntity', id: 'no-such-entity' }], ['--write']);
    assert.equal(r.ok, false);
    assert.equal(r.result.verdict, 'rejected');
    const [reason] = r.result.reasons;
    assert.equal(reason.code, 'admit.transaction-refused');
    assert.equal(reason.transactionCode, r.result.transaction.code);
    assert.ok(reason.message.length > 0);
    assert.equal(r.result.transaction.accepted, false);
    assert.equal(fs.readFileSync(file, 'utf8'), SPEC);
  }));

// An accepted change with several entities and a claim that verifies is admitted and lists the claim as verified.
// @evidence admit-never-writes-a-rejected-change
test('a substantial accepted change is admitted and lists the new claim as verified', () =>
  withProject(async ({ specs, file }) => {
    const ops = [
      { type: 'CreateEntity', kind: 'component', data: { id: 'cache', name: 'Cache', category: 'storage', purpose: 'Keeps hot data.' } },
      { type: 'CreateEntity', kind: 'component', data: { id: 'queue', name: 'Queue', category: 'storage', purpose: 'Buffers writes.' } },
      { type: 'CreateRelationship', id: 'r-api-cache', kind: 'reads', from: 'api', to: 'cache' },
      { type: 'CreateRelationship', id: 'r-api-queue', kind: 'writes', from: 'api', to: 'queue' },
      { type: 'AddClaim', data: { id: 'c-web-reaches-queue', kind: 'structural', statement: 'Web reaches the queue.', evaluate: { method: 'reachable', from: 'web', to: 'queue' } } },
    ];
    const r = await admit(specs, ops);
    assert.equal(r.ok, true, JSON.stringify(r));
    assert.equal(exitCodeOf(r), 0);
    assert.equal(r.result.verdict, 'admitted');
    assert.deepEqual(r.result.reasons, []);
    assert.deepEqual(r.result.diff.claims.added.map((/** @type {any} */ c) => [c.id, c.status]), [['c-web-reaches-queue', 'verified']]);
    assert.equal(r.result.counts.addedClaims, 1);
    assert.deepEqual(r.result.written, [], 'without --write nothing is written');
    assert.equal(fs.readFileSync(file, 'utf8'), SPEC);
  }));

// With --write a rejected change leaves the file byte-identical and an admitted one writes it.
// @evidence admit-never-writes-a-rejected-change
test('--write leaves the spec byte-identical on a rejected change and writes an admitted one', () =>
  withProject(async ({ specs, file }) => {
    const rejected = await admit(specs, [DIRECT], ['--write']);
    assert.equal(rejected.ok, false);
    assert.deepEqual(rejected.result.written, []);
    assert.equal(fs.readFileSync(file, 'utf8'), SPEC);

    const admitted = await admit(specs, [{ type: 'AddClaim', data: REACHES }], ['--write', '--label', 'web reaches db']);
    assert.equal(admitted.ok, true, JSON.stringify(admitted));
    assert.deepEqual(admitted.result.written, ['spec']);
    assert.notEqual(fs.readFileSync(file, 'utf8'), SPEC);
    const claims = await runCommand('claims', ['--project', 'shop'], { specs });
    assert.equal(claims.result.find((/** @type {any} */ c) => c.claimId === 'c-web-reaches-db').status, 'verified');
  }));

// Two runs print identical output, with reasons in id order.
// @evidence admit-never-writes-a-rejected-change
test('admit output is identical across two runs', () =>
  withProject(async ({ specs }) => {
    const ops = [DIRECT, { type: 'CreateEntity', kind: 'component', data: { id: 'queue', name: 'Queue', category: 'storage' } }, { type: 'AddClaim', data: REACHES }];
    const a = await admit(specs, ops);
    const b = await admit(specs, ops);
    assert.equal(JSON.stringify(a), JSON.stringify(b));
    const ids = a.result.reasons.map((/** @type {any} */ x) => `${x.code}/${x.id}`);
    assert.deepEqual(ids, [...ids].sort());
  }));

// --- privilege changes, guarantee weakening, acknowledgement, pending realisation (WG-5273, WG-5275) ---------

const ACCESS_SPEC = `{
  "exegra": "0.1",
  "system": { "id": "shop", "name": "Shop" },
  "components": [
    { "id": "api", "name": "API", "category": "computational", "purpose": "Serves requests." },
    { "id": "edge", "name": "Edge", "category": "storage", "purpose": "Caches pages." },
    { "id": "db", "name": "DB", "category": "storage", "purpose": "Stores data." }
  ],
  "relationships": [
    { "id": "r-edge-db", "kind": "reads", "from": "edge", "to": "db" }
  ],
  "vocabulary": {
    "properties": [{ "entity": "claim", "name": "milestone", "type": "number", "label": "Milestone" }],
    "verificationMethods": { "property": { "label": "Property test", "description": "Checked by a property-based test outside Exegra." } }
  },
  "capabilities": [
    { "id": "content-edit", "name": "Edit content", "core": true },
    { "id": "billing-read", "name": "Read billing", "core": true },
    { "id": "model-optin", "name": "Opt in to an external model provider", "core": true }
  ],
  "roles": [
    { "id": "owner", "name": "Owner", "level": "tenant", "holders": ["person"], "capabilities": ["content-edit", "billing-read"] },
    { "id": "support", "name": "Support", "level": "platform", "holders": ["person"], "capabilities": ["content-edit", "billing-read"] },
    { "id": "operator", "name": "Operator", "level": "platform", "holders": ["service"], "capabilities": ["model-optin"] }
  ],
  "grants": [
    { "id": "support-grant", "issuer": "owner", "grantee": "support", "capabilities": ["content-edit"], "maxDuration": "72 h" }
  ],
  "records": [
    { "id": "page", "name": "Page", "owner": "db", "fields": [{ "name": "body", "type": "text" }] }
  ],
  "copies": [
    { "id": "copy-edge-page", "name": "Edge page", "of": ["page"], "heldBy": "edge", "scope": "shared",
      "freshness": { "bound": 5, "unit": "second" }, "erasure": { "bound": 5, "unit": "second" } }
  ],
  "integrityRules": [
    { "id": "pages-have-owner", "severity": "warning", "statement": "Every record has an owner.", "rule": "forall r : record, nonempty r.owner" }
  ]
}
`;

/** @param {(ctx: {specs: string, file: string}) => Promise<void>} body */
async function withAccessProject(body) {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-admit-'));
  try {
    const specs = path.join(dir, 'specs');
    fs.mkdirSync(path.join(specs, 'shop'), { recursive: true });
    const file = path.join(specs, 'shop', 'spec.jsonc');
    fs.writeFileSync(file, ACCESS_SPEC);
    await body({ specs, file });
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
}

/** @param {any} r @param {string} code */
const reasonsOf = (r, code) => (r.result.reasons ?? []).filter((/** @type {any} */ x) => x.code === code);

// The owner role gains a capability: a privilege-change reason, admitted with --accept admit.privilege-change and listed under acknowledged.
// @evidence admit-privilege-and-guarantee-changes-need-acknowledgement
test('a role that gains a capability is a privilege-change reason until it is accepted', () =>
  withAccessProject(async ({ specs }) => {
    const ops = [{ type: 'SetProperty', id: 'owner', property: 'capabilities', value: ['content-edit', 'billing-read', 'model-optin'] }];
    const r = await admit(specs, ops);
    assert.equal(r.ok, false, JSON.stringify(r));
    assert.equal(r.error?.code, 'admit.rejected');
    const [reason] = reasonsOf(r, 'admit.privilege-change');
    assert.equal(r.result.reasons.length, 1);
    assert.equal(reason.acknowledgeable, true);
    assert.deepEqual([reason.entity, reason.kind, reason.level, reason.capability], ['owner', 'role', 'tenant', 'model-optin']);
    assert.deepEqual(reason.holders, ['person']);

    const ok = await admit(specs, ops, ['--accept', 'admit.privilege-change']);
    assert.equal(ok.ok, true, JSON.stringify(ok));
    assert.equal(ok.result.verdict, 'admitted');
    assert.deepEqual(ok.result.reasons, []);
    assert.deepEqual(ok.result.acknowledged.map((/** @type {any} */ x) => [x.code, x.capability]), [['admit.privilege-change', 'model-optin']]);
  }));

// A removed capability is listed under diff.privilege.removed and does not block.
// @evidence admit-privilege-and-guarantee-changes-need-acknowledgement
test('removing a capability from a role is reported but is not a reason', () =>
  withAccessProject(async ({ specs }) => {
    const r = await admit(specs, [{ type: 'SetProperty', id: 'owner', property: 'capabilities', value: ['content-edit'] }]);
    assert.equal(r.ok, true, JSON.stringify(r));
    assert.deepEqual(r.result.diff.privilege.removed.map((/** @type {any} */ x) => [x.entity, x.capability]), [['owner', 'billing-read']]);
    assert.deepEqual(r.result.reasons, []);
  }));

// A grant with no maxDuration is a privilege-change reason next to its capabilities.
// @evidence admit-privilege-and-guarantee-changes-need-acknowledgement
test('a new grant without maxDuration is a privilege-change reason', () =>
  withAccessProject(async ({ specs }) => {
    const grant = { id: 'open-grant', issuer: 'owner', grantee: 'support', capabilities: ['billing-read'] };
    const r = await admit(specs, [{ type: 'CreateEntity', kind: 'grant', data: grant }]);
    assert.equal(r.ok, false, JSON.stringify(r));
    const changes = reasonsOf(r, 'admit.privilege-change').map((/** @type {any} */ x) => [x.id, x.change]).sort();
    assert.deepEqual(changes, [['open-grant', 'capability-added'], ['open-grant', 'no-max-duration']]);

    const ok = await admit(specs, [{ type: 'CreateEntity', kind: 'grant', data: grant }], ['--accept', 'admit.privilege-change']);
    assert.equal(ok.ok, true, JSON.stringify(ok));
    assert.equal(ok.result.acknowledged.length, 2);
  }));

// A 72 hour copy class beside a 5 second class of the same record is flagged for freshness and erasure; a tighter class is not.
// @evidence admit-privilege-and-guarantee-changes-need-acknowledgement
test('an edge copy class looser than an existing class of the same record is a guarantee-weakened reason', () =>
  withAccessProject(async ({ specs }) => {
    const slow = { id: 'copy-edge-slow', name: 'Slow edge', of: ['page'], heldBy: 'edge', scope: 'shared', freshness: { bound: 72, unit: 'hour' }, erasure: { bound: 72, unit: 'hour' } };
    const r = await admit(specs, [{ type: 'CreateEntity', kind: 'copy', data: slow }]);
    assert.equal(r.ok, false, JSON.stringify(r));
    const found = reasonsOf(r, 'admit.guarantee-weakened').map((/** @type {any} */ x) => [x.id, x.change, x.before, x.after]).sort();
    assert.deepEqual(found, [
      ['copy-edge-slow', 'copy-erasure-looser', '5 second', '72 hour'],
      ['copy-edge-slow', 'copy-freshness-looser', '5 second', '72 hour'],
    ]);
    const tighter = { ...slow, id: 'copy-edge-fast', freshness: { bound: 1, unit: 'second' }, erasure: { bound: 1, unit: 'second' } };
    const fine = await admit(specs, [{ type: 'CreateEntity', kind: 'copy', data: tighter }]);
    assert.equal(fine.ok, true, JSON.stringify(fine));
  }));

// A changed integrity rule is a guarantee-weakened reason with its text before and after.
// @evidence admit-privilege-and-guarantee-changes-need-acknowledgement
test('a changed integrity rule is shown before and after and can be accepted', () =>
  withAccessProject(async ({ specs }) => {
    const ops = [{ type: 'SetProperty', id: 'pages-have-owner', property: 'rule', value: 'forall r : record, true' }, { type: 'SetProperty', id: 'pages-have-owner', property: 'statement', value: 'Every record is fine.' }];
    const r = await admit(specs, ops);
    assert.equal(r.ok, false, JSON.stringify(r));
    const [reason] = reasonsOf(r, 'admit.guarantee-weakened');
    assert.equal(reason.change, 'integrity-rule-changed');
    assert.match(reason.before, /nonempty r\.owner/);
    assert.match(reason.after, /forall r : record, true/);
    const ok = await admit(specs, ops, ['--accept', 'admit.guarantee-weakened']);
    assert.equal(ok.ok, true, JSON.stringify(ok));
    assert.equal(ok.result.acknowledged.length, 1);
  }));

// A requirement of an external method with a milestone is admitted and listed under pendingRealisation.
// @evidence admit-requirement-claims-pend-on-realisation
test('a new requirement claim with a milestone is admitted as pending realisation', () =>
  withAccessProject(async ({ specs }) => {
    const claim = { id: 'req-page-erasure', kind: 'requirement', statement: 'A page SHALL be erased from every edge within a minute of deletion.', milestone: 2, evaluate: { method: 'property' } };
    const r = await admit(specs, [{ type: 'AddClaim', data: claim }]);
    assert.equal(r.ok, true, JSON.stringify(r));
    assert.deepEqual(r.result.reasons, []);
    assert.deepEqual(r.result.pendingRealisation.map((/** @type {any} */ x) => [x.id, x.milestone, x.status]), [['req-page-erasure', 2, 'not-evaluated']]);
  }));

// A requirement without a milestone is rejected as admit.requirement-without-milestone.
// @evidence admit-requirement-claims-pend-on-realisation
test('a new requirement claim without a milestone is rejected', () =>
  withAccessProject(async ({ specs }) => {
    const claim = { id: 'req-page-erasure', kind: 'requirement', statement: 'A page SHALL be erased from every edge within a minute of deletion.', evaluate: { method: 'property' } };
    const r = await admit(specs, [{ type: 'AddClaim', data: claim }]);
    assert.equal(r.ok, false);
    assert.deepEqual(r.result.reasons.map((/** @type {any} */ x) => [x.code, x.id]), [['admit.requirement-without-milestone', 'req-page-erasure']]);
    assert.deepEqual(r.result.pendingRealisation, []);
  }));

// Accepting admit.new-claim-weak, admit.claim-regressed or admit.new-error fails with admit.not-acknowledgeable.
// @evidence admit-privilege-and-guarantee-changes-need-acknowledgement
test('a reason that is not acknowledgeable cannot be accepted', () =>
  withProject(async ({ specs }) => {
    const weak = { id: 'c-nobody', kind: 'structural', statement: 'Nothing tagged nope reaches the db.', evaluate: { method: 'no-relationship', from: { tag: 'nope' }, to: 'db' } };
    const r = await admit(specs, [{ type: 'AddClaim', data: weak }], ['--accept', 'admit.new-claim-weak']);
    assert.equal(r.ok, false);
    assert.equal(r.error?.code, 'admit.not-acknowledgeable');
    assert.equal(exitCodeOf(r), 1);
    const again = await admit(specs, [DIRECT], ['--accept', 'admit.claim-regressed,admit.new-error']);
    assert.equal(again.error?.code, 'admit.not-acknowledgeable');
  }));

// A structural claim that is not verified is still admit.new-claim-weak, even with a milestone.
// @evidence admit-requirement-claims-pend-on-realisation
test('a new claim a model method decides stays weak when it is not verified', () =>
  withAccessProject(async ({ specs }) => {
    const claim = { id: 'c-nobody', kind: 'structural', statement: 'Nothing tagged nope reaches the db.', milestone: 2, evaluate: { method: 'no-relationship', from: { tag: 'nope' }, to: 'db' } };
    const r = await admit(specs, [{ type: 'AddClaim', data: claim }]);
    assert.equal(r.ok, false);
    assert.deepEqual(r.result.reasons.map((/** @type {any} */ x) => [x.code, x.id]), [['admit.new-claim-weak', 'c-nobody']]);
    assert.deepEqual(r.result.pendingRealisation, []);
  }));
