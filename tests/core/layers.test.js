// A layered specification (src/core/layers.js, WG-4989): the platform specification plus product
// files that import its entities by id. Fixtures in tests/fixtures/layers: platform.jsonc, the
// accepted product products/badges.jsonc, and one refused product per rule in refused/.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { analyzeLayers, PRODUCT_SECTIONS, PRODUCT_SECTION_NAMES } from '../../src/core/layers.js';
import { TYPED_SECTIONS } from '../../src/core/layer-values.js';
import { parseSpec } from '../../src/core/parse.js';
import { Project } from '../../src/core/project.js';
import { runCommand } from '../../cli/commands.js';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const FIXTURES = path.join(HERE, '..', 'fixtures', 'layers');
const PLATFORM = path.join(FIXTURES, 'platform.jsonc');
const BADGES = path.join(FIXTURES, 'products', 'badges.jsonc');
const read = (/** @type {string} */ f) => fs.readFileSync(f, 'utf8');
const refused = (/** @type {string} */ name) => path.join(FIXTURES, 'refused', `${name}.jsonc`);

/** A product layer as the workspace hands it over, with the import path found to match. @param {string} file */
const layer = (file) => ({ file: path.basename(file), text: read(file), platform: { declared: '../platform.jsonc', matches: true, expected: '../platform.jsonc' } });

/** The entities of a model as plain values, for comparison. @param {any} model */
const entities = (model) => [...model.entities.values()].map((e) => JSON.parse(JSON.stringify({ id: e.id, kind: e.kind, owner: e.owner, path: e.path, loc: e.loc, data: e.data })));

/** The errors of a layered analysis of the platform and the given product files. @param {string[]} files */
function errors(files) {
  return analyzeLayers(read(PLATFORM), files.map(layer)).diagnostics.filter((d) => d.severity === 'error');
}

/**
 * A specs directory with project "platform" (the platform alone) and project "layered" (the platform
 * and the given product files, listed in project.jsonc), both linking the fixtures.
 * @param {string[]} products
 */
function workspace(products) {
  const specs = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-layers-'));
  const link = (/** @type {string} */ name, /** @type {Record<string, any>} */ extra) => {
    const dir = path.join(specs, name);
    fs.mkdirSync(dir);
    const rel = (/** @type {string} */ f) => path.relative(dir, f).split(path.sep).join('/');
    fs.writeFileSync(path.join(dir, 'project.jsonc'), JSON.stringify({ spec: rel(PLATFORM), ...(extra.products ? { products: extra.products.map(rel) } : {}) }));
  };
  link('platform', {});
  link('layered', { products });
  return { specs, cleanup: () => fs.rmSync(specs, { recursive: true, force: true }) };
}

test('a product file importing the platform passes validation', () => {
  const a = analyzeLayers(read(PLATFORM), [layer(BADGES)]);
  assert.equal(a.errorCount, 0, JSON.stringify(a.diagnostics.filter((d) => d.severity === 'error')));
  assert.deepEqual(a.layers, [{ file: 'badges.jsonc', product: 'badges', entities: ['badges__tier', 'badges__badge', 'badges__curator', 'badges__award', 'badges__key-names-the-tenant', 'badges__grant'] }]);
  const badge = a.model?.entities.get('badges__badge');
  assert.equal(badge?.loc.file, 'badges.jsonc');
  assert.equal(read(BADGES).split('\n')[badge.loc.line - 1].includes('{'), true, 'the location is the line of the declaration in the product file');
  assert.deepEqual(badge.path, ['records', 0], 'the path is the path in the product file');
  assert.equal(a.model?.entities.get('runtime')?.loc.file, undefined, 'a platform entity has no file');
});

test('the CLI validates a project that lists product files and reports the platform hash as semanticHash', async () => {
  const ws = workspace([path.join(FIXTURES, 'products')]);
  try {
    const alone = await runCommand('validate', [], { specs: ws.specs, project: 'platform' });
    const layered = await runCommand('validate', [], { specs: ws.specs, project: 'layered' });
    assert.equal(alone.ok, true);
    assert.equal(layered.ok, true, JSON.stringify(layered.diagnostics));
    assert.equal(layered.semanticHash, alone.semanticHash, 'adding a product file leaves the platform semantic hash unchanged');
    assert.notEqual(layered.result.layeredHash, alone.semanticHash);
    assert.equal(layered.result.products[0].product, 'badges');
    const shown = await runCommand('show', ['badges__badge'], { specs: ws.specs, project: 'layered' });
    assert.match(shown.result.source.file, /badges\.jsonc$/);
  } finally {
    ws.cleanup();
  }
});

test('adding a product file leaves the platform semantic hash unchanged', () => {
  const alone = parseSpec(read(PLATFORM)).model;
  const a = analyzeLayers(read(PLATFORM), [layer(BADGES)]);
  assert.equal(a.baseHash, alone?.semanticHash);
  assert.equal(new Project({ specText: read(PLATFORM) }).semanticHash, new Project({ specText: read(PLATFORM), layers: [layer(BADGES)] }).semanticHash);
});

test('the parsed platform specification is unchanged by layering', () => {
  const alone = parseSpec(read(PLATFORM)).model;
  const a = analyzeLayers(read(PLATFORM), [layer(BADGES)]);
  assert.deepEqual(entities(a.baseModel), entities(alone));
  // In the combined model too, every platform entity keeps its data, path and location.
  const combined = entities(a.model).filter((e) => alone?.entities.has(e.id));
  assert.deepEqual(combined, entities(alone));
});

test('an imported id the platform does not declare is refused with layer.import-unknown', () => {
  const [d, ...rest] = errors([refused('import-unknown')]);
  assert.equal(rest.length, 0);
  assert.equal(d.code, 'layer.import-unknown');
  assert.match(d.message, /"tenant-identifier"/);
  assert.match(d.message, /Correct the id .* or remove it from product\.imports\.entities/);
  assert.equal(d.loc?.file, 'import-unknown.jsonc');
});

test('a product that redefines a platform entity is refused with layer.redefines-entity', () => {
  const found = errors([refused('redefines-entity')]);
  assert.deepEqual(found.map((d) => d.code).sort(), ['layer.namespace-missing', 'layer.redefines-entity']);
  const redefines = found.find((d) => d.code === 'layer.redefines-entity');
  assert.match(redefines?.message ?? '', /"tenant-id".*already declares type "tenant-id"/);
  assert.match(redefines?.message ?? '', /Give the product's entity an id of its own/);
});

test('two product files that declare the same id are refused with layer.redefines-entity', () => {
  const a = analyzeLayers(read(PLATFORM), [layer(BADGES), { ...layer(BADGES), file: 'copy.jsonc' }]);
  const codes = new Set(a.diagnostics.filter((d) => d.severity === 'error').map((d) => d.code));
  assert.ok(codes.has('layer.redefines-entity'));
  assert.match(a.diagnostics.find((d) => d.code === 'layer.redefines-entity')?.message ?? '', /product file badges\.jsonc already declares/);
});

test('a section a product may not declare is refused with layer.kind-not-allowed', () => {
  const found = errors([refused('kind-not-allowed')]);
  assert.deepEqual(found.map((d) => d.code), ['layer.kind-not-allowed']);
  assert.match(found[0].message, /declares "components"/);
  for (const section of Object.keys(PRODUCT_SECTIONS)) assert.ok(found[0].message.includes(section), `the message lists ${section}`);
  for (const key of ['vocabulary', 'functions', 'plans', 'system']) {
    const text = JSON.stringify({ product: { id: 'p', name: 'P', imports: { spec: '../platform.jsonc', entities: [] } }, [key]: [] });
    const a = analyzeLayers(read(PLATFORM), [{ file: 'p.jsonc', text }]);
    assert.ok(a.diagnostics.some((d) => d.code === 'layer.kind-not-allowed'), `${key} is refused`);
  }
});

test('a platform entity used without being imported is refused with layer.import-missing', () => {
  const found = errors([refused('import-missing')]);
  assert.deepEqual(found.map((d) => d.code), ['layer.import-missing', 'layer.import-missing']);
  assert.match(found[0].message, /component "product-module".*Add "product-module" to product\.imports\.entities/);
  assert.match(found[1].message, /type "tenant-id".*Add "tenant-id" to product\.imports\.entities/);
});

test('a reference no layer declares is refused with layer.reference-unknown', () => {
  const found = errors([refused('reference-unknown')]);
  assert.deepEqual(found.map((d) => d.code), ['layer.reference-unknown']);
  assert.match(found[0].message, /refers to "badge-service", which neither the platform specification nor this product file declares/);
});

test('a product file without a header is refused with layer.header-missing', () => {
  const found = errors([refused('header-missing')]);
  assert.deepEqual(found.map((d) => d.code), ['layer.header-missing']);
  assert.match(found[0].message, /add it/);
});

test('a product that imports another platform file is refused with layer.import-mismatch', async () => {
  const ws = workspace([refused('import-mismatch')]);
  try {
    const out = await runCommand('validate', [], { specs: ws.specs, project: 'layered' });
    assert.equal(out.ok, false);
    const d = out.result.diagnostics.find((/** @type {any} */ x) => x.code === 'layer.import-mismatch');
    assert.ok(d, JSON.stringify(out.result.diagnostics));
    assert.match(d.message, /"\.\.\/other-platform\.jsonc".*Set "product\.imports\.spec" to "\.\.\/platform\.jsonc"/);
    assert.match(d.file, /import-mismatch\.jsonc$/);
  } finally {
    ws.cleanup();
  }
});

test('a reference into another product file is refused with layer.cross-product-reference', () => {
  const found = errors([BADGES, refused('cross-product')]);
  assert.deepEqual(found.map((d) => d.code), ['layer.cross-product-reference']);
  assert.match(found[0].message, /"badges__award".*product file badges\.jsonc declares/);
});

test('transactions on a layered project edit the platform text and refuse product entities', () => {
  const project = new Project({ specText: read(PLATFORM), layers: [layer(BADGES)] });
  const before = project.semanticHash;
  const ok = project.apply({ type: 'SetProperty', id: 'runtime', property: 'name', value: 'Tenant runtime' });
  assert.equal(ok.ok, true, ok.message);
  assert.notEqual(project.semanticHash, before);
  assert.match(project.specText, /"Tenant runtime"/);
  assert.ok(project.model?.entities.has('badges__badge'), 'the product stays layered on the edited platform');
  const refusedEdit = project.apply({ type: 'SetProperty', id: 'badges__badge', property: 'name', value: 'Award' });
  assert.equal(refusedEdit.ok, false);
  assert.equal(refusedEdit.code, 'layer.product-entity');
  assert.match(refusedEdit.message ?? '', /edit that file instead/);
});

// ---- Product files may not claim platform powers (WG-5022) -------------------------------------

/** One refused product per rule, the rule code and what its message must say. [fixture, code, message pattern] */
const POWER_REFUSALS = [
  ['role-platform-level', 'layer.platform-power', /has level "platform".*set level to "tenant"/],
  ['role-anonymous-holder', 'layer.platform-power', /lets "anonymous" hold it/],
  ['role-service-holder', 'layer.platform-power', /lets "service" hold it/],
  ['role-external-holder', 'layer.platform-power', /lets "external" hold it/],
  ['contract-public-anonymous', 'layer.platform-power', /is public with the anonymous scheme/],
  ['contract-platform-implemented', 'layer.platform-power', /implemented by the platform component "runtime".*remove implementedBy/],
  ['contract-realisation', 'layer.platform-power', /declares realisation "hand".*only the platform puts code/],
  ['behavior-implementation-level', 'layer.platform-power', /has level "implementation"/],
  ['event-domain', 'layer.platform-power', /is a domain event/],
  ['entity-id-invalid', 'layer.entity-id-invalid', /"BadgesTier".*id pattern/],
  ['entity-id-missing', 'layer.entity-id-missing', /has no "id"/],
  ['capability-core', 'layer.platform-power', /is a core capability.*Remove "core"/],
  ['setting-platform-level', 'layer.platform-power', /is set at, or locked by, the platform level.*tenant, team and person/],
];

test('a product that claims a platform power or has a malformed entity id is refused with the rule for it', () => {
  for (const [name, code, message] of POWER_REFUSALS) {
    const found = errors([refused(name)]);
    const d = found.find((x) => x.code === code);
    assert.ok(d, `${name}: ${JSON.stringify(found.map((x) => x.code))}`);
    assert.match(d.message, message, name);
    assert.equal(d.loc?.file, `${name}.jsonc`, name);
  }
});

test('a product role at tenant level held by people and teams and agents is accepted', () => {
  const text = JSON.stringify({ product: { id: 'p', name: 'P', imports: { spec: '../platform.jsonc', entities: [] } }, roles: [{ id: 'p-role', name: 'R', level: 'tenant', holders: ['person', 'team', 'agent'], capabilities: [] }], contracts: [{ id: 'p-facade', name: 'F', exposure: 'public', auth: { scheme: 'session' }, realisation: 'facade' }] });
  const a = analyzeLayers(read(PLATFORM), [{ file: 'p.jsonc', text, platform: { declared: '../platform.jsonc', matches: true, expected: '../platform.jsonc' } }]);
  assert.deepEqual(a.diagnostics.filter((d) => d.code === 'layer.platform-power'), []);
});

test('two product files with one product id are refused with layer.product-id-duplicate', () => {
  const found = errors([BADGES, refused('duplicate-product-id')]);
  const d = found.find((x) => x.code === 'layer.product-id-duplicate');
  assert.ok(d, JSON.stringify(found.map((x) => x.code)));
  assert.match(d.message, /duplicate-product-id\.jsonc has product id "badges", which product file badges\.jsonc already has/);
  assert.equal(d.loc?.file, 'duplicate-product-id.jsonc');
});

test('a reference through a reference key requires an import', () => {
  const found = errors([refused('import-missing-reference')]).filter((d) => d.code === 'layer.import-missing');
  assert.equal(found.length, 3, JSON.stringify(found.map((d) => d.message)));
  assert.ok(found.some((d) => /"install-bundle" \(at contract\)/.test(d.message)));
  assert.ok(found.some((d) => /"product-module" \(at owner\)/.test(d.message)));
  assert.ok(found.some((d) => /"runtime" \(at subject\)/.test(d.message)));
});

test('a platform entity that references a product entity is refused with layer.platform-references-product', () => {
  const platform = read(PLATFORM);
  const byReference = platform.replace('"to": "runtime"', '"to": "badges__tier"');
  assert.notEqual(byReference, platform);
  const a = analyzeLayers(byReference, [layer(BADGES)]);
  const d = a.diagnostics.find((x) => x.code === 'layer.platform-references-product');
  assert.ok(d, JSON.stringify(a.diagnostics.map((x) => x.code)));
  assert.match(d.message, /"product-module-calls-runtime" refers to "badges__tier" \(at to\)/);
  assert.match(d.message, /product file badges\.jsonc declares/);
  assert.equal(d.loc?.file, undefined, 'the location is in the platform specification');

  const byType = platform.replace('"repr": "uuid"', '"repr": "badges__tier"');
  assert.notEqual(byType, platform);
  const b = analyzeLayers(byType, [layer(BADGES)]);
  assert.ok(b.diagnostics.some((x) => x.code === 'layer.platform-references-product' && /"tenant-id"/.test(x.message) && /"badges__tier"/.test(x.message)), JSON.stringify(b.diagnostics.map((x) => x.code)));

  const clean = analyzeLayers(platform, [layer(BADGES)]);
  assert.equal(clean.diagnostics.some((x) => x.code === 'layer.platform-references-product'), false);
});

test('reload picks up a changed product file', () => {
  const project = new Project({ specText: read(PLATFORM), layers: [layer(BADGES)] });
  const platformHash = project.semanticHash;
  const layeredBefore = project.layeredHash;
  const revision = project.revision;
  assert.equal(project.model?.entities.has('badges__extra'), false);

  const same = project.reload({ layers: [layer(BADGES)] });
  assert.equal(same.ok, true);
  assert.equal(project.revision, revision, 'unchanged product files are not a reload');

  const changed = { ...layer(BADGES), text: read(BADGES).replace('"types": [', '"types": [\n    { "id": "badges__extra", "name": "Extra", "kind": "enum", "values": ["x"] },') };
  const r = project.reload({ layers: [changed] });
  assert.equal(r.ok, true, r.message);
  assert.equal(project.revision, revision + 1);
  assert.ok(project.model?.entities.has('badges__extra'), 'the layered model is built from the changed product file');
  assert.ok(r.affected.includes('badges__extra'));
  assert.equal(project.semanticHash, platformHash, 'the platform hash stays the platform\'s');
  assert.notEqual(project.layeredHash, layeredBefore);
  assert.equal(project.layers[0].text, changed.text);

  const dropped = project.reload({ layers: [] });
  assert.equal(dropped.ok, true);
  assert.equal(project.model?.entities.has('badges__badge'), false, 'a product file removed from the project leaves the model');
});


// ---- Typed sections: values conform to platform types (WG-5046) --------------------------------

const TYPED = path.join(FIXTURES, 'typed');
const complete = ['badge-milestones.jsonc', 'promotions.jsonc'].map((f) => path.join(TYPED, f));

test('the complete products declare everything they name and pass validation with the platform hash unchanged', async () => {
  const ws = workspace(complete);
  try {
    const alone = await runCommand('validate', [], { specs: ws.specs, project: 'platform' });
    const layered = await runCommand('validate', [], { specs: ws.specs, project: 'layered' });
    assert.equal(layered.ok, true, JSON.stringify(layered.result.diagnostics.filter((/** @type {any} */ d) => d.severity === 'error')));
    assert.equal(layered.semanticHash, alone.semanticHash, 'typed sections are not part of the platform hash');
    assert.deepEqual(layered.result.products.map((/** @type {any} */ p) => p.product), ['badge-milestones', 'promotions']);
  } finally {
    ws.cleanup();
  }
  const a = analyzeLayers(read(PLATFORM), complete.map(layer));
  assert.equal(a.errorCount, 0, JSON.stringify(a.diagnostics.filter((d) => d.severity === 'error')));
  const declared = a.layers.flatMap((l) => l.entities);
  for (const id of ['badge_milestones__award', 'badge_milestones__points', 'badge_milestones__silver_notice', 'badge_milestones__silver_mail', 'badge_milestones__silver_follow_up', 'badge_milestones__silver_on_points', 'badge_milestones__silver', 'promotions__promotion', 'promotions__stock', 'promotions__pool', 'promotions__stock_floor', 'promotions__create', 'promotions__redeem']) assert.ok(declared.includes(id), id);
  for (const id of ['badge_milestones__award', 'promotions__redeem']) assert.equal(a.model?.entities.has(id), false, `${id} is a typed value, not an entity of the combined model`);
});

test('a value that does not fit its platform type is refused with layer.value-invalid', () => {
  const found = errors([refused('value-invalid')]).filter((d) => d.code === 'layer.value-invalid');
  assert.equal(found.length, 2, JSON.stringify(found.map((d) => d.message)));
  assert.ok(found.some((d) => /"colour" is not a field of its type/.test(d.message)));
  const missing = found.find((d) => /"fields\.name" lacks the required field "ty"/.test(d.message));
  assert.ok(missing, JSON.stringify(found.map((d) => d.message)));
  assert.match(missing.message, /platform type "object-type-def"/);
  assert.equal(missing.loc?.file, 'value-invalid.jsonc');
  assert.equal(read(refused('value-invalid')).split('\n')[(missing.loc?.line ?? 1) - 1].includes('"name"'), true, 'the location is the field that lacks its type');
});

test('a union value the platform lacks is refused with layer.outside-catalogue', () => {
  const step = errors([refused('step-outside-catalogue')]).filter((d) => d.code === 'layer.outside-catalogue');
  assert.equal(step.length, 2, JSON.stringify(step.map((d) => d.message)));
  assert.ok(step.some((d) => /names "EmailOpened" at on, which is outside the published catalogue.*"trigger-event" has the variants .*LedgerPosted/.test(d.message)));
  assert.ok(step.some((d) => /names "RunScript" at steps\.run\.action.*"automation-step" has the variants .*CreateRecord/.test(d.message)));
  const op = errors([refused('operation-step-outside')]).filter((d) => d.code === 'layer.outside-catalogue');
  assert.equal(op.length, 1);
  assert.match(op[0].message, /names "SendMail" at steps\.0.*"tenant-operation-step" has the variants CreateRecord, UpdateRecord, DeleteRecord, PostLedger/);
});

test('an id outside the namespace of its product is refused with layer.namespace-missing', () => {
  const found = errors([refused('id-not-namespaced')]).filter((d) => d.code === 'layer.namespace-missing');
  assert.deepEqual(found.map((d) => /"([^"]+)"/.exec(d.message)?.[1]), ['badges-tier', 'badges_rank']);
  assert.match(found[0].message, /begins with "badges__" followed by a local name/);
  assert.equal(found[0].loc?.file, 'id-not-namespaced.jsonc');
});

test('a name in a typed section that no product file declares or that another product declares is refused', () => {
  const unknown = errors([refused('reference-unknown-object')]).filter((d) => d.code === 'layer.reference-unknown');
  assert.equal(unknown.length, 2, JSON.stringify(unknown.map((d) => d.message)));
  assert.ok(unknown.some((d) => /"member_tiers__ghost" at on\.RecordCreated\.object, which no product file declares/.test(d.message)));
  assert.ok(unknown.some((d) => /"member_tiers__nothing" at automation/.test(d.message)));
  // A capability nothing declares, named by a role: the same rule as an id no layer declares.
  const alone = errors([refused('capability-other-product')]).filter((d) => d.code === 'layer.reference-unknown');
  assert.equal(alone.length, 1, JSON.stringify(alone.map((d) => d.message)));
  assert.match(alone[0].message, /the capability "badges__grant"/);
  // A capability of the badges product named by a role of another product.
  const cross = errors([BADGES, refused('capability-other-product')]).filter((d) => d.code === 'layer.cross-product-reference');
  assert.equal(cross.length, 1, JSON.stringify(cross.map((d) => d.message)));
  assert.match(cross[0].message, /"badges__grant".*product file badges\.jsonc declares/);
  // A typed value that names the other product's entity.
  const text = JSON.stringify({ product: { id: 'other', name: 'Other', imports: { spec: '../platform.jsonc', entities: [] } }, triggers: [{ id: 'other__t', on: { RecordCreated: { object: 'badge_milestones__award' } }, automation: 'other__a' }] });
  const a = analyzeLayers(read(PLATFORM), [layer(complete[0]), { file: 'other.jsonc', text, platform: { declared: '../platform.jsonc', matches: true, expected: '../platform.jsonc' } }]);
  assert.ok(a.diagnostics.some((d) => d.code === 'layer.cross-product-reference' && /"badge_milestones__award" at on\.RecordCreated\.object, which product file badge-milestones\.jsonc declares/.test(d.message)), JSON.stringify(a.diagnostics.map((d) => d.message)));
});

test('a typed item may not redefine a platform entity or another item', () => {
  const text = JSON.stringify({ product: { id: 'p', name: 'P', imports: { spec: '../platform.jsonc', entities: [] } }, ledgerUnits: [{ id: 'runtime', description: 'd' }, { id: 'p__a', description: 'd' }], ledgerPools: [{ id: 'p__a', description: 'd' }] });
  const a = analyzeLayers(read(PLATFORM), [{ file: 'p.jsonc', text, platform: { declared: '../platform.jsonc', matches: true, expected: '../platform.jsonc' } }]);
  const redefined = a.diagnostics.filter((d) => d.code === 'layer.redefines-entity');
  assert.equal(redefined.length, 2, JSON.stringify(a.diagnostics.map((d) => d.code)));
  assert.ok(redefined.some((d) => /"runtime".*already declares component "runtime"/.test(d.message)));
  assert.ok(redefined.some((d) => /"p__a".*already declares it/.test(d.message)));
});

test('a product capability is reachable when a role confers it and a plan is not needed', () => {
  const file = { file: 'p.jsonc', platform: { declared: '../platform.jsonc', matches: true, expected: '../platform.jsonc' } };
  const header = { id: 'p', name: 'P', imports: { spec: '../platform.jsonc', entities: [] } };
  const capability = { id: 'p__use', name: 'Use', description: 'd' };
  const conferred = JSON.stringify({ product: header, capabilities: [capability], roles: [{ id: 'p__user', name: 'User', level: 'tenant', holders: ['person'], capabilities: ['p__use'] }] });
  const ok = analyzeLayers(read(PLATFORM), [{ ...file, text: conferred }]);
  assert.deepEqual(ok.diagnostics.filter((d) => d.severity === 'error').map((d) => d.code), [], 'no plan entitles it, and none has to');
  const bad = analyzeLayers(read(PLATFORM), [{ ...file, text: JSON.stringify({ product: header, capabilities: [capability] }) }]);
  const d = bad.diagnostics.find((x) => x.code === 'capability.unreachable');
  assert.match(d?.message ?? '', /"p__use" can never be used: no role or grant confers it\.$/);
  assert.doesNotMatch(d?.message ?? '', /plan/);
});

test('Exegra and specc read the same table of typed sections', () => {
  assert.deepEqual(TYPED_SECTIONS.map((s) => s.section), ['objects', 'policies', 'queries', 'views', 'workflows', 'segments', 'settings', 'ledgerUnits', 'ledgerPools', 'ledgerLimits', 'mailTemplates', 'noticeTemplates', 'tokens', 'triggers', 'automations', 'operations']);
  for (const key of TYPED_SECTIONS.map((s) => s.section)) assert.ok(PRODUCT_SECTION_NAMES.includes(key), key);
  for (const key of Object.keys(PRODUCT_SECTIONS)) assert.equal(TYPED_SECTIONS.some((s) => s.section === key), false, `${key} is both an entity section and a typed one`);
  const platform = parseSpec(read(PLATFORM)).model;
  for (const t of TYPED_SECTIONS) assert.equal(platform?.entities.get(t.type)?.kind, 'type', `${t.section} names the platform type ${t.type}`);
});

// ---- Expressions and retention of the typed sections (WG-5060, WG-5061) -----------------------------

test('an expression that does not parse or check in its scope is refused with one rule code per kind', () => {
  const found = (/** @type {string} */ name, /** @type {string} */ code) => errors([refused(name)]).filter((d) => d.code === code);
  const syntax = found('expression-syntax', 'layer.expr-syntax');
  assert.equal(syntax.length, 2, JSON.stringify(syntax.map((d) => d.message)));
  assert.ok(syntax.some((d) => /"member_tiers__on_post".*at "condition", `balance\(param\.owner\) > 1`.*position 0: unknown name "balance"/.test(d.message)), 'a trigger condition that calls what the language lacks');
  assert.ok(syntax.some((d) => /"member_tiers__grant".*at "conditions\.0\.expr".*position 14/.test(d.message)), 'an operation condition with a double-quoted string');
  assert.equal(syntax[0].loc?.file, 'expression-syntax.jsonc');
  const field = found('expression-unknown-field', 'layer.expr-unknown-field');
  assert.equal(field.length, 2, JSON.stringify(field.map((d) => d.message)));
  assert.ok(field.some((d) => /unknown field colour; the object type has the fields name, points, owner/.test(d.message)));
  assert.ok(field.some((d) => /unknown field phone; the object type has the fields email/.test(d.message)), 'a hop to a field of the target object type');
  assert.match(found('expression-unknown-role', 'layer.expr-unknown-role')[0]?.message ?? '', /unknown role member_tiers__ghost/);
  assert.match(found('expression-unknown-param', 'layer.expr-unknown-param')[0]?.message ?? '', /undeclared parameter limit; the scope binds name/);
  const type = found('expression-type', 'layer.expr-type').map((d) => /position \d+: (.*?)\. An expression/.exec(d.message)?.[1]);
  assert.deepEqual(type, ['cannot compare Str with Int', 'len does not accept a Int operand', 'name is not a single reference']);
  for (const name of ['expression-syntax', 'expression-unknown-field', 'expression-unknown-role', 'expression-unknown-param', 'expression-type']) {
    const codes = [...new Set(errors([refused(name)]).map((d) => d.code))];
    assert.equal(codes.every((c) => c.startsWith('layer.expr-')), true, `${name}: ${codes}`);
  }
});

test('a personal field without a retention rule on its object type is refused with layer.retention-missing', () => {
  const all = errors([refused('retention-missing')]);
  assert.deepEqual(all.map((d) => d.code), ['layer.retention-missing'], 'the type without a personal field needs no retention');
  assert.match(all[0].message, /"member_tiers__member".*personal field "email" and no retention \(D-6584\)/);
  assert.equal(all[0].loc?.file, 'retention-missing.jsonc');
  assert.equal(errors(complete).length, 0, 'both complete products carry retention');
});

test('an automation accepts any field and param but is still checked for syntax and roles', () => {
  const step = (/** @type {string} */ condition) => JSON.stringify({ product: { id: 'p', name: 'P', imports: { spec: '../platform.jsonc', entities: [] } }, automations: [{ id: 'p__a', label: 'A', 'run-as': { roles: [] }, start: 's', steps: { s: { action: { Branch: { condition, object: 'p__o', record: 'param.r', then: 's', else: 's' } }, next: 's' } } }] });
  const codes = (/** @type {string} */ condition) => analyzeLayers(read(PLATFORM), [{ file: 'p.jsonc', text: step(condition), platform: { declared: '../platform.jsonc', matches: true, expected: '../platform.jsonc' } }]).diagnostics.filter((d) => d.code.startsWith('layer.expr-')).map((d) => d.code);
  assert.deepEqual(codes("param.anything == 'x' and is_null(record.whatever) and has_role(owner)"), []);
  assert.deepEqual(codes('has_role(ghost)'), ['layer.expr-unknown-role']);
  assert.deepEqual(codes('balance(1)'), ['layer.expr-syntax']);
});

// The header members version and platform (WG-5174): the same validation and rule code as specc's layers.rs.
test('a product header takes version and platform and refuses a malformed one with layer.header-invalid', () => {
  const withHeader = (/** @type {string} */ members) => analyzeLayers(read(PLATFORM), [{ ...layer(BADGES), text: read(BADGES).replace('"id": "badges",', `"id": "badges", ${members}`) }]).diagnostics.filter((d) => d.severity === 'error');
  assert.deepEqual(withHeader('"version": "1.0.0", "platform": { "min": "0.2-draft", "below": "1.0" },').map((d) => d.code), []);
  assert.deepEqual(withHeader('"platform": { "min": "0.2" },').map((d) => d.code), []);
  for (const bad of ['"version": "1.0"', '"version": 1', '"version": "1.0.x"', '"platform": "0.2"', '"platform": { "below": "1.0" }', '"platform": { "min": "latest" }', '"platform": { "min": "0.2", "max": "1.0" }', '"platform": { "min": "1.0", "below": "1.0.0" }', '"platform": { "min": "2.0", "below": "1.9" }']) {
    assert.deepEqual(withHeader(`${bad},`).map((d) => d.code), ['layer.header-invalid'], bad);
  }
  assert.equal(errors([refused('header-version-invalid')])[0]?.code, 'layer.header-invalid');
  assert.match(errors([refused('header-platform-no-min')])[0]?.message ?? '', /has no "min"/);
  assert.match(errors([refused('header-platform-below-not-later')])[0]?.message ?? '', /not later than its first release/);
  assert.match(withHeader('"colour": "red",')[0]?.message ?? '', /holds only id, name, description, version, platform and imports/);
});

// ---- Queries, views and workflows in a product file (WG-5081) -----------------------------------

test('a product file may declare queries and views and workflows and refuses each that does not fit its platform type', () => {
  for (const [name, type] of [['query-value-invalid', 'query-def'], ['view-value-invalid', 'view-def'], ['workflow-value-invalid', 'workflow-def']]) {
    const found = errors([refused(name)]).filter((d) => d.code === 'layer.value-invalid');
    assert.equal(found.length, 1, `${name}: ${JSON.stringify(found.map((d) => d.message))}`);
    assert.match(found[0].message, /"colour" is not a field of its type/, name);
    assert.match(found[0].message, new RegExp(type), name);
  }
  const unknown = errors([refused('view-query-unknown')]).filter((d) => d.code === 'layer.reference-unknown');
  assert.equal(unknown.length, 1, JSON.stringify(unknown.map((d) => d.message)));
  assert.match(unknown[0].message, /ticket_board__ghost/);
});

test('a product declaring a query and a view and a workflow that fit their platform types is accepted', () => {
  const product = {
    product: { id: 'ticket-board', name: 'Ticket board', imports: { spec: '../platform.jsonc', entities: [] } },
    objects: [{ id: 'ticket_board__ticket', label: 'Ticket', fields: { title: { id: 'title', label: 'Title', ty: 'Str', required: true, unique: false }, status: { id: 'status', label: 'Status', ty: 'Str', required: true, unique: false } }, constraints: {} }],
    queries: [{ id: 'ticket_board__open', object: 'ticket_board__ticket', params: [], order: [] }],
    views: [{ id: 'ticket_board__board', route: '/tickets', title: 'Tickets', sections: { open: { query: 'ticket_board__open', args: {}, include: [], markdown: [], single: false } } }],
    workflows: [{ id: 'ticket_board__lifecycle', object: 'ticket_board__ticket', field: 'status', initial: ['open'], transitions: [] }],
  };
  const a = analyzeLayers(read(PLATFORM), [{ file: 'ticket-board.jsonc', text: JSON.stringify(product), platform: { declared: '../platform.jsonc', matches: true, expected: '../platform.jsonc' } }]);
  assert.equal(a.errorCount, 0, JSON.stringify(a.diagnostics.filter((d) => d.severity === 'error').map((d) => d.message)));
});
