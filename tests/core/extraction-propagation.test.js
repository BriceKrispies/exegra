// Extracted facts at every level (WG-5696): in a fixture repository (tests/fixtures/extraction/) adding, removing or
// retargeting an import updates the extracted facts, then the derived interaction at the module, component, subsystem
// and system cuts, then the verdict of a dependent claim. The propagated derived model equals the model derived from
// scratch on the new facts (invariant I4), through the footprints of M3 (rederive, claimsToRecompute). Also the
// reconciliation diagnostics and the provenance surfaces: the mix a derived interaction reports, and what a claim result
// and claim strength say they rest on.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { analyzeSpec } from '../../src/core/analyze.js';
import { evaluateClaim, evaluateClaims } from '../../src/core/claims.js';
import { claimStrength } from '../../src/core/claim-strength.js';
import { deriveModel, derivedJson, rederive, witnessOf, abstractionInvariants } from '../../src/core/abstraction.js';
import { claimsToRecompute } from '../../src/core/footprints.js';
import { attachExtracted, extractedChange, extractionOf, reconcile, stripExtracted } from '../../src/core/extraction.js';
import { Project } from '../../src/core/project.js';
import { moduleDeclarations } from '../../src/core/query.js';
import { extractRepository } from '../../tools/extract.js';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const FIXTURE = path.join(ROOT, 'tests/fixtures/extraction');
const SPEC = fs.readFileSync(path.join(FIXTURE, 'spec.json'), 'utf8');
const CUTS = ['modules', 'components', 'subsystems', 'system'];

/** A private copy of the fixture repository to edit. */
function copyRepo() {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-fixture-'));
  fs.cpSync(path.join(FIXTURE, 'repo'), dir, { recursive: true });
  return dir;
}
/** @param {string} dir @param {string} rel @param {string} text */
const write = (dir, rel, text) => fs.writeFileSync(path.join(dir, rel), text);

const base = /** @type {any} */ (analyzeSpec(SPEC).model);
/** @param {string} dir */
const modelAt = (dir) => attachExtracted(base, extractRepository(dir));
const A2 = 'src/a/two.js';
const edge = (/** @type {string} */ from, /** @type {string} */ to) => `extracted:imports:${from}=>${to}`;
const CROSS_B2 = edge(A2, 'src/b/two.js');
const CROSS_B1 = edge(A2, 'src/b/one.js');
const IMPORT_B2 = "import { value } from '../b/two.js';\nexport const two = () => value;\n";
const IMPORT_B1 = "import { one } from '../b/one.js';\nexport const two = () => one();\n";

/** The witnesses of the interaction between two blocks at a cut, or null. */
function interactionAt(/** @type {any} */ m, /** @type {string} */ cut, /** @type {string} */ from, /** @type {string} */ to) {
  return /** @type {any} */ (deriveModel(m, { cut })).interactions.find((/** @type {any} */ i) => i.from === from && i.to === to && i.kind === 'imports') ?? null;
}

test('the fixture repository starts clean: no import crosses the subsystems, and the claims hold', () => {
  const m = modelAt(copyRepo());
  assert.equal(extractionOf(m)?.edges.length, 2, 'a-one imports a-two, b-one imports b-two');
  assert.equal(evaluateClaim(m, 'a-not-b-components').status, 'verified');
  assert.equal(evaluateClaim(m, 'a-not-b-subsystems').status, 'verified');
  assert.deepEqual(reconcile(m).diagnostics.filter((d) => d.severity === 'warning'), [], 'extracted dependencies with no declared counterpart are not diagnostics');
  assert.equal(interactionAt(m, 'modules', 'module:src/a/one.js', 'module:src/a/two.js')?.witnesses.length, 1);
});

test('adding, removing and retargeting an import moves through every cut and the dependent claim, and equals a derivation from scratch', () => {
  const dir = copyRepo();
  const m0 = modelAt(dir);
  const results0 = evaluateClaims(m0);
  const derived0 = Object.fromEntries(CUTS.map((c) => [c, deriveModel(m0, { cut: c })]));

  // 1. add: a-two imports b-two, across the subsystems
  write(dir, A2, IMPORT_B2);
  const m1 = modelAt(dir);
  assert.deepEqual(extractedChange(m0, m1), [CROSS_B2], 'only the new extracted relationship changed');
  assert.deepEqual(m1.byKind.relationship.filter((/** @type {any} */ r) => r.data.provenance === 'extracted').map((/** @type {any} */ r) => r.id).filter((id) => id === CROSS_B2), [CROSS_B2]);
  const m1rel = /** @type {any} */ (m1.entities.get(CROSS_B2));
  assert.equal(m1rel.data.provenance, 'extracted');
  assert.deepEqual(m1rel.data.sources, [{ from: A2, to: 'src/b/two.js', how: 'static' }]);
  // the new witness at the module, component and subsystem cuts, and inside the one block at the system cut
  assert.deepEqual(interactionAt(m1, 'modules', 'module:src/a/two.js', 'module:src/b/two.js')?.witnesses, [CROSS_B2]);
  assert.deepEqual(interactionAt(m1, 'components', 'a-two', 'b-two')?.witnesses, [CROSS_B2]);
  assert.deepEqual(interactionAt(m1, 'subsystems', 'sub-a', 'sub-b')?.witnesses, [CROSS_B2]);
  const system = /** @type {any} */ (deriveModel(m1, { cut: 'system' }));
  assert.equal(system.interactions.length, 0);
  assert.equal(witnessOf(system, CROSS_B2).fibre !== null, true, 'at the system cut the import is internal to the one block');
  // the interaction reports the provenance of its witnesses
  assert.deepEqual(interactionAt(m1, 'subsystems', 'sub-a', 'sub-b')?.summary.provenance, { extracted: 1 });
  // the dependent claim changes its verdict, with the extracted witness as the counterexample
  const r1 = evaluateClaim(m1, 'a-not-b-subsystems');
  assert.equal(r1.status, 'violated');
  assert.match(r1.explanation, new RegExp(CROSS_B2.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')));
  assert.equal(evaluateClaim(m1, 'a-not-b-components').status, 'violated');
  // propagation through footprints equals derivation from scratch, at every cut
  const affected1 = extractedChange(m0, m1);
  for (const c of CUTS) {
    const { derived, recomputed } = rederive(/** @type {any} */ (derived0[c]), m0, m1, affected1);
    assert.deepEqual(derivedJson(derived), derivedJson(/** @type {any} */ (deriveModel(m1, { cut: c }))), `cut ${c}: propagated equals from scratch`);
    assert.equal(recomputed.all, false, `cut ${c}: not everything is recomputed`);
  }
  // the claims to recompute are exactly those the change can touch
  const recompute = claimsToRecompute(results0, m0, m1, affected1);
  assert.ok(recompute.has('a-not-b-subsystems') && recompute.has('a-not-b-components'));

  // 2. retarget: a-two imports b-one instead
  write(dir, A2, IMPORT_B1);
  const m2 = modelAt(dir);
  assert.deepEqual(extractedChange(m1, m2), [CROSS_B1, CROSS_B2].sort(), 'one relationship left, one arrived');
  assert.equal(interactionAt(m2, 'components', 'a-two', 'b-two'), null);
  assert.deepEqual(interactionAt(m2, 'components', 'a-two', 'b-one')?.witnesses, [CROSS_B1], 'the change moved between blocks');
  assert.deepEqual(interactionAt(m2, 'subsystems', 'sub-a', 'sub-b')?.witnesses, [CROSS_B1]);
  assert.equal(evaluateClaim(m2, 'a-not-b-subsystems').status, 'violated');
  const affected2 = extractedChange(m1, m2);
  for (const c of CUTS) {
    const prev = /** @type {any} */ (deriveModel(m1, { cut: c }));
    assert.deepEqual(derivedJson(rederive(prev, m1, m2, affected2).derived), derivedJson(/** @type {any} */ (deriveModel(m2, { cut: c }))), `cut ${c}: retarget propagated equals from scratch`);
  }

  // 3. remove: everything is restored
  write(dir, A2, 'export const two = () => 2;\n');
  const m3 = modelAt(dir);
  assert.deepEqual(extractedChange(m2, m3), [CROSS_B1]);
  for (const c of CUTS) assert.deepEqual(derivedJson(/** @type {any} */ (deriveModel(m3, { cut: c }))), derivedJson(/** @type {any} */ (derived0[c])), `cut ${c} is restored`);
  assert.equal(evaluateClaim(m3, 'a-not-b-subsystems').status, 'verified');
  assert.equal(evaluateClaim(m3, 'a-not-b-components').status, 'verified');
  const affected3 = extractedChange(m2, m3);
  for (const c of CUTS) {
    const prev = /** @type {any} */ (deriveModel(m2, { cut: c }));
    assert.deepEqual(derivedJson(rederive(prev, m2, m3, affected3).derived), derivedJson(/** @type {any} */ (derived0[c])), `cut ${c}: removal propagated restores the start`);
  }
});

test('the derived models of the fixture with extracted facts satisfy the abstraction invariants', () => {
  const dir = copyRepo();
  write(dir, A2, IMPORT_B2);
  const m = modelAt(dir);
  const out = abstractionInvariants(m, CUTS);
  const faults = Object.entries(out.faults).flatMap(([k, v]) => (Array.isArray(v) ? v.map((x) => `${k}: ${x}`) : []));
  assert.deepEqual(faults, []);
});

test('a Project carries the facts: setFacts replaces them and names the relationships that changed', () => {
  const dir = copyRepo();
  const p = new Project({ name: 'fx', specText: SPEC, extracted: extractRepository(dir) });
  const before = p.model;
  assert.ok(before && extractionOf(before));
  write(dir, A2, IMPORT_B2);
  const { affected, after } = p.setFacts({ extracted: extractRepository(dir) });
  assert.deepEqual(affected, [CROSS_B2]);
  assert.ok(after && after.entities.has(CROSS_B2) && !before.entities.has(CROSS_B2));
  // an edit of the specification keeps the facts
  const tx = p.apply([{ type: 'SetProperty', id: 'a-one', property: 'purpose', value: 'edited' }]);
  assert.equal(tx.ok, true);
  assert.ok(p.model?.entities.has(CROSS_B2));
  // the declared model is untouched by the facts
  assert.equal(p.semanticHash, new Project({ name: 'fx', specText: p.specText }).semanticHash);
  assert.equal(stripExtracted(/** @type {any} */ (p.model)).byKind.relationship.length, 0);
});

test('module elements come from the extracted facts when present and from implementation.modules otherwise', () => {
  const m = modelAt(copyRepo());
  const withFacts = moduleDeclarations(m);
  const without = moduleDeclarations(base);
  assert.deepEqual(withFacts.map((d) => [d.id, d.path, d.component]), without.map((d) => [d.id, d.path, d.component]));
  assert.ok(withFacts.every((d) => d.extracted === true) && without.every((d) => d.extracted === undefined));
  // a declared module the facts do not find stays declared, and is reported
  const gone = analyzeSpec(SPEC.replace('src/a/one.js', 'src/a/gone.js')).model;
  const mg = attachExtracted(/** @type {any} */ (gone), extractRepository(path.join(FIXTURE, 'repo')));
  assert.equal(moduleDeclarations(mg).find((d) => d.path === 'src/a/gone.js')?.extracted, false);
  assert.deepEqual(extractionOf(mg)?.notExtracted, [{ component: 'a-one', path: 'src/a/gone.js' }]);
  assert.ok(extractionOf(mg)?.unowned.includes('src/a/one.js'));
});

test('reconciliation: a declared static dependency inside the surface is redundant, reversed or unwitnessed; runtime wiring is never flagged', () => {
  const dir = copyRepo();
  const doc = JSON.parse(SPEC);
  doc.relationships = [
    { id: 'a-one-imports-a-two', kind: 'imports', from: 'a-one', to: 'a-two', description: 'declared and extracted' },
    { id: 'a-two-imports-a-one', kind: 'imports', from: 'a-two', to: 'a-one', description: 'declared, extracted the other way' },
    { id: 'a-one-imports-b-one', kind: 'imports', from: 'a-one', to: 'b-one', description: 'declared, no import' },
    { id: 'a-one-invokes-b-one', kind: 'invokes', from: 'a-one', to: 'b-one', description: 'runtime wiring: stays declared' },
  ];
  const model = attachExtracted(/** @type {any} */ (analyzeSpec(JSON.stringify(doc)).model), extractRepository(dir));
  const diags = reconcile(model).diagnostics;
  const by = Object.fromEntries(diags.map((d) => [d.relationship ?? d.code, d.code]));
  assert.equal(by['a-one-imports-a-two'], 'reconcile.static-declared-redundant');
  assert.equal(by['a-two-imports-a-one'], 'reconcile.static-direction');
  assert.equal(by['a-one-imports-b-one'], 'reconcile.static-declared-unwitnessed');
  assert.equal(by['a-one-invokes-b-one'], undefined, 'a declared runtime interaction is never flagged for being unextracted');
  // the extracted b-one -> b-two import has no declared counterpart and gives no diagnostic
  assert.ok(!diags.some((d) => /b-two/.test(d.message) && d.code !== 'reconcile.extracted-external'));
});

test('a dynamic-only import is extracted as dynamic, and a declared static import of it is a kind mismatch', () => {
  const dir = copyRepo();
  write(dir, A2, "export const two = async () => (await import('../b/two.js')).value;\n");
  const doc = JSON.parse(SPEC);
  doc.relationships = [{ id: 'a-two-imports-b-two', kind: 'imports', from: 'a-two', to: 'b-two', description: 'declared static' }];
  const model = attachExtracted(/** @type {any} */ (analyzeSpec(JSON.stringify(doc)).model), extractRepository(dir));
  const rel = /** @type {any} */ (model.entities.get(CROSS_B2));
  assert.equal(rel.data.dynamic, true);
  assert.equal(rel.data.sources[0].how, 'dynamic');
  assert.ok(reconcile(model).diagnostics.some((d) => d.code === 'reconcile.static-kind' && d.relationship === 'a-two-imports-b-two'));
});

test('provenance surfaces: claim results and claim strength say what they rest on, and static extraction is never presented as behaviour', () => {
  const dir = copyRepo();
  const declaredOnly = evaluateClaim(base, 'a-not-b-components');
  assert.equal(declaredOnly.basis?.basis, 'none', 'the fixture declares no relationship, so the check reads none');
  const m = modelAt(dir);
  const r = evaluateClaim(m, 'a-not-b-components');
  assert.equal(r.basis?.basis, 'extracted');
  assert.deepEqual(r.basis?.counts, { extracted: 2 });
  assert.match(r.scope, /static imports only/);
  const s = claimStrength(m).get('a-not-b-components');
  assert.equal(s?.check, 'structural');
  assert.equal(s?.details.basis, 'extracted');
  assert.deepEqual(s?.details.witnesses, { extracted: 2 });
  assert.match(s?.details.grounding ?? '', /static imports only/);
  // a mix: one declared, one extracted
  const doc = JSON.parse(SPEC);
  doc.relationships = [{ id: 'b-one-imports-a-one', kind: 'imports', from: 'b-one', to: 'a-one', description: 'declared outside the surface check for the test' }];
  const mixed = attachExtracted(/** @type {any} */ (analyzeSpec(JSON.stringify(doc)).model), extractRepository(dir));
  const sub = interactionAt(mixed, 'components', 'b-one', 'a-one');
  assert.deepEqual(sub?.summary.provenance, { declared: 1 });
  assert.deepEqual(evaluateClaim(mixed, 'a-not-b-components').basis?.counts, { declared: 1, extracted: 2 });
});
