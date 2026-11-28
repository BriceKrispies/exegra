// Observed facts (WG-5696): a recorded session of the traffic recorder becomes facts with provenance `observed`, naming
// the recording; reconciliation reports an observed interaction with no declared relationship, and a declared runtime
// interaction the recording does not show as "not observed", never as false. The recording is a committed fixture
// (tests/fixtures/recordings/live-session.json): no live recording is kept in the repository.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { analyzeSpec } from '../../src/core/analyze.js';
import { attachObserved, observedInteractions, reconcile, OBSERVED_FORMAT } from '../../src/core/extraction.js';
import { deriveModel } from '../../src/core/abstraction.js';
import { observeRecording } from '../../tools/observe.js';
import { readSpecFile } from '../../tools/spec-manifest.js';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const RECORDING = fs.readFileSync(path.join(ROOT, 'tests/fixtures/recordings/live-session.json'), 'utf8');
const self = /** @type {any} */ (analyzeSpec(readSpecFile(path.join(ROOT, 'specs/exegra/spec.jsonc'))).model);
const observed = observeRecording(RECORDING, { id: 'live-session-fixture', source: 'live-session.json' });

// A recorded session fixture gives observed relationships, observed-but-undeclared and not-observed diagnostics.
// @evidence observed-facts-reconcile #
test('a recording is counted into observed facts that name it', () => {
  assert.equal(observed.format, OBSERVED_FORMAT);
  assert.equal(observed.provenance, 'observed');
  assert.deepEqual(observed.recording, { id: 'live-session-fixture', source: 'live-session.json', digest: observed.recording.digest, events: 5 });
  assert.match(observed.recording.digest, /^sha256:[0-9a-f]{64}$/);
  assert.deepEqual(observed.events, { 'page-loaded': 1, 'project-files-read': 2, 'read-intent': 2 });
  assert.deepEqual(observeRecording(RECORDING, { id: 'live-session-fixture', source: 'live-session.json' }), observed, 'the same recording gives the same facts');
});

test('observed interactions are the pairs of components where one emits an observed event and the other consumes it', () => {
  const o = observedInteractions(self, observed);
  assert.deepEqual(o.map((i) => `${i.from}->${i.to}:${i.event}:${i.count}`), ['persistence-client->session:project-files-read:2', 'session->persistence-client:read-intent:2']);
  assert.ok(o.every((i) => i.recording === 'live-session-fixture'));
});

test('observed relationships carry provenance observed and the recording, and are witnesses at every cut beside the declared ones', () => {
  const m = attachObserved(self, observed);
  const rels = m.byKind.relationship.filter((/** @type {any} */ r) => r.data.provenance === 'observed');
  assert.equal(rels.length, 2);
  assert.ok(rels.every((/** @type {any} */ r) => r.data.recording.id === 'live-session-fixture' && r.data.kind === 'notifies'));
  assert.equal(m.byKind.relationship.length, self.byKind.relationship.length + 2, 'declared relationships are neither replaced nor merged');
  const d = /** @type {any} */ (deriveModel(m, { cut: 'l1' }));
  const mix = d.interactions.flatMap((/** @type {any} */ i) => Object.keys(i.summary.provenance));
  assert.ok(mix.includes('observed') && mix.includes('declared'));
});

test('declared runtime interactions the recording does not show are "not observed", never false', () => {
  const r = reconcile(attachObserved(self, observed));
  const not = r.diagnostics.filter((d) => d.code === 'reconcile.not-observed');
  assert.ok(not.length > 0);
  assert.ok(not.every((d) => d.severity === 'info' && /not observed/.test(d.message) && /does not make the relationship false/.test(d.message)));
  assert.ok(!r.diagnostics.some((d) => /\bfalse\b/.test(d.message) && !/does not make the relationship false/.test(d.message)));
  assert.equal(r.summary.notObserved, not.length);
  // a relationship whose events the recording does show is not reported
  assert.ok(!not.some((d) => d.relationship === 'session-calls-persistence-client'));
});

test('an observed interaction with no declared relationship between the components is reported', () => {
  // Drop every declared relationship between the two components.
  const without = /** @type {any} */ ({ ...self, byKind: { ...self.byKind, relationship: self.byKind.relationship.filter((/** @type {any} */ r) => !(['session', 'persistence-client'].includes(r.data.from) && ['session', 'persistence-client'].includes(r.data.to))) } });
  const r = reconcile(attachObserved(without, observed));
  const undeclared = r.diagnostics.filter((d) => d.code === 'reconcile.observed-undeclared');
  assert.deepEqual(undeclared.map((d) => [d.from, d.to]), [['persistence-client', 'session'], ['session', 'persistence-client']]);
  for (const d of undeclared) assert.match(d.message, /live-session-fixture/);
  assert.equal(reconcile(attachObserved(self, observed)).summary.observedUndeclared, 0, 'with the declared relationships there is no such diagnostic');
});
