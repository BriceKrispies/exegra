// The self-model replay (src/core/replay.js): a stream recorded from a real run of Exegra (open a copy of
// its own specification, make an edit, save it; tests/fixtures/live/open-edit-save.json, recorded by
// tests/browser/live.spec.js) replays through the scenario live-session of specs/exegra/spec.jsonc without a
// divergence, and doctored copies of it are reported: an event out of order, an unknown event, a predicted
// response that never comes, a payload that differs, and a prediction older than the bound.
import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { analyzeSpec } from '../../src/core/analyze.js';
import { createReplay, replayStream, replayChecks, REPLAY_CLAIM } from '../../src/core/replay.js';
import { checkTrace } from '../../src/core/claims.js';
import { requestLog } from '../../src/core/contract-trace.js';
import { readSpecFile } from '../../tools/spec-manifest.js';

const { model } = analyzeSpec(readSpecFile(new URL('../../specs/exegra/spec.jsonc', import.meta.url)));
/** @type {{seq: number, id: string, payload: Record<string, any>}[]} */
const STREAM = JSON.parse(fs.readFileSync(new URL('../fixtures/live/open-edit-save.json', import.meta.url), 'utf8'));
const copy = () => STREAM.map((e) => ({ ...e, payload: { ...e.payload } }));
const at = (/** @type {any[]} */ s, /** @type {string} */ id) => s.findIndex((e) => e.id === id);
const kinds = (/** @type {any[]} */ ds) => ds.map((d) => `${d.kind}:${d.event}`);

test('a recorded open edit and save replays through live-session without a divergence', () => {
  assert.ok(model);
  const { trace, divergences, pending } = replayStream(model, STREAM, { closed: true });
  assert.deepEqual(divergences, []);
  assert.deepEqual(pending, []);
  assert.equal(trace.steps.length, STREAM.length);
  assert.equal(trace.scenarioId, 'live-session');
  // Each step names the components responsible, as a simulated step does.
  const save = trace.steps.find((s) => s.event.id === 'save-succeeded');
  assert.ok(save?.fired.some((f) => f.transition === 'session-saved'));
  assert.ok(save?.responsible.includes('session'));
  const write = trace.steps.find((s) => s.event.id === 'ws-write');
  assert.ok(write?.responsible.includes('workspace-service'));
  // A matched event carries the transition that predicted it as its source; logical time is the sequence number.
  assert.equal(write?.event.source.transition, 'dev-write');
  assert.equal(write?.time, STREAM[at(STREAM, 'ws-write')].seq);
  // The initial hash of the file on disk is calibrated from the first read, not reported.
  const read = trace.steps.find((s) => s.event.id === 'ws-read-done');
  assert.ok(read?.calibrated.some((c) => c.behavior === 'workspace-disk-flow' && c.variable === 'diskSpec'));
  // The checks and the request log read the replay like a simulated trace.
  const checks = checkTrace(/** @type {any} */ (model), trace);
  assert.deepEqual(checks.filter((c) => !c.holds && !c.pending), []);
  assert.ok(requestLog(/** @type {any} */ (model), trace).some((l) => l.text.startsWith('→ POST /__exegra/write')));
  assert.deepEqual(replayChecks(/** @type {any} */ (model), divergences, trace.steps.length).map((c) => [c.claimId, c.holds]), [[REPLAY_CLAIM, true]]);
});

test('an event in the wrong order is a divergence', () => {
  const s = copy();
  // The session reports the save before the server has answered it.
  const [ok] = s.splice(at(s, 'save-succeeded'), 1);
  s.splice(at(s, 'write-file-request'), 0, ok);
  const { divergences } = replayStream(/** @type {any} */ (model), s, { closed: true });
  assert.ok(kinds(divergences).includes('unpredicted:save-succeeded'), kinds(divergences).join(', '));
  const checks = replayChecks(/** @type {any} */ (model), divergences, s.length);
  assert.ok(checks.every((c) => c.claimId === REPLAY_CLAIM && !c.holds && typeof c.stepIndex === 'number'));
});

test('an event the specification does not name is a divergence', () => {
  const s = copy();
  s.splice(at(s, 'write-intent'), 0, { seq: 999, id: 'cache-warmed', payload: {} });
  const { divergences } = replayStream(/** @type {any} */ (model), s, { closed: true });
  assert.deepEqual(kinds(divergences), ['unknown-event:cache-warmed']);
});

test('a predicted response that never comes is a divergence', () => {
  // The stream ends after the server wrote the file: the model predicts write-file-ok, which never comes.
  const s = copy().slice(0, at(STREAM, 'ws-write-done') + 1);
  const open = replayStream(/** @type {any} */ (model), s);
  assert.deepEqual(open.divergences, [], 'an open stream still waits for it');
  assert.ok(open.pending.some((p) => p.event === 'write-file-ok'));
  const closed = replayStream(/** @type {any} */ (model), s, { closed: true });
  assert.ok(kinds(closed.divergences).includes('missing:write-file-ok'), kinds(closed.divergences).join(', '));
  const missing = closed.divergences.find((d) => d.event === 'write-file-ok');
  assert.equal(missing?.transition, 'dev-write-ok');
});

test('a predicted event not seen within the bound is missing even while the stream is open', () => {
  const s = copy();
  s.splice(at(s, 'write-file-ok'), 1);
  const { divergences } = replayStream(/** @type {any} */ (model), s, { bound: 3 });
  assert.ok(kinds(divergences).includes('missing:write-file-ok'), kinds(divergences).join(', '));
});

test('a recorded payload value that differs from the prediction is a divergence', () => {
  const s = copy();
  s[at(s, 'write-file-ok')].payload.hash = 'not-the-hash-written';
  const { divergences } = replayStream(/** @type {any} */ (model), s, { closed: true });
  const d = divergences.find((x) => x.kind === 'payload');
  assert.equal(d?.event, 'write-file-ok');
  assert.equal(d?.field, 'hash');
});

test('a predicted event that no behavior consuming it accepts in its state is a divergence', () => {
  // A view the tab storage of the model has no place for: the camera saved for it is predicted (camera-keep)
  // but session-storage-flow accepts camera-saved only for the views it holds.
  const s = copy();
  for (const id of ['view-switched', 'camera-restore-requested', 'camera-none', 'camera-saved']) s[at(s, id)].payload.view = 'no-such-view';
  const { divergences } = replayStream(/** @type {any} */ (model), s, { closed: true });
  assert.ok(kinds(divergences).includes('not-allowed:camera-saved'), kinds(divergences).join(', '));
});

test('the replay is incremental and deterministic', () => {
  const r = createReplay(/** @type {any} */ (model));
  for (const e of STREAM) r.consume(e);
  const whole = replayStream(/** @type {any} */ (model), STREAM);
  assert.deepEqual(r.trace(), whole.trace);
  assert.equal(r.trace().outcome, 'running');
});
