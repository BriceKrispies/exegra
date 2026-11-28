// Conformance L1 (WG-5685, criterion 12; docs/assessment/2026-11-26/conformance.md, L1): the camera memory of
// src/app/main.js is checked at the trace stage, so an edit of the code that breaks it is seen.
//
// The trace-stage check runs the camera code of main.js itself (the text from `const cameraKey` to the end of
// saveCamera, evaluated with a session, a view, a recorder and a session storage standing in for the browser)
// through the scenario of camera-restored-in-model: leave a view with camera cA, switch, move the camera, come
// back. Coming back must restore cA. The claim camera-restored-per-view rests on this test (conformance-trace).

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import vm from 'node:vm';
import { fileURLToPath } from 'node:url';
import { analyzeSpec } from '../../src/core/analyze.js';
import { readSpecFile } from '../../tools/spec-manifest.js';
import { evaluateClaim } from '../../src/core/claims.js';
import { dependencyGraph } from '../../src/core/impact.js';
import { recordsStamp, formalSourcesHash } from '../../tools/tree-stamp.js';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
const MAIN = 'src/app/main.js';
const CLAIM = 'camera-restored-per-view';
const EVIDENCE = 'ev-camera-trace-stage';
const SAVE = 'sessionStorage.setItem(cameraKey(), camera)';

/**
 * The trace-stage check of the camera memory: run the camera code of a main.js text through view switches.
 * @param {string} text the text of main.js
 * @returns {{outcome: 'pass'|'fail', restored: any, trace: string[]}}
 */
export function cameraTrace(text) {
  const from = text.indexOf('const cameraKey = ');
  const to = text.indexOf('/** Pointer or wheel input');
  assert.ok(from >= 0 && to > from, 'main.js holds the camera code between `const cameraKey` and cameraMoved');
  /** @type {string[]} */
  const trace = [];
  const store = new Map();
  const session = { projectName: 'p', viewId: 'structural', scene: {}, placement: {} };
  let camera = /** @type {any} */ ('cA');
  const ctx = vm.createContext({
    session,
    JSON,
    selectionIds: () => [],
    highlightIds: () => null,
    view: { setScene() {}, setSelection() {}, setHighlight() {}, setCamera: (/** @type {any} */ c) => { camera = c; trace.push(`restore ${c}`); }, getCamera: () => camera },
    traffic: { record: (/** @type {string} */ id) => trace.push(id) },
    sessionStorage: { getItem: (/** @type {string} */ k) => (store.has(k) ? store.get(k) : null), setItem: (/** @type {string} */ k, /** @type {string} */ v) => { store.set(k, String(v)); } },
  });
  const api = vm.runInContext(`${text.slice(from, to)}\n;({ pushScene, saveCamera })`, ctx);
  api.pushScene();                       // open the structural view: nothing stored yet
  api.saveCamera();                      // leave it with camera cA
  session.viewId = 'behavioral';
  api.pushScene();
  camera = 'cB';                         // move the camera in the other view
  api.saveCamera();
  session.viewId = 'structural';         // come back
  api.pushScene();
  return { outcome: camera === 'cA' ? 'pass' : 'fail', restored: camera, trace };
}

test('the camera code of main.js restores the camera a view was left with', () => {
  const r = cameraTrace(fs.readFileSync(path.join(ROOT, MAIN), 'utf8'));
  assert.equal(r.outcome, 'pass', r.trace.join(', '));
  assert.ok(r.trace.includes('camera-restored'));
});

test('an edit of main.js that stores no camera makes the camera claims stale and the trace stage refutes it', () => {
  const original = fs.readFileSync(path.join(ROOT, MAIN), 'utf8');
  assert.ok(original.includes(SAVE), `main.js saves the camera with ${SAVE}`);
  const edited = original.replace(SAVE, "sessionStorage.setItem(cameraKey(), '')");
  // The edit, in a temporary copy: the tree is not touched.
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-camera-'));
  try {
    fs.writeFileSync(path.join(dir, 'main.js'), edited);
    const { model } = analyzeSpec(readSpecFile(path.join(ROOT, 'specs/exegra/spec.jsonc')));
    assert.ok(model);
    const before = recordsStamp(ROOT);
    const after = recordsStamp(ROOT, { [MAIN]: edited });
    assert.notEqual(before, after);
    const formal = formalSourcesHash(ROOT);
    // Every test evidence recorded passing on the tree before the edit, with the files its run covered as verify
    // recorded them (specs/exegra/evidence/results.json); the camera test reads main.js.
    const real = JSON.parse(fs.readFileSync(path.join(ROOT, 'specs/exegra/evidence/results.json'), 'utf8')).results ?? {};
    /** @type {Record<string, any>} */
    const results = {};
    for (const e of model.byKind.evidence ?? []) {
      if (e.data.kind !== 'test') continue;
      const covers = e.id === EVIDENCE ? [MAIN] : Array.isArray(real[e.id]?.covers) ? real[e.id].covers : [];
      results[e.id] = { outcome: 'pass', stamp: before, covers };
    }
    const recorded = { results };
    const fresh = evaluateClaim(model, CLAIM, { recorded, stamps: { tree: before, formal } });
    assert.equal(fresh.status, 'supported', fresh.explanation);
    assert.equal(fresh.stage, 'trace');

    // Without rerunning anything: the claim and every claim whose evidence covers main.js read stale.
    const g = dependencyGraph(model, { recorded });
    const covering = new Set(g.edges.filter(([x, y]) => x.kind === 'evidence' && y.kind === 'file' && y.id === MAIN).map(([x]) => x.id));
    const claims = new Set([CLAIM, ...g.edges.filter(([x, y]) => x.kind === 'claim' && y.kind === 'evidence' && covering.has(y.id)).map(([x]) => x.id)]);
    for (const id of claims) {
      const r = evaluateClaim(model, id, { recorded, stamps: { tree: after, formal } });
      assert.equal(r.verdict?.freshness, 'stale', id);
      assert.notEqual(r.status, 'supported', id);
    }

    // Running the trace-stage check on the edited copy refutes the claim.
    const run = cameraTrace(fs.readFileSync(path.join(dir, 'main.js'), 'utf8'));
    assert.equal(run.outcome, 'fail');
    const refuted = evaluateClaim(model, CLAIM, { recorded: { results: { ...results, [EVIDENCE]: { outcome: 'fail', stamp: after, covers: [MAIN] } } }, stamps: { tree: after, formal } });
    assert.equal(refuted.status, 'violated', refuted.explanation);
    assert.equal(refuted.verdict?.strength, 'refuted');
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
});
