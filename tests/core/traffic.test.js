// The traffic recorder and its producers outside the page (WG-4777): the bounded stream with logical sequence
// numbers (src/app/traffic-recorder.js), the development server's own events returned with each answer and
// inferred for external edits (tools/vite-plugin-exegra.js), the engine runner's worker messages
// (src/app/engine-runner.js), and the sha-256 that names texts (src/core/sha256.js). The producers inside the
// page (session, persistence client, scene, toolbar) are exercised by tests/browser/live.spec.js.
import test from 'node:test';
import assert from 'node:assert/strict';
import crypto from 'node:crypto';
import fs from 'node:fs/promises';
import http from 'node:http';
import os from 'node:os';
import path from 'node:path';
import { createTrafficRecorder } from '../../src/app/traffic-recorder.js';
import { createEngineRunner } from '../../src/app/engine-runner.js';
import { exegraDevServer, changeTrace, hashFiles } from '../../tools/vite-plugin-exegra.js';
import { hashText } from '../../tools/workspace.js';
import { sha256Hex } from '../../src/core/sha256.js';

test('the recorder keeps a bounded stream with logical sequence numbers and keeps wall-clock times out of the replay', () => {
  let clock = 1000;
  const r = createTrafficRecorder({ limit: 3, clock: () => (clock += 7) });
  const seen = [];
  r.subscribe((e) => seen.push(e.id));
  for (const id of ['a', 'b', 'c', 'd', 'e']) r.record(id, { requestId: id === 'c' ? 7 : undefined });
  assert.deepEqual(r.events().map((e) => [e.seq, e.id]), [[3, 'c'], [4, 'd'], [5, 'e']]);
  assert.equal(r.dropped, 2);
  assert.deepEqual(seen, ['a', 'b', 'c', 'd', 'e']);
  assert.ok(r.events().every((e) => typeof e.at === 'number'));
  assert.ok(r.forReplay().every((e) => !('at' in e)), 'forReplay strips the wall-clock time');
  assert.equal(r.answer('c', 7)?.seq, 3);
  assert.equal(r.answer('c', 8), null);
  assert.deepEqual([r.nextRequestId(), r.nextRequestId()], [1, 2]);
  // A recorded payload is a copy: later changes of the producer's object do not reach the stream.
  const p = { n: 1 };
  r.record('f', p);
  p.n = 2;
  assert.equal(r.events().at(-1)?.payload.n, 1);
  assert.equal(r.forReplay().find((e) => e.id === 'f')?.payload.n, 1);
  r.record('g', {}, { inferred: true });
  assert.equal(r.forReplay().at(-1)?.inferred, true);
});

test('sha256Hex agrees with the workspace hash', () => {
  for (const text of ['', 'abc', 'é€😀'.repeat(40), 'x'.repeat(100_003)]) {
    assert.equal(sha256Hex(text), crypto.createHash('sha256').update(text, 'utf8').digest('hex'));
    assert.equal(sha256Hex(text), hashText(text));
  }
});

/** A development server middleware over a fresh specs directory with one project, "demo". */
async function withServer(/** @type {(base: string, dir: string) => Promise<void>} */ fn) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'exegra-traffic-'));
  await fs.mkdir(path.join(dir, 'demo'), { recursive: true });
  await fs.writeFile(path.join(dir, 'demo', 'spec.jsonc'), '{ "system": { "name": "Demo" } }\n', 'utf8');
  /** @type {any} */
  let handler = null;
  const plugin = /** @type {any} */ (exegraDevServer({ specsDir: dir }));
  plugin.configureServer({ middlewares: { use: (/** @type {any} */ f) => { handler = f; } }, httpServer: null, config: { logger: { error() {} } } });
  const server = http.createServer((req, res) => handler(req, res, () => { res.statusCode = 404; res.end(); }));
  await new Promise((resolve) => server.listen(0, '127.0.0.1', () => resolve(undefined)));
  const { port } = /** @type {any} */ (server.address());
  try { await fn(`http://127.0.0.1:${port}/__exegra`, dir); }
  finally { server.close(); await fs.rm(dir, { recursive: true, force: true }); }
}

/** @param {Response} res */
const traceOf = (res) => JSON.parse(decodeURIComponent(res.headers.get('x-exegra-trace') ?? '[]'));
/** @param {number} requestId @param {any} [body] */
const headers = (requestId, body) => ({ 'x-exegra-client': '1', 'x-exegra-request-id': String(requestId), ...(body ? { 'Content-Type': 'application/json' } : {}) });

test('the development server returns its own events with each answer stamped with the request id', () => withServer(async (base) => {
  const list = await fetch(`${base}/projects`, { headers: headers(1) });
  assert.deepEqual(traceOf(list).map((/** @type {any} */ e) => [e.id, e.payload.requestId]), [['ws-list', 1], ['ws-list-done', 1], ['list-projects-ok', 1]]);
  assert.deepEqual(traceOf(list)[2].payload.projects, ['demo']);

  const read = await fetch(`${base}/project?name=demo`, { headers: headers(2) });
  const files = await read.json();
  const readTrace = traceOf(read);
  assert.deepEqual(readTrace.map((/** @type {any} */ e) => e.id), ['ws-read', 'ws-read-done', 'read-project-ok']);
  assert.equal(readTrace[2].payload.spec, files.spec.hash, 'texts are named by their sha-256');
  assert.equal(readTrace[2].payload.layout, null);

  const text = '{ "system": { "name": "Demo 2" } }\n';
  const write = await fetch(`${base}/write`, { method: 'POST', headers: headers(3, true), body: JSON.stringify({ name: 'demo', file: 'spec', text, baseHash: files.spec.hash }) });
  const wt = traceOf(write);
  assert.deepEqual(wt.map((/** @type {any} */ e) => e.id), ['ws-write', 'disk-file-replaced', 'ws-write-done', 'write-file-ok']);
  assert.equal(wt[0].payload.text, hashText(text));
  assert.equal(wt[3].payload.hash, hashText(text));
  assert.ok(wt.filter((/** @type {any} */ e) => e.id !== 'disk-file-replaced').every((/** @type {any} */ e) => e.payload.requestId === 3));

  const stale = await fetch(`${base}/write`, { method: 'POST', headers: headers(4, true), body: JSON.stringify({ name: 'demo', file: 'spec', text: 'x', baseHash: files.spec.hash }) });
  assert.equal(stale.status, 409);
  assert.deepEqual(traceOf(stale).map((/** @type {any} */ e) => [e.id, e.payload.current]), [['ws-write', undefined], ['ws-write-conflict', hashText(text)], ['write-file-conflict', hashText(text)]]);

  const missing = await fetch(`${base}/project?name=nope`, { headers: headers(5) });
  assert.deepEqual(traceOf(missing).map((/** @type {any} */ e) => [e.id, e.payload.code]), [['ws-read', undefined], ['ws-read-missing', undefined], ['read-project-failed', 'not-found']]);

  // A request without a request id gets no trace: nothing is recorded for callers that do not record.
  const quiet = await fetch(`${base}/projects`, { headers: { 'x-exegra-client': '1' } });
  assert.equal(quiet.headers.get('x-exegra-trace'), null);

  // Its own write is not an external edit; any other hash is, and is marked inferred.
  assert.deepEqual(changeTrace('demo', 'spec', hashText(text)).map((e) => e.id), ['ws-change', 'file-change-notice-sent']);
  const ext = changeTrace('demo', 'spec', 'other');
  assert.deepEqual(ext.map((e) => [e.id, !!e.inferred]), [['disk-edited-externally', true], ['disk-file-replaced', true], ['ws-change', false], ['file-change-notice-sent', false]]);
  assert.deepEqual(changeTrace('demo', 'recorded', 'r1').map((e) => e.id), ['ws-write-recorded', 'disk-file-replaced', 'ws-recorded-done', 'ws-change', 'file-change-notice-sent']);
  assert.equal(hashFiles({ b: '2', a: '1' }), sha256Hex(JSON.stringify({ a: '1', b: '2' })));
}));

test('the engine runner records the worker messages with the scenario standing for input and trace', async () => {
  /** @type {any[]} */
  const workers = [];
  const g = /** @type {any} */ (globalThis);
  const saved = g.Worker;
  g.Worker = class {
    constructor() { /** @type {any[]} */ this.posted = []; workers.push(this); }
    /** @param {any} m */
    postMessage(m) { this.posted.push(m); }
    terminate() {}
  };
  try {
    /** @type {[string, any][]} */
    const rec = [];
    const runner = createEngineRunner({ record: (id, payload = {}) => { rec.push([id, payload]); } });
    void runner.run(/** @type {any} */ ({ scenario: { id: 'sc-a' } }));
    // A second run while the first waits terminates that worker and starts another.
    const second = runner.run(/** @type {any} */ ({ scenario: { id: 'sc-b' } }));
    const w = workers.at(-1);
    w.onmessage({ data: { id: w.posted[0].id, ok: true, trace: JSON.stringify({ steps: [] }) } });
    await second;
    assert.deepEqual(rec.map(([id, p]) => [id, p.id ?? null, p.input ?? p.trace ?? null, p.generation ?? null]), [
      ['engine-run-posted', 1, 'sc-a', null],
      ['worker-terminated', null, null, null],
      ['engine-run-posted', 2, 'sc-b', null],
      ['worker-run-done', 2, 'sc-b', 1],
      ['engine-run-returned', 2, 'sc-b', null],
    ]);
    // A refusal is recorded as the error event of the contract.
    const third = runner.run(/** @type {any} */ ({ scenario: { id: 'sc-c' } }));
    const w3 = workers.at(-1);
    w3.onmessage({ data: { id: w3.posted.at(-1).id, ok: false, error: 'bad input' } });
    await assert.rejects(third);
    assert.deepEqual(rec.at(-1), ['engine-run-refused', { code: 'engine.refused', id: 3, error: 'bad input' }]);
    runner.dispose();
  } finally {
    g.Worker = saved;
  }
});
