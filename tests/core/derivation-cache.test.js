// The persistent cache of the derived model (src/core/derivation-cache.js, WG-5636): a hit gives exactly
// what a miss gives, any change to an input or to Exegra's derivation sources is a miss, a damaged entry
// is a miss, and concurrent processes share one cache safely. Each process runs with its own cache directory.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { spawn, spawnSync } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { encode, decode, derivationSourceHash } from '../../src/core/derivation-cache.js';

const REPO = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
const PLATFORM = fs.readFileSync(path.join(REPO, 'tests', 'fixtures', 'layers', 'platform.jsonc'), 'utf8');
const tmp = () => fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-cache-test-'));

/** A specs directory holding project `p` with the platform fixture as its specification. */
function workspace() {
  const dir = tmp();
  fs.mkdirSync(path.join(dir, 'specs', 'p'), { recursive: true });
  fs.writeFileSync(path.join(dir, 'specs', 'p', 'spec.jsonc'), PLATFORM);
  return { dir, specs: path.join(dir, 'specs'), spec: path.join(dir, 'specs', 'p', 'spec.jsonc'), config: path.join(dir, 'specs', 'p', 'project.jsonc'), cache: path.join(dir, 'cache') };
}

/** @param {string} cache @param {Record<string, string>} [extra] */
const envFor = (cache, extra = {}) => ({ ...process.env, EXEGRA_MODEL_CACHE_DIR: cache, EXEGRA_CACHE_TRACE: '1', EXEGRA_NO_CACHE: '', ...extra });

/** Run the CLI: its stdout and the cache events it traced. */
function exegra(/** @type {string[]} */ args, /** @type {Record<string, string>} */ env) {
  const r = spawnSync(process.execPath, [path.join(REPO, 'cli', 'exegra.js'), ...args], { cwd: REPO, env, encoding: 'utf8', maxBuffer: 1 << 28 });
  return { status: r.status, stdout: r.stdout, events: (r.stderr.match(/exegra-cache: .*/g) ?? []).map((l) => l.slice(14)) };
}
const entries = (/** @type {string} */ cache) => (fs.existsSync(cache) ? fs.readdirSync(cache).filter((f) => f.endsWith('.entry')) : []);

test('a hit gives byte-identical validate and claims output to a cold run', () => {
  const w = workspace();
  for (const command of ['validate', 'claims']) {
    const args = [command, '--project', 'p', '--specs', w.specs];
    const off = exegra(args, envFor(w.cache, { EXEGRA_NO_CACHE: '1' }));
    assert.deepEqual(off.events, [], 'EXEGRA_NO_CACHE=1 touches no cache');
    assert.deepEqual(entries(w.cache), []);
    const cold = exegra(args, envFor(w.cache));
    const warm = exegra(args, envFor(w.cache));
    assert.ok(cold.events.includes('miss parse') && cold.events.includes('store parse'), cold.events.join());
    assert.ok(warm.events.includes('hit parse') && warm.events.includes('hit validate'), warm.events.join());
    assert.equal(warm.stdout, cold.stdout);
    assert.equal(cold.stdout, off.stdout);
    for (const f of entries(w.cache)) fs.rmSync(path.join(w.cache, f));
  }
});

test('changing a specification file or the project config is a miss', () => {
  const w = workspace();
  const args = ['validate', '--project', 'p', '--specs', w.specs];
  exegra(args, envFor(w.cache));
  assert.ok(exegra(args, envFor(w.cache)).events.includes('hit parse'));
  // The specification file: a change of content, not of a modification time.
  fs.writeFileSync(w.spec, PLATFORM.replace('\n', '\n// an added comment\n'));
  const edited = exegra(args, envFor(w.cache));
  assert.ok(edited.events.includes('miss parse'), edited.events.join());
  // The project config names another file as the specification.
  fs.writeFileSync(path.join(w.specs, 'p', 'other.jsonc'), PLATFORM.replace('\n', '\n// another file\n// and more\n'));
  fs.rmSync(w.spec);
  fs.writeFileSync(w.config, '{ "spec": "other.jsonc" }\n');
  const moved = exegra(args, envFor(w.cache));
  assert.ok(moved.events.includes('miss parse'), moved.events.join());
  assert.ok(exegra(args, envFor(w.cache)).events.includes('hit parse'));
});

test('editing an Exegra derivation source is a miss', () => {
  const root = tmp();
  fs.cpSync(path.join(REPO, 'src', 'core'), path.join(root, 'src', 'core'), { recursive: true });
  fs.cpSync(path.join(REPO, 'src', 'engine', 'lean'), path.join(root, 'src', 'engine', 'lean'), { recursive: true });
  fs.copyFileSync(path.join(REPO, 'package.json'), path.join(root, 'package.json'));
  fs.symlinkSync(path.join(REPO, 'node_modules'), path.join(root, 'node_modules'), 'junction');
  const before = derivationSourceHash(root);
  const script = path.join(root, 'derive.mjs');
  fs.writeFileSync(script, "import { parseSpec } from './src/core/parse.js';\nimport fs from 'node:fs';\nconst r = parseSpec(fs.readFileSync(process.argv[2], 'utf8'));\nprocess.stdout.write(String(r.model.entities.size));\n");
  const spec = path.join(root, 'spec.jsonc');
  fs.writeFileSync(spec, PLATFORM);
  const cache = path.join(root, 'cache');
  const run = () => {
    const r = spawnSync(process.execPath, [script, spec], { cwd: root, env: envFor(cache), encoding: 'utf8' });
    assert.equal(r.status, 0, r.stderr);
    return (r.stderr.match(/exegra-cache: .*/g) ?? []).map((l) => l.slice(14));
  };
  assert.ok(run().includes('miss parse'));
  assert.ok(run().includes('hit parse'));
  fs.appendFileSync(path.join(root, 'src', 'core', 'own.js'), '\n// edited\n');
  assert.notEqual(derivationSourceHash(root), before);
  assert.ok(run().includes('miss parse'), 'a changed derivation source does not reuse the entry');
  assert.ok(run().includes('hit parse'));
});

test('a damaged entry is a miss and never an error and is replaced', () => {
  const w = workspace();
  const args = ['validate', '--project', 'p', '--specs', w.specs];
  const cold = exegra(args, envFor(w.cache));
  for (const damage of [
    (/** @type {Buffer} */ b) => b.subarray(0, Math.floor(b.length / 2)),
    (/** @type {Buffer} */ b) => { const c = Buffer.from(b); c[c.length - 10] ^= 0x55; return c; },
    () => Buffer.from('not an entry'),
    () => Buffer.alloc(0),
  ]) {
    for (const f of entries(w.cache)) fs.writeFileSync(path.join(w.cache, f), damage(fs.readFileSync(path.join(w.cache, f))));
    const r = exegra(args, envFor(w.cache));
    assert.equal(r.status, 0);
    assert.equal(r.stdout, cold.stdout);
    assert.ok(r.events.includes('miss parse'), r.events.join());
    assert.ok(exegra(args, envFor(w.cache)).events.includes('hit parse'), 'the damaged entry was rewritten');
  }
});

test('concurrent processes on one cache all succeed with the same output', async () => {
  const w = workspace();
  const args = ['claims', '--project', 'p', '--specs', w.specs];
  const once = (/** @type {Record<string, string>} */ env) => new Promise((resolve) => {
    const p = spawn(process.execPath, [path.join(REPO, 'cli', 'exegra.js'), ...args], { cwd: REPO, env });
    let out = '';
    p.stdout.on('data', (d) => { out += d; });
    p.stderr.resume();
    p.on('close', (status) => resolve({ status, out }));
  });
  const runs = /** @type {{status: number, out: string}[]} */ (await Promise.all(Array.from({ length: 4 }, () => once(envFor(w.cache)))));
  assert.deepEqual(runs.map((r) => r.status), [0, 0, 0, 0]);
  assert.equal(new Set(runs.map((r) => r.out)).size, 1);
  assert.equal(entries(w.cache).length, 2, 'one parse entry and one validate entry');
  assert.deepEqual(fs.readdirSync(w.cache).filter((f) => f.endsWith('.tmp')), []);
  const off = exegra(args, envFor(w.cache, { EXEGRA_NO_CACHE: '1' }));
  assert.equal(off.stdout, runs[0].out);
});

test('the encoding reproduces Maps and Sets and null prototypes and negative zero and shared references and cycles', () => {
  const shared = { n: 1 };
  const bare = Object.create(null);
  bare.k = [shared, -0, Infinity, NaN, undefined];
  const cyc = /** @type {any} */ ({ name: 'c' });
  cyc.self = cyc;
  const value = /** @type {any} */ ({ m: new Map([['a', shared], [{ x: 1 }, bare]]), s: new Set([1, 'two']), bare, cyc, tag: ['a', 1], n: null });
  Object.defineProperty(value, '__proto__', { value: 5, enumerable: true, writable: true, configurable: true });
  const back = decode(encode(value));
  assert.equal(back.m.get('a'), back.bare.k[0], 'shared references stay shared');
  assert.equal(Object.getPrototypeOf(back.bare), null);
  assert.ok(Object.is(back.bare.k[1], -0));
  assert.equal(back.bare.k[2], Infinity);
  assert.ok(Number.isNaN(back.bare.k[3]));
  assert.ok(4 in back.bare.k && back.bare.k[4] === undefined);
  assert.equal(back.cyc.self, back.cyc);
  assert.deepEqual([...back.s], [1, 'two']);
  assert.deepEqual(back.tag, ['a', 1]);
  assert.equal(Object.getOwnPropertyDescriptor(back, '__proto__')?.value, 5);
  assert.throws(() => encode({ f() {} }), /function/);
  assert.throws(() => encode(new Date()), /class/);
});
