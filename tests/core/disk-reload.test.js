// The browser app re-derives the model when a product file changes on disk (WG-5041): the workspace
// watcher reports a changed, added or removed product file as the file 'products', and the session's
// reload (src/app/disk-reload.js) takes the product layers of a fresh read of the project.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { Project } from '../../src/core/project.js';
import { createWorkspace } from '../../tools/workspace.js';
import { layersOf, reloadFromDisk } from '../../src/app/disk-reload.js';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const FIXTURES = path.join(HERE, '..', 'fixtures', 'layers');
const PLATFORM = fs.readFileSync(path.join(FIXTURES, 'platform.jsonc'), 'utf8');
const BADGES = fs.readFileSync(path.join(FIXTURES, 'products', 'badges.jsonc'), 'utf8');
const EXTRA = BADGES.replace('"types": [', '"types": [\n    { "id": "badges__extra", "name": "Extra", "kind": "enum", "values": ["x"] },');

/** A project "layered" whose product files are the .jsonc files of the directory products/, beside the platform. @param {(ctx: {ws: any, products: string}) => Promise<void>} body */
async function withProject(body) {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-disk-reload-'));
  try {
    const specs = path.join(dir, 'specs');
    const products = path.join(dir, 'products');
    fs.mkdirSync(path.join(specs, 'layered'), { recursive: true });
    fs.mkdirSync(products);
    fs.writeFileSync(path.join(dir, 'platform.jsonc'), PLATFORM);
    fs.writeFileSync(path.join(specs, 'layered', 'project.jsonc'), JSON.stringify({ spec: '../../platform.jsonc', products: ['../../products'] }));
    await body({ ws: createWorkspace(specs), products });
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
}

/** Waits for the next change the subscription reports. @param {any[]} changes @param {number} had */
async function nextChange(changes, had) {
  for (let i = 0; i < 60 && changes.length === had; i++) await new Promise((r) => setTimeout(r, 50));
  return changes[had];
}

test('an added then changed then removed product file is reported by the watcher and re-derives the session model', () =>
  withProject(async ({ ws, products }) => {
    const first = await ws.read('layered');
    const project = new Project({ name: 'layered', specText: first.spec.text, layoutText: null, layers: layersOf(first) });
    assert.equal(project.model?.entities.has('badges__badge'), false, 'no product file yet');

    /** @type {any[]} */
    const changes = [];
    const stop = ws.watch('layered', (c) => changes.push(c));
    try {
      await new Promise((r) => setTimeout(r, 100));
      const reload = async (/** @type {number} */ had) => {
        const change = await nextChange(changes, had);
        assert.equal(change?.file, 'products');
        return reloadFromDisk(project, 'products', await ws.read('layered'));
      };

      fs.writeFileSync(path.join(products, 'badges.jsonc'), BADGES);
      assert.equal((await reload(0)).ok, true);
      assert.ok(project.model?.entities.has('badges__badge'), 'an added product file enters the model');
      assert.equal(project.model?.entities.has('badges__extra'), false);

      fs.writeFileSync(path.join(products, 'badges.jsonc'), EXTRA);
      assert.equal((await reload(1)).ok, true);
      assert.ok(project.model?.entities.has('badges__extra'), 'a changed product file is re-derived');

      fs.rmSync(path.join(products, 'badges.jsonc'));
      assert.equal((await reload(2)).ok, true);
      assert.equal(project.model?.entities.has('badges__badge'), false, 'a removed product file leaves the model');
    } finally {
      stop();
    }
  }));

test('a product file that does not parse keeps the last valid model and the next good read adopts it', () =>
  withProject(async ({ ws, products }) => {
    fs.writeFileSync(path.join(products, 'badges.jsonc'), BADGES);
    const first = await ws.read('layered');
    const project = new Project({ name: 'layered', specText: first.spec.text, layoutText: null, layers: layersOf(first) });
    assert.ok(project.model?.entities.has('badges__badge'));
    const hash = project.layeredHash;

    fs.writeFileSync(path.join(products, 'badges.jsonc'), '{ "product": ');
    reloadFromDisk(project, 'products', await ws.read('layered'));
    assert.ok(project.errorCount > 0 || project.layeredHash !== hash, 'the broken product file is seen');

    fs.writeFileSync(path.join(products, 'badges.jsonc'), EXTRA);
    const r = reloadFromDisk(project, 'products', await ws.read('layered'));
    assert.equal(r.ok, true);
    assert.ok(project.model?.entities.has('badges__extra'));
  }));

test('a reload of the specification keeps the product layers of the read', async () => {
  const layers = [{ file: 'badges.jsonc', text: BADGES, hash: 'x', platform: { declared: '../platform.jsonc', matches: true, expected: '../platform.jsonc' } }];
  const project = new Project({ specText: PLATFORM, layers: layersOf({ layers }) });
  const r = reloadFromDisk(project, 'spec', { spec: { text: PLATFORM.replace('"name": "', '"name": "Renamed ') }, layers });
  assert.equal(r.ok, true);
  assert.ok(project.model?.entities.has('badges__badge'));
});
