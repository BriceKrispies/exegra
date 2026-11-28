// Further browser-level checks: containment navigation, id renames, external
// file changes and conflicts, and the benchmark scene.
import { test, expect } from '@playwright/test';
import fs from 'node:fs';
import path from 'node:path';
import { ROOT, SCRATCH, resetScratch, readScratch } from './scratch.js';

const SHOTS = path.join(ROOT, 'screenshots');
fs.mkdirSync(SHOTS, { recursive: true });

/** @type {string[]} */
let pageErrors = [];

test.beforeEach(async ({ page }) => {
  resetScratch('multiplayer');
  pageErrors = [];
  page.on('pageerror', (e) => pageErrors.push(e.message));
});

test.afterEach(() => {
  expect(pageErrors, 'no uncaught errors in the page').toEqual([]);
});

/** @param {import('@playwright/test').Page} page */
async function open(page) {
  await page.goto(`/?project=${SCRATCH.multiplayer}`);
  await page.waitForFunction((name) => {
    const x = /** @type {any} */ (window).__exegra;
    return x?.session.projectName === name && x.session.model && x.view.getStats().nodes > 0;
  }, SCRATCH.multiplayer);
  await page.waitForTimeout(500);
}

/** @param {import('@playwright/test').Page} page @param {string} body */
const ex = (page, body) => page.evaluate(`(() => { const { session, view } = window.__exegra; ${body} })()`);

/** @param {import('@playwright/test').Page} page @param {string} id */
async function clickEntity(page, id) {
  const pt = /** @type {any} */ (await ex(page, `return view.screenPoint(${JSON.stringify(id)});`));
  expect(pt, `entity ${id} has a screen position`).not.toBeNull();
  await page.mouse.click(pt.x, pt.y);
}

/**
 * A screen point that picks the container itself: its front edge, nudged sideways when a relationship line crosses
 * the default point (the layout decides where lines run).
 * @param {import('@playwright/test').Page} page @param {string} id
 */
async function containerPoint(page, id) {
  const base = /** @type {any} */ (await ex(page, `return view.screenPoint(${JSON.stringify(id)});`));
  for (const dx of [0, -60, 60, -120, 120, -180, 180]) {
    await page.mouse.click(base.x + dx, base.y);
    const picked = await ex(page, `return session.selection ?? null;`);
    if (picked === id || (Array.isArray(picked) && picked.length === 1 && picked[0] === id)) return { x: base.x + dx, y: base.y };
  }
  throw new Error(`no point on the front edge of ${id} picks it`);
}

const waitSaved = (/** @type {import('@playwright/test').Page} */ page) =>
  page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.saveState === 'saved');

test('nested subsystems collapse, expand and isolate without changing the model', async ({ page }) => {
  await open(page);
  const before = /** @type {any} */ (await ex(page, `return { hash: session.project.semanticHash, rev: session.project.revision, nodes: session.scene.nodes.length };`));
  // Double-click the subsystem container: it collapses to one node and its relationships are lifted onto it.
  const pt = await containerPoint(page, 'data');
  await page.mouse.dblclick(pt.x, pt.y);
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.ui.collapsed.has('data'));
  const collapsed = /** @type {any} */ (await ex(page, `return { ids: session.scene.nodes.map((n) => n.id), lifted: session.scene.edges.filter((e) => e.lifted).length, notes: session.scene.notes.join(' ') };`));
  expect(collapsed.ids).toContain('data');
  expect(collapsed.ids).not.toContain('game-database');
  expect(collapsed.lifted).toBeGreaterThan(0);
  expect(collapsed.notes).toMatch(/collapsed block/);
  await ex(page, `session.toggleCollapsed('data');`);
  expect(await ex(page, `return session.scene.nodes.length;`)).toBe(before.nodes);
  // Isolate a subsystem: only its subtree is drawn.
  await ex(page, `session.setIsolate('game-runtime');`);
  const isolated = /** @type {string[]} */ (await ex(page, `return session.scene.nodes.map((n) => n.id);`));
  expect(isolated).toEqual(expect.arrayContaining(['game-runtime', 'game-coordinator']));
  expect(isolated).not.toContain('web-client');
  await ex(page, `session.setIsolate(null);`);
  // None of this is a model change.
  const after = /** @type {any} */ (await ex(page, `return { hash: session.project.semanticHash, rev: session.project.revision };`));
  expect(after).toEqual({ hash: before.hash, rev: before.rev });
  // Top-down orthographic mode and fit-to-selection work on the same scene.
  await page.getByTestId('camera-top').click();
  expect((/** @type {any} */ (await ex(page, `return view.getCamera();`))).mode).toBe('top');
  await page.waitForTimeout(300);
  await clickEntity(page, 'api-service');
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.selection === 'api-service');
  await page.getByTestId('fit').click();
  await page.waitForTimeout(600);
  await page.screenshot({ path: path.join(SHOTS, 'test-top-view.png') });
  await page.getByTestId('camera-perspective').click();
  expect((/** @type {any} */ (await ex(page, `return view.getCamera();`))).mode).toBe('perspective');
});

test('renaming an id rewrites every reference in the source', async ({ page }) => {
  await open(page);
  await ex(page, `session.select('game-database');`);
  await page.getByTestId('inspector').getByRole('button', { name: /rename id/i }).click();
  await page.getByTestId('rename-id').fill('state-store');
  await page.getByTestId('rename-submit').click();
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.model.entities.has('state-store'));
  expect(await ex(page, `return session.project.errorCount;`)).toBe(0);
  expect(await ex(page, `return session.selection;`)).toBe('state-store');
  await waitSaved(page);
  const text = /** @type {string} */ (readScratch('multiplayer', 'spec.jsonc'));
  expect(text).not.toMatch(/"game-database"/);
  expect(text).toContain('"to": "state-store"');
});

test('external file changes reload; a concurrent change is a conflict and never a silent overwrite', async ({ page }) => {
  await open(page);
  const file = path.join(ROOT, 'specs', SCRATCH.multiplayer, 'spec.jsonc');
  const original = fs.readFileSync(file, 'utf8');
  const name = /** @type {string} */ (await ex(page, `return session.model.entities.get('web-client').data.name;`));

  // 1. Another program edits the file: the application notices and reloads the model and the scene.
  const external = original.replace(`"name": ${JSON.stringify(name)}`, '"name": "Browser client"');
  expect(external).not.toBe(original);
  fs.writeFileSync(file, external);
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.model.entities.get('web-client').data.name === 'Browser client');
  await expect(page.locator('.scene-label[data-entity-id="web-client"]')).toContainText('Browser client');

  // 2. The file breaks on disk: the problem is reported and the last valid model is kept.
  fs.writeFileSync(file, external.replace('"components": [', '"components": '));
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.log.some((/** @type {any} */ l) => l.kind === 'error' && /syntax errors/.test(l.message)));
  expect(await ex(page, `return session.model.entities.get('web-client').data.name;`)).toBe('Browser client');
  expect(await ex(page, `return session.project.errorCount;`)).toBe(0);

  // 3. The disk holds something this session has not loaded. An edit here must not overwrite it.
  fs.writeFileSync(file, external);
  await page.route('**/__exegra/events*', (r) => r.abort());   // this session no longer hears about external changes
  await page.reload();
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra?.session.model);
  const theirs = external.replace('"name": "Browser client"', '"name": "Edited elsewhere"');
  fs.writeFileSync(file, theirs);
  await ex(page, `session.apply({ type: 'SetProperty', id: 'shared-cache', property: 'name', value: 'Mine' }, { label: 'Local edit' });`);
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.saveState === 'conflict');
  expect(fs.readFileSync(file, 'utf8'), 'the file on disk was not overwritten').toBe(theirs);
  await expect(page.getByTestId('save-state')).toContainText(/conflict/i);
  // Explicit resolution: take the version on disk.
  await page.getByTestId('save-state').click();
  await page.getByText(/reload from disk/i).first().click();
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.saveState === 'saved');
  expect(await ex(page, `return session.model.entities.get('web-client').data.name;`)).toBe('Edited elsewhere');
  expect(fs.readFileSync(file, 'utf8')).toBe(theirs);
  // Adopting the disk version ends the undo history (undo would overwrite the newer file) and says so.
  expect(await ex(page, `return session.project.canUndo;`)).toBe(false);
  expect(await ex(page, `return session.log.some((l) => l.kind === 'info' && /in-memory version was replaced/.test(l.message));`)).toBe(true);
  pageErrors = pageErrors.filter((m) => !/EventSource|events/.test(m));
});

test('benchmark specification with hundreds of entities loads and reports render statistics', async ({ page }) => {
  await page.goto('/?project=benchmark');
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra?.view.getStats().nodes > 0, null, { timeout: 30_000 });
  // A large model opens as a subsystem overview; open every subsystem to draw all of it.
  const overview = /** @type {number} */ (await ex(page, `return session.scene.nodes.length;`));
  expect(overview).toBeLessThan(50);
  await ex(page, `for (const id of [...session.ui.collapsed]) session.toggleCollapsed(id);`);
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.view.getStats().nodes > 300, null, { timeout: 30_000 });
  await page.waitForTimeout(800);
  const info = /** @type {any} */ (await ex(page, `return { stats: view.getStats(), components: session.model.byKind.component.length, relationships: session.model.byKind.relationship.length, illustrative: session.model.system.data.illustrative };`));
  expect(info.components).toBeGreaterThanOrEqual(300);
  expect(info.relationships).toBeGreaterThanOrEqual(400);
  expect(info.stats.nodes).toBe(info.components);
  expect(info.stats.edges).toBe(info.relationships);
  expect(info.illustrative).toBe(true);
  await expect(page.getByTestId('render-stats')).toContainText(/draw calls/i);
  // Selection stays accurate in a dense scene.
  await clickEntity(page, 'svc-05-10');
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.selection === 'svc-05-10');
  // A transaction and re-projection of ~400 components stays well inside interactive time.
  const t = /** @type {number} */ (await page.evaluate(() => {
    const { session } = /** @type {any} */ (window).__exegra;
    const t0 = performance.now();
    session.project.apply({ type: 'SetProperty', id: 'svc-05-10', property: 'name', value: 'Renamed' }, { origin: 'test' });
    session.project.undo();
    return performance.now() - t0;
  }));
  expect(t).toBeLessThan(2000);
  await page.screenshot({ path: path.join(SHOTS, 'test-benchmark.png') });
});

test('stepping a simulation sends a labelled marker along the edge from sender to receiver', async ({ page }) => {
  // Exegra's own edit scenario, in its architecture view with every subsystem open.
  await page.goto('/?project=exegra');
  await page.waitForFunction(() => {
    const x = /** @type {any} */ (window).__exegra;
    return x?.session.projectName === 'exegra' && x.session.model && x.view.getStats().nodes > 0;
  }, null, { timeout: 30_000 });
  await ex(page, `session.setView('architecture'); for (const id of [...session.ui.collapsed]) session.toggleCollapsed(id); session.simLoad('visual-edit-flow');`);
  // The run executes in a worker; stepping starts once its trace has arrived.
  await page.waitForFunction(() => !!(/** @type {any} */ (window).__exegra.session.sim.simulation), null, { timeout: 30_000 });
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.view.getStats().nodes >= 60, null, { timeout: 30_000 });
  await page.waitForTimeout(600);

  // Step 0: the edit request comes in from outside.
  await ex(page, `session.simStep();`);
  const first = /** @type {any[]} */ (await ex(page, `return view.getFlows();`));
  expect(first.map((f) => [f.kind, f.to])).toEqual([['enter', 'composition-root']]);
  await expect(page.locator('.scene-flow-label--enter')).toHaveCount(1);
  await expect(page.getByTestId('sim-flow')).toHaveText(/outside \(scenario\) → Composition root/);

  // Step 1: the operation travels along the declared edge to the transaction system, and moves.
  await page.waitForTimeout(1600);
  await ex(page, `session.simStep();`);
  const a = /** @type {any[]} */ (await ex(page, `return view.getFlows();`));
  expect(a.map((f) => [f.kind, f.from, f.to, f.edge, f.reverse])).toEqual([['edge', 'composition-root', 'transactions', 'composition-root-submits-edits-transactions', false]]);
  const label = page.locator('.scene-flow-label--edge');
  await expect(label).toHaveText('Operation submitted');
  const p0 = await label.boundingBox();
  await page.waitForTimeout(450);
  const b = /** @type {any[]} */ (await ex(page, `return view.getFlows();`));
  const p1 = await label.boundingBox();
  expect(b[0].progress).toBeGreaterThan(a[0].progress);
  expect(p0 && p1 && Math.hypot(p1.x - p0.x, p1.y - p0.y)).toBeGreaterThan(5);
  await expect(page.getByTestId('sim-flow')).toHaveText(/Composition root → Transaction system$/);
  await page.screenshot({ path: path.join(SHOTS, 'test-sim-flow-edge.png') });

  // Step 9: the save goes from the session to the persistence client, along the relationship that connects them.
  for (let i = 2; i <= 9; i++) await ex(page, `session.simStep();`);
  const save = /** @type {any[]} */ (await ex(page, `return view.getFlows().filter((f) => f.event === 'Write intended');`));
  expect(save.map((f) => [f.kind, f.from, f.to])).toEqual([['edge', 'session', 'persistence-client']]);
  await expect(page.locator('.scene-flow-label--edge')).toHaveText('Write intended');
  await expect(page.getByTestId('sim-flow')).toHaveText(/Application session → Persistence client$/);
});
