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

test('stepping a simulation sends a labelled marker along the edge from sender to receiver', { tag: '@full' }, async ({ page }) => {
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

  // Steps 0-4: the session opens the project (read, opened, watch) before the edit arrives (WG-5733).
  for (let i = 0; i <= 4; i++) await ex(page, `session.simStep();`);
  await page.waitForTimeout(400);

  // Step 5: the edit request comes in from outside.
  await ex(page, `session.simStep();`);
  const first = /** @type {any[]} */ (await ex(page, `return view.getFlows();`));
  expect(first.map((f) => [f.kind, f.to])).toEqual([['enter', 'composition-root']]);
  await expect(page.locator('.scene-flow-label--enter')).toHaveCount(1);
  await expect(page.getByTestId('sim-flow')).toHaveText(/outside \(scenario\) → Composition root/);

  // Step 6: the operation travels along the declared edge to the transaction system, and moves.
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

  // Step 16: the save goes from the session to the persistence client, along the relationship that connects them.
  for (let i = 7; i <= 16; i++) await ex(page, `session.simStep();`);
  const save = /** @type {any[]} */ (await ex(page, `return view.getFlows().filter((f) => f.event === 'Write intended');`));
  expect(save.map((f) => [f.kind, f.from, f.to])).toEqual([['edge', 'session', 'persistence-client']]);
  await expect(page.locator('.scene-flow-label--edge')).toHaveText('Write intended');
  await expect(page.getByTestId('sim-flow')).toHaveText(/Application session → Persistence client$/);
});
