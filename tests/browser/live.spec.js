// Live mode of the simulator panel: the application opens a copy of its own specification, an
// edit is made and saved, and the panel shows those real events, replayed through the
// self-model, on the components responsible for them, with no divergence.
import { test, expect } from '@playwright/test';
import fs from 'node:fs';
import path from 'node:path';
import { SCRATCH, resetScratch, readScratch } from './scratch.js';

const SHOT_DIR = process.env.EXEGRA_SHOT_DIR ?? '';

/** @type {string[]} */
let pageErrors = [];

test.beforeEach(async ({ page }) => {
  resetScratch('exegra');
  pageErrors = [];
  page.on('pageerror', (e) => pageErrors.push(e.message));
  page.on('console', (m) => { if (m.type() === 'error' && !/favicon|404/.test(m.text())) pageErrors.push(m.text()); });
});

test.afterEach(() => {
  expect(pageErrors, 'no uncaught errors in the page').toEqual([]);
});

/** @param {import('@playwright/test').Page} page */
async function openSelf(page) {
  await page.goto(`/?project=${SCRATCH.exegra}`);
  await page.waitForFunction((name) => {
    const x = /** @type {any} */ (window).__exegra;
    return x?.session.projectName === name && x.session.model && x.view.getStats().nodes > 0;
  }, SCRATCH.exegra);
  await page.waitForTimeout(500);
}

/** Run a function against window.__exegra. @param {import('@playwright/test').Page} page @param {string} body */
const ex = (page, body) => page.evaluate(`(() => { const { session, view } = window.__exegra; ${body} })()`);

/** @param {import('@playwright/test').Page} page */
const openSimulation = async (page) => {
  if (await page.getByTestId('sim-live').isVisible()) return;
  await page.getByTestId('tab-btn-simulation').first().click();
  await expect(page.getByTestId('sim-live')).toBeVisible();
};

test('live mode replays an edit and its save through the self-model on the right components without divergence', { tag: '@full' }, async ({ page }) => {
  await openSelf(page);
  // Settle: the change stream is open and nothing is awaited before the edit.
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.traffic.events().some((/** @type {any} */ e) => e.id === 'ws-watch'));

  await openSimulation(page);
  await page.getByTestId('sim-live').click();
  await expect(page.getByTestId('sim-live')).toHaveAttribute('aria-pressed', 'true');

  // A real edit through the transaction pipeline, then its save.
  const before = /** @type {number} */ (await ex(page, `return session.traffic.events().length;`));
  const result = /** @type {any} */ (await ex(page, `return session.apply({ type: 'SetProperty', id: 'session', property: 'name', value: 'Application session (live)' }, { label: 'Rename session' });`));
  expect(result.ok).toBe(true);
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.saveState === 'saved');
  expect(readScratch('exegra', 'spec.jsonc')).toContain('Application session (live)');
  // Wait for the server's change notice of our own write, which the model predicts after the save.
  await page.waitForFunction((n) => {
    const evs = /** @type {any} */ (window).__exegra.session.traffic.events().slice(n);
    return evs.some((/** @type {any} */ e) => e.id === 'external-change-received');
  }, before);
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.live.awaiting.length === 0);

  const live = /** @type {any} */ (await ex(page, `
    const steps = session.sim.simulation.steps;
    const byEvent = {};
    for (const st of steps) (byEvent[st.event.id] ??= []).push({ responsible: st.responsible, fired: st.fired.map((f) => f.transition) });
    const seqs = session.traffic.events().map((e) => e.seq);
    return { divergences: session.live.divergences, ids: steps.map((s) => s.event.id), byEvent, checks: session.sim.checks.filter((c) => !c.holds && !c.pending),
      logicalTime: steps.every((st, i) => st.time === seqs[i] && st.time === st.event.seq) };
  `));
  if (process.env.EXEGRA_DUMP) fs.writeFileSync(process.env.EXEGRA_DUMP, JSON.stringify({ live, stream: await ex(page, 'return session.traffic.forReplay();') }, null, 1));
  expect(live.divergences, 'no divergence between the real run and the self-model').toEqual([]);
  expect(live.checks, 'no failed check on the live trace').toEqual([]);
  expect(live.logicalTime, 'the live trace time is the recorded sequence number').toBe(true);

  // The edit and its save, in the order they really happened, each on the component the model says.
  const order = ['edit-applied', 'commit-notified', 'write-intent', 'write-file-request', 'ws-write', 'ws-write-done', 'write-file-ok', 'save-succeeded'];
  const at = order.map((id) => live.ids.lastIndexOf(id));
  expect(at.every((i) => i >= 0), `every event of the save was recorded: ${order.filter((_, i) => at[i] < 0)}`).toBe(true);
  expect([...at].sort((a, b) => a - b)).toEqual(at);
  const on = (/** @type {string} */ id) => live.byEvent[id].at(-1);
  expect(on('commit-notified').responsible).toContain('session');
  expect(on('write-intent').responsible).toContain('persistence-client');
  expect(on('write-file-request').responsible).toContain('dev-server-plugin');
  expect(on('ws-write').responsible).toContain('workspace-service');
  expect(on('save-succeeded').responsible).toContain('session');
  expect(on('save-succeeded').fired).toContain('session-saved');
  expect(on('edit-applied').fired).toContain('history-edit');

  // The panel shows it: the live status, the request log of the write, no divergence.
  await expect(page.getByTestId('sim-live-status')).toContainText('0 divergences');
  await expect(page.getByTestId('sim-requests')).toContainText('POST /__exegra/write');
  await expect(page.getByTestId('sim-divergences')).toContainText('None');

  if (SHOT_DIR) {
    fs.mkdirSync(SHOT_DIR, { recursive: true });
    await page.screenshot({ path: path.join(SHOT_DIR, 'live-desktop.png') });
    await page.getByTestId('sim-live-status').scrollIntoViewIfNeeded();
    await page.screenshot({ path: path.join(SHOT_DIR, 'live-desktop-status.png') });
    await page.getByTestId('sim-divergences').scrollIntoViewIfNeeded();
    await page.screenshot({ path: path.join(SHOT_DIR, 'live-desktop-divergences.png') });
  }

  // The same panel on a phone: no horizontal scroll, and the source buttons are touch targets.
  await page.setViewportSize({ width: 390, height: 844 });
  await page.waitForTimeout(400);
  await openSimulation(page);
  await page.waitForTimeout(400);
  await expect(page.getByTestId('sim-live-status')).toContainText('0 divergences');
  const box = await page.getByTestId('sim-live').boundingBox();
  expect(box && box.height >= 44 && box.width >= 44, 'the Live button is at least 44 px').toBe(true);
  const overflow = /** @type {number} */ (await page.evaluate(() => document.documentElement.scrollWidth - document.documentElement.clientWidth));
  expect(overflow, 'no horizontal scroll at phone width').toBeLessThanOrEqual(0);
  if (SHOT_DIR) {
    await page.screenshot({ path: path.join(SHOT_DIR, 'live-phone.png') });
    // For the record, not asserted: a view switch, where the model's camera memory still disagrees with the code (WG-4782).
    await page.setViewportSize({ width: 1600, height: 1000 });
    await ex(page, `session.setView('claims');`);
    await page.waitForTimeout(800);
    await openSimulation(page);
    await page.getByTestId('sim-divergences').scrollIntoViewIfNeeded();
    await page.screenshot({ path: path.join(SHOT_DIR, 'live-desktop-view-switch-divergence.png') });
  }
});
