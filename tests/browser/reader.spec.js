// Browser tests of the reader surface: a view of the reader projection replaces the scene
// with a page, and its links select entities through the session.
import { test, expect } from '@playwright/test';
import { SCRATCH, resetScratch } from './scratch.js';

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
async function open(page) {
  await page.goto(`/?project=${SCRATCH.exegra}`);
  await page.waitForFunction((name) => {
    const x = /** @type {any} */ (window).__exegra;
    return x?.session.projectName === name && x.session.model;
  }, SCRATCH.exegra);
}

/** @param {import('@playwright/test').Page} page @param {string} id */
const setView = (page, id) => page.evaluate((v) => /** @type {any} */ (window).__exegra.session.setView(v), id);

test('reader view replaces the scene and its links select entities', async ({ page }) => {
  await open(page);
  await setView(page, 'reader');
  const reader = page.locator('#reader-host');
  await expect(reader).toBeVisible();
  await expect(page.locator('#scene-controls')).toBeHidden();
  await expect(reader.locator('.rd-h1')).toHaveText('Reader');

  // The index opens a kind's table; a row's link selects that entity.
  await reader.locator('.rd-kind', { hasText: 'Component' }).first().click();
  await expect(reader.locator('.rd-h1')).toHaveText('Component');
  const first = reader.locator('.rd-table tbody .rd-link').first();
  const id = await first.getAttribute('data-entity');
  await first.click();
  await expect.poll(() => page.evaluate(() => /** @type {any} */ (window).__exegra.session.selection)).toBe(id);
  await expect(first).toHaveAttribute('aria-current', 'true');

  // Leaving the reader view brings the scene back.
  await setView(page, 'architecture');
  await expect(reader).toBeHidden();
  await expect(page.locator('#scene-controls')).toBeVisible();
});

test('reader page follows an edit of the model', async ({ page }) => {
  await open(page);
  await setView(page, 'reader');
  const reader = page.locator('#reader-host');
  await expect(reader.locator('.rd-lede, .rd-prose').first()).toBeVisible();
  await page.evaluate(() => {
    const { session } = /** @type {any} */ (window).__exegra;
    session.apply([{ type: 'SetProperty', id: session.model.system.id, property: 'description', value: 'Edited for the reader test.' }], { label: 'Edit description' });
  });
  await expect(reader).toContainText('Edited for the reader test.');
});
