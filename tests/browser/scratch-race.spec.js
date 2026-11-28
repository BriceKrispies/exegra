// WG-5738: `exegra verify` once failed browser references because the development server resolved the application's
// eager glob over specs/ into static imports of the scratch projects' files (zz-test-*/evidence/results.json,
// extracted/facts.json), and a page loaded while another test recreated its scratch project imported a file that was
// momentarily missing. The application no longer globs scratch projects (src/app/session.js), and resetScratch
// resets a project in place without deleting a directory (tests/browser/scratch.js). This test reproduces the old
// failure mode on purpose: it deletes and recreates a whole scratch project, the files the old glob matched
// included, while the application is loaded, and reloads the page in the gap.
import { test, expect } from '@playwright/test';
import fs from 'node:fs';
import path from 'node:path';
import { SCRATCH, SPECS, resetScratch } from './scratch.js';

/** @type {string[]} */
let pageErrors = [];

test.beforeEach(async ({ page }) => {
  resetScratch('multiplayer');
  pageErrors = [];
  page.on('pageerror', (e) => pageErrors.push(e.message));
  page.on('console', (m) => { if (m.type() === 'error' && !/favicon/.test(m.text())) pageErrors.push(m.text()); });
});

test.afterEach(() => {
  expect(pageErrors, 'no uncaught errors in the page').toEqual([]);
});

/** A scratch project of this worker that only this test uses, holding every kind of file the old glob matched. */
const PROBE = path.join(SPECS, `zz-test-recreated-w${Number(process.env.TEST_PARALLEL_INDEX ?? 0) || 0}`);

function createProbe() {
  fs.mkdirSync(path.join(PROBE, 'evidence'), { recursive: true });
  fs.mkdirSync(path.join(PROBE, 'extracted'), { recursive: true });
  fs.writeFileSync(path.join(PROBE, 'spec.jsonc'), '{ "system": { "id": "probe", "name": "Probe" } }\n');
  fs.writeFileSync(path.join(PROBE, 'layout.jsonc'), '{}\n');
  fs.writeFileSync(path.join(PROBE, 'evidence', 'results.json'), '{ "results": {} }\n');
  fs.writeFileSync(path.join(PROBE, 'extracted', 'facts.json'), '{}\n');
  fs.writeFileSync(path.join(PROBE, 'extracted', 'observed.json'), '{}\n');
}

/** @param {import('@playwright/test').Page} page */
async function loaded(page) {
  await page.waitForFunction((name) => {
    const x = /** @type {any} */ (window).__exegra;
    return x?.session.projectName === name && x.session.model && x.view.getStats().nodes > 0;
  }, SCRATCH.multiplayer);
}

// @evidence scratch-projects-outside-app-glob
test('recreating a scratch project while the application is loaded never breaks a page load', { tag: '@full' }, async ({ page }) => {
  createProbe();
  try {
    await page.goto(`/?project=${SCRATCH.multiplayer}`);
    await loaded(page);
    // The page's module graph names no scratch project file: nothing a test deletes is imported by the application.
    const scratchUrls = await page.evaluate(() => performance.getEntriesByType('resource').map((e) => e.name).filter((u) => /\/specs\/zz-test-/.test(decodeURIComponent(u))));
    expect(scratchUrls, 'the application imports no file of a scratch project').toEqual([]);
    for (let round = 0; round < 3; round++) {
      // The old recreation: the whole project removed, a page loaded in the gap, then the project written again.
      fs.rmSync(PROBE, { recursive: true, force: true });
      await page.reload();
      await loaded(page);
      createProbe();
      await page.reload();
      await loaded(page);
    }
    // The recreated project is still a project the persistence service lists: it is reached that way, not by the glob.
    expect(await page.evaluate((name) => /** @type {any} */ (window).__exegra.session.projects.some((/** @type {any} */ p) => p.name === name), path.basename(PROBE))).toBe(true);
  } finally {
    fs.rmSync(PROBE, { recursive: true, force: true });
  }
});
