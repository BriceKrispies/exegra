// The interface at phone and tablet size, driven by touch. Each test is tagged with
// the size it is about; playwright.config.js runs @phone tests in the `phone` project
// (390 by 844, touch) and @tablet tests in the `tablet` project (820 by 1180, touch).
// Everything edits scratch copies (tests/browser/scratch.js), never a shipped project.
import { test, expect } from '@playwright/test';
import fs from 'node:fs';
import path from 'node:path';
import { ROOT, SCRATCH, resetScratch } from './scratch.js';
import { settled } from './settle.js';

const SHOTS = path.join(ROOT, 'screenshots');
fs.mkdirSync(SHOTS, { recursive: true });

/** @typedef {import('@playwright/test').Page} Page */

/** @type {string[]} */
let pageErrors = [];

test.beforeEach(async ({ page }) => {
  resetScratch('exegra');
  resetScratch('multiplayer');
  pageErrors = [];
  page.on('pageerror', (e) => pageErrors.push(e.message));
});

test.afterEach(() => {
  expect(pageErrors, 'no uncaught errors in the page').toEqual([]);
});

/** @param {Page} page @param {'exegra'|'multiplayer'} which */
async function open(page, which) {
  await page.goto(`/?project=${SCRATCH[which]}`);
  await page.waitForFunction((name) => {
    const x = /** @type {any} */ (window).__exegra;
    return x?.session.projectName === name && x.session.model && x.view.getStats().nodes > 0;
  }, SCRATCH[which]);
  await settled(page); // initial fit animation
}

/** Run a function against window.__exegra. @param {Page} page @param {string} body */
const ex = (page, body) => page.evaluate(`(() => { const { session, view } = window.__exegra; ${body} })()`);

/** The page never scrolls sideways. @param {Page} page @param {string} where */
async function expectNoHorizontalScroll(page, where) {
  const m = /** @type {any} */ (await page.evaluate(() => ({
    doc: document.documentElement.scrollWidth, body: document.body.scrollWidth, inner: window.innerWidth,
  })));
  expect(m.doc, `${where}: document scrollWidth ${m.doc} <= innerWidth ${m.inner}`).toBeLessThanOrEqual(m.inner);
  expect(m.body, `${where}: body scrollWidth ${m.body} <= innerWidth ${m.inner}`).toBeLessThanOrEqual(m.inner);
}

/**
 * Every visible interactive element on screen, and the ones smaller than 44 by 44 CSS px.
 * A checkbox or radio button counts at the size of its largest label when that is bigger.
 * @param {Page} page
 * @returns {Promise<{checked: number, offenders: string[]}>}
 */
function smallTargets(page) {
  return page.evaluate(() => {
    const MIN = 44 - 0.5;
    const SEL = 'button, a[href], input:not([type="hidden"]), select, textarea, summary, [role="button"], [role="tab"], [role="menuitem"], [role="option"], [role="treeitem"], [tabindex]:not([tabindex="-1"])';
    /** @param {Element} el */
    const describe = (el) => {
      const h = /** @type {HTMLElement} */ (el);
      const id = h.dataset.testid ? `[data-testid=${h.dataset.testid}]` : h.id ? `#${h.id}` : '';
      const cls = typeof h.className === 'string' && h.className ? `.${h.className.trim().split(/\s+/).join('.')}` : '';
      const text = (h.getAttribute('aria-label') ?? h.textContent ?? '').trim().replace(/\s+/g, ' ').slice(0, 40);
      return `${h.tagName.toLowerCase()}${id}${cls} "${text}"`;
    };
    /** Is any part of the element inside the window and inside every scrolling ancestor? @param {Element} el @param {DOMRect} r */
    const onScreen = (el, r) => {
      let top = Math.max(0, r.top), left = Math.max(0, r.left), bottom = Math.min(window.innerHeight, r.bottom), right = Math.min(window.innerWidth, r.right);
      for (let p = el.parentElement; p && p !== document.body; p = p.parentElement) {
        const cs = getComputedStyle(p);
        if (cs.overflowX === 'visible' && cs.overflowY === 'visible') continue;
        const pr = p.getBoundingClientRect();
        top = Math.max(top, pr.top); left = Math.max(left, pr.left); bottom = Math.min(bottom, pr.bottom); right = Math.min(right, pr.right);
      }
      return bottom - top > 1 && right - left > 1;
    };
    const offenders = [];
    let checked = 0;
    for (const el of document.querySelectorAll(SEL)) {
      if (!el.checkVisibility({ checkOpacity: true, checkVisibilityCSS: true })) continue;
      if (el.closest('[inert]')) continue;
      const r = el.getBoundingClientRect();
      if (r.width === 0 || r.height === 0 || !onScreen(el, r)) continue;
      checked++;
      let w = r.width, h = r.height;
      const input = /** @type {HTMLInputElement} */ (el);
      if (input.tagName === 'INPUT' && (input.type === 'checkbox' || input.type === 'radio')) {
        for (const label of input.labels ?? []) {
          const lr = label.getBoundingClientRect();
          if (lr.width * lr.height > w * h) { w = lr.width; h = lr.height; }
        }
      }
      if (w < MIN || h < MIN) offenders.push(`${describe(el)} ${Math.round(w)}x${Math.round(h)}`);
    }
    return { checked, offenders };
  });
}

/** @param {Page} page @param {string} where */
async function expectTouchTargets(page, where) {
  const r = await smallTargets(page);
  expect(r.checked, `${where}: interactive elements were found`).toBeGreaterThan(0);
  expect(r.offenders, `${where}: controls smaller than 44 by 44 CSS px:\n  ${r.offenders.join('\n  ')}`).toEqual([]);
}

/**
 * The share of the window where the 3D scene is not covered by the interface: sampled on
 * a grid, a point counts when it is on the canvas and outside every visible piece of
 * chrome (app bar, navigation, panels, transport, floating controls, overlay cards, toasts).
 * @param {Page} page
 */
function sceneCoverage(page) {
  return page.evaluate(() => {
    const canvas = /** @type {HTMLElement} */ (document.querySelector('[data-testid="scene-canvas"]'));
    const c = canvas.getBoundingClientRect();
    const chrome = [...document.querySelectorAll('#appbar, #nav, .panel, #transport, #scene-controls, .appbar__history, .overlay__card, .overlay__details--notes, .overlay__illustrative, .toast, .menu-sheet, .appbar__tools')]
      .filter((el) => el.checkVisibility({ checkOpacity: true, checkVisibilityCSS: true }))
      .map((el) => el.getBoundingClientRect());
    const W = window.innerWidth, H = window.innerHeight, N = 40, M = 80;
    let free = 0;
    for (let i = 0; i < N; i++) {
      for (let j = 0; j < M; j++) {
        const x = (i + 0.5) * W / N, y = (j + 0.5) * H / M;
        const onCanvas = x >= c.left && x < c.right && y >= c.top && y < c.bottom;
        if (onCanvas && !chrome.some((r) => x >= r.left && x < r.right && y >= r.top && y < r.bottom)) free++;
      }
    }
    return free / (N * M);
  });
}

/** Ids of components whose drawn position is on an uncovered part of the canvas. @param {Page} page */
async function tappableComponents(page) {
  return /** @type {string[]} */ (await page.evaluate(() => {
    const { session, view } = /** @type {any} */ (window).__exegra;
    const out = [];
    for (const n of session.scene.nodes) {
      if (n.entityKind !== 'component') continue;
      const pt = view.screenPoint(n.id);
      if (!pt) continue;
      const hit = document.elementFromPoint(pt.x, pt.y);
      if (hit instanceof HTMLElement && hit.dataset.testid === 'scene-canvas') out.push(n.id);
    }
    return out;
  }));
}

/** Tap the canvas where an entity is drawn; the point must not be covered. @param {Page} page @param {string} id */
async function tapEntity(page, id) {
  const pt = /** @type {{x: number, y: number}|null} */ (await ex(page, `return view.screenPoint(${JSON.stringify(id)});`));
  expect(pt, `${id} has a screen position`).not.toBeNull();
  const p = /** @type {{x: number, y: number}} */ (pt);
  const hit = await page.evaluate(({ x, y }) => /** @type {HTMLElement|null} */ (document.elementFromPoint(x, y))?.dataset.testid ?? null, p);
  expect(hit, `${id} is drawn on an uncovered part of the scene`).toBe('scene-canvas');
  await page.touchscreen.tap(p.x, p.y);
}

/** @param {Page} page @param {string} id */
const waitSelected = (page, id) => page.waitForFunction((x) => /** @type {any} */ (window).__exegra.session.selection === x, id);

/** The context panel's (or the explorer's) sheet detent. @param {Page} page @param {'context'|'explorer'} which */
const detent = (page, which = 'context') => page.locator(`#panel-${which}`).getAttribute('data-detent');

/** Choose an item from the app bar's overflow menu. @param {Page} page @param {string} testid */
async function overflow(page, testid) {
  await page.getByTestId('appbar-overflow').tap();
  await expect(page.locator('#appbar-tools')).toBeVisible();
  await page.getByTestId(testid).tap();
}

/** Close the open sheet with its close button. @param {Page} page @param {'context'|'explorer'} which */
async function closeSheet(page, which = 'context') {
  // by test id: the explorer's rows also carry data-action="collapse" buttons
  await page.getByTestId(`collapse-${which}`).tap();
  await expect(page.locator(`#panel-${which}`)).toHaveAttribute('data-detent', 'closed');
}

/** Where the page frame's fixed chrome is. @param {Page} page */
function frame(page) {
  return page.evaluate(() => {
    const r = (/** @type {string} */ sel) => { const b = /** @type {HTMLElement} */ (document.querySelector(sel)).getBoundingClientRect(); return [b.x, b.y, b.width, b.height].map(Math.round); };
    return { appbar: r('#appbar'), nav: r('#nav') };
  });
}

/**
 * The document never scrolls: the page is at the top and the app bar and the navigation are
 * exactly where they were with nothing open.
 * @param {Page} page @param {{appbar: number[], nav: number[]}} base @param {string} where
 */
async function expectFrameStill(page, base, where) {
  const s = /** @type {any} */ (await page.evaluate(() => ({
    scrollTop: /** @type {Element} */ (document.scrollingElement).scrollTop, scrollY: window.scrollY,
    app: /** @type {HTMLElement} */ (document.getElementById('app')).scrollTop,
  })));
  expect(s.scrollTop, `${where}: document.scrollingElement.scrollTop`).toBe(0);
  expect(s.scrollY, `${where}: window.scrollY`).toBe(0);
  expect(s.app, `${where}: the app frame's scrollTop`).toBe(0);
  expect(await frame(page), `${where}: the app bar and the navigation have not moved`).toEqual(base);
}

/** Find an entity through the full-screen search and pick it. @param {Page} page @param {string} id */
async function searchAndPick(page, id) {
  await page.getByTestId('search-open').tap();
  await page.getByTestId('search-input').fill(id);
  await page.locator(`.search__option[data-entity-id="${id}"]`).tap();
  await waitSelected(page, id);
  await expect(page.getByTestId('search-input')).toBeHidden();
}

test('phone layout has no horizontal scroll and 44 px targets and the scene covers most of the screen', { tag: '@phone' }, async ({ page }) => {
  // This test is about the layout at rest, checked after every sheet change; with motion reduced the sheets
  // land at once instead of after their 300 ms transition (the touch test below keeps the motion on).
  await page.emulateMedia({ reducedMotion: 'reduce' });
  await open(page, 'multiplayer');
  expect(page.viewportSize()).toEqual({ width: 390, height: 844 });

  // With nothing open the scene is the screen.
  await expectNoHorizontalScroll(page, 'initial');
  await expectTouchTargets(page, 'initial');
  const coverage = await sceneCoverage(page);
  expect(coverage, `the uncovered scene is ${(coverage * 100).toFixed(1)}% of the window`).toBeGreaterThanOrEqual(0.6);
  await page.screenshot({ path: path.join(SHOTS, 'test-phone-initial.png') });

  // Every destination at each detent: the page itself never scrolls; at full height no
  // sideways scroll and no small target.
  const base = await frame(page);
  for (const dest of ['explorer', 'inspector', 'simulation', 'verification']) {
    await page.getByTestId(`tab-btn-${dest}`).tap();
    const which = dest === 'explorer' ? 'explorer' : 'context';
    const panel = page.locator(`#panel-${which}`);
    await expect(panel).toHaveAttribute('data-detent', 'half');
    await settled(page); // sheet motion
    await expectFrameStill(page, base, `${dest} at half`);
    await page.locator(`#panel-${which} .panel__handle`).tap();
    await expect(panel).toHaveAttribute('data-detent', 'full');
    await settled(page);
    await expectFrameStill(page, base, `${dest} at full`);
    await expectNoHorizontalScroll(page, dest);
    await expectTouchTargets(page, dest);
    await page.screenshot({ path: path.join(SHOTS, `test-phone-${dest}.png`) });
    await page.locator(`#panel-${which} .panel__handle`).tap(); // full -> peek
    await expect(panel).toHaveAttribute('data-detent', 'peek');
    await settled(page);
    await expectFrameStill(page, base, `${dest} at peek`);
    await closeSheet(page, which);
  }
  // A selection made in code opens the inspector at peek; the frame stays put.
  const any = /** @type {string} */ (await ex(page, `return session.model.byKind.component[0].id;`));
  await ex(page, `session.select(${JSON.stringify(any)});`);
  await expect(page.locator('#panel-context')).toHaveAttribute('data-detent', 'peek');
  await settled(page);
  await expectFrameStill(page, base, 'inspector after a selection');
  await closeSheet(page);
  for (const dest of ['changes', 'diagnostics', 'source', 'realisation']) {
    await page.getByTestId('nav-more').tap();
    await expectTouchTargets(page, 'more menu');
    await page.getByTestId(`more-${dest}`).tap();
    await expect(page.locator(`#tab-${dest}`)).toBeVisible();
    await settled(page);
    await expectFrameStill(page, base, dest);
    await expectNoHorizontalScroll(page, dest);
    await expectTouchTargets(page, dest);
    await page.screenshot({ path: path.join(SHOTS, `test-phone-${dest}.png`) });
    await closeSheet(page);
  }

  // The project and view picker.
  await page.getByTestId('title-picker').tap();
  await expect(page.locator('#appbar-picker')).toBeVisible();
  await expectNoHorizontalScroll(page, 'picker');
  await expectTouchTargets(page, 'picker');
  await page.getByTestId('title-picker').tap();

  // The overflow menu, the search sheet and a dialog.
  await page.getByTestId('appbar-overflow').tap();
  await expectNoHorizontalScroll(page, 'overflow menu');
  await expectTouchTargets(page, 'overflow menu');
  await page.screenshot({ path: path.join(SHOTS, 'test-phone-overflow.png') });
  await page.getByTestId('new-component').tap();
  await expect(page.getByTestId('create-dialog')).toBeVisible();
  const dlg = /** @type {any} */ (await page.getByTestId('create-dialog').boundingBox());
  expect(dlg.width, 'a dialog fills the phone screen').toBeGreaterThanOrEqual(389);
  await expectNoHorizontalScroll(page, 'create dialog');
  await expectTouchTargets(page, 'create dialog');
  await page.getByTestId('dialog-cancel').tap();
  await page.getByTestId('search-open').tap();
  await page.getByTestId('search-input').fill('game');
  await expectNoHorizontalScroll(page, 'search');
  await expectTouchTargets(page, 'search');
});

test('every function is reachable by touch on a phone', { tag: '@phone' }, async ({ page }) => {
  test.setTimeout(240_000);
  await open(page, 'multiplayer');

  // Each destination opens as a sheet; tapping it again closes it.
  for (const dest of ['explorer', 'inspector', 'simulation', 'verification']) {
    const which = dest === 'explorer' ? 'explorer' : 'context';
    await page.getByTestId(`tab-btn-${dest}`).tap();
    await expect(page.locator(`#panel-${which}`)).toHaveAttribute('data-detent', 'half');
    if (which === 'context') await expect(page.locator(`#tab-${dest}`)).toBeVisible();
    await page.getByTestId(`tab-btn-${dest}`).tap();
    await expect(page.locator(`#panel-${which}`)).toHaveAttribute('data-detent', 'closed');
  }

  // Search selects and frames an entity and shows it in the inspector at peek.
  await searchAndPick(page, 'game-database');
  await expect(page.locator('#panel-context')).toHaveAttribute('data-detent', 'peek');
  const dbName = /** @type {string} */ (await ex(page, `return session.model.entities.get('game-database').data.name;`));
  await expect(page.locator('#panel-context [data-summary]')).toContainText(dbName);
  await closeSheet(page);

  // Select by tapping the canvas.
  await page.getByTestId('fit').tap();
  await settled(page);
  const visible = await tappableComponents(page);
  expect(visible.length, 'some components are drawn on the uncovered scene').toBeGreaterThan(1);
  const target = visible.includes('api-service') ? 'api-service' : visible[0];
  await tapEntity(page, target);
  await waitSelected(page, target);
  await expect(page.locator('#panel-context')).toHaveAttribute('data-detent', 'peek');

  // Drag up to edit a property in the inspector, then undo and redo from the floating controls.
  await page.locator('#panel-context .panel__handle').tap();
  await expect(page.locator('#panel-context')).toHaveAttribute('data-detent', 'half');
  const name = page.getByTestId('inspector').locator('[data-prop="name"] input');
  await name.tap();
  await name.fill('Touched name');
  await name.press('Enter');
  await page.waitForFunction((id) => /** @type {any} */ (window).__exegra.session.model.entities.get(id).data.name === 'Touched name', target);
  await closeSheet(page);
  await page.getByTestId('undo').tap();
  await page.waitForFunction((id) => /** @type {any} */ (window).__exegra.session.model.entities.get(id).data.name !== 'Touched name', target);
  await page.getByTestId('redo').tap();
  await page.waitForFunction((id) => /** @type {any} */ (window).__exegra.session.model.entities.get(id).data.name === 'Touched name', target);

  // Create, from the overflow menu, in a full-screen dialog.
  await overflow(page, 'new-component');
  await expect(page.getByTestId('create-dialog')).toBeVisible();
  await page.getByTestId('create-name').tap();
  await page.getByTestId('create-name').fill('Pocket service');
  await page.getByTestId('create-submit').tap();
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.model.entities.has('pocket-service'));

  // Connect mode: two taps on the canvas open the connect dialog.
  if (await detent(page) !== 'closed') await closeSheet(page);
  await page.getByTestId('fit').tap();
  await settled(page);
  await overflow(page, 'mode-connect');
  await expect(page.getByTestId('connect-indicator')).toBeVisible();
  const ends = await tappableComponents(page);
  expect(ends.length, 'two components can be tapped').toBeGreaterThan(1);
  await tapEntity(page, ends[0]);
  await tapEntity(page, ends[1]);
  await expect(page.getByTestId('connect-dialog')).toBeVisible();
  await expect(page.getByTestId('connect-from')).toHaveValue(ends[0]);
  await expect(page.getByTestId('connect-to')).toHaveValue(ends[1]);
  await page.getByTestId('dialog-cancel').tap();
  await expect(page.getByTestId('connect-indicator')).toBeHidden();

  // Delete with the cascade preview, then undo.
  await searchAndPick(page, 'game-database');
  await overflow(page, 'delete-entity');
  await expect(page.getByTestId('delete-dialog')).toContainText('telemetry-reads-game-database');
  await page.getByTestId('delete-cascade').tap();
  await page.getByTestId('delete-submit').tap();
  await page.waitForFunction(() => !/** @type {any} */ (window).__exegra.session.model.entities.has('game-database'));
  if (await detent(page) === 'half' || await detent(page) === 'full') await closeSheet(page);
  await page.getByTestId('undo').tap();
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.model.entities.has('game-database'));

  // Rename an id from the inspector.
  await searchAndPick(page, 'game-database');
  await page.locator('#panel-context .panel__handle').tap();
  await page.getByTestId('rename-id-open').tap();
  await page.getByTestId('rename-id').fill('state-store');
  await page.getByTestId('rename-submit').tap();
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.model.entities.has('state-store'));
  await closeSheet(page);

  // Explorer: select a row, then collapse, isolate and hide from its actions.
  await page.getByTestId('tab-btn-explorer').tap();
  const row = page.locator('#explorer [data-entity-id="data"]').first();
  await row.tap();
  await waitSelected(page, 'data');
  await row.locator('[data-action="collapse"]').tap();
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.ui.collapsed.has('data'));
  await row.locator('[data-action="collapse"]').tap();
  await row.locator('[data-action="isolate"]').tap();
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.ui.isolate === 'data');
  await row.locator('[data-action="isolate"]').tap();
  await row.locator('[data-action="visibility"]').tap();
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.ui.hidden.has('data'));
  await row.locator('[data-action="visibility"]').tap();
  await closeSheet(page, 'explorer');

  // Layout, camera, legend and render statistics.
  await page.getByTestId('appbar-overflow').tap();
  await page.getByTestId('layout-select').tap();
  await page.getByTestId('layout-select').selectOption('packed');
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.layout.requested === 'packed');
  await page.getByTestId('toggle-legend').tap();
  await expect(page.locator('.overlay__card--legend')).toBeVisible();
  await overflow(page, 'toggle-render-stats');
  await expect(page.getByTestId('render-stats')).toBeVisible();
  await page.getByTestId('camera-top').tap();
  expect((/** @type {any} */ (await ex(page, `return view.getCamera();`))).mode).toBe('top');
  await page.getByTestId('camera-perspective').tap();
  expect((/** @type {any} */ (await ex(page, `return view.getCamera();`))).mode).toBe('perspective');
  await overflow(page, 'toggle-legend');
  await overflow(page, 'toggle-render-stats');
  await expect(page.locator('.overlay__card--legend')).toBeHidden();

  // Simulation: load a scenario in the Simulate sheet, then step with the docked transport.
  await page.getByTestId('tab-btn-simulation').tap();
  await page.getByTestId('sim-scenario').tap();
  await page.getByTestId('sim-scenario').selectOption('command-happy-path');
  await page.waitForFunction(() => !!(/** @type {any} */ (window).__exegra.session.sim.simulation));
  await closeSheet(page);
  const transport = page.locator('#transport');
  await expect(transport).toBeVisible();
  const tr = /** @type {any} */ (await transport.boundingBox());
  const nav = /** @type {any} */ (await page.locator('#nav').boundingBox());
  expect(tr.y + tr.height, 'the transport docks above the navigation').toBeLessThanOrEqual(nav.y + 0.5);
  await page.getByTestId('transport-step').tap();
  await page.getByTestId('transport-step').tap();
  expect(await ex(page, `return session.sim.stepIndex;`)).toBe(1);
  await expect(page.getByTestId('sim-readout')).toContainText('step 2/');
  await page.getByTestId('transport-back').tap();
  expect(await ex(page, `return session.sim.stepIndex;`)).toBe(0);
  await page.getByTestId('transport-play').tap();
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.sim.playing === true);
  await page.getByTestId('transport-play').tap();
  await page.getByTestId('sim-end').tap();
  await page.waitForFunction(() => { const s = /** @type {any} */ (window).__exegra.session.sim; return s.stepIndex === s.simulation.steps.length - 1; });
  // Faults and the timeline live in the Simulate sheet.
  await page.getByTestId('transport-open').tap();
  await expect(page.locator('#tab-simulation')).toBeVisible();
  await page.getByTestId('sim-fault-early-ack').tap();
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.sim.faults.includes('early-ack'));
  await page.waitForFunction(() => !!(/** @type {any} */ (window).__exegra.session.sim.simulation));
  await page.getByTestId('sim-run').tap();
  await expect(page.getByTestId('sim-violation-banner')).toBeVisible();
  await page.getByTestId('sim-timeline').locator('[data-testid="sim-row-0"]').tap();
  expect(await ex(page, `return session.sim.stepIndex;`)).toBe(0);
  await page.screenshot({ path: path.join(SHOTS, 'test-phone-simulation-transport.png') });
  await closeSheet(page);

  // Verification: filter, open a claim's detail.
  await page.getByTestId('tab-btn-verification').tap();
  await page.getByTestId('claim-filter-violated').tap();
  const claimRow = page.getByTestId('claims-table').locator('[data-entity-id="database-reached-only-by-runtime"]');
  await claimRow.tap();
  await waitSelected(page, 'database-reached-only-by-runtime');
  await page.getByTestId('tab-btn-inspector').tap();
  await expect(page.getByTestId('claim-result')).toContainText('Violated');
  await closeSheet(page);

  // Source, realisation, diagnostics and changes from More.
  await page.getByTestId('nav-more').tap();
  await page.getByTestId('more-source').tap();
  await expect(page.getByTestId('source-text')).toBeVisible();
  expect(await detent(page)).toBe('full');
  await closeSheet(page);
  await page.getByTestId('nav-more').tap();
  await page.getByTestId('more-realisation').tap();
  await page.getByTestId('generate-artifacts').tap();
  await expect(page.getByTestId('generated-file-manifest.json')).toBeVisible();
  await closeSheet(page);
  await page.getByTestId('validation-state').tap(); // the status pill opens Diagnostics
  await expect(page.locator('#tab-diagnostics')).toBeVisible();
  await expect(page.getByTestId('diagnostics-summary')).toBeVisible();
  await closeSheet(page);
  await page.getByTestId('nav-more').tap();
  await page.getByTestId('more-changes').tap();
  await expect(page.locator('#tab-changes .change').first()).toBeVisible();
  await closeSheet(page);

  // Export downloads the bundle; import is offered.
  const download = page.waitForEvent('download');
  await overflow(page, 'export');
  expect((await download).suggestedFilename()).toBe(`${SCRATCH.multiplayer}.exegra.json`);
  await page.getByTestId('appbar-overflow').tap();
  await expect(page.getByTestId('import')).toBeVisible();
  await expect(page.getByTestId('import')).toBeEnabled();
  await page.getByTestId('appbar-overflow').tap();

  // Switch view and project from the title button's picker sheet.
  const current = /** @type {string} */ (await ex(page, `return session.viewId;`));
  const views = /** @type {any[]} */ (await ex(page, `return session.views;`));
  const other = views.find((v) => v.id !== current) ?? views[0];
  await page.getByTestId('title-picker').tap();
  await page.getByTestId(`pick-view-${other.id}`).tap();
  await page.waitForFunction((id) => /** @type {any} */ (window).__exegra.session.scene.viewId === id, other.id);
  await expect(page.getByTestId('title-picker')).toContainText(other.name);
  await page.getByTestId('title-picker').tap();
  await page.getByTestId(`pick-project-${SCRATCH.exegra}`).tap();
  await page.waitForFunction((n) => /** @type {any} */ (window).__exegra.session.projectName === n, SCRATCH.exegra);
  await expectNoHorizontalScroll(page, 'after every function');
});

test('panels open beside the scene on a tablet and the desktop shows explorer scene and context panel side by side', { tag: '@tablet' }, async ({ page, browser }) => {
  /** @param {{x: number, y: number, width: number, height: number}} a @param {{x: number, y: number, width: number, height: number}} b */
  const overlap = (a, b) => Math.max(0, Math.min(a.x + a.width, b.x + b.width) - Math.max(a.x, b.x)) * Math.max(0, Math.min(a.y + a.height, b.y + b.height) - Math.max(a.y, b.y));

  await open(page, 'multiplayer');
  expect(page.viewportSize()?.width).toBe(820);
  for (const dest of ['inspector', 'explorer', 'verification']) {
    await page.getByTestId(`tab-btn-${dest}`).tap();
    const panel = page.locator(dest === 'explorer' ? '#panel-explorer' : '#panel-context');
    await expect(panel).toBeVisible();
    await settled(page);
    const p = /** @type {any} */ (await panel.boundingBox());
    const c = /** @type {any} */ (await page.getByTestId('scene-canvas').boundingBox());
    expect(overlap(p, c), `${dest}: the panel and the scene do not overlap`).toBeLessThanOrEqual(1);
    expect(p.x, `${dest}: the panel is to the right of the scene`).toBeGreaterThanOrEqual(c.x + c.width - 1);
    expect(c.width, `${dest}: the scene keeps a usable width`).toBeGreaterThanOrEqual(300);
    await page.screenshot({ path: path.join(SHOTS, `test-tablet-${dest}.png`) });
  }
  await expectNoHorizontalScroll(page, 'tablet');

  // A desktop opens with the explorer, the scene and the context panel visible, nothing opened by hand.
  const desk = await browser.newContext({ viewport: { width: 1600, height: 1000 }, baseURL: test.info().project.use.baseURL });
  const dp = await desk.newPage();
  dp.on('pageerror', (e) => pageErrors.push(e.message));
  await open(dp, 'multiplayer');
  const rects = {
    explorer: /** @type {any} */ (await dp.locator('#panel-explorer').boundingBox()),
    canvas: /** @type {any} */ (await dp.getByTestId('scene-canvas').boundingBox()),
    context: /** @type {any} */ (await dp.locator('#panel-context').boundingBox()),
  };
  await expect(dp.locator('#explorer')).toBeVisible();
  await expect(dp.getByTestId('inspector')).toBeVisible();
  for (const [k, r] of Object.entries(rects)) expect(r, `${k} is laid out`).not.toBeNull();
  expect(overlap(rects.explorer, rects.canvas), 'explorer and scene do not overlap').toBeLessThanOrEqual(1);
  expect(overlap(rects.canvas, rects.context), 'scene and context panel do not overlap').toBeLessThanOrEqual(1);
  expect(overlap(rects.explorer, rects.context), 'explorer and context panel do not overlap').toBeLessThanOrEqual(1);
  expect(rects.explorer.x + rects.explorer.width).toBeLessThanOrEqual(rects.canvas.x + 1);
  expect(rects.canvas.x + rects.canvas.width).toBeLessThanOrEqual(rects.context.x + 1);
  expect(rects.canvas.width, 'the scene keeps a usable width').toBeGreaterThanOrEqual(360);
  await dp.screenshot({ path: path.join(SHOTS, 'test-desktop-layout.png') });
  await desk.close();
});

test('the simulator shows the request log of contract events on a phone', { tag: '@phone' }, async ({ page }) => {
  await open(page, 'exegra');
  await page.getByTestId('tab-btn-simulation').tap();
  await page.getByTestId('sim-scenario').selectOption('write-with-stale-base-hash');
  await page.waitForFunction(() => !!(/** @type {any} */ (window).__exegra.session.sim.simulation));
  await ex(page, `session.simRunToEnd();`);

  // The Requests section reads like a request log: a request, a refused write and a retry.
  const requests = page.getByTestId('sim-requests');
  await requests.scrollIntoViewIfNeeded();
  await expect(requests).toContainText('→ POST /__exegra/write');
  await expect(requests).toContainText('← refused conflict {current: "h2"}');
  await expect(requests).toContainText('← ok {ok: true, hash: "h3"}');
  await expect(requests.locator('li')).toHaveCount(4);
  await expect(page.getByTestId('sim-checks')).toContainText('4 contract events fit their contracts and every response answers a request');

  // Every line is a jump target of at least 44 px, and the page does not scroll sideways.
  for (const btn of await requests.locator('button').all()) {
    const box = /** @type {any} */ (await btn.boundingBox());
    expect(box.height, 'a request line is at least 44 px tall').toBeGreaterThanOrEqual(43.5);
  }
  await expectNoHorizontalScroll(page, 'request log');
  await page.getByTestId('sim-request-3').tap();
  expect(await ex(page, `return session.sim.stepIndex;`)).toBe(3);
  await page.screenshot({ path: path.join(SHOTS, 'test-phone-request-log.png') });
});

test('a phone walks the levels of the self-specification by touch and inspects a derived edge and a block', { tag: '@phone' }, async ({ page }) => {
  await open(page, 'exegra');
  await ex(page, `session.setView('architecture');`);
  // The level controls are in the app bar's tools: choose L0, the system in its environment.
  await page.getByTestId('appbar-overflow').tap();
  await expect(page.locator('#appbar-tools')).toBeVisible();
  await expectTouchTargets(page, 'tools menu with the level controls');
  await page.getByTestId('cut-select').selectOption('l0');
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.scene.abstraction?.cut === 'l0');
  await page.keyboard.press('Escape');
  await settled(page);
  await expectNoHorizontalScroll(page, 'L0');
  await page.screenshot({ path: path.join(SHOTS, 'test-phone-nav-l0.png') });

  // Select the system: the inspector comes forward and shows it as a block; its Expand button opens it into its subsystems.
  await ex(page, "session.select('exegra', { source: 'scene' });");
  await waitSelected(page, 'exegra');
  await expect(page.locator('#panel-context')).toHaveAttribute('data-detent', 'peek');
  await page.locator('#panel-context .panel__handle').tap(); // peek -> half
  await page.locator('#panel-context .panel__handle').tap(); // half -> full
  await expect(page.locator('#panel-context')).toHaveAttribute('data-detent', 'full');
  await settled(page);
  await expect(page.getByTestId('block-panel')).toHaveAttribute('data-element', 'exegra');
  await page.getByTestId('block-expand').tap();
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.scene.abstraction?.cut === 'l1');
  await expectTouchTargets(page, 'block panel');

  // The bundled edge application -> semantic-core lists every relationship it stands for, each a 44 px link.
  const n = /** @type {number} */ (await ex(page, `const e = session.scene.edges.find((x) => x.key === 'application->semantic-core:invokes'); session.select(e.entityId, { edge: e.id }); return e.witnesses.length;`));
  await expect(page.getByTestId('witness-row')).toHaveCount(n);
  await expectNoHorizontalScroll(page, 'witness list');
  await expectTouchTargets(page, 'witness list');
  await page.screenshot({ path: path.join(SHOTS, 'test-phone-nav-witnesses.png') });
});
