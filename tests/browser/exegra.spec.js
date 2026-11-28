// Browser-level verification of the running application. Each test drives the
// real UI (canvas clicks at projected entity positions, real form controls) and
// checks the result in three places where it matters: the semantic model in
// the page, the rendered DOM, and the files on disk.
import { test, expect } from '@playwright/test';
import fs from 'node:fs';
import path from 'node:path';
import { ROOT, SCRATCH, resetScratch, readScratch } from './scratch.js';

const SHOTS = path.join(ROOT, 'screenshots');
fs.mkdirSync(SHOTS, { recursive: true });

/** @type {string[]} */
let pageErrors = [];

test.beforeEach(async ({ page }) => {
  resetScratch('exegra');
  resetScratch('multiplayer');
  pageErrors = [];
  page.on('pageerror', (e) => pageErrors.push(e.message));
  page.on('console', (m) => { if (m.type() === 'error' && !/favicon|404/.test(m.text())) pageErrors.push(m.text()); });
});

test.afterEach(() => {
  expect(pageErrors, 'no uncaught errors in the page').toEqual([]);
});

/** @param {import('@playwright/test').Page} page @param {'exegra'|'multiplayer'} which */
async function open(page, which) {
  await page.goto(`/?project=${SCRATCH[which]}`);
  await page.waitForFunction((name) => {
    const x = /** @type {any} */ (window).__exegra;
    return x?.session.projectName === name && x.session.model && x.view.getStats().nodes > 0;
  }, SCRATCH[which]);
  await page.waitForTimeout(500); // initial fit animation
}

/** Run a function against window.__exegra. @param {import('@playwright/test').Page} page @param {string} body */
const ex = (page, body) => page.evaluate(`(() => { const { session, view } = window.__exegra; ${body} })()`);

/** Click the canvas where an entity is drawn. @param {import('@playwright/test').Page} page @param {string} id */
async function clickEntity(page, id) {
  const pt = /** @type {{x:number,y:number}|null} */ (await ex(page, `return view.screenPoint(${JSON.stringify(id)});`));
  expect(pt, `entity ${id} has a screen position`).not.toBeNull();
  await page.mouse.click(/** @type {any} */ (pt).x, /** @type {any} */ (pt).y);
}

const waitSaved = (/** @type {import('@playwright/test').Page} */ page) =>
  page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.saveState === 'saved');

test('selecting a component shows model-derived properties, and an inspector rename persists to spec.jsonc and survives reload', async ({ page }) => {
  await open(page, 'multiplayer');
  await clickEntity(page, 'api-service');
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.selection === 'api-service');
  const data = /** @type {any} */ (await ex(page, `return session.model.entities.get('api-service').data;`));
  const inspector = page.getByTestId('inspector');
  await expect(inspector.locator('[data-prop="name"] input')).toHaveValue(data.name);
  await expect(inspector.locator('[data-prop="purpose"] textarea')).toHaveValue(data.purpose);
  await expect(inspector.locator('[data-prop="category"] select')).toHaveValue(data.category);
  // A model-defined (vocabulary) property gets a control without any code knowing about it.
  const ext = /** @type {string[]} */ (await ex(page, `return Object.entries(session.model.meta.entities.component.properties).filter(([, d]) => d.extension).map(([k]) => k);`));
  expect(ext.length).toBeGreaterThan(0);
  await expect(inspector.locator(`[data-prop="${ext[0]}"]`)).toBeVisible();
  // Selecting a relationship shows its semantics.
  const rel = /** @type {string} */ (await ex(page, `return session.scene.edges.find((e) => e.entityKind === 'relationship').entityId;`));
  await clickEntity(page, rel);
  await page.waitForFunction((r) => /** @type {any} */ (window).__exegra.session.selection === r, rel);
  await expect(inspector).toContainText('Semantics');
  // Editing through the inspector: the rename reaches the file.
  const before = /** @type {string} */ (readScratch('multiplayer', 'spec.jsonc'));
  await clickEntity(page, 'api-service');
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.selection === 'api-service');
  const name = page.getByTestId('inspector').locator('[data-prop="name"] input');
  const oldName = await name.inputValue();
  await name.fill('Command gateway');
  await name.press('Enter');
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.model.entities.get('api-service').data.name === 'Command gateway');
  await waitSaved(page);
  // The source file changed in exactly one place.
  const after = /** @type {string} */ (readScratch('multiplayer', 'spec.jsonc'));
  expect(after).toBe(before.replace(`"name": ${JSON.stringify(oldName)}`, '"name": "Command gateway"'));
  // The scene label follows.
  await expect(page.locator('.scene-label[data-entity-id="api-service"]')).toContainText('Command gateway');
  // And the source editor shows the same text as the file.
  await page.getByTestId('tab-btn-source').click();
  await expect(page.getByTestId('source-text')).toHaveValue(after);
  // Reload: the change is still there, loaded from disk.
  await page.reload();
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra?.session.model?.entities.get('api-service')?.data.name === 'Command gateway');
  await expect(page.locator('.scene-label[data-entity-id="api-service"]')).toContainText('Command gateway');
});

/**
 * Put a whole text into the source editor as one paste. Locator.fill on a long multi-line text makes the browser
 * emit one input event per line and lay the textarea out after each (about 2 s for the 650 line fixture); a paste is
 * one input event, which is what the editor reacts to.
 * @param {import('@playwright/test').Locator} editor @param {string} text
 */
const pasteSource = (editor, text) => editor.evaluate((/** @type {HTMLTextAreaElement} */ ta, /** @type {string} */ t) => {
  ta.focus();
  ta.value = t;
  ta.dispatchEvent(new InputEvent('input', { bubbles: true, inputType: 'insertFromPaste' }));
}, text);

test('source edit updates the scene; invalid source is rejected and the draft is kept', { tag: '@full' }, async ({ page }) => {
  await open(page, 'multiplayer');
  await page.getByTestId('tab-btn-source').click();
  const editor = page.getByTestId('source-text');
  const original = await editor.inputValue();
  const oldName = /** @type {string} */ (await ex(page, `return session.model.entities.get('shared-cache').data.name;`));

  // A valid textual edit reaches the model, the scene and the disk.
  const edited = original.replace(`"name": ${JSON.stringify(oldName)}`, '"name": "Session cache"');
  expect(edited).not.toBe(original);
  await pasteSource(editor, edited);
  await expect(page.getByTestId('source-state')).toContainText(/draft/i);
  await page.getByTestId('source-apply').click();
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.model.entities.get('shared-cache').data.name === 'Session cache');
  await expect(page.locator('.scene-label[data-entity-id="shared-cache"]')).toContainText('Session cache');
  await waitSaved(page);
  expect(readScratch('multiplayer', 'spec.jsonc')).toBe(edited);

  // Malformed source: rejected, nothing lost, last valid model intact.
  const hashBefore = await ex(page, `return session.project.semanticHash;`);
  const malformed = edited.replace('"components": [', '"components": ');
  await pasteSource(editor, malformed);
  await page.getByTestId('source-apply').click();
  await expect(page.getByTestId('source-rejection')).toBeVisible();
  await expect(editor).toHaveValue(malformed);
  expect(await ex(page, `return session.project.semanticHash;`)).toBe(hashBefore);
  expect(await ex(page, `return session.project.specText;`)).toBe(edited);
  expect(readScratch('multiplayer', 'spec.jsonc')).toBe(edited);

  // Inconsistent (well-formed JSON, dangling reference): also rejected with a located diagnostic.
  const dangling = edited.replace('"to": "game-database"', '"to": "no-such-thing"');
  expect(dangling).not.toBe(edited);
  await pasteSource(editor, dangling);
  await expect(page.getByTestId('source-diagnostics')).toContainText('no-such-thing');
  await page.getByTestId('source-apply').click();
  await expect(page.getByTestId('source-rejection')).toBeVisible();
  await expect(editor).toHaveValue(dangling);
  expect(await ex(page, `return session.project.semanticHash;`)).toBe(hashBefore);

  // Discarding the draft returns to the committed source.
  await page.getByTestId('source-discard').click();
  await expect(editor).toHaveValue(edited);
});

test('moving a node changes layout.jsonc only', { tag: '@full' }, async ({ page }) => {
  await open(page, 'multiplayer');
  const specBefore = readScratch('multiplayer', 'spec.jsonc');
  const before = /** @type {any} */ (await ex(page, `return { hash: session.project.semanticHash, rev: session.project.revision, x: session.placement['web-client'].x };`));
  const pt = /** @type {{x:number,y:number}} */ (await ex(page, `return view.screenPoint('web-client');`));
  await page.mouse.move(pt.x, pt.y);
  await page.mouse.down();
  await page.mouse.move(pt.x - 30, pt.y + 10, { steps: 4 });
  await page.mouse.move(pt.x - 90, pt.y + 40, { steps: 6 });
  await page.mouse.up();
  await page.waitForFunction((rev) => /** @type {any} */ (window).__exegra.session.project.revision > rev, before.rev);
  await waitSaved(page);
  const after = /** @type {any} */ (await ex(page, `return { hash: session.project.semanticHash, x: session.placement['web-client'].x, pins: session.project.layout.views[session.viewId].positions };`));
  expect(after.hash, 'semantic hash is unchanged by a move').toBe(before.hash);
  expect(after.x).toBeLessThan(before.x);
  expect(Object.keys(after.pins)).toEqual(['web-client']);
  expect(readScratch('multiplayer', 'spec.jsonc'), 'the specification file is byte-identical').toBe(specBefore);
  expect(readScratch('multiplayer', 'layout.jsonc')).toContain('"web-client"');
  // The pin survives a reload; resetting the layout removes it.
  await page.reload();
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra?.session.placement?.['web-client']);
  expect(await ex(page, `return session.placement['web-client'].x;`)).toBeCloseTo(after.x, 2);
  await page.getByTestId('reset-layout').click();
  await page.waitForFunction(() => !Object.keys(/** @type {any} */ (window).__exegra.session.project.layout.views[/** @type {any} */ (window).__exegra.session.viewId]?.positions ?? {}).length);
  expect(await ex(page, `return session.placement['web-client'].x;`)).toBeCloseTo(before.x, 2);
});

test('simulation steps through the trace; early-ack fault violates the invariant', async ({ page }) => {
  await open(page, 'multiplayer');
  await page.getByTestId('tab-btn-simulation').click();
  await page.getByTestId('sim-scenario').selectOption('command-happy-path');
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.sim.scenarioId === 'command-happy-path');
  await page.waitForFunction(() => !!(/** @type {any} */ (window).__exegra.session.sim.simulation)); // the run executes in a worker
  const step = page.locator('button[data-testid="sim-step"]').last();
  // Step through; the UI timeline equals the recorded trace of the core simulator.
  for (let i = 0; i < 3; i++) await step.click();
  expect(await ex(page, `return session.sim.stepIndex;`)).toBe(2);
  const uiRows = await page.getByTestId('sim-timeline').locator('[data-testid^="sim-row-"]').count();
  expect(uiRows).toBe(1 + 3);
  await page.getByTestId('sim-run').click();
  const run = /** @type {any} */ (await ex(page, `
    const t = session.sim.simulation.trace();
    return { outcome: t.outcome, steps: t.steps.map((s) => s.event.id + ':' + s.fired.map((f) => f.transition).join('+')), checks: session.sim.checks };`));
  expect(run.outcome).toBe('quiescent');
  expect(run.checks.every((/** @type {any} */ c) => c.holds), 'no claim is violated on the happy path').toBe(true);
  await expect(page.getByTestId('sim-violation-banner')).toHaveCount(0);
  // Determinism: the same scenario run again in the page yields the identical trace.
  const again = /** @type {string[]} */ (await ex(page, `session.simReset(); session.simRunToEnd(); return session.sim.simulation.trace().steps.map((s) => s.event.id + ':' + s.fired.map((f) => f.transition).join('+'));`));
  expect(again).toEqual(run.steps);
  expect(await page.getByTestId('sim-timeline').locator('[data-testid^="sim-row-"]').count()).toBe(1 + run.steps.length);

  // Inject the early-acknowledgement fault: the declared behavior now violates the guarantee.
  await page.getByTestId('sim-fault-early-ack').check();
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.sim.faults.includes('early-ack'));
  await page.waitForFunction(() => !!(/** @type {any} */ (window).__exegra.session.sim.simulation)); // the restarted run has finished
  await page.getByTestId('sim-run').click();
  const banner = page.getByTestId('sim-violation-banner');
  await expect(banner).toBeVisible();
  const bad = /** @type {any} */ (await ex(page, `return session.sim.checks.filter((c) => !c.holds && !c.pending);`));
  expect(bad.map((/** @type {any} */ c) => c.claimId)).toContain('ack-implies-durable');
  const violatedAt = bad.find((/** @type {any} */ c) => c.claimId === 'ack-implies-durable').stepIndex;
  // Inspect the offending step: the configuration shows acked without durable.
  await ex(page, `session.simSeek(${violatedAt});`);
  const cfg = /** @type {any} */ (await ex(page, `return session.sim.simulation.steps[${violatedAt}].config.machines;`));
  expect(cfg['worker-flow'].vars.acked).toBe(true);
  expect(cfg['database-flow'].vars.durable).toBe(false);
  await expect(page.locator('section[data-testid="sim-step"]')).toContainText('worker-ack-early');
  // The behavior projection shows the same step: the fired transition is marked active.
  const behaviorView = /** @type {string} */ (await ex(page, `return session.views.find((v) => v.projection === 'behavior').id;`));
  await page.getByTestId('view-select').selectOption(behaviorView);
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.scene.projection === 'behavior');
  const active = /** @type {string[]} */ (await ex(page, `return session.scene.edges.filter((e) => e.status === 'active').map((e) => e.entityId);`));
  const fired = /** @type {string[]} */ (await ex(page, `return session.sim.simulation.steps[session.sim.stepIndex].fired.map((f) => f.transition);`));
  expect(active).toEqual(expect.arrayContaining(fired));
  await page.waitForTimeout(500);
  await page.screenshot({ path: path.join(SHOTS, 'test-sim-violation.png') });
});
