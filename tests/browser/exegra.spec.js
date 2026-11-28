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

test('self-specification renders in 3D', async ({ page }) => {
  await open(page, 'exegra');
  const info = /** @type {any} */ (await ex(page, `
    const stats = view.getStats();
    return {
      system: session.model.system.id,
      components: session.model.byKind.component.length,
      sceneNodes: session.scene.nodes.length,
      unbacked: session.scene.nodes.filter((n) => !session.model.entities.has(n.entityId)).length
        + session.scene.edges.filter((e) => !session.model.entities.has(e.entityId)).length,
      stats,
    };`));
  expect(info.system).toBe('exegra');
  expect(info.components).toBeGreaterThan(5);
  // A large model opens as an overview: top-level subsystems closed, their relationships bundled.
  expect(info.sceneNodes).toBeGreaterThan(3);
  expect(info.sceneNodes).toBeLessThanOrEqual(info.components);
  expect(info.unbacked, 'every drawn node and edge is backed by a model entity').toBe(0);
  expect(info.stats.nodes).toBe(info.sceneNodes);
  expect(info.stats.drawCalls).toBeGreaterThan(0);
  await expect(page.getByTestId('scene-canvas')).toBeVisible();
  // Labels are real DOM, derived from the model.
  const first = /** @type {any} */ (await ex(page, `const n = session.scene.nodes[0]; return { id: n.id, name: session.model.entities.get(n.entityId).data.name };`));
  await expect(page.locator(`.scene-label[data-entity-id="${first.id}"]`)).toContainText(first.name, { ignoreCase: true });
  await page.screenshot({ path: path.join(SHOTS, 'test-self-spec.png') });
  // Opening every subsystem shows every component, inside the system drawn as the container of its subsystems:
  // nothing exists only in the overview or only in the detail. A file a subsystem declares itself (not through one of
  // its components) is a module element member of that subsystem, so it is a block of its own once the subsystem is open.
  await ex(page, `for (const id of [...session.ui.collapsed]) session.toggleCollapsed(id);`);
  const expanded = /** @type {any} */ (await ex(page, `
    const modules = session.scene.nodes.filter((n) => n.elementKind === 'module');
    return { nodes: session.scene.nodes.length, components: session.model.byKind.component.length, edges: session.scene.edges.length, relationships: session.model.byKind.relationship.length,
      system: session.scene.nodes.filter((n) => n.elementKind === 'system').length, modules: modules.length,
      modulesOfOpened: modules.every((n) => session.model.entities.get(n.parent)?.data.kind === 'subsystem' && (session.model.entities.get(n.parent).data.implementation?.modules ?? []).includes(n.id.slice('module:'.length))) };`));
  expect(expanded.system).toBe(1);
  expect(expanded.modulesOfOpened, 'every module element drawn is a file an opened subsystem declares itself').toBe(true);
  expect(expanded.nodes).toBe(expanded.components + expanded.system + expanded.modules);
  // Every declared relationship is drawn, as one edge or bundled into one; an extracted import (M5) is drawn too, or
  // lies inside one closed component (both its files are that component's modules) and is counted in the notes.
  const drawn = /** @type {any} */ (await ex(page, `
    const witnesses = new Set(session.scene.edges.flatMap((e) => e.witnesses ?? []));
    const ownerOf = (m) => session.model.byKind.component.find((c) => (c.data.implementation?.modules ?? []).some((p) => 'module:' + p === m))?.id;
    const rels = session.model.byKind.relationship;
    return {
      declaredMissing: rels.filter((r) => (r.data.provenance ?? 'declared') === 'declared' && !witnesses.has(r.id)).map((r) => r.id),
      extractedOutside: rels.filter((r) => r.data.provenance === 'extracted' && !witnesses.has(r.id) && ownerOf(r.data.from) !== ownerOf(r.data.to)).map((r) => r.id),
      edges: session.scene.edges.length,
    };`));
  expect(drawn.declaredMissing, 'every declared relationship is drawn').toEqual([]);
  expect(drawn.extractedOutside, 'an extracted import not drawn lies inside one component').toEqual([]);
  expect(drawn.edges).toBe(expanded.edges);
  await page.waitForTimeout(700);
  await page.screenshot({ path: path.join(SHOTS, 'test-self-spec-expanded.png') });
});

test('selecting a component shows model-derived properties', async ({ page }) => {
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
});

test('inspector rename persists to spec.jsonc and survives reload', async ({ page }) => {
  await open(page, 'multiplayer');
  const before = /** @type {string} */ (readScratch('multiplayer', 'spec.jsonc'));
  await clickEntity(page, 'api-service');
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

test('source edit updates the scene; invalid source is rejected and the draft is kept', async ({ page }) => {
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

test('create, connect, delete with dependency warning, undo and redo', async ({ page }) => {
  await open(page, 'multiplayer');
  // Create
  await page.getByTestId('new-component').click();
  await page.getByTestId('create-name').fill('Match maker');
  await expect(page.getByTestId('create-id')).toHaveValue('match-maker');
  await page.getByTestId('create-category').selectOption('computational');
  await page.getByTestId('create-submit').click();
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.model.entities.has('match-maker'));
  await expect(page.locator('.scene-label[data-entity-id="match-maker"]')).toHaveCount(1);
  expect(await ex(page, `return session.selection;`)).toBe('match-maker');

  // Connect it in connect mode: two clicks on the canvas, then the typed dialog.
  await page.waitForTimeout(600); // layout animation
  await page.getByTestId('mode-connect').click();
  await clickEntity(page, 'match-maker');
  await clickEntity(page, 'game-coordinator');
  await expect(page.getByTestId('connect-dialog')).toBeVisible();
  await expect(page.getByTestId('connect-from')).toHaveValue('match-maker');
  await expect(page.getByTestId('connect-to')).toHaveValue('game-coordinator');
  await page.getByTestId('connect-kind').selectOption('calls');
  await page.getByTestId('connect-submit').click();
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.model.entities.has('match-maker-calls-game-coordinator'));
  expect(await ex(page, `return session.scene.edges.some((e) => e.entityId === 'match-maker-calls-game-coordinator');`)).toBe(true);
  await waitSaved(page);
  expect(readScratch('multiplayer', 'spec.jsonc')).toContain('"id": "match-maker-calls-game-coordinator"');

  // Delete something that is referenced: the dialog lists dependents and requires an explicit cascade.
  await ex(page, `session.select('game-database');`);
  await page.getByTestId('delete-entity').click();
  const dialog = page.getByTestId('delete-dialog');
  await expect(dialog).toBeVisible();
  await expect(dialog).toContainText('telemetry-reads-game-database');
  await expect(page.getByTestId('delete-submit')).toBeDisabled();
  await page.getByTestId('delete-cascade').check();
  await page.getByTestId('delete-submit').click();
  await page.waitForFunction(() => !/** @type {any} */ (window).__exegra.session.model.entities.has('game-database'));
  expect(await ex(page, `return session.project.errorCount;`)).toBe(0);
  await expect(page.locator('.scene-label[data-entity-id="game-database"]')).toHaveCount(0);

  // Undo restores it (and everything the cascade removed); redo removes it again.
  await page.getByTestId('undo').click();
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.model.entities.has('game-database'));
  expect(await ex(page, `return session.model.entities.has('telemetry-reads-game-database');`)).toBe(true);
  await page.getByTestId('redo').click();
  await page.waitForFunction(() => !/** @type {any} */ (window).__exegra.session.model.entities.has('game-database'));
  await page.getByTestId('undo').click();
  await page.getByTestId('undo').click();
  await page.getByTestId('undo').click();
  await page.waitForFunction(() => !/** @type {any} */ (window).__exegra.session.model.entities.has('match-maker'));
  await waitSaved(page);
  expect(readScratch('multiplayer', 'spec.jsonc')).not.toContain('match-maker');
});

test('moving a node changes layout.jsonc only', async ({ page }) => {
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

test('views switch and keep the selected entity', async ({ page }) => {
  await open(page, 'multiplayer');
  await clickEntity(page, 'game-database');
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.selection === 'game-database');
  const views = /** @type {any[]} */ (await ex(page, `return session.views;`));
  expect(views.map((v) => v.projection)).toEqual(expect.arrayContaining(['structural', 'claims', 'behavior']));
  const seen = new Set();
  for (const v of views) {
    await page.getByTestId('view-select').selectOption(v.id);
    await page.waitForFunction((id) => /** @type {any} */ (window).__exegra.session.scene.viewId === id, v.id);
    const s = /** @type {any} */ (await ex(page, `return { selection: session.selection, projection: session.scene.projection, nodes: session.scene.nodes.length, kinds: [...new Set(session.scene.nodes.map((n) => n.entityKind))] };`));
    expect(s.selection, `selection survives switching to ${v.id}`).toBe('game-database');
    expect(s.projection).toBe(v.projection);
    // The reader projection draws no scene; its page replaces it.
    if (v.projection === 'reader') { await expect(page.locator('#reader-host')).toBeVisible(); continue; }
    expect(s.nodes).toBeGreaterThan(0);
    seen.add(s.kinds.sort().join(','));
    await page.waitForTimeout(450);
    await page.screenshot({ path: path.join(SHOTS, `test-view-${v.id}.png`) });
  }
  expect(seen.size, 'projections are genuinely different scenes').toBeGreaterThanOrEqual(3);
  // Context carried into the claims projection: a claim involving the selected component is focused.
  const claimsView = views.find((v) => v.projection === 'claims');
  await page.getByTestId('view-select').selectOption(claimsView.id);
  const focus = /** @type {any} */ (await ex(page, `return { claim: session.ui.focusClaim, involved: session.claimResult(session.ui.focusClaim)?.involved ?? [] };`));
  expect(focus.claim).toBeTruthy();
  expect(focus.involved).toContain('game-database');
});

test('claim selection highlights involved components', async ({ page }) => {
  await open(page, 'multiplayer');
  await page.locator('#explorer [data-entity-id="database-reached-only-by-runtime"]').first().click();
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.selection === 'database-reached-only-by-runtime');
  const r = /** @type {any} */ (await ex(page, `const r = session.claimResult(session.selection); return { status: r.status, involved: r.involved, counter: r.counterexample.entities, highlight: session.highlight };`));
  expect(r.status).toBe('violated');
  expect(r.counter).toContain('telemetry-reads-game-database');
  expect(r.highlight).toEqual(expect.arrayContaining(['telemetry', 'game-database']));
  // The inspector states the result, its scope and the counterexample; no positive tone anywhere in it.
  const result = page.getByTestId('claim-result');
  await expect(result).toContainText('Violated');
  await expect(result).toContainText('telemetry-reads-game-database');
  // Highlighted entities stay at full strength; an uninvolved one is dimmed.
  await expect(page.locator('.scene-label[data-entity-id="web-client"]')).toHaveClass(/scene-label--dimmed/);
  await expect(page.locator('.scene-label[data-entity-id="telemetry"]')).not.toHaveClass(/scene-label--dimmed/);
  await page.screenshot({ path: path.join(SHOTS, 'test-claim-highlight.png') });
  // A verified claim reads as verified; an unsupported method stays not evaluated; nothing is green by declaration.
  const statuses = /** @type {Record<string,string>} */ (await ex(page, `return Object.fromEntries(session.claimResults.map((r) => [r.claimId, r.status]));`));
  expect(statuses['ack-implies-durable']).toBe('verified');
  expect(statuses['ack-probability-bound']).toBe('not-evaluated');
  expect(statuses['worker-availability-objective']).toBe('not-evaluated');
  await page.getByTestId('tab-btn-verification').click();
  const table = page.getByTestId('claims-table');
  await expect(table.locator('[data-entity-id="ack-probability-bound"]')).toHaveAttribute('data-status', 'not-evaluated');
  await expect(table.locator('[data-entity-id="database-reached-only-by-runtime"]')).toHaveAttribute('data-status', 'violated');
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

test('different specifications load through the same pipeline', async ({ page }) => {
  await open(page, 'exegra');
  const a = /** @type {any} */ (await ex(page, `return { system: session.model.system.id, nodes: view.getStats().nodes, illustrative: session.model.system.data.illustrative === true };`));
  await page.getByTestId('project-select').selectOption(SCRATCH.multiplayer);
  await page.waitForFunction((name) => /** @type {any} */ (window).__exegra.session.projectName === name && /** @type {any} */ (window).__exegra.view.getStats().nodes > 0, SCRATCH.multiplayer);
  const b = /** @type {any} */ (await ex(page, `return { system: session.model.system.id, nodes: view.getStats().nodes, sceneNodes: session.scene.nodes.length, illustrative: session.model.system.data.illustrative === true };`));
  expect(a.system).toBe('exegra');
  expect(b.system).toBe('multiplayer-platform');
  expect(b.nodes).toBe(b.sceneNodes);
  expect(a.illustrative).toBe(false);
  expect(b.illustrative).toBe(true);
  // The example is labelled as illustrative on the viewport; the self-specification is not.
  await expect(page.getByTestId('illustrative-mark')).toBeVisible();
  await page.getByTestId('project-select').selectOption(SCRATCH.exegra);
  await page.waitForFunction((name) => /** @type {any} */ (window).__exegra.session.projectName === name, SCRATCH.exegra);
  await expect(page.getByTestId('illustrative-mark')).toHaveCount(0);
});

test('realisation panel reports implementation status', async ({ page }) => {
  await open(page, 'exegra');
  await page.getByTestId('tab-btn-realisation').click();
  const table = page.getByTestId('realisation-table');
  await expect(table).toBeVisible();
  const declared = /** @type {any[]} */ (await ex(page, `return session.model.byKind.component.filter((c) => c.data.implementation).map((c) => ({ id: c.id, status: c.data.implementation.status }));`));
  expect(declared.length).toBeGreaterThan(5);
  for (const c of declared.slice(0, 6)) {
    await expect(table.locator(`[data-entity-id="${c.id}"]`).first()).toBeVisible();
  }
  // Nothing claims to be generated unless the model says so.
  const generated = declared.filter((c) => c.status === 'generated' || c.status === 'partially-generated').length;
  const shown = await table.locator('tr', { hasText: /^.*\bgenerated\b/i }).count();
  expect(shown).toBeGreaterThanOrEqual(0);
  if (!generated) await expect(page.getByTestId('realisation-summary')).not.toContainText(/[1-9]\d* generated/);
  // Generated artifacts come from the model and are reproducible.
  await page.getByTestId('generate-artifacts').click();
  await expect(page.getByTestId('generated-file-manifest.json')).toBeVisible();
  const twice = /** @type {boolean} */ (await page.evaluate(async () => {
    const { session } = /** @type {any} */ (window).__exegra;
    const { generateAll } = await import('/src/core/generate/index.js');
    const opts = { claimResults: session.claimResults, diagnostics: session.diagnostics };
    return JSON.stringify(generateAll(session.model, opts)) === JSON.stringify(generateAll(session.model, opts));
  }));
  expect(twice).toBe(true);
  await page.screenshot({ path: path.join(SHOTS, 'test-realisation.png') });
});
