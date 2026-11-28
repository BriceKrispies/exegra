// Multiscale navigation on Exegra's own specification (WG-5695). A person walks from the system in its
// environment (L0) through the subsystems (L1), persistence expanded, one component expanded to its module
// elements, to the semantic core expanded with persistence collapsed. At every step the scene's semantic content
// is compared with what the command line derives for the same cut (`exegra derive`), a derived edge lists its
// complete witness set, a block shows its purpose, boundary and interfaces, and the claim stated at a cut shows
// the result the command line gives at that cut (`exegra evaluate --cut`).
import { test, expect } from '@playwright/test';
import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { ROOT, SCRATCH, resetScratch } from './scratch.js';

const SHOTS = path.join(ROOT, 'screenshots');
fs.mkdirSync(SHOTS, { recursive: true });

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

/** Run a function against window.__exegra. @param {import('@playwright/test').Page} page @param {string} body */
const ex = (page, body) => page.evaluate(`(() => { const { session, view } = window.__exegra; ${body} })()`);

/** The command line on the scratch copy of the self-specification. @param {string[]} args */
function cli(args) {
  const run = spawnSync(process.execPath, ['cli/exegra.js', ...args, '--project', SCRATCH.exegra], { cwd: ROOT, encoding: 'utf8', maxBuffer: 64 * 1024 * 1024 });
  const out = JSON.parse(run.stdout);
  expect(out.ok, `exegra ${args.join(' ')}: ${run.stdout.slice(0, 400)}`).toBe(true);
  return out.result;
}

/** @param {import('@playwright/test').Page} page */
async function openArchitecture(page) {
  await page.goto(`/?project=${SCRATCH.exegra}`);
  await page.waitForFunction((name) => {
    const x = /** @type {any} */ (window).__exegra;
    return x?.session.projectName === name && x.session.model && x.view.getStats().nodes > 0;
  }, SCRATCH.exegra);
  await ex(page, `session.setView('architecture');`);
  await page.waitForTimeout(400);
}

/** The scene's semantic content, as src/core/projections.js sceneSemantics states it. @param {import('@playwright/test').Page} page */
const dump = (page) => /** @type {Promise<any>} */ (ex(page, `
  const s = session.scene;
  const byKey = (a, b) => (a.key < b.key ? -1 : a.key > b.key ? 1 : 0);
  return {
    cut: s.abstraction?.cut ?? null, hierarchy: s.abstraction?.hierarchy, cutBlocks: s.abstraction?.blocks ?? [], expanded: s.abstraction?.expanded ?? [],
    blocks: s.nodes.filter((n) => n.block).map((n) => n.id).sort(),
    interactions: s.edges.filter((e) => e.key).map((e) => ({ key: e.key, witnesses: [...e.witnesses] })).sort(byKey),
    summaries: s.edges.filter((e) => e.pathSummary).length,
    levelClaims: s.levelClaims ?? [],
    nodes: s.nodes.map((n) => ({ ...n })),
  };`));

/** What `exegra derive` prints for the same cut, reduced to blocks and interactions. @param {string[]} args */
function derived(args) {
  const d = cli(['derive', ...args]);
  return {
    d,
    blocks: d.blocks.map((/** @type {any} */ b) => b.id).sort(),
    interactions: d.interactions.map((/** @type {any} */ i) => ({ key: i.key, witnesses: i.witnesses })).sort((/** @type {any} */ a, /** @type {any} */ b) => (a.key < b.key ? -1 : a.key > b.key ? 1 : 0)),
  };
}

/** The ad hoc cut arguments that denote the scene's current cut. @param {any} sem */
const cutArgs = (sem) => (sem.cut ? ['--cut', sem.cut] : ['--hierarchy', sem.hierarchy, ...(sem.expanded.length ? ['--expand', sem.expanded.join(',')] : ['--depth', '0'])]);

/**
 * One step of the walk: the scene equals the derived model, an edge lists its witnesses, a block shows its interface,
 * and the claim stated at a cut agrees with the command line.
 * @param {import('@playwright/test').Page} page @param {string} name @param {string} blockId
 */
async function checkStep(page, name, blockId) {
  const sem = await dump(page);
  const cutDerived = derived(cutArgs(sem));
  expect({ blocks: sem.blocks, interactions: sem.interactions }, `${name}: the scene is the CLI-derived model of its cut`).toEqual({ blocks: cutDerived.blocks, interactions: cutDerived.interactions });
  expect(sem.summaries, `${name}: nothing is hidden`).toBe(0);

  // The edge with most witnesses: its inspector lists every one of them, with kind, contract, carried data and provenance.
  const edge = sem.interactions.reduce((/** @type {any} */ a, /** @type {any} */ b) => (b.witnesses.length > a.witnesses.length ? b : a));
  const edgeId = /** @type {string} */ (await ex(page, `return session.scene.edges.find((e) => e.key === ${JSON.stringify(edge.key)}).id;`));
  await ex(page, `session.select(${JSON.stringify(edgeId)}, { edge: ${JSON.stringify(edgeId)} });`);
  const inspector = page.getByTestId('inspector');
  await expect(inspector.getByTestId('derived-interaction')).toHaveAttribute('data-key', edge.key);
  const rows = inspector.getByTestId('witness-row');
  await expect(rows).toHaveCount(edge.witnesses.length);
  expect(await rows.evaluateAll((els) => els.map((e) => /** @type {HTMLElement} */ (e).dataset.witness))).toEqual(cutDerived.d.interactions.find((/** @type {any} */ i) => i.key === edge.key).witnesses);
  for (const f of ['contract', 'carries', 'provenance']) await expect(rows.first().locator(`[data-field="${f}"]`)).toHaveCount(1);
  // Each witness navigates to the relationship it is, and the list stays on the same derived interaction.
  const last = edge.witnesses[edge.witnesses.length - 1];
  await rows.last().locator(`button[data-entity-id="${last}"]`).click();
  await page.waitForFunction((id) => /** @type {any} */ (window).__exegra.session.selection === id, last);
  await expect(inspector.getByTestId('derived-interaction')).toHaveAttribute('data-key', edge.key);
  await expect(inspector.locator(`[data-testid="witness-row"][data-witness="${last}"]`)).toHaveAttribute('aria-current', 'true');
  await expect(inspector.locator('[data-section="semantics"]')).toBeVisible();

  // A block: purpose, boundary, derived interface, declared interface with the agreement result, knowledge status.
  await ex(page, `session.select(${JSON.stringify(blockId)});`);
  const panel = inspector.getByTestId('block-panel');
  await expect(panel).toHaveAttribute('data-element', blockId);
  // A module element states no purpose of its own: the inspector says it is that of the component declaring it.
  if (blockId.startsWith('module:')) await expect(inspector.getByTestId('block-purpose')).toContainText('the component declaring it');
  else await expect(inspector.getByTestId('block-purpose')).toHaveAttribute('data-stated', 'true');
  await expect(inspector.getByTestId('block-knowledge')).toHaveAttribute('data-status', /transparent|opaque|unknown/);
  const boundary = cutDerived.d.boundaries[blockId];
  await expect(inspector.getByTestId('block-boundary')).toHaveAttribute('data-out', String(boundary.out.length));
  await expect(inspector.getByTestId('block-boundary')).toHaveAttribute('data-in', String(boundary.in.length));
  const groups = cutDerived.d.interfaces[blockId].groups;
  if (groups.length) await expect(inspector.getByTestId('interface-group')).toHaveCount(groups.length);
  const agreement = cutDerived.d.interfaces[blockId].ports.length === 0 ? 'no-declared-interface'
    : cutDerived.d.diagnostics.some((/** @type {any} */ x) => x.condition === 'V3' && x.entities.includes(blockId)) ? 'disagrees' : 'agrees';
  await expect(inspector.getByTestId('block-agreement')).toHaveAttribute('data-agreement', agreement);

  // The claim stated at a cut: the result at this cut is the command line's, and its counterexample is drawn or it says it is not expressible.
  const cliClaim = cli(['evaluate', 'core-independent-of-ui', ...cutArgs(sem)]).results[0];
  const shown = sem.levelClaims.find((/** @type {any} */ c) => c.claimId === 'core-independent-of-ui');
  expect(shown, `${name}: the level-bound claim is shown`).toBeTruthy();
  expect(shown.status).toBe(cliClaim.status);
  expect(shown.expressible).toBe(!(cliClaim.diagnostics ?? []).some((/** @type {any} */ x) => x.code === 'claim.not-expressible'));
  if (cliClaim.status === 'violated') expect(shown.notDrawn).toEqual([]);
  await expect(page.locator('[data-testid="level-claim"][data-claim="core-independent-of-ui"]')).toHaveAttribute('data-status', cliClaim.status);
  await ex(page, 'session.select(null);');
  return sem;
}

test('the self-specification is walked from the system in its environment down to an expanded subsystem with each step equal to the CLI', async ({ page }) => {
  test.setTimeout(180_000);
  await openArchitecture(page);
  const hash = await ex(page, 'return session.project.semanticHash;');
  const verdicts = await ex(page, 'return session.claimResults.map((r) => [r.claimId, r.status]);');

  // 1. L0: Exegra as one block among the people and systems around it.
  await page.getByTestId('cut-select').selectOption('l0');
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.scene.abstraction?.cut === 'l0');
  const l0 = await checkStep(page, 'L0', 'exegra');
  expect(l0.nodes.find((/** @type {any} */ n) => n.id === 'exegra')).toMatchObject({ elementKind: 'system', collapsed: true });
  expect(l0.nodes.filter((/** @type {any} */ n) => (n.marks ?? []).some((/** @type {any} */ m) => m.kind === 'external')).length).toBe(14);
  expect(l0.levelClaims[0].expressible, 'the claim names the semantic core, hidden inside exegra at L0').toBe(false);
  await expect(page.locator('[data-testid="level-claim"][data-claim="core-independent-of-ui"]')).toHaveAttribute('data-expressible', 'false');
  await page.screenshot({ path: path.join(SHOTS, 'test-nav-l0.png') });

  // 2. L1: double-click the system to open it into its subsystems.
  await page.waitForTimeout(600);
  const sys = /** @type {any} */ (await ex(page, `return view.screenPoint('exegra');`));
  await page.mouse.dblclick(sys.x, sys.y);
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.scene.abstraction?.cut === 'l1');
  await checkStep(page, 'L1', 'application');
  // The bundled edge the owner saw: application -> semantic-core invokes, selected on the canvas, lists all its witnesses.
  await page.waitForTimeout(700);
  const bundle = /** @type {any} */ (await ex(page, `const e = session.scene.edges.find((x) => x.key === 'application->semantic-core:invokes'); return { id: e.id, n: e.witnesses.length };`));
  expect(bundle.n).toBeGreaterThan(1);
  const pt = /** @type {any} */ (await ex(page, `return view.screenPoint(${JSON.stringify(bundle.id)});`));
  await page.mouse.click(pt.x, pt.y);
  const picked = await ex(page, 'return session.selectedEdge;');
  if (picked === bundle.id) await expect(page.getByTestId('inspector').getByTestId('witness-row')).toHaveCount(bundle.n);
  await page.screenshot({ path: path.join(SHOTS, 'test-nav-l1.png') });

  // 3. Persistence expanded, every other subsystem collapsed; expanding it changed no other block.
  const before = await dump(page);
  await ex(page, `session.select('persistence');`);
  await page.getByTestId('block-expand').click();
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.scene.abstraction?.cut === 'persistence-expanded');
  const persistence = await checkStep(page, 'persistence expanded', 'workspace-service');
  const inside = /** @type {string[]} */ (await ex(page, `const m = session.model; return session.scene.nodes.map((n) => n.id).filter((id) => id === 'persistence' || (m.entities.get(id)?.data.parent === 'persistence'));`));
  /** @param {any} s */
  const outside = (s) => s.nodes.filter((/** @type {any} */ n) => !inside.includes(n.id) && n.id !== 'persistence').map((/** @type {any} */ n) => JSON.stringify({ ...n, parent: undefined }));
  expect(outside(persistence), 'expanding persistence leaves every other block as it was').toEqual(outside(before));
  await page.screenshot({ path: path.join(SHOTS, 'test-nav-persistence.png') });

  // No step changed the model, a verdict or the semantic hash.
  expect(await ex(page, 'return session.project.semanticHash;')).toBe(hash);
  expect(await ex(page, 'return session.claimResults.map((r) => [r.claimId, r.status]);')).toEqual(verdicts);
  expect(await ex(page, 'return session.project.canUndo;')).toBe(false);
});

// The deeper steps of the walk, outside the gate (@full): from persistence expanded, a component opened into its
// module elements, then the semantic core expanded, each step equal to the CLI.
test('a component opens into its module elements and the semantic core expands with each step equal to the CLI', { tag: '@full' }, async ({ page }) => {
  test.setTimeout(180_000);
  await openArchitecture(page);
  const hash = await ex(page, 'return session.project.semanticHash;');
  const verdicts = await ex(page, 'return session.claimResults.map((r) => [r.claimId, r.status]);');
  await page.getByTestId('cut-select').selectOption('persistence-expanded');
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.scene.abstraction?.cut === 'persistence-expanded');

  // 1. One component expanded into its module elements.
  await ex(page, `session.select('workspace-service');`);
  await page.getByTestId('block-expand').click();
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.scene.nodes.some((n) => n.elementKind === 'module'));
  const modules = await checkStep(page, 'workspace service to modules', 'module:tools/workspace.js');
  const declared = await ex(page, "return session.model.entities.get('workspace-service').data.implementation.modules.map((m) => 'module:' + m).sort();");
  expect(modules.blocks.filter((/** @type {string} */ b) => b.startsWith('module:'))).toEqual(declared);
  await page.screenshot({ path: path.join(SHOTS, 'test-nav-modules.png') });

  // 2. The semantic core expanded with persistence collapsed.
  await page.getByTestId('cut-select').selectOption('semantic-core-expanded');
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.scene.abstraction?.cut === 'semantic-core-expanded');
  await checkStep(page, 'semantic core expanded', 'claim-evaluator');
  await page.screenshot({ path: path.join(SHOTS, 'test-nav-semantic-core.png') });

  // No step changed the model, a verdict or the semantic hash.
  expect(await ex(page, 'return session.project.semanticHash;')).toBe(hash);
  expect(await ex(page, 'return session.claimResults.map((r) => [r.claimId, r.status]);')).toEqual(verdicts);
  expect(await ex(page, 'return session.project.canUndo;')).toBe(false);
});

test('a hidden block on a path becomes a labelled path summary and the view switches hierarchy', { tag: '@full' }, async ({ page }) => {
  await openArchitecture(page);
  await page.getByTestId('cut-select').selectOption('l1');
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.scene.abstraction?.cut === 'l1');
  await ex(page, `session.setHidden('persistence', true);`);
  const s = /** @type {any} */ (await ex(page, `
    const e = session.scene.edges.find((x) => x.pathSummary && x.from === 'application' && x.to === 'filesystem');
    return { edge: e ? { label: e.label, via: e.pathSummary.via, line: e.line, witnesses: e.witnesses } : null, notes: session.scene.notes, report: session.scene.filterReport,
      drawn: session.scene.nodes.some((n) => n.id === 'persistence') };`));
  expect(s.drawn).toBe(false);
  expect(s.edge).toMatchObject({ via: ['persistence'], line: 'dotted' });
  expect(s.edge.label).toMatch(/^may reach via 1 hidden \(Persistence\)/);
  expect(s.report.pathSummaries).toBeGreaterThan(0);
  expect(s.notes.join(' ')).toMatch(/1 element is hidden \(Persistence\); \d+ derived interactions touch hidden blocks, and \d+ connections through them are drawn as dotted path summaries/);
  // Selecting the summary lists the relationships along it.
  await ex(page, `const e = session.scene.edges.find((x) => x.id === 'summary:application->filesystem'); session.select(e.entityId, { edge: e.id });`);
  await expect(page.getByTestId('inspector').getByTestId('witness-row')).toHaveCount(s.edge.witnesses.length);
  await page.screenshot({ path: path.join(SHOTS, 'test-nav-hidden.png') });
  await ex(page, `session.setHidden('persistence', false);`);

  // The runtime hierarchy: the same view, drawn by where things run.
  await page.getByTestId('hierarchy-select').selectOption('runtime');
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.scene.abstraction?.hierarchy === 'runtime');
  const rt = await dump(page);
  const d = derived(cutArgs(rt));
  // The system has no members in the runtime hierarchy: a block the scene reports and does not draw.
  const notDrawn = /** @type {string[]} */ (await ex(page, 'return session.scene.filterReport?.removedBlocks ?? [];'));
  expect(notDrawn).toEqual(['exegra']);
  expect(await ex(page, 'return session.scene.notes.some((n) => n.includes("no members and no relationships"));')).toBe(true);
  expect({ blocks: [...rt.blocks, ...notDrawn].sort(), interactions: rt.interactions }).toEqual({ blocks: d.blocks, interactions: d.interactions });
});

test('the application attaches the extracted facts as the CLI does and adopts a changed fact file', { tag: '@full' }, async ({ page }) => {
  await openArchitecture(page);
  await page.getByTestId('cut-select').selectOption('l1');
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.scene.abstraction?.cut === 'l1');
  // The static dependencies are extracted facts (specs/<project>/extracted/facts.json), not declared relationships:
  // without them the scene has no imports interaction at all, and the comparison below fails.
  const imports = /** @type {any} */ (await ex(page, `return {
    attached: !!session.project.extracted,
    edges: session.scene.edges.filter((e) => e.kind === 'imports').map((e) => ({ key: e.key, witnesses: [...e.witnesses], marks: (e.marks ?? []).map((m) => m.kind + ':' + m.text) })),
  };`));
  expect(imports.attached, 'the session attaches the extracted facts to the project').toBe(true);
  const d = cli(['derive', '--cut', 'l1']);
  const expected = d.interactions.filter((/** @type {any} */ i) => i.kind === 'imports').map((/** @type {any} */ i) => ({ key: i.key, witnesses: i.witnesses }));
  expect(expected.length, 'the CLI derives imports interactions at L1 from the extracted facts').toBeGreaterThan(0);
  expect(imports.edges.map((/** @type {any} */ e) => ({ key: e.key, witnesses: e.witnesses })).sort((/** @type {any} */ a, /** @type {any} */ b) => (a.key < b.key ? -1 : 1)))
    .toEqual([...expected].sort((/** @type {any} */ a, /** @type {any} */ b) => (a.key < b.key ? -1 : 1)));
  const sem = await dump(page);
  const all = derived(['--cut', 'l1']);
  expect({ blocks: sem.blocks, interactions: sem.interactions }).toEqual({ blocks: all.blocks, interactions: all.interactions });
  // Their provenance is shown: every imports edge is marked as extracted, in text.
  for (const e of imports.edges) expect(e.marks, e.key).toContain('not-declared:extracted');
  // Selecting one lists its witnesses with provenance "extracted".
  await ex(page, `const e = session.scene.edges.find((x) => x.kind === 'imports'); session.select(e.entityId, { edge: e.id });`);
  await expect(page.getByTestId('witness-row').first().locator('[data-field="provenance"]')).toHaveText('extracted');

  // The fact file removed on disk: the application re-reads it and the imports interactions go; restored, they return.
  const file = path.join(ROOT, 'specs', SCRATCH.exegra, 'extracted', 'facts.json');
  const text = fs.readFileSync(file, 'utf8');
  fs.rmSync(file);
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.scene.edges.every((e) => e.kind !== 'imports'), null, { timeout: 20_000 });
  fs.writeFileSync(file, text);
  await page.waitForFunction((n) => /** @type {any} */ (window).__exegra.session.scene.edges.filter((e) => e.kind === 'imports').length === n, expected.length, { timeout: 20_000 });
  expect(await ex(page, 'return session.log.some((l) => /extracted facts changed on disk/.test(l.message));')).toBe(true);
});
