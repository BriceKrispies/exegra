// An accepted candidate decomposition is navigable at once (WG-5735, M7; src/core/decomposition.js acceptCandidate,
// `exegra accept-decomposition`). On a scratch copy of the self-specification the command line accepts the audit's second
// grouping of the semantic core as one transaction; the application, opened afterwards, offers the new hierarchy and its
// two cuts, draws each as the command line derives it (blocks, interactions and their witnesses), shows the level-bound
// claim stated at l1 at the cut where the semantic core is one block and the one at the cut that opens it as the command
// line evaluates them, and keeps the logical hierarchy as it was. The screenshots are saved to screenshots/ as
// test-accepted-*.png, for the navigation walk the audit asks for. Run: npx playwright test tests/browser/decomposition-navigation.spec.js
import { test, expect } from '@playwright/test';
import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import os from 'node:os';
import { ROOT, SCRATCH, resetScratch } from './scratch.js';

const SHOTS = path.join(ROOT, 'screenshots');
fs.mkdirSync(SHOTS, { recursive: true });
const AUDIT = 'tests/fixtures/decomposition/semantic-core-audit.json';
const CANDIDATE = 'audit-second';
/** A claim stated at a cut of the accepted hierarchy: core-independent-of-ui's statement, at the scope as one block. */
const ACC_CLAIM = 'accepted-core-independent-of-ui';

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
  const run = spawnSync(process.execPath, ['cli/exegra.js', ...args, '--project', SCRATCH.exegra], { cwd: ROOT, encoding: 'utf8', maxBuffer: 256 * 1024 * 1024 });
  const out = JSON.parse(run.stdout);
  expect(out.ok, `exegra ${args.join(' ')}: ${run.stdout.slice(0, 600)}`).toBe(true);
  return out.result;
}

/** The scene's semantic content. @param {import('@playwright/test').Page} page */
const dump = (page) => /** @type {Promise<any>} */ (ex(page, `
  const s = session.scene;
  const byKey = (a, b) => (a.key < b.key ? -1 : a.key > b.key ? 1 : 0);
  return {
    cut: s.abstraction?.cut ?? null, hierarchy: s.abstraction?.hierarchy ?? null, cutBlocks: s.abstraction?.blocks ?? [],
    blocks: s.nodes.filter((n) => n.block).map((n) => n.id).sort(),
    interactions: s.edges.filter((e) => e.key).map((e) => ({ key: e.key, witnesses: [...e.witnesses] })).sort(byKey),
    summaries: s.edges.filter((e) => e.pathSummary).length,
    levelClaims: s.levelClaims ?? [],
  };`));

/** What `exegra derive` prints for a cut, reduced to blocks and interactions. @param {string} cut */
function derived(cut) {
  const d = cli(['derive', '--cut', cut]);
  return {
    blocks: d.blocks.map((/** @type {any} */ b) => b.id).sort(),
    interactions: d.interactions.map((/** @type {any} */ i) => ({ key: i.key, witnesses: i.witnesses })).sort((/** @type {any} */ a, /** @type {any} */ b) => (a.key < b.key ? -1 : a.key > b.key ? 1 : 0)),
    d,
  };
}

/** @param {import('@playwright/test').Page} page @param {string} hierarchy @param {string} cut */
async function openCut(page, hierarchy, cut) {
  await page.getByTestId('hierarchy-select').selectOption(hierarchy);
  await page.waitForFunction((h) => /** @type {any} */ (window).__exegra.session.scene.abstraction?.hierarchy === h, hierarchy);
  await page.getByTestId('cut-select').selectOption(cut);
  await page.waitForFunction((c) => /** @type {any} */ (window).__exegra.session.scene.abstraction?.cut === c, cut);
  await page.waitForTimeout(500);
}

test('an accepted decomposition is navigated at once and its level-bound claim agrees with the command line', async ({ page }) => {
  test.setTimeout(240_000);
  const logicalBefore = cli(['derive', '--cut', 'l1']);

  // 1. The decision, as one transaction on the scratch copy.
  const accepted = cli(['accept-decomposition', '--scope', 'semantic-core', '--file', AUDIT, '--candidate', CANDIDATE]);
  expect(accepted.hierarchy).toBe(CANDIDATE);
  expect(accepted.cuts).toEqual([`${CANDIDATE}-top`, `${CANDIDATE}-cut`]);
  expect(accepted.conditions.map((/** @type {any} */ c) => `${c.id}:${c.status}`)).toEqual(['V1:pass', 'V2:pass', 'V3:pass', 'V4:pass', 'V5:pass', 'V6:not-applicable', 'V7:pass']);
  expect(accepted.transaction.semanticChanged).toBe(true);
  const blocks = ['editing', 'model-kernel', 'simulation', 'verdicts', 'well-formedness'];
  expect(accepted.components.sort()).toEqual(blocks);
  // A level-bound claim of the new hierarchy, stated at its top cut through a second transaction.
  const original = cli(['get', 'core-independent-of-ui'])[0].data;
  const ops = path.join(fs.mkdtempSync(path.join(os.tmpdir(), 'exegra-acc-')), 'claim.json');
  fs.writeFileSync(ops, JSON.stringify([{ type: 'CreateEntity', kind: 'claim', data: { ...original, id: ACC_CLAIM, statement: `${original.statement} (stated at the accepted hierarchy's top cut)`, evaluate: { ...original.evaluate, cut: `${CANDIDATE}-top` } } }]));
  cli(['apply', '--file', ops]);

  // 2. The application opens it and offers the hierarchy and the cuts, without any further step.
  await page.goto(`/?project=${SCRATCH.exegra}`);
  await page.waitForFunction((name) => {
    const x = /** @type {any} */ (window).__exegra;
    return x?.session.projectName === name && x.session.model && x.view.getStats().nodes > 0;
  }, SCRATCH.exegra);
  await ex(page, `session.setView('architecture');`);
  await page.waitForTimeout(400);
  const hierarchies = await page.getByTestId('hierarchy-select').locator('option').evaluateAll((os) => os.map((o) => /** @type {HTMLOptionElement} */ (o).value));
  expect(hierarchies).toContain(CANDIDATE);

  // 3. The scope as one block: the scene is the derived model of the cut, and the claim stated at l1 is expressible.
  await openCut(page, CANDIDATE, `${CANDIDATE}-top`);
  const top = await dump(page);
  const topCli = derived(`${CANDIDATE}-top`);
  expect({ blocks: top.blocks, interactions: top.interactions }).toEqual({ blocks: topCli.blocks, interactions: topCli.interactions });
  expect(top.summaries).toBe(0);
  const claimTop = cli(['evaluate', ACC_CLAIM]).results[0];
  // The scope as one block is the cut l1 of the logical hierarchy, so the claim stated there must say what
  // core-independent-of-ui says at l1, in the same mode.
  expect(claimTop.status).toBe(cli(['evaluate', 'core-independent-of-ui']).results[0].status);
  expect((claimTop.diagnostics ?? []).some((/** @type {any} */ x) => x.code === 'claim.not-expressible')).toBe(false);
  const shownTop = top.levelClaims.find((/** @type {any} */ c) => c.claimId === ACC_CLAIM);
  expect(shownTop?.status).toBe(claimTop.status);
  expect(shownTop?.expressible).toBe(true);
  await page.screenshot({ path: path.join(SHOTS, 'test-accepted-top.png') });

  // 4. The scope opened into the five blocks of the candidate.
  await openCut(page, CANDIDATE, `${CANDIDATE}-cut`);
  const cut = await dump(page);
  const cutCli = derived(`${CANDIDATE}-cut`);
  expect({ blocks: cut.blocks, interactions: cut.interactions }).toEqual({ blocks: cutCli.blocks, interactions: cutCli.interactions });
  for (const b of blocks) expect(cut.blocks).toContain(b);
  expect(cut.hierarchy).toBe(CANDIDATE);
  const claimCut = cli(['evaluate', ACC_CLAIM, '--cut', `${CANDIDATE}-cut`]).results[0];
  const shownCut = cut.levelClaims.find((/** @type {any} */ c) => c.claimId === ACC_CLAIM);
  expect(shownCut?.status).toBe(claimCut.status);
  expect(shownCut?.expressible).toBe(!(claimCut.diagnostics ?? []).some((/** @type {any} */ x) => x.code === 'claim.not-expressible'));
  await page.screenshot({ path: path.join(SHOTS, 'test-accepted-cut.png') });

  // 5. A block of the candidate: its panel shows the boundary the command line derives, and an edge lists its witnesses.
  await ex(page, `session.select('model-kernel', { source: 'scene' });`);
  const panel = page.getByTestId('inspector').getByTestId('block-panel');
  await expect(panel).toHaveAttribute('data-element', 'model-kernel');
  const boundary = cutCli.d.boundaries['model-kernel'];
  await expect(page.getByTestId('inspector').getByTestId('block-boundary')).toHaveAttribute('data-out', String(boundary.out.length));
  await expect(page.getByTestId('inspector').getByTestId('block-boundary')).toHaveAttribute('data-in', String(boundary.in.length));
  const edge = cut.interactions.reduce((/** @type {any} */ a, /** @type {any} */ b) => (b.witnesses.length > a.witnesses.length ? b : a));
  const edgeId = /** @type {string} */ (await ex(page, `return session.scene.edges.find((e) => e.key === ${JSON.stringify(edge.key)}).id;`));
  await ex(page, `session.select(${JSON.stringify(edgeId)}, { edge: ${JSON.stringify(edgeId)} });`);
  await expect(page.getByTestId('inspector').getByTestId('witness-row')).toHaveCount(edge.witnesses.length);
  await page.screenshot({ path: path.join(SHOTS, 'test-accepted-witnesses.png') });

  // 6. The logical hierarchy is as it was: the cut l1 derives the same blocks and interactions.
  await ex(page, 'session.select(null);');
  await openCut(page, 'logical', 'l1');
  const l1 = await dump(page);
  const key = (/** @type {any} */ a, /** @type {any} */ b) => (a.key < b.key ? -1 : a.key > b.key ? 1 : 0);
  expect({ blocks: l1.blocks, interactions: l1.interactions }).toEqual({
    blocks: logicalBefore.blocks.map((/** @type {any} */ b) => b.id).sort(),
    interactions: logicalBefore.interactions.map((/** @type {any} */ i) => ({ key: i.key, witnesses: i.witnesses })).sort(key),
  });
  expect(l1.blocks).toContain('semantic-core');
  await page.screenshot({ path: path.join(SHOTS, 'test-accepted-logical.png') });
});
