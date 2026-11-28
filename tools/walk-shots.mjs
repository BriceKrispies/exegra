// Evidence for multiscale navigation (WG-5695): walk Exegra's own specification from the system in its
// environment down to module elements in the running application, on a phone and a desktop layout, and at
// every step save a screenshot and a semantic dump of the scene with the result of comparing it with what the
// command line derives for the same cut. Usage (the development server must be running):
//   node tools/walk-shots.mjs [--url http://127.0.0.1:5173/] [--project exegra] [--out screenshots/walk] [--sizes phone,desktop]
// Writes <out>/<size>-<n>-<step>.png and .json, and <out>/summary.json; exits 1 when a step differs from the CLI.
import { chromium } from '@playwright/test';
import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const args = process.argv.slice(2);
const opt = (/** @type {string} */ name, /** @type {string} */ dflt) => {
  const i = args.indexOf(name);
  return i >= 0 ? args[i + 1] : dflt;
};
const URL_BASE = opt('--url', 'http://127.0.0.1:5173/');
const PROJECT = opt('--project', 'exegra');
const OUT = path.resolve(ROOT, opt('--out', 'screenshots/walk'));
const SIZES = /** @type {Record<string, any>} */ ({
  desktop: { viewport: { width: 1600, height: 1000 } },
  phone: { viewport: { width: 390, height: 844 }, isMobile: true, hasTouch: true, deviceScaleFactor: 2 },
});
const sizes = opt('--sizes', 'phone,desktop').split(',').filter((s) => SIZES[s]);
fs.mkdirSync(OUT, { recursive: true });

/**
 * The steps of the walk. `run` is evaluated in the page with session and view in scope; `focus` names the inspector
 * section to bring into view for the screenshot.
 * @type {{name: string, run: string, focus?: string}[]}
 */
const STEPS = [
  { name: 'l0-system-in-its-environment', run: `session.select(null); session.setCut('l0');` },
  { name: 'l1-subsystems', run: `session.select(null); session.setCut('l1');` },
  { name: 'persistence-expanded', run: `session.select(null); session.setCut('persistence-expanded');` },
  { name: 'component-to-modules', run: `session.select(null); session.setCut('persistence-expanded'); session.toggleCollapsed('workspace-service');` },
  { name: 'semantic-core-expanded-persistence-collapsed', run: `session.select(null); session.setCut('semantic-core-expanded');` },
  {
    name: 'bundled-edge-witnesses',
    run: `session.setCut('l1'); const e = session.scene.edges.find((x) => x.key === 'application->semantic-core:invokes'); session.select(e.entityId, { edge: e.id, source: 'scene' });`,
    focus: 'derived-interaction',
  },
  { name: 'block-interface', run: `session.setCut('l1'); session.select('persistence', { source: 'scene' });`, focus: 'block-panel' },
  { name: 'hidden-block-path-summaries', run: `session.select(null); session.setCut('l1'); session.setHidden('persistence', true);` },
];

/** The scene's semantic content (src/core/projections.js, sceneSemantics). */
const DUMP = `
  const s = session.scene;
  const byKey = (a, b) => (a.key < b.key ? -1 : a.key > b.key ? 1 : 0);
  const sel = session.selection;
  const edge = session.selectedEdge ? s.edges.find((e) => e.id === session.selectedEdge) : null;
  return {
    view: s.viewId, hierarchy: s.abstraction?.hierarchy ?? null, cut: s.abstraction?.cut ?? null, cutBlocks: s.abstraction?.blocks ?? [], expanded: s.abstraction?.expanded ?? [],
    blocks: s.nodes.filter((n) => n.block).map((n) => n.id).sort(),
    containers: s.nodes.filter((n) => n.container).map((n) => n.id).sort(),
    interactions: s.edges.filter((e) => e.key).map((e) => ({ key: e.key, witnesses: [...e.witnesses] })).sort(byKey),
    pathSummaries: s.edges.filter((e) => e.pathSummary).map((e) => ({ from: e.from, to: e.to, via: e.pathSummary.via, witnesses: e.witnesses })),
    marks: Object.fromEntries(s.nodes.filter((n) => n.marks?.length).map((n) => [n.id, n.marks.map((m) => m.kind)])),
    filterReport: s.filterReport ?? null, levelClaims: s.levelClaims ?? [], notes: s.notes,
    layout: session.layout.used, selection: sel, selectedEdge: edge ? { id: edge.id, key: edge.key ?? null, witnesses: edge.witnesses } : null,
    inspector: [...document.querySelectorAll('[data-testid="witness-row"]')].map((r) => r.dataset.witness),
    block: document.querySelector('[data-testid="block-panel"]')?.dataset.element ?? null,
    semanticHash: session.project.semanticHash,
  };`;

/** @param {string[]} cliArgs */
function cli(cliArgs) {
  const run = spawnSync(process.execPath, ['cli/exegra.js', ...cliArgs, '--project', PROJECT], { cwd: ROOT, encoding: 'utf8', maxBuffer: 64 * 1024 * 1024 });
  return JSON.parse(run.stdout);
}

/** Compare a dump with `exegra derive` and `exegra evaluate` at the same cut. @param {any} d */
function compare(d) {
  const cutArgs = d.cut ? ['--cut', d.cut] : ['--hierarchy', d.hierarchy, ...(d.expanded.length ? ['--expand', d.expanded.join(',')] : ['--depth', '0'])];
  const derived = cli(['derive', ...cutArgs]).result;
  const blocks = derived.blocks.map((/** @type {any} */ b) => b.id).sort();
  const interactions = derived.interactions.map((/** @type {any} */ i) => ({ key: i.key, witnesses: i.witnesses })).sort((/** @type {any} */ a, /** @type {any} */ b) => (a.key < b.key ? -1 : a.key > b.key ? 1 : 0));
  // A hidden block is the one thing the scene removes on purpose: compare the rest, and the summaries that replace it.
  const hidden = new Set(d.filterReport?.removedBlocks ?? []);
  const expectBlocks = blocks.filter((/** @type {string} */ b) => !hidden.has(b));
  const expectInteractions = interactions.filter((/** @type {any} */ i) => { const [from, rest] = i.key.split('->'); return !hidden.has(from) && !hidden.has(rest.slice(0, rest.lastIndexOf(':'))); });
  const claims = (d.levelClaims ?? []).map((/** @type {any} */ c) => {
    const r = cli(['evaluate', c.claimId, ...cutArgs]).result.results[0];
    return { claimId: c.claimId, shown: c.status, cli: r.status, equal: r.status === c.status };
  });
  const edgeEqual = d.selectedEdge?.key ? JSON.stringify(d.inspector) === JSON.stringify(derived.interactions.find((/** @type {any} */ i) => i.key === d.selectedEdge.key)?.witnesses) : null;
  return {
    cli: `exegra derive ${cutArgs.join(' ')}`,
    blocksEqual: JSON.stringify(d.blocks) === JSON.stringify(expectBlocks),
    interactionsEqual: JSON.stringify(d.interactions) === JSON.stringify(expectInteractions),
    witnessListEqual: edgeEqual,
    claims,
  };
}

const browser = await chromium.launch().catch(() => chromium.launch({ channel: 'chrome' }));
/** @type {any[]} */
const summary = [];
let failed = false;
for (const size of sizes) {
  const context = await browser.newContext(SIZES[size]);
  const page = await context.newPage();
  /** @type {string[]} */
  const problems = [];
  page.on('pageerror', (e) => problems.push(`[pageerror] ${e.message}`));
  page.on('console', (m) => { if (m.type() === 'error') problems.push(`[console] ${m.text()}`); });
  await page.goto(`${URL_BASE}?project=${encodeURIComponent(PROJECT)}`, { waitUntil: 'load' });
  await page.waitForFunction((name) => {
    const x = /** @type {any} */ (window).__exegra;
    return x?.session.projectName === name && x.session.model && x.view.getStats().nodes > 0;
  }, PROJECT, { timeout: 60_000 });
  await page.evaluate(`(() => { const { session } = window.__exegra; session.setView('architecture'); session.resetCut(); for (const id of [...session.ui.hidden]) session.setHidden(id, false); })()`);
  for (const [i, step] of STEPS.entries()) {
    await page.evaluate(`(() => { const { session, view } = window.__exegra; ${step.run} })()`);
    await page.waitForTimeout(900);
    await page.evaluate(`(() => { const { session } = window.__exegra; session.requestFit(); })()`);
    await page.waitForTimeout(700);
    if (step.focus) await page.locator(`[data-testid="${step.focus}"]`).first().scrollIntoViewIfNeeded().catch(() => {});
    const base = path.join(OUT, `${size}-${i + 1}-${step.name}`);
    await page.screenshot({ path: `${base}.png` });
    const dump = /** @type {any} */ (await page.evaluate(`(() => { const { session, view } = window.__exegra; ${DUMP} })()`));
    const result = compare(dump);
    const ok = result.blocksEqual && result.interactionsEqual && result.witnessListEqual !== false && result.claims.every((/** @type {any} */ c) => c.equal);
    if (!ok) failed = true;
    fs.writeFileSync(`${base}.json`, JSON.stringify({ size, step: step.name, ok, comparison: result, scene: dump }, null, 1) + '\n');
    summary.push({ size, step: step.name, ok, cut: dump.cut ?? `interactive (${dump.cutBlocks.length} blocks)`, blocks: dump.blocks.length, interactions: dump.interactions.length, layout: dump.layout, comparison: result });
    console.log(`${ok ? 'ok  ' : 'DIFF'} ${size} ${i + 1} ${step.name}: ${dump.blocks.length} blocks, ${dump.interactions.length} interactions, layout ${dump.layout}`);
  }
  await page.evaluate(`(() => { const { session } = window.__exegra; session.setHidden('persistence', false); session.resetCut(); session.select(null); })()`);
  for (const p of problems.slice(0, 20)) console.log(p);
  await context.close();
}
fs.writeFileSync(path.join(OUT, 'summary.json'), JSON.stringify(summary, null, 1) + '\n');
console.log(`saved ${summary.length} steps under ${path.relative(ROOT, OUT)}`);
await browser.close();
process.exit(failed ? 1 : 0);
