// The Simulation tab runs the engine in a Web Worker: a long run does not block the page.
import { test, expect } from '@playwright/test';
import { SCRATCH, resetScratch } from './scratch.js';

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

/** @param {import('@playwright/test').Page} page @param {string} body */
const ex = (page, body) => page.evaluate(`(() => { const { session, view } = window.__exegra; ${body} })()`);

test('a long simulation runs in a worker while the page stays responsive', { tag: '@full' }, async ({ page }) => {
  await page.goto(`/?project=${SCRATCH.multiplayer}`);
  await page.waitForFunction((name) => {
    const x = /** @type {any} */ (window).__exegra;
    return x?.session.projectName === name && x.session.model && x.view.getStats().nodes > 0;
  }, SCRATCH.multiplayer);
  await page.waitForTimeout(500);

  // A scenario that loops up to a large step limit, added through a transaction. Every step evaluates
  // an expression of 8192 terms (all zero) while the trace stays small: one variable, one event. The
  // step limit keeps the run at several seconds on the behaviour calculus's scheduler, which evaluates
  // boxed integers with checked arithmetic: about 1.1 ms per step of this expression in WebAssembly over
  // 5000 steps (measured 2026-11-27, Node 24), against about 0.6 ms for the float evaluator of the
  // removed format-1 engine, whose 20000 steps this test used to run (WG-5681).
  const created = await ex(page, `
    const term = (d) => d === 0 ? '(n - n)' : '(' + term(d - 1) + ' + ' + term(d - 1) + ')';
    const subject = session.model.byKind.component[0].id;
    const r = session.apply([
      { type: 'CreateEntity', kind: 'event', data: { id: 'load-tick', name: 'Load tick' } },
      { type: 'CreateEntity', kind: 'behavior', data: {
        id: 'load-ticker', name: 'Load ticker', subject, initial: 'load-on',
        variables: [{ name: 'n', type: 'number', initial: 0 }],
        states: [{ id: 'load-on', name: 'On' }],
        transitions: [{ id: 'load-step', from: 'load-on', to: 'load-on', on: 'load-tick',
          effects: [{ set: 'n', to: 'n + 1 + ' + term(12) }, { emit: 'load-tick', after: 1 }] }],
      } },
      { type: 'CreateEntity', kind: 'scenario', data: {
        id: 'load-long-run', name: 'Long run', behaviors: ['load-ticker'], steps: [{ at: 0, event: 'load-tick' }], maxSteps: 5000,
      } },
    ], { label: 'Add a long-running scenario' });
    return r.ok ? true : r.message;`);
  expect(created).toBe(true);

  // Count animation frames, and note whether the UI reacted to input, while the run is in progress.
  await ex(page, `
    const f = window.__frames = { whileRunning: 0, uiWhileRunning: null, stop: false };
    const tick = () => { if (session.sim.running) f.whileRunning++; if (!f.stop) requestAnimationFrame(tick); };
    requestAnimationFrame(tick);
    session.on('ui', () => { if (session.ui.mode === 'connect' && f.uiWhileRunning === null) f.uiWhileRunning = session.sim.running; });`);

  await page.getByTestId('tab-btn-simulation').click();
  await page.getByTestId('sim-scenario').selectOption('load-long-run');
  await expect(page.getByTestId('sim-running')).toBeVisible();
  await expect(page.getByTestId('sim-readout')).toHaveText('running…');

  // The toolbar still reacts while the engine runs.
  await page.getByTestId('mode-connect').click();
  await page.waitForFunction(() => /** @type {any} */ (window).__exegra.session.ui.mode === 'connect');

  await page.waitForFunction(() => {
    const s = /** @type {any} */ (window).__exegra.session.sim;
    return !s.running && !!s.simulation;
  }, null, { timeout: 60_000 });
  const frames = /** @type {any} */ (await ex(page, `window.__frames.stop = true; return window.__frames;`));
  expect(frames.uiWhileRunning, 'the toolbar reacted while the run was in progress').toBe(true);
  expect(frames.whileRunning, 'animation frames kept coming while the run was in progress').toBeGreaterThanOrEqual(5);

  // The finished run is stepped as before: the first step adds one to n.
  await page.getByTestId('mode-select').click();
  const first = /** @type {any} */ (await ex(page, `
    session.simStep();
    const s = session.sim;
    return { index: s.stepIndex, outcome: s.simulation.outcome, after: s.simulation.steps[0].fired[0].sets[0].after };`));
  expect(first).toEqual({ index: 0, outcome: 'running', after: 1 });
  await expect(page.getByTestId('sim-running')).toHaveCount(0);
});
