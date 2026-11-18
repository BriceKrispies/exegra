// The Lean core runs in the browser: the page loads src/engine/lean/ (wasm64) through src/core/lean.js,
// lists the registered functions, answers an unknown function with an error value, and engine.run
// reproduces a golden trace exactly; the application opens the self-specification with the Lean engine
// loaded. Needs `npm run build:formal-wasm`.
import { test, expect } from '@playwright/test';
import fs from 'node:fs';
import path from 'node:path';

const GOLDENS = path.join(process.cwd(), 'tests', 'conformance', 'goldens');

/** @type {string[]} */
let pageErrors = [];

test.beforeEach(({ page }) => {
  pageErrors = [];
  page.on('pageerror', (e) => pageErrors.push(e.message));
});

test.afterEach(() => {
  expect(pageErrors, 'no uncaught errors in the page').toEqual([]);
});

test('the Lean core runs in the page and reproduces golden traces', async ({ page }) => {
  await page.goto('/?project=exegra');
  await page.waitForFunction(() => {
    const x = /** @type {any} */ (window).__exegra;
    return x?.session.projectName === 'exegra' && x.session.model;
  });
  const names = ['fixture/core-flow', 'exegra/app-start-and-open'];
  const inputs = names.map((n) => fs.readFileSync(path.join(GOLDENS, `${n}.input.json`), 'utf8'));
  const out = await page.evaluate(async (texts) => {
    const lean = await import('/src/core/lean.js');
    await lean.initLean();
    const started = performance.now();
    const traces = texts.map((t) => lean.callText('engine.run', t));
    return {
      ready: lean.leanReady(),
      functions: lean.leanFunctions().map((/** @type {{name: string}} */ f) => f.name),
      unknown: lean.call('no.such.function', {}),
      traces,
      ms: performance.now() - started,
    };
  }, inputs);
  expect(out.ready).toBe(true);
  expect(out.functions).toContain('engine.run');
  expect(out.unknown).toEqual({ ok: false, error: 'unknown function "no.such.function"' });
  names.forEach((n, i) => {
    const r = out.traces[i];
    expect(r.ok, n).toBe(true);
    const golden = JSON.parse(fs.readFileSync(path.join(GOLDENS, `${n}.trace.json`), 'utf8'));
    expect(JSON.parse(r.text), n).toEqual(golden);
  });
  test.info().annotations.push({ type: 'timing', description: `two goldens in ${out.ms.toFixed(1)} ms` });
});
