// The Lean core runs in the browser: the page loads src/engine/lean/ (wasm64) through src/core/lean.js,
// lists the registered functions, answers an unknown function with an error value, and engine.run
// reproduces a golden trace exactly; the application opens the self-specification with the Lean engine
// loaded, and the verified kernel derives the self-specification in the page (parse and hash, timed).
// Needs `npm run build:formal-wasm`.
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

test('the verified kernel derives the self-specification in the page', async ({ page }) => {
  await page.goto('/?project=exegra');
  await page.waitForFunction(() => {
    const x = /** @type {any} */ (window).__exegra;
    return x?.session.projectName === 'exegra' && x.session.model;
  });
  const out = await page.evaluate(async () => {
    const x = /** @type {any} */ (window).__exegra;
    const { parseSpec } = await import('/src/core/parse.js');
    const { semanticHash } = await import('/src/core/hash.js');
    const text = x.session.project.specText;
    const times = [];
    let hash = '';
    for (let i = 0; i < 7; i++) {
      const t0 = performance.now();
      const { model, diagnostics } = parseSpec(text);
      hash = semanticHash(model);
      times.push(performance.now() - t0);
      if (diagnostics.length) return { error: diagnostics[0].message };
    }
    times.sort((a, b) => a - b);
    return { hash, projectHash: x.session.project.semanticHash, entities: x.session.model.entities.size, median: times[3] };
  });
  expect(out.error).toBeUndefined();
  expect(out.hash).toMatch(/^[0-9a-f]{14}$/);
  expect(out.hash).toBe(out.projectHash);
  expect(out.entities).toBeGreaterThan(1000);
  test.info().annotations.push({ type: 'timing', description: `parse and hash of specs/exegra: median ${out.median.toFixed(1)} ms` });
});
