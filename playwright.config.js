import { createHash } from 'node:crypto';
import path from 'node:path';
import { defineConfig, devices } from '@playwright/test';

// One dev server port per checkout: the webServer below reuses a server already listening on its port, so two
// checkouts (worktrees) running Playwright at the same time on one port would test, and save into, each other's
// files. The default is derived from the repository root path (5200-5999); EXEGRA_TEST_PORT overrides it.
const PORT = Number(process.env.EXEGRA_TEST_PORT) || 5200 + (createHash('sha256').update(path.resolve(import.meta.dirname)).digest().readUInt32BE(0) % 800);

// The gate runs `npm run test:browser` (playwright test --grep-invert @full): the smoke journeys. That run has a wall-clock
// budget, the cap on the whole run, which includes starting the Vite server (the cap counts from the start of the run, so
// it is the server start plus the tests, not the tests alone). Measured: the three journeys of exegra.spec.js take 20 s
// in all, about 14 s of tests and the rest the server start; the M4 walk adds its own time. A test tagged @full re-checks one claim of the
// specification; `npm run test:browser:full`, `npm run verify` (each evidence reference runs its own tests) and the Check
// workflow run it, outside the budget.
const GATE = process.argv.includes('--grep-invert');
const GATE_BUDGET_MS = 60_000;

// Uses the locally installed Chrome so that no browser download is required.
const chrome = { browserName: /** @type {const} */ ('chromium'), channel: 'chrome' };

export default defineConfig({
  testDir: 'tests/browser',
  timeout: 60_000,
  globalTimeout: GATE ? GATE_BUDGET_MS : 0,
  // Two workers by default (the cap for test jobs); EXEGRA_TEST_WORKERS overrides. Each worker slot has its own
  // scratch projects (tests/browser/scratch.js), so the tests do not share files.
  workers: Math.max(1, Number(process.env.EXEGRA_TEST_WORKERS) || 2),
  fullyParallel: true,
  // The second reporter records each test's outcome with the tree stamp, for `exegra verify` to reuse.
  reporter: [['list'], ['./tools/outcomes-playwright-reporter.js']],
  globalSetup: './tests/browser/global-setup.js',
  globalTeardown: './tests/browser/global-teardown.js',
  use: {
    baseURL: `http://127.0.0.1:${PORT}`,
    ...chrome,
  },
  // The interface is designed for a phone first. Every existing test runs at desktop size;
  // tests/browser/mobile.spec.js tags each test with the size it is about (@phone, @tablet),
  // and a project picks its tests by tag, so running that file runs each test exactly once.
  projects: [
    {
      name: 'desktop',
      testIgnore: /mobile\.spec\.js$/,
      use: { ...chrome, viewport: { width: 1600, height: 1000 } },
    },
    {
      name: 'phone',
      testMatch: /mobile\.spec\.js$/,
      grep: /@phone/,
      // iPhone 13 is 390 by 844 CSS pixels with touch; Chrome emulates it (the descriptor's WebKit is not used).
      use: { ...devices['iPhone 13'], ...chrome, viewport: { width: 390, height: 844 }, hasTouch: true, isMobile: true },
    },
    {
      name: 'tablet',
      testMatch: /mobile\.spec\.js$/,
      grep: /@tablet/,
      use: { ...devices['iPad Mini'], ...chrome, viewport: { width: 820, height: 1180 }, hasTouch: true, isMobile: true },
    },
  ],
  webServer: {
    command: `npx vite --port ${PORT} --strictPort`,
    url: `http://127.0.0.1:${PORT}`,
    reuseExistingServer: true,
    timeout: 60_000,
  },
});
