import { defineConfig, devices } from '@playwright/test';

const PORT = Number(process.env.EXEGRA_TEST_PORT) || 5199;

// Uses the locally installed Chrome so that no browser download is required.
const chrome = { browserName: /** @type {const} */ ('chromium'), channel: 'chrome' };

export default defineConfig({
  testDir: 'tests/browser',
  timeout: 60_000,
  workers: 1,
  fullyParallel: false,
  reporter: [['list']],
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
