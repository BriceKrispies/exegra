// Drive index.html in headless browsers with Playwright and print window.result.
// Usage: node check.mjs [url=http://127.0.0.1:5209/] [browsers=chromium,firefox,webkit]
import { chromium, firefox, webkit } from 'playwright';

const url = process.argv[2] ?? 'http://127.0.0.1:5209/';
const which = (process.argv[3] ?? 'chromium,firefox,webkit').split(',');
const kinds = { chromium, firefox, webkit };
// chromium: the installed Google Chrome (channel 'chrome'), so no Playwright Chromium download is needed
const options = { chromium: { channel: 'chrome' }, firefox: {}, webkit: {} };
for (const name of which) {
  const browser = await kinds[name].launch(options[name]);
  try {
    const page = await browser.newPage();
    page.on('pageerror', (e) => console.log(`[${name}] page error: ${e.message}`));
    await page.goto(url);
    await page.waitForFunction(() => window.result, null, { timeout: 300000 });
    console.log(`${name} ${browser.version()}:`, JSON.stringify(await page.evaluate(() => window.result), null, 1));
  } finally {
    await browser.close();
  }
}
