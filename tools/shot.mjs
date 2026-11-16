// Development aid: load the running app, optionally run a snippet, save a screenshot,
// and print console errors. Usage:
//   node tools/shot.mjs <out.png> [--url <url>] [--eval "<js run in page>"] [--wait <ms>] [--size 1600x1000]
import { chromium } from '@playwright/test';

const args = process.argv.slice(2);
const out = args[0];
const opt = (/** @type {string} */ name, /** @type {string} */ dflt) => {
  const i = args.indexOf(name);
  return i >= 0 ? args[i + 1] : dflt;
};
const [w, h] = opt('--size', '1600x1000').split('x').map(Number);
const browser = await chromium.launch().catch(() => chromium.launch({ channel: 'chrome' }));
const page = await browser.newPage({ viewport: { width: w, height: h } });
/** @type {string[]} */
const problems = [];
page.on('console', (m) => { if (m.type() === 'error' || m.type() === 'warning') problems.push(`[${m.type()}] ${m.text()}`); });
page.on('pageerror', (e) => problems.push(`[pageerror] ${e.message}\n${e.stack?.split('\n').slice(0, 4).join('\n')}`));
await page.goto(opt('--url', 'http://127.0.0.1:5173/'), { waitUntil: 'load' });
await page.waitForTimeout(Number(opt('--wait', '1500')));
const code = opt('--eval', '');
if (code) {
  const result = await page.evaluate(`(async () => { ${code} })()`).catch((e) => `EVAL ERROR: ${e.message}`);
  if (result !== undefined) console.log('eval:', typeof result === 'string' ? result : JSON.stringify(result));
  await page.waitForTimeout(Number(opt('--after', '700')));
}
await page.screenshot({ path: out });
for (const p of problems.slice(0, 25)) console.log(p);
console.log(`saved ${out} (${problems.length} console problem(s))`);
await browser.close();
