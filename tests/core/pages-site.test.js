// The GitHub Pages site (.github/workflows/pages.yml, vite.config.js): the static build is published
// from main, after the Lean core is built and Exegra's own specification validates, and it loads under
// the repository's sub-path because its asset URLs are relative.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
const workflow = fs.readFileSync(path.join(repoRoot, '.github', 'workflows', 'pages.yml'), 'utf8');

/** The `run:` and `uses:` values of the workflow's steps, in order. */
function steps() {
  return [...workflow.matchAll(/^\s*-?\s*(run|uses):\s*(.+)$/gm)].map((m) => ({ key: m[1], value: m[2].trim() }));
}

/** @param {(s: {key: string, value: string}) => boolean} pred */
function indexOfStep(pred) {
  const i = steps().findIndex(pred);
  assert.notEqual(i, -1, 'the workflow has the step');
  return i;
}

test('the production build uses relative asset URLs so it loads under a sub-path', async () => {
  const config = (await import('../../vite.config.js')).default;
  assert.equal(config.base, './');
});

test('the Pages workflow runs on every push to main', () => {
  assert.match(workflow, /^on:\s*\n\s+push:\s*\n\s+branches:\s*\[\s*main\s*\]/m);
  assert.match(workflow, /^\s+pages:\s*write$/m);
  assert.match(workflow, /^\s+id-token:\s*write$/m);
});

test('the Pages workflow builds the Lean core and validates the specification before it builds and deploys dist', () => {
  const lean = indexOfStep((s) => s.key === 'run' && /tools\/build-formal-wasm\.js|npm run build:formal-wasm/.test(s.value));
  const validate = indexOfStep((s) => s.key === 'run' && /cli\/exegra\.js validate --project exegra/.test(s.value));
  const build = indexOfStep((s) => s.key === 'run' && /vite build/.test(s.value));
  const upload = indexOfStep((s) => s.key === 'uses' && s.value.startsWith('actions/upload-pages-artifact@'));
  const deploy = indexOfStep((s) => s.key === 'uses' && s.value.startsWith('actions/deploy-pages@'));
  assert.ok(lean < validate && validate < build && build < upload && upload < deploy, 'the steps run in that order');
  assert.match(workflow, /upload-pages-artifact@[^\n]+\n\s+with:\s*\n\s+path:\s*dist\s*$/m);
});
