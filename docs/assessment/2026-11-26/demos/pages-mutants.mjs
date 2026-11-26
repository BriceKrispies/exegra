// The two workflow assertions of tests/core/pages-site.test.js, copied verbatim, applied to mutants of
// .github/workflows/pages.yml under which no push to main publishes a validated build.
import fs from 'node:fs';
const orig = fs.readFileSync('../../../../.github/workflows/pages.yml', 'utf8');
function check(workflow) {
  const steps = () => [...workflow.matchAll(/^\s*-?\s*(run|uses):\s*(.+)$/gm)].map((m) => ({ key: m[1], value: m[2].trim() }));
  const idx = (p) => { const i = steps().findIndex(p); if (i === -1) throw new Error('missing step'); return i; };
  if (!/^on:\s*\n\s+push:\s*\n\s+branches:\s*\[\s*main\s*\]/m.test(workflow)) return 'FAIL on-push';
  if (!/^\s+pages:\s*write$/m.test(workflow) || !/^\s+id-token:\s*write$/m.test(workflow)) return 'FAIL perms';
  const lean = idx((s) => s.key === 'run' && /tools\/build-formal-wasm\.js|npm run build:formal-wasm/.test(s.value));
  const validate = idx((s) => s.key === 'run' && /cli\/exegra\.js validate --project exegra/.test(s.value));
  const build = idx((s) => s.key === 'run' && /vite build/.test(s.value));
  const upload = idx((s) => s.key === 'uses' && s.value.startsWith('actions/upload-pages-artifact@'));
  const deploy = idx((s) => s.key === 'uses' && s.value.startsWith('actions/deploy-pages@'));
  if (!(lean < validate && validate < build && build < upload && upload < deploy)) return 'FAIL order';
  if (!/upload-pages-artifact@[^\n]+\n\s+with:\s*\n\s+path:\s*dist\s*$/m.test(workflow)) return 'FAIL path';
  return 'PASS';
}
const mutants = {
  original: orig,
  'deploy job never runs (if: false)': orig.replace("if: github.ref == 'refs/heads/main'", 'if: false'),
  'validation failure ignored (|| true)': orig.replace('validate --project exegra --pretty', 'validate --project exegra --pretty || true'),
  'push limited to a path that never changes': orig.replace('branches: [main]', 'branches: [main]\n    paths: [does-not-exist/**]'),
  'deploy no longer waits for build (needs removed)': orig.replace('    needs: build\n', ''),
  'whole workflow disabled at job level': orig.replace('    runs-on: ubuntu-latest\n    steps:', "    if: false\n    runs-on: ubuntu-latest\n    steps:"),
};
for (const [name, text] of Object.entries(mutants)) console.log(`${check(text).padEnd(6)} ${name}${text === orig && name !== 'original' ? '  (mutation did not apply!)' : ''}`);
