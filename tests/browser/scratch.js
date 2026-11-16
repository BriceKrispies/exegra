// Browser tests never touch the shipped specifications. They work on scratch
// copies under specs/zz-test-*, recreated before every test.
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

export const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
export const SPECS = path.join(ROOT, 'specs');
export const SCRATCH = { exegra: 'zz-test-exegra', multiplayer: 'zz-test-multiplayer' };
// Where each scratch project is copied from. The multiplayer platform is a test
// fixture (an illustrative example with behaviors, faults and seeded violations),
// not a shipped project.
const SOURCES = { exegra: path.join(SPECS, 'exegra'), multiplayer: path.join(ROOT, 'tests', 'fixtures', 'multiplayer') };

/** @param {'exegra'|'multiplayer'} which */
export function resetScratch(which) {
  const dir = path.join(SPECS, SCRATCH[which]);
  // Reset in place: the dev server's glob of specs/*/spec.jsonc must never see the file missing,
  // or a page load in that moment fails to resolve its import.
  fs.mkdirSync(dir, { recursive: true });
  for (const entry of fs.readdirSync(dir)) {
    if (entry !== 'spec.jsonc') fs.rmSync(path.join(dir, entry), { recursive: true, force: true });
  }
  fs.copyFileSync(path.join(SOURCES[which], 'spec.jsonc'), path.join(dir, 'spec.jsonc'));
  const recorded = path.join(SOURCES[which], 'evidence', 'results.json');
  if (fs.existsSync(recorded)) {
    fs.mkdirSync(path.join(dir, 'evidence'), { recursive: true });
    fs.copyFileSync(recorded, path.join(dir, 'evidence', 'results.json'));
  }
}

export function removeScratch() {
  for (const name of Object.values(SCRATCH)) fs.rmSync(path.join(SPECS, name), { recursive: true, force: true });
}

/** @param {'exegra'|'multiplayer'} which @param {string} file */
export function readScratch(which, file) {
  const p = path.join(SPECS, SCRATCH[which], file);
  return fs.existsSync(p) ? fs.readFileSync(p, 'utf8') : null;
}
