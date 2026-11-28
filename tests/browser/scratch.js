// Browser tests never touch the shipped specifications. They work on scratch
// copies under specs/zz-test-*, recreated before every test.
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { readSpecFile } from '../../tools/spec-manifest.js';

export const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
export const SPECS = path.join(ROOT, 'specs');
// Each Playwright worker slot (TEST_PARALLEL_INDEX, stable across worker restarts) owns its own pair of
// scratch projects, zz-test-exegra-w0, zz-test-multiplayer-w0, zz-test-exegra-w1, ..., so edits, saves, the
// journal and change notices never cross workers. The names resolve when read, inside the worker.
export const SCRATCH = {
  get exegra() { return scratchName('exegra'); },
  get multiplayer() { return scratchName('multiplayer'); },
};

/** The slot of the current process; the global setup and teardown (no worker) address every slot. */
function slot() { return Number(process.env.TEST_PARALLEL_INDEX ?? 0) || 0; }
/** @param {'exegra'|'multiplayer'} which @param {number} [index] */
export function scratchName(which, index = slot()) { return `zz-test-${which}-w${index}`; }
/** How many worker slots the run may use (playwright.config.js reads the same variable). */
export function workerCount() { return Math.max(1, Number(process.env.EXEGRA_TEST_WORKERS) || 2); }
// Where each scratch project is copied from. The multiplayer platform is a test
// fixture (an illustrative example with behaviors, faults and seeded violations),
// not a shipped project.
const SOURCES = { exegra: path.join(SPECS, 'exegra'), multiplayer: path.join(ROOT, 'tests', 'fixtures', 'multiplayer') };

/** @param {'exegra'|'multiplayer'} which @param {number} [index] */
export function resetScratch(which, index = slot()) {
  const dir = path.join(SPECS, scratchName(which, index));
  // Reset in place: the dev server's glob of specs/*/spec.jsonc must never see the file missing,
  // or a page load in that moment fails to resolve its import.
  fs.mkdirSync(dir, { recursive: true });
  for (const entry of fs.readdirSync(dir)) {
    if (entry !== 'spec.jsonc') fs.rmSync(path.join(dir, entry), { recursive: true, force: true });
  }
  // The part files of a manifest specification first, so the manifest never names a part that is not there; then
  // the facts extracted from the implementation, which the application attaches as the command line does.
  for (const sub of ['parts', 'extracted']) {
    const from = path.join(SOURCES[which], sub);
    if (fs.existsSync(from)) fs.cpSync(from, path.join(dir, sub), { recursive: true });
  }
  fs.copyFileSync(path.join(SOURCES[which], 'spec.jsonc'), path.join(dir, 'spec.jsonc'));
  const recorded = path.join(SOURCES[which], 'evidence', 'results.json');
  if (fs.existsSync(recorded)) {
    fs.mkdirSync(path.join(dir, 'evidence'), { recursive: true });
    fs.copyFileSync(recorded, path.join(dir, 'evidence', 'results.json'));
  }
}

export function removeScratch() {
  for (const entry of fs.readdirSync(SPECS)) {
    if (entry.startsWith('zz-test-')) fs.rmSync(path.join(SPECS, entry), { recursive: true, force: true });
  }
}

/**
 * A scratch project's file. The specification is read resolved: a manifest specification (the self-specification
 * keeps its entities in part files) gives the assembled text, so a test sees what the application saved wherever it
 * went; a plain specification is its own text.
 * @param {'exegra'|'multiplayer'} which @param {string} file
 */
export function readScratch(which, file) {
  const p = path.join(SPECS, SCRATCH[which], file);
  if (!fs.existsSync(p)) return null;
  return file === 'spec.jsonc' ? readSpecFile(p) : fs.readFileSync(p, 'utf8');
}
