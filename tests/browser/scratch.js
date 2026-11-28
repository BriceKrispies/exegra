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

/**
 * Make `to` hold exactly the files of `from` (recursively), in place: files are overwritten or added, files `from`
 * lacks are removed, and no directory is ever deleted (one `from` lacks is emptied).
 * @param {string|null} from @param {string} to
 */
function syncInPlace(from, to) {
  fs.mkdirSync(to, { recursive: true });
  const wanted = new Set(from && fs.existsSync(from) ? fs.readdirSync(from) : []);
  for (const entry of fs.readdirSync(to, { withFileTypes: true })) {
    const at = path.join(to, entry.name);
    if (entry.isDirectory()) { if (!wanted.has(entry.name)) syncInPlace(null, at); continue; }
    if (!wanted.has(entry.name)) fs.rmSync(at, { force: true });
  }
  for (const name of wanted) {
    const src = path.join(/** @type {string} */ (from), name);
    if (fs.statSync(src).isDirectory()) syncInPlace(src, path.join(to, name));
    else fs.copyFileSync(src, path.join(to, name));
  }
}

/** @param {'exegra'|'multiplayer'} which @param {number} [index] */
export function resetScratch(which, index = slot()) {
  const dir = path.join(SPECS, scratchName(which, index));
  // Reset in place, never deleting a directory (WG-5738): the specification file is never missing, and a directory
  // the development server or a page might be reading is never removed. The application does not glob scratch
  // projects at all (src/app/session.js leaves out specs/zz-test-*), so a reset cannot break a page that is loading.
  fs.mkdirSync(dir, { recursive: true });
  // The part files of a manifest specification first, so the manifest never names a part that is not there; then
  // the facts extracted from the implementation, which the application attaches as the command line does, and the
  // recorded results. Anything else in the scratch project (a journal, a layout the last test saved) is emptied.
  const source = SOURCES[which];
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    if (entry.name === 'spec.jsonc' || ['parts', 'extracted', 'evidence'].includes(entry.name)) continue;
    if (entry.isDirectory()) syncInPlace(null, path.join(dir, entry.name));
    else fs.rmSync(path.join(dir, entry.name), { force: true });
  }
  for (const sub of ['parts', 'extracted']) syncInPlace(fs.existsSync(path.join(source, sub)) ? path.join(source, sub) : null, path.join(dir, sub));
  fs.copyFileSync(path.join(source, 'spec.jsonc'), path.join(dir, 'spec.jsonc'));
  const recorded = path.join(source, 'evidence', 'results.json');
  syncInPlace(null, path.join(dir, 'evidence'));
  if (fs.existsSync(recorded)) fs.copyFileSync(recorded, path.join(dir, 'evidence', 'results.json'));
}

/** Every directory a scratch project of this run may hold, for checks that no helper deletes one (WG-5738). */
export function scratchDirs() {
  return fs.readdirSync(SPECS).filter((e) => e.startsWith('zz-test-')).map((e) => path.join(SPECS, e));
}

/**
 * Remove every scratch project. Only the global teardown calls it, after the last test; the application never globs
 * specs/zz-test-* (src/app/session.js), so removing them cannot reach a page.
 */
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
