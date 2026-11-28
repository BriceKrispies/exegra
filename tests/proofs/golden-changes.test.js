// The golden traces and inputs of tests/conformance changed exactly as tests/conformance/golden-changes.json says (WG-5681,
// criterion 22). It compares every golden with its version at the base commit through git history, so it runs with the
// proofs (npm run test:proofs, npm run verify, the Check workflow), not in the routine suite.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { REPO_ROOT, goldenChanges, listGoldens } from '../../tools/conformance.js';

/** @param {string} p */
const readJson = (p) => JSON.parse(fs.readFileSync(p, 'utf8'));

test('golden changes are exactly the manifest', (t) => {
  // tests/conformance/golden-changes.json (WG-5681, criterion 22): every golden that differs from its
  // version at the base commit, with its class; strip(version-2 trace) = version-1 trace for the shape change.
  const manifest = readJson(path.join(REPO_ROOT, 'tests', 'conformance', 'golden-changes.json'));
  let changes;
  try {
    changes = goldenChanges(manifest.base);
  } catch (e) {
    t.skip(`${/** @type {Error} */ (e).message} (a shallow checkout; the Check workflow fetches the history)`);
    return;
  }
  assert.deepEqual(changes, manifest.changes);
  const counts = /** @type {Record<string, number>} */ ({});
  for (const c of Object.values(changes)) counts[c] = (counts[c] ?? 0) + 1;
  assert.equal(Object.keys(changes).length, listGoldens().length, 'every golden changed (version 1 to version 2)');
  // The exegra goldens changed again on purpose after WG-5681: the composition root of the multiscale work (WG-5692)
  // re-addressed behaviours, and the two-session-write event (WG-5720) joined every exegra input; the two-session
  // edit race is a new golden. Re-subjecting workspace-flow (WG-5728) edited the source-edit-flow input as well, and the
  // save path speaking the persistence client's interface (WG-5729) re-recorded write-with-stale-base-hash.
  assert.deepEqual(counts, { 'version 2': 43, 'input re-recorded, trace equal under strip': 31, 'trace removed (refused)': 2, 'input edited, trace re-recorded': 12, added: 1 });
});
