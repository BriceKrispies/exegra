// Order independence of the self-specification's scenarios (WG-5697 criterion 7, invariant I2), on the
// scheduler's runs: every scenario, and every negative run of its claims, run with its behaviours
// reversed and in every rotation, gives each of its invariant and temporal claims the verdict of the
// scenario's own order. invariant_rename (formal/Exegra/Core) proves the same of every interleaving
// in the calculus.
//
// It runs every scenario in every rotation, several hundred engine runs, so it lives with the proof
// checks rather than in the unit suite or in live claim evaluation: the claim
// composition-order-independent is backed by this test as external evidence.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { runCommand } from '../../cli/commands.js';

// exegra order-check runs every self-specification scenario and the negative runs of its claims with the behaviours reversed and in every rotation, and no invariant or temporal verdict differs from the scenario's own order.
// @evidence composition-order-independent
test('reordering the behaviours of any self-specification scenario changes no claim verdict', async () => {
  const r = /** @type {any} */ (await runCommand('order-check', ['--project', 'exegra']));
  assert.equal(r.ok, true);
  assert.ok(r.result.results.length >= 30, 'every scenario of the self-specification is checked');
  assert.deepEqual(r.result.differences, []);
  assert.equal(r.result.verdictsIndependent, true);
});
