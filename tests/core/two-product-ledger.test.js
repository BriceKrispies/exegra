// The two-product ledger (WG-5685, criterion 7; composition F6): each product's claim that the platform ledger
// holds at most one hold holds on every execution of its own scenario, and installing the second product is
// refused, naming the composed scenario {ledger, badges__awarder, promotions__awarder} and the counterexample
// held = 2 (cli/admit.js, admitProduct).

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { admitProduct } from '../../cli/admit.js';

const DIR = path.join(path.dirname(fileURLToPath(import.meta.url)), '..', 'fixtures', 'two-product-ledger');
const BASE = fs.readFileSync(path.join(DIR, 'spec.jsonc'), 'utf8');
/** @param {string} p */
const layer = (p) => ({ file: `${p}.jsonc`, text: fs.readFileSync(path.join(DIR, 'products', `${p}.jsonc`), 'utf8'), platform: { declared: '../spec.jsonc', matches: true, expected: '../spec.jsonc' } });

test('each product alone keeps its one-hold claim on every execution of its own scenario', () => {
  for (const p of ['badges', 'promotions']) {
    const r = admitProduct(BASE, [], layer(p));
    assert.equal(r.verdict, 'admitted', JSON.stringify(r.reasons));
    const own = r.own.find((/** @type {any} */ o) => o.claim === `${p}__one-hold`);
    assert.equal(own?.scenario, `${p}__solo`);
    assert.equal(own?.status, 'complete');
  }
});

test('installing the second product is refused with the composed scenario and held 2', () => {
  const r = admitProduct(BASE, [layer('badges')], layer('promotions'));
  assert.equal(r.verdict, 'rejected');
  // Both claims still hold on their own scenarios.
  assert.deepEqual(r.own.map((/** @type {any} */ o) => [o.claim, o.status]).sort(), [['badges__one-hold', 'complete'], ['promotions__one-hold', 'complete']]);
  const reasons = r.reasons.filter((/** @type {any} */ x) => x.code === 'admit.product-composition-violated');
  assert.deepEqual(reasons.map((/** @type {any} */ x) => x.id).sort(), ['badges__one-hold', 'promotions__one-hold']);
  for (const x of reasons) {
    assert.deepEqual([...x.scenario.behaviors].sort(), ['badges__awarder', 'ledger', 'promotions__awarder']);
    assert.deepEqual(x.counterexample.values, { 'ledger.held': 2 });
    assert.match(x.message, /\{ledger, badges__awarder, promotions__awarder\}/);
    assert.match(x.message, /ledger\.held = 2/);
  }
});
