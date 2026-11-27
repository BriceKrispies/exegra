// Fixture for tests/core/fact-producers.test.js (not run by npm test): the tests of
// docs/assessment/2026-11-26/demos/skipped-test-counts-as-pass.test.js, which a reference used to count as a
// pass although the test that matters skipped itself, sat alone in a suite that skipped, or was a todo.
import { test, describe } from 'node:test';
import assert from 'node:assert/strict';
test('trivially true helper', () => { assert.ok(true); });
test('the real check of the claim', (t) => { if (!process.env.HAS_TOOL) { t.skip('tool missing'); return; } assert.fail('would fail'); });
describe('suite whose only test is skipped', () => { test('inner real check', { skip: 'not linked' }, () => { assert.fail('x'); }); });
test('publishes on every push', { todo: 'not written' }, () => {});
