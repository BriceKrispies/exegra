// Fixture for tests/core/verify-batching.test.js (not run by npm test): one file with passing, failing, skipped and
// suite-nested tests, to show which reference each outcome is attributed to.
import { test, describe } from 'node:test';
import assert from 'node:assert/strict';
test('passes one', () => { assert.ok(true); });
test('passes two', () => { assert.ok(true); });
test('fails alone', () => { assert.fail('this test fails'); });
test('skips itself', { skip: 'not here' }, () => {});
describe('group', () => { test('inner passes', () => { assert.ok(true); }); });
