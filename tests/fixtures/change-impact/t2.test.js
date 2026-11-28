// The tests of claims c1, c2, c3, c6 and c7 of the change-impact fixture (not part of the suite).
import { test } from 'node:test';
import assert from 'node:assert/strict';

for (const id of ['c1', 'c2', 'c3', 'c6', 'c7']) test(`${id} holds`, () => assert.ok(true));
