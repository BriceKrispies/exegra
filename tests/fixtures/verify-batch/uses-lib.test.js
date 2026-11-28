// Loads lib.js: a change to lib.js changes what this file covers.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { answer } from './lib.js';
test('lib answers', () => { assert.equal(answer, 41); });
