// Reads data.json with fs: a data file a test reads is covered too.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
test('data parses', () => { assert.ok(JSON.parse(fs.readFileSync(new URL('./data.json', import.meta.url), 'utf8')).ok); });
