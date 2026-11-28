// The discharge graph of assumptions (WG-5685, criterion 5): an assumption depends on the claims that discharge it,
// a claim on the assumptions it cites, and validation refuses a cycle (assumption.discharge-cycle), the hypothesis
// of Exegra.Core.discharge_sound.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { analyzeSpec } from '../../src/core/analyze.js';

const repoRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..', '..');
const SPEC = fs.readFileSync(path.join(repoRoot, 'tests', 'fixtures', 'discharge-cycle', 'spec.jsonc'), 'utf8');

test('validation refuses a cycle in the discharge graph', () => {
  const { diagnostics } = analyzeSpec(SPEC);
  const cycles = diagnostics.filter((d) => d.code === 'assumption.discharge-cycle');
  assert.equal(cycles.length, 1, JSON.stringify(diagnostics));
  assert.equal(cycles[0].severity, 'error');
  assert.equal(cycles[0].entityId, 'a');
  assert.match(cycles[0].message, /a → c1 → b → c2 → a/);
});

test('an acyclic discharge graph is accepted', () => {
  const acyclic = SPEC.replace('"assumptions": ["a"], "discharges": ["b"]', '"discharges": ["b"]');
  assert.notEqual(acyclic, SPEC);
  const { diagnostics, errorCount } = analyzeSpec(acyclic);
  assert.equal(errorCount, 0, JSON.stringify(diagnostics.filter((d) => d.severity === 'error')));
  assert.ok(!diagnostics.some((d) => d.code === 'assumption.discharge-cycle'));
});
