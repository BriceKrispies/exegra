// Refinement of the self-specification's declared abstractions over every interleaving and fault mask (WG-5734): each
// refines-composition claim's abstraction is explored with its members in every driving scenario of the claim
// (engine.refineExplore, formal/Exegra/BoundaryExplore.lean, whose certificate explore_holds proves sound), and every
// boundary trace the members can show must be one the abstraction shows with the same faults.
//
// The explorations visit every product node of each scenario, so this runs with the proof checks rather than in live
// claim evaluation: the claim declared-abstractions-refined-over-interleavings is backed by this test as evidence.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { analyzeSpec } from '../../src/core/analyze.js';
import { initEngine } from '../../src/core/engine.js';
import { checkAbstraction } from '../../src/core/composition.js';
import { readSpecFile } from '../../tools/spec-manifest.js';

initEngine();
const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');

// @evidence declared-abstractions-refined-over-interleavings
test('every declared abstraction a refines-composition claim names is refined over every interleaving and fault mask of its scenarios', () => {
  const m = /** @type {any} */ (analyzeSpec(readSpecFile(path.join(ROOT, 'specs/exegra/spec.jsonc'))).model);
  const claims = (m.byKind.claim ?? []).filter((/** @type {any} */ c) => c.data.evaluate?.method === 'refines-composition');
  assert.ok(claims.length >= 4, 'the persistence abstractions and the recorded write are checked');
  for (const c of claims) {
    const ev = c.data.evaluate;
    const r = checkAbstraction(m, ev.behavior, { scenarios: ev.scenarios, finest: ev.finest === true, explore: { bound: 64, maxStates: 20000 } });
    assert.equal(r.verdict, 'certificate', `${c.id}: ${JSON.stringify(r.counterexample?.explored ?? r.counterexample ?? r.notes)}`);
    assert.equal(r.strength, 'explored', c.id);
    for (const run of r.runs) {
      assert.equal(run.explored.verdict, 'certificate', `${c.id} in ${run.scenario}`);
      assert.ok(run.explored.states > 0);
    }
  }
});
