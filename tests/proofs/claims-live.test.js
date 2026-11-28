// Claim evaluation over the whole self-specification and against the Lean prover (WG-5682): every behavioural claim of
// the self-specification is verified with a violating negative (every trace claim, several hundred engine runs), and the
// live view and exegra prove report an evaluation error alike (it runs lake). These are sweeps and prover runs, so they run
// with the proofs (npm run test:proofs, npm run verify, the Check workflow), not in the routine suite.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { analyzeSpec } from '../../src/core/analyze.js';
import { evaluateClaims } from '../../src/core/claims.js';
import { initEngine } from '../../src/core/engine.js';
import { Project } from '../../src/core/project.js';
import { readSpecFile } from '../../tools/spec-manifest.js';

initEngine();

/** @param {string} text */
function load(text) {
  const { model, errorCount, diagnostics } = analyzeSpec(text);
  assert.equal(errorCount, 0, JSON.stringify(diagnostics.filter((d) => d.severity === 'error'), null, 1));
  assert.ok(model);
  return model;
}

test('negatives: every behavioral claim of the exegra specification is verified with a violating negative', () => {
  const model = load(readSpecFile(new URL('../../specs/exegra/spec.jsonc', import.meta.url)));
  const trace = evaluateClaims(model).filter((r) => r.evaluator === 'exegra.trace/0.1');
  assert.ok(trace.length >= 10, `expected the edit-flow claims, found ${trace.length}`);
  for (const r of trace) {
    assert.equal(r.status, 'verified', `${r.claimId}: ${r.explanation}`);
    assert.ok(r.negatives && r.negatives.length >= 1, `${r.claimId} declares no negative`);
    assert.ok(r.negatives.every((n) => n.violated), `${r.claimId}: a negative did not violate it`);
  }
});

// WG-5682: the live view and exegra prove evaluate claim expressions with one Lean evaluator (claimTruth of
// formal/Exegra/ProveB.lean); an expression that cannot be evaluated is a violation in both.
test('prove and the live view agree on an evaluation error', async (t) => {
  await initEngine();
  const text = readFileSync(new URL('../fixtures/liveness/spec.jsonc', import.meta.url), 'utf8');
  const project = new Project({ name: 'liveness', specText: text, layoutText: null });
  assert.ok(project.model, 'the fixture parses');
  const live = evaluateClaims(project.model).find((c) => c.claimId === 'claim-divides-by-zero');
  assert.equal(live?.status, 'violated', 'the live view reports a violation');
  assert.match(live.explanation, /cannot be evaluated/);
  const { lakeAvailable, proveScenario } = await import('../../tools/prove.js');
  if (!lakeAvailable()) { t.skip('lake is not on the PATH; the prove half was not checked'); return; }
  const proved = proveScenario(project.model, 'blink-f4').claims.find((/** @type {any} */ c) => c.claimId === 'claim-divides-by-zero');
  assert.equal(proved?.result, 'counterexample', 'exegra prove reports a violation');
  assert.equal(proved.counterexample.stepCount, 0, 'already in the initial configuration');
});
