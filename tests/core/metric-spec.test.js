// Metric claims in a specification (format 2, WG-4729; docs/simulation.md, "Specification-level
// form" and "Claims over metrics"): a specification declares a resource, an open workload, a
// request class, a format-2 scenario and a metric-bound claim; engineInput derives version 2
// with times in base units and distributions lowered, and evaluateClaims reports model-holds (or
// violated) with the run count and confidence, never verified.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { analyzeSpec } from '../../src/core/analyze.js';
import { evaluateClaim } from '../../src/core/claims.js';
import { initEngine } from '../../src/core/engine.js';
import { engineInput } from '../../src/core/engine.js';

initEngine();

/** @param {string} bound @param {string[]} [twinFaults] */
const SPEC = (bound, twinFaults = ['slow-server']) => `{
  "exegra": "0.1",
  "system": { "id": "queue", "name": "Queue" },
  "components": [{ "id": "c-server", "name": "Server", "category": "computational" }],
  "events": [{ "id": "job", "name": "Job" }, { "id": "served", "name": "Served" }],
  "behaviors": [{
    "id": "station", "name": "Station", "subject": "c-server", "initial": "idle",
    "states": [{ "id": "idle", "name": "Idle" }],
    "transitions": [
      { "id": "take", "from": "idle", "to": "idle", "on": "job",
        "effects": [{ "use": "server", "demand": { "exponential": { "mean": "1 ms" } }, "then": "served", "payload": { "request": "event.request" } }] },
      { "id": "done", "from": "idle", "to": "idle", "on": "served" }
    ]
  }],
  "resources": [{ "id": "server", "kind": "cpu", "capacity": 1, "source": { "kind": "assumed" } }],
  "workloads": [{ "id": "jobs", "kind": "open", "event": "job", "process": "poisson", "rate": "200/s", "source": { "kind": "assumed" } }],
  "requestClasses": [{ "id": "job-time", "start": { "event": "job" }, "key": "request", "ends": [{ "event": "served", "outcome": "ok" }] }],
  "faults": [{ "id": "slow-server", "name": "Slow server", "kind": "scale-demand", "resource": "server", "num": 20, "den": 1 }],
  "scenarios": [{ "id": "steady", "name": "Steady", "behaviors": ["station"], "steps": [], "workloads": ["jobs"],
    "seed": "4729", "warmup": "1 s", "horizon": "3 s", "stopAt": "4 s", "maxSteps": 100000 }],
  "claims": [{ "id": "job-p90-bounded", "kind": "measured",
    "statement": "The p90 response time of a job stays within the bound.",
    "evaluate": { "method": "metric-bound", "scenarios": ["steady"],
      "metric": { "kind": "response-time", "of": "job-time", "statistic": "p90" }, "op": "<=", "bound": "${bound}",
      "fraction": "0.5", "confidence": "0.9", "runs": 8, "seed": "4729",
      "negatives": [{ "scenario": "steady", "faults": ${JSON.stringify(twinFaults)} }] } }]
}`;

/** @param {string} text */
function load(text) {
  const { model, errorCount, diagnostics } = analyzeSpec(text);
  assert.equal(errorCount, 0, JSON.stringify(diagnostics.filter((d) => d.severity === 'error'), null, 1));
  assert.ok(model);
  return model;
}

test('engineInput derives format 2 from declared resources, workloads and request classes', () => {
  const input = /** @type {any} */ (engineInput(load(SPEC('20 ms')), 'steady'));
  assert.equal(input.version, 2);
  assert.deepEqual(input.time, { unit: 'us', perSecond: 1000000 });
  assert.equal(input.scenario.horizon, 3000000);
  assert.equal(input.scenario.warmup, 1000000);
  assert.deepEqual(input.workloads[0].phases, [{ from: 0, until: 3000000, rate: { num: 200, den: 1 } }]);
  assert.equal(input.behaviors[0].transitions[0].effects[0].demand.kind, 'table');
  assert.ok(input.unitExponential.length > 1000);
  assert.equal(input.requests[0].id, 'job-time');
});

test('a metric-bound claim in a specification reads model-holds with its runs and confidence, and its twin fails', () => {
  const r = evaluateClaim(load(SPEC('20 ms')), 'job-p90-bounded');
  assert.equal(r.status, 'model-holds', r.explanation);
  assert.match(r.scope, /N = 8/);
  assert.match(r.scope, /Never verified/);
  assert.match(r.explanation, /negative 0 .*: fails/);
});

test('a metric-bound claim whose bound the model misses is violated, never verified', () => {
  const r = evaluateClaim(load(SPEC('100 us')), 'job-p90-bounded');
  assert.equal(r.status, 'violated', r.explanation);
  assert.ok(r.counterexample);
});
