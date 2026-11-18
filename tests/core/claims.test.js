import { test } from 'node:test';
import assert from 'node:assert/strict';
import { analyzeSpec } from '../../src/core/analyze.js';
import { evaluateClaims, evaluateClaim, checkTrace } from '../../src/core/claims.js';
import { initEngine, runScenario } from '../../src/core/engine.js';
import { Project } from '../../src/core/project.js';
import { readFileSync } from 'node:fs';

initEngine();

/** @param {string} text */
function load(text) {
  const { model, errorCount, diagnostics } = analyzeSpec(text);
  assert.equal(errorCount, 0, JSON.stringify(diagnostics.filter((d) => d.severity === 'error'), null, 1));
  assert.ok(model);
  return model;
}

// ---------------------------------------------------------------------------
// Structural claims
// ---------------------------------------------------------------------------

const STRUCTURAL = `{
  "exegra": "0.1",
  "system": { "id": "shop", "name": "Shop" },
  "components": [
    { "id": "web", "name": "Web", "category": "client" },
    { "id": "api", "name": "API", "category": "computational", "purpose": "Serves requests.",
      "ports": [ { "id": "api-http", "name": "http", "direction": "provides" } ] },
    { "id": "db", "name": "DB", "category": "storage" },
    { "id": "cache", "name": "Cache", "category": "storage" },
    { "id": "ext", "name": "Partner", "category": "external" }
  ],
  "relationships": [
    { "id": "r-web-api", "kind": "calls", "from": "web", "to": "api" },
    { "id": "r-api-db", "kind": "writes", "from": "api", "to": "db" },
    { "id": "r-api-cache", "kind": "reads", "from": "api", "to": "cache" },
    { "id": "r-api-ext", "kind": "data-flow", "from": "api", "to": "ext" }
  ],
  "claims": [
    { "id": "c-nr-ok", "kind": "structural", "statement": "Web never touches the db directly.",
      "subjects": ["web"],
      "evaluate": { "method": "no-relationship", "from": "web", "to": "db", "kinds": ["calls", "writes"] } },
    { "id": "c-nr-bad", "kind": "structural", "statement": "API never writes the db.",
      "evaluate": { "method": "no-relationship", "from": "api", "to": "db" } },
    { "id": "c-nr-trans", "kind": "structural", "statement": "Web cannot reach the db at all.",
      "evaluate": { "method": "no-relationship", "from": "web", "to": "db", "transitive": true } },
    { "id": "c-nr-vacuous", "kind": "structural", "statement": "Nothing tagged nope reaches the db.",
      "evaluate": { "method": "no-relationship", "from": { "tag": "nope" }, "to": "db" } },
    { "id": "c-reach-ok", "kind": "structural", "statement": "Web reaches the db.",
      "evaluate": { "method": "reachable", "from": "web", "to": "db" } },
    { "id": "c-reach-bad", "kind": "structural", "statement": "Web and db reach the partner.",
      "evaluate": { "method": "reachable", "from": ["web", "db"], "to": "ext" } },
    { "id": "c-reach-self", "kind": "structural", "statement": "The db reaches itself.",
      "evaluate": { "method": "reachable", "from": "db", "to": "db" } },
    { "id": "c-via-ok", "kind": "structural", "statement": "Web reaches the db only via the API.",
      "evaluate": { "method": "only-via", "from": "web", "to": "db", "via": "api" } },
    { "id": "c-via-bad", "kind": "structural", "statement": "Web reaches the partner only via the cache.",
      "evaluate": { "method": "only-via", "from": "web", "to": "ext", "via": "cache" } },
    { "id": "c-port-ok", "kind": "structural", "statement": "API provides http.",
      "evaluate": { "method": "has-port", "select": "api", "direction": "provides", "name": "http" } },
    { "id": "c-port-bad", "kind": "structural", "statement": "API and db provide a port.",
      "evaluate": { "method": "has-port", "select": ["api", "db"], "direction": "provides" } },
    { "id": "c-prop-ok", "kind": "structural", "statement": "API has a purpose.",
      "evaluate": { "method": "property-defined", "select": "api", "property": "purpose" } },
    { "id": "c-prop-bad", "kind": "structural", "statement": "API and db have a purpose.",
      "evaluate": { "method": "property-defined", "select": ["api", "db"], "property": "purpose" } },
    { "id": "c-acyclic-ok", "kind": "structural", "statement": "Dependencies are acyclic.",
      "evaluate": { "method": "acyclic" } },
    { "id": "c-magic", "kind": "structural", "statement": "Declared with a method this build lacks.",
      "evaluate": { "method": "magic-check" } },
    { "id": "c-ev-none", "kind": "measured", "statement": "p99 latency is under 200 ms.",
      "evaluate": { "method": "external-evidence" } },
    { "id": "c-ev-doc", "kind": "measured", "statement": "The partner offers an SLA.",
      "evaluate": { "method": "external-evidence" } },
    { "id": "c-ev-test", "kind": "measured", "statement": "The load test passes.",
      "evaluate": { "method": "external-evidence" } },
    { "id": "c-ev-contra", "kind": "measured", "statement": "Throughput meets the target.",
      "evaluate": { "method": "external-evidence" } }
  ],
  "evidence": [
    { "id": "e-doc", "claim": "c-ev-doc", "kind": "document", "ref": "docs/sla.pdf" },
    { "id": "e-test", "claim": "c-ev-test", "kind": "test", "ref": "tests/load.test.js" },
    { "id": "e-contra", "claim": "c-ev-contra", "kind": "measurement", "ref": "bench/run-3.json", "supports": false, "observed": "850 rps" },
    { "id": "e-override", "claim": "c-nr-ok", "kind": "test", "ref": "tests/boundary.test.js" }
  ]
}`;

const smodel = load(STRUCTURAL);
const claim = (id, opts) => evaluateClaim(smodel, id, opts);

test('evaluateClaims returns one result per claim in declaration order, hashed to the model', () => {
  const results = evaluateClaims(smodel);
  assert.deepEqual(results.map((r) => r.claimId), smodel.byKind.claim.map((c) => c.id));
  assert.equal(new Set(results.map((r) => r.semanticHash)).size, 1);
  for (const r of results) {
    assert.ok(r.scope.length > 0, r.claimId);
    assert.ok(r.explanation.length > 0, r.claimId);
    assert.ok(Array.isArray(r.assumptions));
    assert.ok(Array.isArray(r.evidence));
  }
});

test('no-relationship: holds', () => {
  const r = claim('c-nr-ok');
  assert.equal(r.status, 'verified');
  assert.equal(r.evaluator, 'exegra.structural/0.1');
  assert.equal(r.method, 'no-relationship');
  assert.equal(r.counterexample, undefined);
  assert.match(r.scope, /2 relationships/);
  assert.ok(r.involved.includes('web') && r.involved.includes('db'));
});

test('no-relationship: a direct relationship is the counterexample', () => {
  const r = claim('c-nr-bad');
  assert.equal(r.status, 'violated');
  assert.deepEqual(r.counterexample.entities, ['r-api-db']);
  assert.deepEqual(r.counterexample.path, ['api', 'r-api-db', 'db']);
  assert.ok(r.involved.includes('r-api-db'));
});

test('no-relationship transitive: a multi-hop path is the counterexample', () => {
  const r = claim('c-nr-trans');
  assert.equal(r.status, 'violated');
  assert.deepEqual(r.counterexample.path, ['web', 'r-web-api', 'api', 'r-api-db', 'db']);
  assert.deepEqual(r.counterexample.entities, ['r-web-api', 'r-api-db']);
});

test('a selector that selects nothing is inconclusive, never verified', () => {
  const r = claim('c-nr-vacuous');
  assert.equal(r.status, 'inconclusive');
  assert.match(r.explanation, /from/);
});

test('reachable: holds and fails with the unreachable components', () => {
  assert.equal(claim('c-reach-ok').status, 'verified');
  const bad = claim('c-reach-bad');
  assert.equal(bad.status, 'violated');
  assert.deepEqual(bad.counterexample.entities, ['db']);
});

test('reachable: being a member of the target set is not reaching it', () => {
  const r = claim('c-reach-self');
  assert.equal(r.status, 'violated');
  assert.deepEqual(r.counterexample.entities, ['db']);
});

test('only-via: holds, and a bypassing path is the counterexample', () => {
  assert.equal(claim('c-via-ok').status, 'verified');
  const bad = claim('c-via-bad');
  assert.equal(bad.status, 'violated');
  assert.deepEqual(bad.counterexample.path, ['web', 'r-web-api', 'api', 'r-api-ext', 'ext']);
});

test('has-port: holds and names the components without a matching port', () => {
  assert.equal(claim('c-port-ok').status, 'verified');
  const bad = claim('c-port-bad');
  assert.equal(bad.status, 'violated');
  assert.deepEqual(bad.counterexample.entities, ['db']);
});

test('property-defined: holds and names the components lacking the property', () => {
  assert.equal(claim('c-prop-ok').status, 'verified');
  const bad = claim('c-prop-bad');
  assert.equal(bad.status, 'violated');
  assert.deepEqual(bad.counterexample.entities, ['db']);
});

test('acyclic: holds on the dependency graph', () => {
  const r = claim('c-acyclic-ok');
  assert.equal(r.status, 'verified');
  assert.match(r.scope, /3 relationships/);
});

test('acyclic: a cycle is reported as a closed path; `within` restricts the graph', () => {
  const m = load(`{
    "exegra": "0.1",
    "system": { "id": "loop", "name": "Loop" },
    "components": [
      { "id": "a", "name": "A", "category": "logical" },
      { "id": "b", "name": "B", "category": "logical" },
      { "id": "c", "name": "C", "category": "logical" }
    ],
    "relationships": [
      { "id": "r-ab", "kind": "depends-on", "from": "a", "to": "b" },
      { "id": "r-bc", "kind": "depends-on", "from": "b", "to": "c" },
      { "id": "r-ca", "kind": "depends-on", "from": "c", "to": "a" }
    ],
    "claims": [
      { "id": "cyc", "kind": "structural", "statement": "No cycles.", "evaluate": { "method": "acyclic" } },
      { "id": "cyc-part", "kind": "structural", "statement": "No cycles among a and b.",
        "evaluate": { "method": "acyclic", "within": ["a", "b"] } }
    ]
  }`);
  const r = evaluateClaim(m, 'cyc');
  assert.equal(r.status, 'violated');
  const path = r.counterexample.path;
  assert.equal(path.length, 7);
  assert.equal(path[0], path[6]);
  assert.deepEqual([...path.filter((_, i) => i % 2 === 1)].sort(), ['r-ab', 'r-bc', 'r-ca']);
  assert.equal(evaluateClaim(m, 'cyc-part').status, 'verified');
});

test('an unsupported method is not-evaluated and says so', () => {
  const r = claim('c-magic');
  assert.equal(r.status, 'not-evaluated');
  assert.equal(r.evaluator, 'none');
  assert.equal(r.method, 'magic-check');
});

test('the result is deterministic', () => {
  assert.deepEqual(evaluateClaims(smodel), evaluateClaims(smodel));
});

// ---------------------------------------------------------------------------
// Evidence
// ---------------------------------------------------------------------------

test('external-evidence: no evidence is not-evaluated', () => {
  const r = claim('c-ev-none');
  assert.equal(r.status, 'not-evaluated');
  assert.equal(r.evaluator, 'exegra.evidence/0.1');
  assert.deepEqual(r.evidence, []);
});

test('external-evidence: an author-entered document is supported, and says nothing was executed', () => {
  const r = claim('c-ev-doc');
  assert.equal(r.status, 'supported');
  assert.match(r.explanation, /author-entered/);
  assert.match(r.explanation, /did not execute/);
  assert.deepEqual(r.evidence, [{ id: 'e-doc', kind: 'document', ref: 'docs/sla.pdf', supports: true, recorded: 'none' }]);
});

test('external-evidence: a test with no recorded result is inconclusive', () => {
  const r = claim('c-ev-test');
  assert.equal(r.status, 'inconclusive');
  assert.equal(r.evidence[0].recorded, 'none');
  const withEmpty = claim('c-ev-test', { recorded: { results: {} } });
  assert.equal(withEmpty.status, 'inconclusive');
});

test('external-evidence: a recorded pass is supported and says Exegra holds an execution result', () => {
  const r = claim('c-ev-test', { recorded: { results: { 'e-test': { outcome: 'pass', detail: '12 passed', ranAt: 'recorded' } } } });
  assert.equal(r.status, 'supported');
  assert.equal(r.evidence[0].recorded, 'pass');
  assert.equal(r.evidence[0].detail, '12 passed');
  assert.match(r.explanation, /recorded result of executing/);
});

test('external-evidence: a recorded fail is violated', () => {
  const r = claim('c-ev-test', { recorded: { results: { 'e-test': { outcome: 'fail' } } } });
  assert.equal(r.status, 'violated');
  assert.deepEqual(r.counterexample.entities, ['e-test']);
});

test('external-evidence: contradicting evidence is violated', () => {
  const r = claim('c-ev-contra');
  assert.equal(r.status, 'violated');
  assert.equal(r.evidence[0].supports, false);
  assert.equal(r.evidence[0].detail, '850 rps');
});

test('a recorded fail turns a verified model-evaluated claim into violated', () => {
  assert.equal(claim('c-nr-ok').status, 'verified');
  const pass = claim('c-nr-ok', { recorded: { results: { 'e-override': { outcome: 'pass' } } } });
  assert.equal(pass.status, 'verified');
  const fail = claim('c-nr-ok', { recorded: { results: { 'e-override': { outcome: 'fail' } } } });
  assert.equal(fail.status, 'violated');
  assert.equal(fail.evaluator, 'exegra.structural/0.1');
  assert.deepEqual(fail.counterexample.entities, ['e-override']);
});

// ---------------------------------------------------------------------------
// Trace claims
// ---------------------------------------------------------------------------

const TRACE_SPEC = `{
  "exegra": "0.1",
  "system": { "id": "rpc", "name": "RPC" },
  "components": [
    { "id": "client", "name": "Client", "category": "client" },
    { "id": "server", "name": "Server", "category": "computational" }
  ],
  "relationships": [ { "id": "r-call", "kind": "calls", "from": "client", "to": "server" } ],
  "events": [
    { "id": "send", "name": "Send" },
    { "id": "request", "name": "Request" },
    { "id": "response", "name": "Response" },
    { "id": "orphan", "name": "Orphan" }
  ],
  "behaviors": [
    { "id": "client-fsm", "name": "Client", "subject": "client", "initial": "c-idle",
      "states": [ { "id": "c-idle", "name": "Idle" }, { "id": "c-waiting", "name": "Waiting" } ],
      "transitions": [
        { "id": "c-send", "from": "c-idle", "to": "c-waiting", "on": "send", "effects": [ { "emit": "request", "after": 1 } ] },
        { "id": "c-done", "from": "c-waiting", "to": "c-idle", "on": "response" }
      ] },
    { "id": "server-fsm", "name": "Server", "subject": "server", "initial": "s-idle",
      "variables": [ { "name": "count", "type": "number", "initial": 0 } ],
      "states": [ { "id": "s-idle", "name": "Idle" }, { "id": "s-served", "name": "Served" } ],
      "transitions": [
        { "id": "s-handle", "from": "s-idle", "to": "s-served", "on": "request",
          "effects": [ { "set": "count", "to": "count + 1" }, { "emit": "response", "after": 1 } ] },
        { "id": "s-again", "from": "s-served", "to": "s-served", "on": "request",
          "effects": [ { "set": "count", "to": "count + 1" } ] }
      ] }
  ],
  "faults": [
    { "id": "drop-response", "name": "Drop response", "kind": "drop-event", "event": "response" },
    { "id": "dup-request", "name": "Duplicate request", "kind": "inject-event", "event": "request", "at": 5 },
    { "id": "early-request", "name": "Request before send", "kind": "inject-event", "event": "request", "at": 0 },
    { "id": "send-disabled", "name": "Client cannot send", "kind": "disable-transition", "transition": "c-send" }
  ],
  "scenarios": [
    { "id": "happy", "name": "Happy path", "behaviors": ["client-fsm", "server-fsm"], "steps": [ { "at": 0, "event": "send" } ] },
    { "id": "lossy", "name": "Lost response", "behaviors": ["client-fsm", "server-fsm"], "faults": ["drop-response"], "steps": [ { "at": 0, "event": "send" } ] },
    { "id": "dup", "name": "Duplicate request", "behaviors": ["client-fsm", "server-fsm"], "faults": ["dup-request"], "steps": [ { "at": 0, "event": "send" } ] },
    { "id": "rogue", "name": "Request without send", "behaviors": ["client-fsm", "server-fsm"], "faults": ["early-request"], "steps": [ { "at": 2, "event": "send" } ] },
    { "id": "server-only", "name": "Server alone", "behaviors": ["server-fsm"], "steps": [ { "at": 0, "event": "request" } ] },
    { "id": "empty", "name": "Nothing happens", "behaviors": ["server-fsm"], "steps": [] },
    { "id": "capped", "name": "Happy path, capped at three steps", "behaviors": ["client-fsm", "server-fsm"], "maxSteps": 3, "steps": [ { "at": 0, "event": "send" } ] }
  ],
  "claims": [
    { "id": "inv-ok", "kind": "invariant", "statement": "At most one request is served.",
      "evaluate": { "method": "state-invariant", "scenarios": ["happy"], "expr": "server-fsm.count <= 1", "negatives": [ { "scenario": "happy", "faults": ["dup-request"] } ] } },
    { "id": "inv-bad", "kind": "invariant", "statement": "At most one request is served, even with duplicates.",
      "evaluate": { "method": "state-invariant", "scenarios": ["happy", "dup"], "expr": "server-fsm.count <= 1" } },
    { "id": "inv-client", "kind": "invariant", "statement": "The server is idle, or has served exactly one request.",
      "evaluate": { "method": "state-invariant", "scenarios": ["happy"], "expr": "server-fsm.state == 's-idle' || server-fsm.count == 1", "negatives": [ { "scenario": "happy", "faults": ["dup-request"] } ] } },
    { "id": "inv-states-only", "kind": "invariant", "statement": "The client is idle or waiting.",
      "evaluate": { "method": "state-invariant", "scenarios": ["happy"], "expr": "client-fsm.state == 'c-idle' || client-fsm.state == 'c-waiting'" } },
    { "id": "prec-ok", "kind": "temporal", "statement": "The server handles only after the client sent.",
      "evaluate": { "method": "precedes", "scenarios": ["happy"], "first": { "transition": "c-send" }, "then": { "transition": "s-handle" }, "negatives": [ { "scenario": "happy", "faults": ["send-disabled", "early-request"] } ] } },
    { "id": "prec-bad", "kind": "temporal", "statement": "The server handles only after the client sent, even with stray requests.",
      "evaluate": { "method": "precedes", "scenarios": ["rogue"], "first": { "transition": "c-send" }, "then": { "transition": "s-handle" } } },
    { "id": "prec-vacuous", "kind": "temporal", "statement": "Completion follows a request.",
      "evaluate": { "method": "precedes", "scenarios": ["server-only"], "first": { "event": "request" }, "then": { "transition": "c-done" } } },
    { "id": "ev-ok", "kind": "temporal", "statement": "The client completes.",
      "evaluate": { "method": "eventually", "scenarios": ["happy"], "occurs": { "transition": "c-done" }, "negatives": [ { "scenario": "happy", "faults": ["drop-response"] } ] } },
    { "id": "ev-bad", "kind": "temporal", "statement": "The client completes even when the response is lost.",
      "evaluate": { "method": "eventually", "scenarios": ["lossy"], "occurs": { "transition": "c-done" } } },
    { "id": "ev-final", "kind": "temporal", "statement": "The client ends idle.",
      "evaluate": { "method": "eventually", "scenarios": ["happy"], "expr": "client-fsm.state == 'c-idle'", "negatives": [ { "scenario": "happy", "faults": ["drop-response"] } ] } },
    { "id": "never-ok", "kind": "temporal", "statement": "No duplicate handling.",
      "evaluate": { "method": "never", "scenarios": ["happy"], "occurs": { "transition": "s-again" }, "negatives": [ { "scenario": "happy", "faults": ["dup-request"] } ] } },
    { "id": "never-bad", "kind": "temporal", "statement": "No duplicate handling under duplicates.",
      "evaluate": { "method": "never", "scenarios": ["dup"], "occurs": { "transition": "s-again" } } },
    { "id": "inv-impl-vacuous", "kind": "invariant", "statement": "Many requests imply a negative count.",
      "evaluate": { "method": "state-invariant", "scenarios": ["happy"], "expr": "server-fsm.count > 5 => server-fsm.count < 0" } },
    { "id": "inv-impl-ok", "kind": "invariant", "statement": "Once counted, exactly one request was counted.",
      "evaluate": { "method": "state-invariant", "scenarios": ["happy"], "expr": "server-fsm.count >= 1 => server-fsm.count == 1", "negatives": [ { "scenario": "happy", "faults": ["dup-request"] } ] } },
    { "id": "inv-empty", "kind": "invariant", "statement": "At most one request is served in a scenario with no steps.",
      "evaluate": { "method": "state-invariant", "scenarios": ["empty"], "expr": "server-fsm.count <= 1" } },
    { "id": "never-foreign", "kind": "temporal", "statement": "The client never sends, in a server-only scenario.",
      "evaluate": { "method": "never", "scenarios": ["server-only"], "occurs": { "transition": "c-send" } } },
    { "id": "never-orphan", "kind": "temporal", "statement": "The orphan event never happens.",
      "evaluate": { "method": "never", "scenarios": ["happy"], "occurs": { "event": "orphan" } } },
    { "id": "never-lost", "kind": "temporal", "statement": "The response is never delivered when it is dropped.",
      "evaluate": { "method": "never", "scenarios": ["lossy"], "occurs": { "event": "response" } } },
    { "id": "neg-none", "kind": "invariant", "statement": "At most one request is served; no negative is declared.",
      "evaluate": { "method": "state-invariant", "scenarios": ["happy"], "expr": "server-fsm.count <= 1" } },
    { "id": "neg-holds", "kind": "invariant", "statement": "At most one request is served; its negative cannot break it.",
      "evaluate": { "method": "state-invariant", "scenarios": ["happy"], "expr": "server-fsm.count <= 1", "negatives": [ { "scenario": "happy", "faults": ["drop-response"] } ] } },
    { "id": "neg-mixed", "kind": "invariant", "statement": "At most one request is served; one negative breaks it, one does not.",
      "evaluate": { "method": "state-invariant", "scenarios": ["happy"], "expr": "server-fsm.count <= 1",
        "negatives": [ { "scenario": "happy", "faults": ["dup-request"] }, { "scenario": "happy", "faults": ["drop-response"] } ] } },
    { "id": "neg-capped", "kind": "temporal", "statement": "The client completes within three steps; the negative run is cut off first.",
      "evaluate": { "method": "eventually", "scenarios": ["capped"], "occurs": { "transition": "c-done" }, "negatives": [ { "scenario": "capped", "faults": ["early-request"] } ] } }
  ]
}`;

const tmodel = load(TRACE_SPEC);
const tclaim = (id) => evaluateClaim(tmodel, id);

test('state-invariant holding: verified, and the scope says it covers only these traces', () => {
  const r = tclaim('inv-ok');
  assert.equal(r.status, 'verified');
  assert.equal(r.evaluator, 'exegra.trace/0.1');
  assert.match(r.scope, /happy \(3 steps\)/);
  assert.match(r.scope, /not of all possible executions/);
  assert.equal(r.counterexample, undefined);
});

test('state-invariant violated by a fault: counterexample names scenario and step', () => {
  const r = tclaim('inv-bad');
  assert.equal(r.status, 'violated');
  assert.equal(r.counterexample.scenario, 'dup');
  assert.equal(r.counterexample.stepIndex, 3);
  assert.match(r.scope, /dup \(4 steps, faults: dup-request\)/);
  assert.ok(r.involved.includes('s-again'));
});

test('state-invariant over state names holds', () => {
  assert.equal(tclaim('inv-client').status, 'verified');
  // True by construction of the machine: no fault can break it, so no negative exists and it is not verified.
  assert.equal(tclaim('inv-states-only').status, 'inconclusive');
});

test('precedes holding and violated', () => {
  assert.equal(tclaim('prec-ok').status, 'verified');
  const bad = tclaim('prec-bad');
  assert.equal(bad.status, 'violated');
  assert.equal(bad.counterexample.scenario, 'rogue');
  assert.equal(bad.counterexample.stepIndex, 0);
});

test('precedes whose "then" never occurs is vacuous, so inconclusive', () => {
  assert.equal(tclaim('prec-vacuous').status, 'inconclusive');
});

test('eventually holding and violated', () => {
  assert.equal(tclaim('ev-ok').status, 'verified');
  assert.equal(tclaim('ev-final').status, 'verified');
  const bad = tclaim('ev-bad');
  assert.equal(bad.status, 'violated');
  assert.equal(bad.counterexample.scenario, 'lossy');
});

test('never holding and violated', () => {
  assert.equal(tclaim('never-ok').status, 'verified');
  const bad = tclaim('never-bad');
  assert.equal(bad.status, 'violated');
  assert.equal(bad.counterexample.stepIndex, 3);
});

test('an implication whose antecedent is never true is inconclusive, not verified', () => {
  const r = tclaim('inv-impl-vacuous');
  assert.equal(r.status, 'inconclusive');
  assert.match(r.explanation, /antecedent `server-fsm.count > 5` was never true/);
  assert.equal(tclaim('inv-impl-ok').status, 'verified');
});

test('state-invariant over traces that all have zero steps is inconclusive', () => {
  const r = tclaim('inv-empty');
  assert.equal(r.status, 'inconclusive');
  assert.match(r.explanation, /zero steps/);
});

test('never about something that cannot occur in the scenario is inconclusive', () => {
  const foreign = tclaim('never-foreign');
  assert.equal(foreign.status, 'inconclusive');
  assert.match(foreign.explanation, /cannot occur in this scenario/);
  const orphan = tclaim('never-orphan');
  assert.equal(orphan.status, 'inconclusive');
  assert.match(orphan.explanation, /absence shows nothing/);
  // An event the scenario can produce (here: emitted, then dropped) is a real "never", not a vacuous one; but the
  // drop fault drops every response, so no added fault can deliver one and no negative exists: not verified.
  const lost = tclaim('never-lost');
  assert.equal(lost.status, 'inconclusive');
  assert.doesNotMatch(lost.explanation, /cannot occur in this scenario/);
  assert.match(lost.explanation, /declares no negative/);
});

test('checkTrace: a vacuous implication is pending on a finished trace, holds on a running one', () => {
  const trace = runScenario(tmodel, 'happy');
  const done = checkTrace(tmodel, trace).find((x) => x.claimId === 'inv-impl-vacuous');
  assert.equal(done.holds, false);
  assert.equal(done.pending, true);
  assert.match(done.explanation, /never true/);
  const running = checkTrace(tmodel, { ...trace, outcome: 'running' }).find((x) => x.claimId === 'inv-impl-vacuous');
  assert.equal(running.holds, true);
});

// ---------------------------------------------------------------------------
// checkTrace
// ---------------------------------------------------------------------------

test('checkTrace evaluates exactly the claims that list the trace scenario', () => {
  const listing = (sc) => tmodel.byKind.claim.filter((c) => Array.isArray(c.data.evaluate.scenarios) && c.data.evaluate.scenarios.includes(sc)).map((c) => c.id).sort();
  for (const sc of ['happy', 'dup', 'lossy']) {
    const results = checkTrace(tmodel, runScenario(tmodel, sc));
    assert.deepEqual(results.map((r) => r.claimId).sort(), listing(sc), sc);
    for (const r of results) assert.ok(r.explanation.length > 0);
  }
  const happy = Object.fromEntries(checkTrace(tmodel, runScenario(tmodel, 'happy')).map((r) => [r.claimId, r]));
  assert.equal(happy['inv-ok'].holds, true);
});

test('checkTrace reports the step at which a listed claim fails on that trace', () => {
  const failing = [];
  for (const sc of tmodel.byKind.scenario) {
    for (const r of checkTrace(tmodel, runScenario(tmodel, sc.id))) if (!r.holds) failing.push(r);
  }
  assert.ok(failing.length > 0, 'the fixture contains at least one violated trace claim');
  assert.ok(failing.some((r) => typeof r.stepIndex === 'number'));
});

test('checkTrace on an unfinished run holds eventually only if it already occurred', () => {
  const trace = runScenario(tmodel, 'happy');
  const running = { ...trace, outcome: 'running', steps: trace.steps.slice(0, 1) };
  const r = checkTrace(tmodel, running).find((x) => x.claimId === 'ev-ok');
  assert.equal(r.holds, false);
  assert.match(r.explanation, /not finished/);
  const done = checkTrace(tmodel, { ...trace, outcome: 'running' }).find((x) => x.claimId === 'ev-ok');
  assert.equal(done.holds, true);
});

// ---------------------------------------------------------------------------
// Negatives: a trace claim is verified only when a declared negative violates it
// ---------------------------------------------------------------------------

test('negatives: verified needs a violating negative', () => {
  const ok = tclaim('inv-ok');
  assert.equal(ok.status, 'verified');
  assert.deepEqual(ok.negatives.map((n) => [n.scenario, n.faults, n.violated]), [['happy', ['dup-request'], true]]);
  assert.match(ok.explanation, /Each of its 1 negative violated it: "happy" with dup-request at step \d+/);

  const none = tclaim('neg-none');
  assert.equal(none.status, 'inconclusive');
  assert.deepEqual(none.negatives, []);
  assert.match(none.explanation, /declares no negative, so nothing shows this check can fail/);

  const holds = tclaim('neg-holds');
  assert.equal(holds.status, 'inconclusive');
  assert.equal(holds.negatives[0].violated, false);
  assert.match(holds.explanation, /the negative "happy" with drop-response did not violate it \(the claim held on that run, which ended quiescent\)/);

  const mixed = tclaim('neg-mixed');
  assert.equal(mixed.status, 'inconclusive');
  assert.deepEqual(mixed.negatives.map((n) => n.violated), [true, false]);

  const capped = tclaim('neg-capped');
  assert.equal(capped.status, 'inconclusive');
  assert.equal(capped.negatives[0].outcome, 'step-limit');
  assert.match(capped.explanation, /the run was cut off at its step limit before the expected occurrence was seen/);

  // A claim violated on its own scenarios stays violated; negatives do not soften it.
  assert.equal(tclaim('inv-bad').status, 'violated');
});

/** @param {string} claimJson */
const withClaim = (claimJson) => TRACE_SPEC.replace('"claims": [', `"claims": [ ${claimJson},`);
/** @param {string} text */
const errorCodes = (text) => analyzeSpec(text).diagnostics.filter((d) => d.severity === 'error').map((d) => d.code);

test('negatives: malformed negatives are validation errors and follow renames', () => {
  /** @param {string} neg */
  const claim = (neg) => withClaim(`{ "id": "bad-neg", "kind": "invariant", "statement": "x", "evaluate": { "method": "state-invariant", "scenarios": ["happy", "lossy"], "expr": "server-fsm.count <= 1", "negatives": ${neg} } }`);
  assert.deepEqual(errorCodes(claim('{}')), ['claim.param.type']);
  assert.deepEqual(errorCodes(claim('[ { "scenario": "dup", "faults": ["drop-response"] } ]')), ['claim.negative.scenario']);
  assert.deepEqual(errorCodes(claim('[ { "scenario": "happy" } ]')), ['claim.negative.faults']);
  assert.deepEqual(errorCodes(claim('[ { "scenario": "happy", "faults": [] } ]')), ['claim.negative.faults']);
  assert.deepEqual(errorCodes(claim('[ { "scenario": "lossy", "faults": ["drop-response"] } ]')), ['claim.negative.faults']);
  assert.deepEqual(errorCodes(claim('[ { "scenario": "happy", "faults": ["dup-request"], "why": "x" } ]')), ['claim.negative.unknown']);
  assert.ok(errorCodes(claim('[ { "scenario": "happy", "faults": ["no-such-fault"] } ]')).length >= 1);
  assert.deepEqual(errorCodes(claim('[ { "scenario": "happy", "faults": ["dup-request"], "note": "duplicates break it" } ]')), []);

  const p = new Project({ specText: claim('[ { "scenario": "happy", "faults": ["dup-request"] } ]') });
  assert.equal(p.errorCount, 0);
  const r = p.apply({ type: 'RenameEntity', id: 'dup-request', newId: 'duplicate-request' });
  assert.equal(r.ok, true, r.message);
  assert.equal(p.errorCount, 0);
  assert.match(p.specText, /"negatives": \[ \{ "scenario": "happy", "faults": \["duplicate-request"\] \} \]/);
  const r2 = p.apply({ type: 'RenameEntity', id: 'happy', newId: 'happy-path' });
  assert.equal(r2.ok, true, r2.message);
  assert.equal(p.errorCount, 0);
  assert.match(p.specText, /"negatives": \[ \{ "scenario": "happy-path"/);
});

test('negatives: every behavioral claim of the exegra specification is verified with a violating negative', () => {
  const model = load(readFileSync(new URL('../../specs/exegra/spec.jsonc', import.meta.url), 'utf8'));
  const trace = evaluateClaims(model).filter((r) => r.evaluator === 'exegra.trace/0.1');
  assert.ok(trace.length >= 10, `expected the edit-flow claims, found ${trace.length}`);
  for (const r of trace) {
    assert.equal(r.status, 'verified', `${r.claimId}: ${r.explanation}`);
    assert.ok(r.negatives && r.negatives.length >= 1, `${r.claimId} declares no negative`);
    assert.ok(r.negatives.every((n) => n.violated), `${r.claimId}: a negative did not violate it`);
  }
});

// ---------------------------------------------------------------------------
// Vacuity of only-via and of eventually (WG-4827)
// ---------------------------------------------------------------------------

const VACUOUS = `{
  "exegra": "0.1",
  "system": { "id": "vac", "name": "Vacuity" },
  "components": [
    { "id": "a", "name": "A", "category": "logical", "purpose": "p" },
    { "id": "b", "name": "B", "category": "logical", "purpose": "p" },
    { "id": "v", "name": "V", "category": "logical", "purpose": "p" }
  ],
  "relationships": [ { "id": "a-b", "kind": "calls", "from": "a", "to": "b" } ],
  "events": [ { "id": "go", "name": "Go" }, { "id": "ack", "name": "Ack" } ],
  "behaviors": [
    { "id": "m", "name": "M", "subject": "a", "initial": "idle", "variables": [],
      "states": [ { "id": "idle", "name": "Idle" }, { "id": "done", "name": "Done" } ],
      "transitions": [ { "id": "t-go", "from": "idle", "to": "done", "on": "go", "effects": [ { "emit": "ack" } ] } ] }
  ],
  "faults": [ { "id": "f-drop-go", "name": "Drop go", "kind": "drop-event", "event": "go" } ],
  "scenarios": [
    { "id": "s", "name": "S", "behaviors": ["m"], "steps": [ { "at": 0, "event": "go" } ] }
  ],
  "claims": [
    { "id": "only-no-path", "kind": "structural", "statement": "v is the only way from b to a.", "subjects": ["a"],
      "evaluate": { "method": "only-via", "from": "b", "to": "a", "via": "v" } },
    { "id": "only-from-is-via", "kind": "structural", "statement": "Every path from a goes through a.", "subjects": ["a"],
      "evaluate": { "method": "only-via", "from": "a", "to": "b", "via": "a" } },
    { "id": "ev-script", "kind": "temporal", "statement": "go is eventually delivered.", "subjects": ["m"],
      "evaluate": { "method": "eventually", "scenarios": ["s"], "occurs": { "event": "go" },
        "negatives": [ { "scenario": "s", "faults": ["f-drop-go"] } ] } },
    { "id": "ev-reaction", "kind": "temporal", "statement": "ack is eventually sent by the system.", "subjects": ["m"],
      "evaluate": { "method": "eventually", "scenarios": ["s"], "occurs": { "event": "ack" },
        "negatives": [ { "scenario": "s", "faults": ["f-drop-go"] } ] } }
  ]
}`;

const vmodel = load(VACUOUS);
const vclaim = (id) => evaluateClaim(vmodel, id);

test('only-via: no directed path at all is vacuous, so inconclusive', () => {
  const r = vclaim('only-no-path');
  assert.equal(r.status, 'inconclusive');
  assert.match(r.explanation, /holds vacuously/);
});

test('only-via: a source that is itself the via component is inconclusive, not verified by construction', () => {
  assert.equal(vclaim('only-from-is-via').status, 'inconclusive');
});

test('eventually: a scripted input is not a reaction of the system', () => {
  const r = vclaim('ev-script');
  assert.equal(r.status, 'inconclusive');
  assert.match(r.explanation, /only as the scenario's own scripted input/);
});

test('eventually: an occurrence the system emits, with a violating negative, is verified', () => {
  assert.equal(vclaim('ev-reaction').status, 'verified');
});
