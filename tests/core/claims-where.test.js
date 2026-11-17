import { test } from 'node:test';
import assert from 'node:assert/strict';
import { analyzeSpec } from '../../src/core/analyze.js';
import { evaluateClaim } from '../../src/core/claims.js';

// Today the web calls the db directly; the target routes it through the API.
const SPEC = `{
  "exegra": "0.1",
  "system": { "id": "shop", "name": "Shop" },
  "vocabulary": { "properties": [
    { "entity": "relationship", "name": "layer", "type": "enum", "values": ["current", "target", "retiring"] }
  ] },
  "components": [
    { "id": "web", "name": "Web", "category": "client" },
    { "id": "api", "name": "API", "category": "computational" },
    { "id": "db", "name": "DB", "category": "storage" }
  ],
  "relationships": [
    { "id": "r-web-db", "kind": "calls", "from": "web", "to": "db", "layer": "retiring" },
    { "id": "r-web-api", "kind": "calls", "from": "web", "to": "api", "layer": "target" },
    { "id": "r-api-db", "kind": "writes", "from": "api", "to": "db", "layer": "current" }
  ],
  "claims": [
    { "id": "c-target", "kind": "structural", "statement": "In the target, the web reaches the db only via the API.",
      "evaluate": { "method": "only-via", "from": "web", "to": "db", "via": "api", "where": { "property": "layer", "values": ["current", "target"] } } },
    { "id": "c-today", "kind": "structural", "statement": "Today, the web reaches the db only via the API.",
      "evaluate": { "method": "only-via", "from": "web", "to": "db", "via": "api", "where": { "property": "layer", "values": ["current", "retiring"] } } },
    { "id": "c-all", "kind": "structural", "statement": "Over every layer, the web reaches the db only via the API.",
      "evaluate": { "method": "only-via", "from": "web", "to": "db", "via": "api" } },
    { "id": "c-reach-target", "kind": "structural", "statement": "In the target, the web reaches the API.",
      "evaluate": { "method": "reachable", "from": "web", "to": "api", "where": { "property": "layer", "values": ["current", "target"] } } },
    { "id": "c-reach-today", "kind": "structural", "statement": "Today, the web reaches the API.",
      "evaluate": { "method": "reachable", "from": "web", "to": "api", "where": { "property": "layer", "values": ["current", "retiring"] } } },
    { "id": "c-nr-target", "kind": "structural", "statement": "In the target, the web has no direct link to the db.",
      "evaluate": { "method": "no-relationship", "from": "web", "to": "db", "where": { "property": "layer", "values": ["current", "target"] } } },
    { "id": "c-misspelt", "kind": "structural", "statement": "A misspelt layer would empty the graph.",
      "evaluate": { "method": "no-relationship", "from": "web", "to": "db", "where": { "property": "layer", "values": ["targte"] } } },
    { "id": "c-acyclic", "kind": "structural", "statement": "The target graph is acyclic.",
      "evaluate": { "method": "acyclic", "kinds": ["calls", "writes"], "where": { "property": "layer", "values": ["current", "target"] } } }
  ]
}`;

const { model, errorCount, diagnostics } = analyzeSpec(SPEC);
const claim = (/** @type {string} */ id) => evaluateClaim(/** @type {any} */ (model), id);

test('the spec with a where filter loads without errors', () => {
  assert.equal(errorCount, 0, JSON.stringify(diagnostics.filter((d) => d.severity === 'error'), null, 1));
});

test('where scopes only-via to one layer, so the same rule holds for the target and fails for today', () => {
  assert.equal(claim('c-target').status, 'verified');
  const today = claim('c-today');
  assert.equal(today.status, 'violated');
  assert.deepEqual(today.counterexample.path, ['web', 'r-web-db', 'db']);
  assert.match(today.scope, /with layer current or retiring/);
  assert.equal(claim('c-all').status, 'violated');
});

test('where scopes reachable and no-relationship', () => {
  assert.equal(claim('c-reach-target').status, 'verified');
  assert.equal(claim('c-reach-today').status, 'violated');
  assert.equal(claim('c-nr-target').status, 'verified');
  assert.equal(claim('c-acyclic').status, 'verified');
});

test('a value no relationship carries is inconclusive, never verified', () => {
  const r = claim('c-misspelt');
  assert.equal(r.status, 'inconclusive');
  assert.match(r.explanation, /"targte"/);
});

test('a malformed where is a validation error', () => {
  const bad = SPEC.replace('"where": { "property": "layer", "values": ["targte"] }', '"where": { "property": "layer", "values": [] }');
  const r = analyzeSpec(bad);
  assert.ok(r.diagnostics.some((d) => d.code === 'claim.param.type' && d.severity === 'error'), JSON.stringify(r.diagnostics));
});
