// The verified kernel's model derivation and semantic hash (formal/Exegra/Model.lean and
// Hash.lean, called through src/core/parse.js and src/core/hash.js) against the JavaScript they
// replaced (tests/oracle/parse-reference.js): identical diagnostics, model and hash on
// - every specification the tests read: specs/exegra, specs/benchmark and tests/fixtures/**;
// - every specification text the core tests parse (tests/fixtures/parse-corpus/cases.json.gz:
//   the distinct texts parseSpec received while tests/core/{model,vocabulary,roundtrip,references,
//   data-model,contract-trace,fault-model,metric-spec,projections,flows,generate,claims,sim,replay,
//   import-markdown,cli,workspace}.test.js ran, the invalid-spec cases among them; 81 of the 206
//   have diagnostics);
// - the edge cases below (repeated keys, array-index keys, non-ASCII keys, unusual numbers).
// The two sweeps over every specification the tests read run in tests/proofs/model-kernel.test.js, outside the
// routine suite (npm run test:proofs, npm run verify and the Check workflow run them).

import { test } from 'node:test';
import { same } from '../oracle/same-model.js';

const BASE = (extra) => `{ "exegra": "0.1", "system": { "id": "s", "name": "S" }, ${extra} }`;

test('edge cases derive identically', () => {
  const cases = [
    '[]', '"x"', '{}', '{ "exegra": "0.2" }', '{ "exegra": { "v": 1 } }', '{ "exegra": 0.1 }',
    BASE('"components": [ { "id": "a", "name": "A", "category": "logical", "name": "B" } ]'),
    `{ "exegra": "0.1", "exegra": "0.1", "system": { "id": "s", "name": "S" }, "vocabulary": { "categories": { "x": 1 } } }`,
    BASE('"components": [ { "id": "a", "name": "A", "category": "logical", "tags": ["b", "a"], "10": 1, "9": 2, "z": 3, "ä": 4, "😀": 5, "": 6 } ]'),
    BASE('"components": [ { "id": "a", "name": "A", "category": "logical", "implementation": { "status": "manual", "notes": "-0 1e400", "x": -0, "y": 1e400, "z": 1.5e-7, "w": 123456789012345678901234 } } ]'),
    BASE('"components": [ { "id": "Bad--id", "name": "A" }, { "id": "a-", "name": "A" }, { "id": "a", "name": 1 }, { "id": "a", "name": "A" }, { "name": "no id" }, 7 ]'),
    BASE('"relationships": [ { "id": "r", "kind": "calls", "from": "s", "to": "nowhere" } ], "claims": [ { "id": "c", "kind": "structural", "statement": "x", "evaluate": { "method": "no-relationship", "from": ["s", "q"], "to": { "ids": "s", "within": "z" } } } ]'),
    BASE('"vocabulary": { "categories": { "k": { "label": 5, "shape": "nope", "extra": true }, "j": [1, null, "x"] }, "relationshipKinds": { "r": { "label": "R", "line": "dashed", "color": "blue", "dependency": "yes" } }, "entityKinds": { "goal": { "label": "Goal", "section": "goals", "properties": { "parent": { "type": "ref", "ref": "goal" }, "toString": { "type": "list", "items": { "type": "list" } }, "id": { "type": "string" } } }, "Bad": {}, "component": { "label": "x", "section": "y" } }, "properties": [ { "entity": "component", "name": "constructor", "type": "string" }, { "entity": "nope", "name": "x", "type": "string" }, { "entity": "component", "name": "risk", "type": "enum", "values": [] }, 3 ], "verificationMethods": { "reachable": { "label": "x" }, "audit": { "label": "Audit", "description": 1, "z": 0 } }, "extra": 1 }, "goals": [ { "id": "g", "parent": "s" } ]'),
    BASE('"vocabulary": [], "unknownSection": 1, "components": {}'),
    BASE('"vocabulary": { "categories": { "a": { "label": "A", "shape": "box", "color": "slate" }, "a": { "label": "B" } } }'),
  ];
  for (const [i, text] of cases.entries()) same(text, `edge ${i}`);
});
