// Semantic integrity: the parser and validator reject or report everything the
// meta-model does not describe, and never drop it silently.
import test from 'node:test';
import assert from 'node:assert/strict';
import { analyzeSpec } from '../../src/core/analyze.js';
import { semanticHash, normalize } from '../../src/core/hash.js';
import { selectComponents, dependencies, inboundRefs } from '../../src/core/query.js';

const BASE = `{
  // a comment
  "exegra": "0.1",
  "system": { "id": "sys", "name": "Sys" },
  "components": [
    { "id": "grp", "name": "Group", "kind": "subsystem", "category": "logical", "purpose": "g" },
    { "id": "a", "name": "A", "category": "computational", "parent": "grp", "purpose": "a",
      "ports": [ { "id": "a-out", "name": "out", "direction": "requires" } ] },
    { "id": "b", "name": "B", "category": "storage", "purpose": "b" }
  ],
  "relationships": [
    { "id": "a-writes-b", "kind": "writes", "from": "a-out", "to": "b", "description": "d" }
  ]
}`;

/** @param {string} text */
const codes = (text) => analyzeSpec(text).diagnostics.map((d) => d.code);

test('a well-formed specification has no diagnostics and indexes nested entities', () => {
  const { model, diagnostics, errorCount } = analyzeSpec(BASE);
  assert.equal(errorCount, 0);
  assert.deepEqual(diagnostics, []);
  assert.ok(model);
  assert.equal(model.entities.get('a-out')?.owner, 'a');
  assert.deepEqual(model.entities.get('a')?.path, ['components', 1]);
  assert.equal(model.entities.get('b')?.loc.line, 9);
});

test('duplicate ids are rejected, across entity kinds', () => {
  const text = BASE.replace('"id": "a-writes-b"', '"id": "b"');
  const { diagnostics, errorCount } = analyzeSpec(text);
  assert.equal(errorCount, 1);
  assert.equal(diagnostics[0].code, 'id.duplicate');
  assert.equal(diagnostics[0].loc?.line, 12);
});

test('unresolved and wrongly typed references are reported with locations', () => {
  const missing = analyzeSpec(BASE.replace('"to": "b"', '"to": "nope"'));
  assert.deepEqual(missing.diagnostics.filter((d) => d.severity === 'error').map((d) => d.code), ['ref.unresolved']);
  assert.equal(missing.diagnostics[0].entityId, 'a-writes-b');
  const wrongKind = analyzeSpec(BASE.replace('"to": "b"', '"to": "sys"'));
  assert.ok(wrongKind.diagnostics.some((d) => d.code === 'ref.kind'));
});

test('unsupported constructs are diagnosed, never silently dropped', () => {
  assert.ok(codes(BASE.replace('"purpose": "b"', '"purpose": "b", "colour": "red"')).includes('property.unknown'));
  assert.ok(codes(BASE.replace('"relationships"', '"deployments": [], "relationships"')).includes('spec.unknown-section'));
  assert.ok(codes(BASE.replace('"kind": "writes"', '"kind": "teleports"')).includes('property.enum'));
  assert.ok(codes(BASE.replace('"exegra": "0.1"', '"exegra": "9.9"')).includes('schema.version'));
});

test('an unknown claim evaluation method is a warning, not an error, and not a silent pass', () => {
  const text = BASE.replace('"relationships"', '"claims": [ { "id": "c1", "kind": "structural", "statement": "s", "evaluate": { "method": "divination" } } ], "relationships"');
  const { diagnostics, errorCount } = analyzeSpec(text);
  assert.equal(errorCount, 0);
  assert.ok(diagnostics.some((d) => d.code === 'claim.method.unsupported' && d.severity === 'warning'));
});

test('syntax errors yield diagnostics with positions and no model', () => {
  const { model, diagnostics } = analyzeSpec(BASE.replace('"name": "B",', '"name": "B"'));
  assert.equal(model, null);
  assert.ok(diagnostics[0].code.startsWith('syntax.'));
  assert.equal(diagnostics[0].loc?.line, 9);
});

test('containment rules: any element may be a parent, and containment must not cycle', () => {
  // Composite is derived from having members, so a component that is not a subsystem may contain another.
  const nested = analyzeSpec(BASE.replace('"parent": "grp"', '"parent": "b"'));
  assert.equal(nested.errorCount, 0, JSON.stringify(nested.diagnostics));
  assert.ok(analyzeSpec(BASE.replace('"parent": "grp"', '"parent": "sys"')).errorCount === 0, 'the system is a parent too');
  const cyc = BASE.replace('"category": "logical", "purpose": "g"', '"category": "logical", "purpose": "g", "parent": "grp"');
  assert.ok(codes(cyc).includes('component.parent-cycle'));
});

test('expressions are checked for syntax and scope', () => {
  const behaviors = (/** @type {string} */ guard) => BASE.replace('"relationships"', `"events": [ { "id": "go", "name": "Go", "payload": [ { "name": "n", "type": "number" } ] } ],
  "behaviors": [ { "id": "m", "name": "M", "subject": "a", "initial": "s0",
    "variables": [ { "name": "count", "type": "number", "initial": 0 } ],
    "states": [ { "id": "s0", "name": "S0" }, { "id": "s1", "name": "S1" } ],
    "transitions": [ { "id": "t1", "from": "s0", "to": "s1", "on": "go", "guard": ${JSON.stringify(guard)}, "effects": [ { "set": "count", "to": "count + event.n" } ] } ] } ],
  "scenarios": [ { "id": "sc", "name": "Sc", "behaviors": ["m"], "steps": [ { "at": 0, "event": "go", "payload": { "n": 1 } } ] } ],
  "relationships"`);
  assert.equal(analyzeSpec(behaviors('event.n > 0 && count == 0')).errorCount, 0);
  assert.ok(codes(behaviors('event.n >')).includes('expr.syntax'));
  assert.ok(codes(behaviors('missing == 1')).includes('expr.reference'));
  assert.ok(codes(behaviors('event.zzz == 1')).includes('expr.reference'));
});

test('model-defined vocabulary extends categories, relationship kinds and properties', () => {
  const text = BASE
    .replace('"system"', '"vocabulary": { "categories": { "queue": { "label": "Queue", "shape": "pipe", "color": "rose" } }, "relationshipKinds": { "mirrors": { "label": "Mirrors", "line": "dotted", "color": "violet", "dependency": false } }, "properties": [ { "entity": "component", "name": "tier", "type": "enum", "values": ["gold", "silver"] } ] }, "system"')
    .replace('"category": "storage", "purpose": "b"', '"category": "queue", "purpose": "b", "tier": "gold"')
    .replace('"kind": "writes"', '"kind": "mirrors"');
  const { model, errorCount, diagnostics } = analyzeSpec(text);
  assert.equal(errorCount, 0, JSON.stringify(diagnostics));
  assert.equal(model?.meta.entities.component.properties.tier.extension, true);
  assert.ok(codes(text.replace('"tier": "gold"', '"tier": "bronze"')).includes('property.enum'));
});

test('gaps are reported as info: missing purpose, unconnected component', () => {
  const text = BASE.replace(', "purpose": "b"', '').replace('"to": "b"', '"to": "a"');
  const d = analyzeSpec(text).diagnostics;
  assert.ok(d.some((x) => x.code === 'gap.missing-property' && x.entityId === 'b' && x.severity === 'info'));
  assert.ok(d.some((x) => x.code === 'gap.unconnected' && x.entityId === 'b'));
});

test('equivalent inputs normalize to equal semantic content', () => {
  const reordered = `{
    "relationships": [ { "to": "b", "from": "a-out", "description": "d", "kind": "writes", "id": "a-writes-b" } ],
    "components": [
      { "purpose": "b", "category": "storage", "name": "B", "id": "b" },   /* moved */
      { "id": "grp", "name": "Group", "kind": "subsystem", "category": "logical", "purpose": "g" },
      { "id": "a", "ports": [ { "direction": "requires", "name": "out", "id": "a-out" } ], "name": "A", "category": "computational", "parent": "grp", "purpose": "a" }
    ],
    "system": { "name": "Sys", "id": "sys" },
    "exegra": "0.1",
  }`;
  const m1 = analyzeSpec(BASE).model;
  const m2 = analyzeSpec(reordered).model;
  assert.ok(m1 && m2);
  assert.deepEqual(normalize(m1), normalize(m2));
  assert.equal(semanticHash(m1), semanticHash(m2));
  const m3 = analyzeSpec(BASE.replace('"name": "B"', '"name": "B2"')).model;
  assert.notEqual(semanticHash(m1), semanticHash(m3));
});

test('queries resolve ports to components and select through containment', () => {
  const { model } = analyzeSpec(BASE);
  assert.ok(model);
  assert.deepEqual(dependencies(model, 'a').map((d) => d.id), ['b']);
  assert.deepEqual(dependencies(model, 'b', { direction: 'in' }).map((d) => d.id), ['a']);
  assert.deepEqual(selectComponents(model, 'grp').map((c) => c.id), ['grp', 'a']);
  assert.deepEqual(selectComponents(model, { category: 'storage' }).map((c) => c.id), ['b']);
  assert.deepEqual(selectComponents(model, {}).map((c) => c.id), []);
  assert.deepEqual(inboundRefs(model, 'b').map((r) => r.from), ['a-writes-b']);
});

test('spec-supplied names that exist on Object.prototype are not treated as known', () => {
  const claim = BASE.replace('"relationships"', '"claims": [ { "id": "c1", "kind": "structural", "statement": "s", "evaluate": { "method": "toString" } } ], "relationships"');
  const { diagnostics } = analyzeSpec(claim);
  assert.ok(diagnostics.some((d) => d.code === 'claim.method.unsupported' && d.severity === 'warning'));
  assert.ok(codes(BASE.replace('"relationships"', '"constructor": [], "relationships"')).includes('spec.unknown-section'));
  const vocab = BASE.replace('"system"', '"vocabulary": { "properties": [ { "entity": "constructor", "name": "tier", "type": "string" } ] }, "system"');
  assert.ok(codes(vocab).includes('vocabulary.entity'));
});

// Test evidence references: validate and exegra verify use one rule (src/core/evidence-ref.js).
import { testRefProblem, describeTestRefProblem } from '../../src/core/evidence-ref.js';

/** @param {string[]} refs */
const specWithTestRefs = (refs) => BASE.replace(/\}\s*$/, `,
  "claims": [ { "id": "c", "kind": "invariant", "statement": "s", "subjects": ["a"], "assumptions": [],
    "evaluate": { "method": "external-evidence" } } ],
  "evidence": [ ${refs.map((ref, i) => `{ "id": "ev${i}", "claim": "c", "kind": "test", "ref": ${JSON.stringify(ref)} }`).join(', ')} ]
}`);

test('test evidence references: an unsafe one is a validation error and a plain one is not', () => {
  const bad = analyzeSpec(specWithTestRefs(['tests/core/model.test.js#a title, with a comma']));
  const errors = bad.diagnostics.filter((d) => d.code === 'evidence.ref-unsafe');
  assert.equal(errors.length, 1);
  assert.equal(errors[0].severity, 'error');
  assert.equal(errors[0].entityId, 'ev0');
  assert.deepEqual(errors[0].path, ['evidence', 0, 'ref']);
  assert.match(errors[0].message, /"ev0"|Evidence "ev0"/);
  assert.match(errors[0].message, /","/);
  assert.match(errors[0].message, /character 33/);
  assert.equal(bad.errorCount, 1);

  const good = analyzeSpec(specWithTestRefs(['tests/core/model.test.js#a plain title', 'tests/core/model.test.js']));
  assert.equal(good.diagnostics.filter((d) => d.code === 'evidence.ref-unsafe').length, 0);
  assert.equal(good.errorCount, 0);
});

test('validate and verify share one rule: the validator flags exactly the references the rule refuses', () => {
  const refs = [
    'tests/core/a.test.js', 'tests/browser/x.spec.js#a title', 'tests/core/a.test.js#pattern: 1-2_3/4.5',
    'tests/core/a.test.js#has, comma', 'tests/core/a.test.js#semi;colon', "tests/core/a.test.js#it's",
    '#no file before the hash', 'tests/core/a.test.js#(parens)',
  ];
  const diagnosed = new Set(analyzeSpec(specWithTestRefs(refs)).diagnostics
    .filter((d) => d.code === 'evidence.ref-unsafe').map((d) => d.entityId));
  refs.forEach((ref, i) => {
    assert.equal(diagnosed.has(`ev${i}`), testRefProblem(ref) !== null, `ref ${JSON.stringify(ref)}`);
  });
  assert.deepEqual(testRefProblem('tests/core/a.test.js#has, comma'), { reason: 'characters', characters: [','], position: 25 });
  assert.equal(testRefProblem('#no file before the hash')?.reason, 'no-file');
  assert.match(describeTestRefProblem('a,b', testRefProblem('a,b') ?? { reason: 'no-file' }), /","|"," /);
});

test('a realisation-root reference may use any printable character in its title, but not in its file', () => {
  assert.equal(testRefProblem('platform:apps/api/a.test.ts#suite > case, with (parens)'), null);
  assert.equal(testRefProblem('platform:apps/api/a,b.test.ts#suite > case')?.reason, 'characters');
  assert.equal(testRefProblem('tests/core/a.test.js#suite > case')?.reason, 'characters');
  assert.equal(testRefProblem('platform:apps/api/a.test.ts#tab\there')?.reason, 'characters');
});
