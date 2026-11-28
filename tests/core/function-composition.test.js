// Functional composition along the hierarchy (src/core/function-composition.js, WG-5730): function entities attach
// to elements, and a composite's declared signature must equal the composition of its stages' signatures. The
// compiler fixtures (tests/fixtures/multiscale-external/compiler.jsonc and compiler-mismatch.jsonc) are loaded
// through the command line with --spec.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { runCommand } from '../../cli/commands.js';
import { analyzeSpec } from '../../src/core/analyze.js';
import { functionComposition } from '../../src/core/function-composition.js';

const FIXTURES = path.join(path.dirname(fileURLToPath(import.meta.url)), '..', 'fixtures', 'multiscale-external');
const COMPILER = path.join(FIXTURES, 'compiler.jsonc');
const MISMATCH = path.join(FIXTURES, 'compiler-mismatch.jsonc');

/** @param {any} r */
const codes = (r) => r.diagnostics.filter((/** @type {any} */ d) => d.severity === 'error').map((/** @type {any} */ d) => d.code);

/** The compiler fixture as data, edited, and analysed. @param {(spec: any) => void} edit */
function analyseEdited(edit) {
  const spec = JSON.parse(fs.readFileSync(COMPILER, 'utf8'));
  edit(spec);
  return analyzeSpec(JSON.stringify(spec));
}
/** @param {any} spec @param {string} id */
const fn = (spec, id) => spec.functions.find((/** @type {any} */ f) => f.id === id);

// The compiler fixture (pipeline, shared diagnostics, three levels of composition) validates, and the compose command derives each composite's signature from its stages.
// @evidence function-composition-along-hierarchy
test('the compiler fixture validates and composes its function entities along the hierarchy', async () => {
  const v = /** @type {any} */ (await runCommand('validate', ['--spec', COMPILER]));
  assert.equal(v.ok, true);
  assert.equal(v.result.errors, 0);
  assert.equal(v.result.warnings, 0);
  const c = /** @type {any} */ (await runCommand('compose-functions', ['--spec', COMPILER]));
  assert.equal(c.ok, true);
  assert.equal(c.result.holds, true);
  assert.deepEqual(c.result.composites.map((/** @type {any} */ x) => [x.function, x.element, x.stages.map((/** @type {any} */ s) => s.function)]), [
    ['analyse', 'frontend', ['lex', 'parse', 'check']],
    ['compile', 'compiler', ['analyse', 'generate']],
    ['generate', 'backend', ['optimise', 'emit']],
  ]);
  // The derived signature of the top composite is its first stage's parameters and its last stage's returns, through two levels.
  const compile = c.result.composites.find((/** @type {any} */ x) => x.function === 'compile');
  assert.deepEqual(compile.derived, { params: [{ name: 'source', type: 'source-text' }], returns: 'object-code', errors: 'diagnostic' });
  assert.deepEqual(compile.derived, compile.declared);
  assert.equal(c.result.attached.length, 8);
});

// The compiler-mismatch fixture is refused with function.composition-returns and, one level up, function.composition-chain.
// @evidence function-composition-along-hierarchy
test('a composite whose declared signature differs from its members composition is diagnosed in the negative fixture', async () => {
  const v = /** @type {any} */ (await runCommand('validate', ['--spec', MISMATCH]));
  assert.equal(v.ok, false);
  const found = v.diagnostics.filter((/** @type {any} */ d) => d.severity === 'error').map((/** @type {any} */ d) => `${d.code} ${d.entityId}`);
  assert.deepEqual(found.sort(), ['function.composition-chain compile', 'function.composition-returns analyse']);
  const c = /** @type {any} */ (await runCommand('compose-functions', ['--spec', MISMATCH, 'analyse']));
  assert.equal(c.result.holds, false);
  assert.match(c.result.composites[0].problems[0].message, /declares that it returns syntax-tree, but its last stage "check" returns typed-tree/);
});

// Each rule of the signature, each with a negative edit of the compiler fixture.
// @evidence function-composition-along-hierarchy
test('each part of the signature is checked with a negative edit', () => {
  assert.deepEqual(codes(analyseEdited(() => {})), []);
  assert.deepEqual(codes(analyseEdited((s) => { fn(s, 'analyse').params[0].type = 'token-stream'; fn(s, 'analyse').body = 'try call check(try call parse(try call lex(source)))'; })).filter((c) => c.startsWith('function.composition')), ['function.composition-params', 'function.composition-params'], 'analyse against its first stage, and compile against analyse as its first stage');
  // Renaming the first stage's parameter without the composite following it.
  assert.ok(codes(analyseEdited((s) => { fn(s, 'analyse').params[0].name = 'input'; fn(s, 'analyse').body = 'try call check(try call parse(try call lex(input)))'; })).includes('function.composition-params'));
  // Stage order that does not chain.
  assert.ok(codes(analyseEdited((s) => { fn(s, 'analyse').composition.stages = ['lex', 'check', 'parse']; })).includes('function.composition-chain'));
  // A later stage with two parameters.
  assert.ok(codes(analyseEdited((s) => { fn(s, 'parse').params.push({ name: 'extra', type: 'i64' }); })).includes('function.composition-arity'));
  // Stages with different error unions.
  assert.ok(codes(analyseEdited((s) => {
    s.types.push({ id: 'other-error', name: 'Other error', kind: 'union', variants: [{ name: 'Boom', fields: [{ name: 'message', type: 'string' }] }] });
    fn(s, 'emit').errors = 'other-error';
  })).includes('function.composition-errors'));
  // A composite that does not declare the errors its stages share.
  assert.ok(codes(analyseEdited((s) => { delete fn(s, 'generate').errors; })).includes('function.composition-errors'));
  // A stage that is not a member of the composite's element.
  assert.ok(codes(analyseEdited((s) => { fn(s, 'emit').element = 'lexer'; })).includes('function.composition-stage'));
  // A stage that is not a function, and a composition that lists its own function.
  // A stage that names no entity is refused by reference resolution before the composition is checked.
  assert.ok(codes(analyseEdited((s) => { fn(s, 'generate').composition.stages = ['optimise', 'no-such-function']; })).includes('ref.unresolved'));
  assert.ok(codes(analyseEdited((s) => { fn(s, 'generate').composition.stages = ['generate', 'emit']; })).includes('function.composition-cycle'));
});

test('a function on an element whose members carry functions, with no composition declared, is a warning', () => {
  const r = analyseEdited((s) => { delete fn(s, 'generate').composition; });
  const w = r.diagnostics.filter((/** @type {any} */ d) => d.code === 'function.composition-missing');
  assert.deepEqual(w.map((/** @type {any} */ d) => [d.severity, d.entityId]), [['warning', 'generate']]);
});

test('composition is a function of the specification, independent of declaration order', () => {
  const a = functionComposition(/** @type {any} */ (analyseEdited(() => {}).model));
  const b = functionComposition(/** @type {any} */ (analyseEdited((s) => { s.functions.reverse(); }).model));
  assert.deepEqual(a, b);
});
