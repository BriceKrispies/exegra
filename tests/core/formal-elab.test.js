// Elaboration of format-2 engine input into the behaviour calculus (formal/Exegra/Elab.lean, `engine.elab`;
// WG-5681 criteria 16 and 17).
//
// - Every conformance golden (all version 2) and every version-2
//   fixture under tests/ is elaborated; exactly the inputs of tests/conformance/expected-refusals.json are
//   refused, each with its kind. The test prints how many inputs are accepted and refused per kind.
// - The five behaviours of WG-4688 are decided (docs/simulation.md, "Elaboration into the behaviour
//   calculus"): a repeated behaviour id and an id declared both as an event and as a behaviour, fault or
//   scenario are refused as ill-typed; a negative delay is refused when the input is decoded; a variable
//   named time or state is refused; and `set a` to an object value copies it, so in the next step guards
//   and effects both see `a == b`.
//
// Needs `npm run build:formal-wasm`.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { call, initLean } from '../../src/core/lean.js';

const TESTS = path.join(path.dirname(fileURLToPath(import.meta.url)), '..');
const GOLDENS = path.join(TESTS, 'conformance', 'goldens');
const EXPECTED = JSON.parse(fs.readFileSync(path.join(TESTS, 'conformance', 'expected-refusals.json'), 'utf8')).refused;

await initLean();

/** The elaboration of one input: decoded or not, and the summary. @param {any} input */
function elab(input) {
  const r = call('engine.elab', input);
  if (!r.ok) return { decoded: false, error: r.error };
  return { decoded: true, ...r.value };
}

/** Every golden input, by `goldens/<source>/<name>`. @returns {[string, any][]} */
function goldenInputs() {
  /** @type {[string, any][]} */
  const out = [];
  for (const source of fs.readdirSync(GOLDENS).sort()) {
    for (const f of fs.readdirSync(path.join(GOLDENS, source)).filter((x) => x.endsWith('.input.json')).sort()) {
      out.push([`goldens/${source}/${f.replace(/\.input\.json$/, '')}`, JSON.parse(fs.readFileSync(path.join(GOLDENS, source, f), 'utf8'))]);
    }
  }
  return out;
}

/** Every version-2 engine-input fixture under tests/fixtures: a file holding one, or holding one under `base`. */
function fixtureInputs() {
  /** @type {[string, any][]} */
  const out = [];
  const walk = (/** @type {string} */ dir) => {
    for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
      const p = path.join(dir, e.name);
      if (e.isDirectory()) walk(p);
      else if (e.name.endsWith('.json')) {
        let j;
        try { j = JSON.parse(fs.readFileSync(p, 'utf8')); } catch { continue; }
        const input = j?.format === 'exegra-sim-input' ? j : j?.base?.format === 'exegra-sim-input' ? j.base : null;
        if (input?.version === 2) out.push([path.relative(TESTS, p).replace(/\\/g, '/').replace(/\.json$/, ''), input]);
      }
    }
  };
  walk(path.join(TESTS, 'fixtures'));
  return out;
}

test('every lifted golden and version-2 fixture elaborates, except the expected refusals', () => {
  /** @type {Record<string, number>} */
  const counts = { accepted: 0 };
  /** @type {Record<string, string>} */
  const refused = {};
  const inputs = [...goldenInputs(), ...fixtureInputs()];
  for (const [name, input] of inputs) {
    const r = elab(input);
    if (!r.decoded) {
      // The format-2 decoder refuses it (the legacy engine refuses it too): not an input to elaborate.
      counts.undecoded = (counts.undecoded ?? 0) + 1;
      refused[name] = 'undecoded';
      if (EXPECTED[name]?.error) assert.match(r.error, new RegExp(EXPECTED[name].error), `${name} is refused for its reason`);
      continue;
    }
    if (r.accepted) counts.accepted++;
    else {
      counts[r.kind] = (counts[r.kind] ?? 0) + 1;
      refused[name] = r.kind;
      if (EXPECTED[name]?.construct) assert.match(r.detail, new RegExp(EXPECTED[name].construct), `${name} names the construct`);
    }
  }
  process.stdout.write(`elaboration of ${inputs.length} inputs: ${Object.entries(counts).map(([k, n]) => `${n} ${k}`).join(', ')}\n`);
  assert.deepEqual(refused, Object.fromEntries(Object.entries(EXPECTED).map(([k, v]) => [k, v.kind])));
});

/** A small version-2 input: one behaviour `m`, events `go` and `next`. @param {any} [over] */
function tiny(over = {}) {
  return {
    format: 'exegra-sim-input', version: 2, time: { unit: 'tick', perSecond: null },
    events: [{ id: 'go' }, { id: 'next' }],
    behaviors: [{ id: 'm', initial: 's', states: ['s'], variables: [{ name: 'n', initial: 0 }],
      transitions: [{ id: 't', from: 's', to: 's', on: 'go', guard: null, faultOnly: false, effects: [{ set: 'n', to: 'n + 1' }] }] }],
    faults: [],
    scenario: { id: 'sc', steps: [{ at: 0, event: 'go' }], faults: [], stepLimit: 10 },
    ...over,
  };
}

// Decimal literals and initial values elaborate; 0.1 + 0.2 == 0.3 is true on the calculus path and 0.1 + 0.2 is written as 0.3; the expression-showcase golden input with inexact := 0.1 + 0.2 and quo := a / b is accepted.
// @evidence numbers-are-exact-rationals
test('a decimal literal', () => {
  // Numbers are exact rationals (WG-5683): a decimal literal, an initial value or a payload elaborates,
  // and 0.1 + 0.2 == 0.3 evaluates to true on the calculus path.
  for (const to of ['0.1 + 0.2', 'a + 0.5']) {
    const input = tiny();
    input.behaviors[0].variables.push({ name: 'a', initial: 1 });
    input.behaviors[0].transitions[0].effects = [{ set: 'n', to }];
    assert.equal(elab(input).accepted, true, to);
  }
  const init = tiny();
  init.behaviors[0].variables[0].initial = 0.5;
  assert.equal(elab(init).accepted, true, 'a decimal initial value');
  const exact = tiny();
  exact.behaviors[0].variables.push({ name: 'ok', initial: false }, { name: 'x', initial: 0 });
  exact.behaviors[0].transitions[0].effects = [{ set: 'x', to: '0.1 + 0.2' }, { set: 'ok', to: '0.1 + 0.2 == 0.3' }];
  assert.equal(elab(exact).accepted, true);
  const r = call('engine.run', exact);
  assert.ok(r.ok, r.ok ? '' : r.error);
  const trace = r.value;
  assert.equal(trace.semantics, undefined, 'run on the calculus, not the legacy interpreter');
  assert.equal(trace.final.machines.m.vars.ok, true, '0.1 + 0.2 == 0.3');
  assert.equal(trace.final.machines.m.vars.x, 0.3, '0.1 + 0.2 is written as 0.3');
  // fixture/expression-showcase with its original inexact := 0.1 + 0.2 (and quo := a / b) is accepted.
  const showcase = JSON.parse(fs.readFileSync(path.join(GOLDENS, 'fixture', 'expression-showcase.input.json'), 'utf8'));
  const setsOf = (/** @type {any} */ b) => b.transitions.flatMap((/** @type {any} */ t) => t.effects).map((/** @type {any} */ e) => `${e.set} := ${e.to}`);
  const ops = showcase.behaviors.find((/** @type {any} */ b) => b.id === 'ops-machine');
  assert.ok(setsOf(ops).includes('inexact := 0.1 + 0.2'));
  assert.ok(setsOf(ops).includes('quo := a / b'));
  assert.equal(elab(showcase).accepted, true, 'expression-showcase is accepted');
});

test('a minimal input is accepted', () => {
  const r = elab(tiny());
  assert.equal(r.accepted, true, JSON.stringify(r));
  assert.equal(r.machines, 1);
});

test('WG-4688: a repeated behaviour id is refused as ill-typed', () => {
  const base = tiny();
  const r = elab({ ...base, behaviors: [base.behaviors[0], base.behaviors[0]] });
  assert.equal(r.accepted, false);
  assert.equal(r.kind, 'illTyped');
  assert.match(r.detail, /repeated/);
});

test('WG-4688: an id declared both as an event and as a behaviour, fault or scenario is refused', () => {
  for (const extra of ['m', 'sc']) {
    const input = tiny();
    input.events.push({ id: extra });
    const r = elab(input);
    assert.equal(r.accepted, false, extra);
    assert.equal(r.kind, 'illTyped');
    assert.match(r.detail, /both as an event/);
  }
});

test('WG-4688: a negative after or by is refused', () => {
  const after = tiny();
  after.behaviors[0].transitions[0].effects.push({ emit: 'next', after: -1 });
  const r = elab(after);
  assert.equal(r.decoded, false, 'a negative delay is refused when the input is decoded');
  assert.match(r.error, /must be an integer in \[0,/);
  const by = tiny({ faults: [{ id: 'f', kind: 'delay-event', event: 'go', by: -2 }] });
  by.scenario.faults = ['f'];
  const r2 = elab(by);
  assert.equal(r2.decoded, false);
  assert.match(r2.error, /must be an integer in \[0,/);
});

test('WG-4688: a variable named time or state is refused', () => {
  for (const name of ['time', 'state']) {
    const input = tiny();
    input.behaviors[0].variables.push({ name, initial: 0 });
    const r = elab(input);
    assert.equal(r.accepted, false, name);
    assert.equal(r.kind, 'illTyped');
    assert.match(r.detail, /reserved/);
  }
});

test('WG-4688: set a to an object value copies it, and the next step sees a == b', () => {
  const input = tiny();
  const b = input.behaviors[0];
  b.variables = [{ name: 'a', initial: {} }, { name: 'b', initial: { x: 1, y: [2, 3] } }, { name: 'same', initial: false }];
  b.transitions = [
    { id: 'copy', from: 's', to: 's', on: 'go', guard: null, faultOnly: false, effects: [{ set: 'a', to: 'b' }, { emit: 'next', after: 0 }] },
    { id: 'look', from: 's', to: 's', on: 'next', guard: 'a == b', faultOnly: false, effects: [{ set: 'same', to: 'a == b' }] },
  ];
  assert.equal(elab(input).accepted, true, 'the copy is in the calculus fragment');
  const r = call('engine.run', input);
  assert.ok(r.ok, r.ok ? '' : r.error);
  const steps = r.value.steps;
  assert.equal(steps.length, 2);
  assert.deepEqual(steps[1].fired.map((/** @type {any} */ f) => f.transition), ['look'], 'the guard a == b holds in the step after the copy');
  assert.equal(steps[1].config.machines.m.vars.same, true, 'the effect sees a == b');
  assert.deepEqual(steps[1].config.machines.m.vars.a, { x: 1, y: [2, 3] });
});
