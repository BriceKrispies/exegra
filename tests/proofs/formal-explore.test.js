// Exhaustive exploration with the explorer of the behaviour calculus (formal/Exegra/ProveB.lean),
// through `exegra prove` (tools/prove.js, src/core/proof-export.js), on the fixture protocol
// tests/fixtures/race: two clients increment a counter.
//
// - The read-modify-write store has a lost-update race that its scripted run does not show (the
//   simulator's trace check passes) and that another order of the simultaneous events does show:
//   prove must report a counterexample, a run of the successor relation that ends with the
//   invariant false, accepted by Lean.
// - The atomic store has no such race, under every order and with or without its lost-write fault:
//   prove must report the invariant verified for every reachable configuration, with the same N of
//   visited calculus states on every run.
// - Temporal claims (formal/Exegra/ProveB.lean, monitors of Core/BehavCheck.lean) are checked on every complete run: a `precedes` that
//   holds, an `eventually` that holds, an `eventually` that fails because a path ends (quiescent) before the
//   event, and a `precedes` that holds in the scripted run and is violated by a reordering.
//
// Every check needs Lake (it builds formal/ and checks the generated proof file). Without it the
// test is skipped with a message: a skip is not a pass.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { Project } from '../../src/core/project.js';
import { checkTrace } from '../../src/core/claims.js';
import { runScenario } from '../../src/core/engine.js';
import { spawnSync } from 'node:child_process';
import { lakeAvailable, proveScenario, nativeLibOptions, FORMAL } from '../../tools/prove.js';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const SPEC = path.join(HERE, '..', 'fixtures', 'race', 'spec.jsonc');

function model() {
  const project = new Project({ name: 'race', specText: fs.readFileSync(SPEC, 'utf8'), layoutText: null });
  assert.ok(project.model, 'the fixture parses');
  return project.model;
}

const NO_LAKE = 'lake is not on the PATH (install elan with the toolchain in formal/lean-toolchain); exhaustive exploration was not checked';

// exegra prove on the race fixture: the lost update is a counterexample accepted by Lean, its scripted run passes the trace check, the atomic store holds for all N configurations with the same N on two runs, and its precedes claim holds on every complete run. Skipped, with a message, when lake is not on the PATH.
// @evidence exhaustive-exploration-sound #
test('the scripted run of the racy store passes its trace check', () => {
  const m = model();
  const check = checkTrace(m, runScenario(m, 'lost-update-race')).find((c) => c.claimId === 'racy-no-lost-update');
  assert.equal(check?.holds, true, 'the race needs another order of the simultaneous events');
});

test('exhaustive exploration finds the lost update as a counterexample accepted by Lean', (t) => {
  if (!lakeAvailable()) { t.skip(NO_LAKE); return; }
  const m = model();
  const out = proveScenario(m, 'lost-update-race', { withSteps: true });
  const c = out.claims.find((x) => x.claimId === 'racy-no-lost-update');
  assert.ok(c, 'the claim is checked');
  assert.equal(c.method, 'lean-exhaustive');
  assert.equal(c.result, 'counterexample');
  assert.ok(c.axioms.length > 0, 'the axioms of the theorem are reported');
  assert.ok(fs.existsSync(path.join(FORMAL, c.file.replace(/^formal\//, ''))), 'the proof file was written');
  const cex = c.counterexample;
  // The violating run delivers some simultaneous event ahead of an earlier one.
  assert.ok(cex.choices.some((/** @type {number} */ k) => k > 0), 'the run reorders simultaneous events');
  assert.equal(cex.steps.length, cex.stepCount);
  assert.equal(cex.stepList.length, cex.stepCount);
  const last = cex.steps[cex.steps.length - 1].config.machines['racy-store'].vars;
  assert.notEqual(last.value, last.writes, 'the invariant is false at the end of the run');
  assert.match(c.explanation, /is false after step/);
});

// exegra prove reports the atomic store's invariant as holding with method lean-exhaustive, the bound and N, after Lean accepted the theorem in the generated file. Skipped, with a message, when lake is not on the PATH.
// @evidence invariants-proved-within-bounds # the atomic store is verified for every reachable configuration
test('the atomic store is verified for every reachable configuration, reproducibly', (t) => {
  if (!lakeAvailable()) { t.skip(NO_LAKE); return; }
  const m = model();
  const first = proveScenario(m, 'atomic-increments');
  const second = proveScenario(m, 'atomic-increments');
  const c1 = first.claims.find((x) => x.claimId === 'atomic-no-lost-update');
  const c2 = second.claims.find((x) => x.claimId === 'atomic-no-lost-update');
  assert.equal(c1?.result, 'holds');
  assert.equal(c1.method, 'lean-exhaustive');
  assert.ok(Number.isInteger(c1.states) && c1.states > 1, 'N distinct configurations were visited');
  assert.equal(c1.bound, first.bound);
  assert.equal(c2?.states, c1.states, 'the same N on every run');
  assert.match(c1.explanation, /for every reachable configuration/);
  assert.match(c1.explanation, new RegExp(`visited ${c1.states} distinct calculus states`));
  const temporal = first.claims.find((x) => x.claimId === 'atomic-read-precedes-write');
  assert.equal(temporal?.result, 'holds');
});

// exegra prove on the race fixture: an eventually holds on every path; an eventually fails with a counterexample run that drops the event and ends without it; a precedes that the scripted run satisfies is violated by a run that reorders simultaneous events. Skipped, with a message, when lake is not on the PATH.
// @evidence temporal-claims-checked-on-all-runs # temporal claims: eventually holds
test('temporal claims: eventually holds, eventually fails on a path that ends first, precedes fails under reordering', (t) => {
  if (!lakeAvailable()) { t.skip(NO_LAKE); return; }
  const m = model();
  const atomic = proveScenario(m, 'atomic-increments', { withSteps: true });
  const holds = atomic.claims.find((x) => x.claimId === 'atomic-a-write-happens');
  assert.equal(holds?.result, 'holds', "A's write happens on every path");
  assert.ok(holds.axioms.length > 0);
  const ends = atomic.claims.find((x) => x.claimId === 'atomic-b-write-happens');
  assert.equal(ends?.result, 'counterexample', "a path drops B's write and ends without it");
  const cex = ends.counterexample;
  assert.deepEqual(cex.faults, ['write-b-lost']);
  assert.ok(!cex.steps.some((/** @type {any} */ s) => s.kind === 'deliver' && s.event.id === 'write-b'), 'write-b is never delivered');
  assert.ok(cex.steps.some((/** @type {any} */ s) => s.kind === 'drop' && s.event.id === 'write-b'), 'the run drops it');
  const racy = proveScenario(m, 'lost-update-race', { withSteps: true });
  const prec = racy.claims.find((x) => x.claimId === 'racy-a-writes-first');
  assert.equal(prec?.result, 'counterexample', 'the scripted order passes; another order of simultaneous events violates it');
  assert.ok(prec.counterexample.choices.some((/** @type {number} */ k) => k > 0), 'the run reorders simultaneous events');
  const fired = prec.counterexample.steps.flatMap((/** @type {any} */ s) => s.fired.map((/** @type {any} */ f) => f.transition));
  assert.ok(fired.includes('racy-write-b') && !fired.includes('racy-write-a'), 'B writes with no earlier write by A');
  const scripted = checkTrace(m, runScenario(m, 'lost-update-race')).find((c) => c.claimId === 'racy-a-writes-first');
  assert.equal(scripted?.holds, true, "the simulator's trace check passes on the scripted run");
});

// WG-5681, criteria 18 and 26: the explorer on the behaviour calculus (tests/fixtures/behaviour-order).
const ORDER = path.join(HERE, '..', 'fixtures', 'behaviour-order', 'spec.jsonc');

function orderModel() {
  const project = new Project({ name: 'behaviour-order', specText: fs.readFileSync(ORDER, 'utf8'), layoutText: null });
  assert.ok(project.model, 'the fixture parses');
  return project.model;
}

/** @param {any} out @param {string} id */
const claimOf = (out, id) => out.claims.find((/** @type {any} */ c) => c.claimId === id);

test('(a) b.y == 0 holds whichever of a and b is listed first', (t) => {
  if (!lakeAvailable()) { t.skip(NO_LAKE); return; }
  const m = orderModel();
  assert.equal(claimOf(proveScenario(m, 'order-ab'), 'ab-b-stays-zero')?.result, 'holds');
  assert.equal(claimOf(proveScenario(m, 'order-ba'), 'ba-b-stays-zero')?.result, 'holds');
});

test('(b) the blinker, whose runs never end, is incomplete for eventually and for its invariant, never holds', (t) => {
  if (!lakeAvailable()) { t.skip(NO_LAKE); return; }
  const out = proveScenario(orderModel(), 'blink');
  assert.equal(claimOf(out, 'blinker-turns-on')?.result, 'incomplete');
  assert.equal(claimOf(out, 'blinker-two-states')?.result, 'incomplete');
});

test('(c) a guard dividing by zero gives a counterexample that ends in the error state', (t) => {
  if (!lakeAvailable()) { t.skip(NO_LAKE); return; }
  const c = claimOf(proveScenario(orderModel(), 'divide', { withSteps: true }), 'divider-runs');
  assert.equal(c?.result, 'counterexample');
  const last = c.counterexample.steps.at(-1);
  assert.match(last.error?.message ?? '', /Division by zero/);
  assert.match(c.explanation, /error state/);
});

test('(d) "for every reachable configuration" is said only of a holds result', (t) => {
  if (!lakeAvailable()) { t.skip(NO_LAKE); return; }
  const m = orderModel();
  const results = [...proveScenario(m, 'order-ab').claims, ...proveScenario(m, 'blink').claims, ...proveScenario(m, 'divide').claims];
  for (const c of results) {
    assert.equal(/for every reachable configuration/.test(c.explanation), c.result === 'holds', `${c.claimId}: ${c.result}`);
  }
});

test('(e) a draw with more outcomes than the explorer tries makes the result incomplete', (t) => {
  if (!lakeAvailable()) { t.skip(NO_LAKE); return; }
  const c = claimOf(proveScenario(orderModel(), 'big-draw'), 'drawer-safe');
  assert.equal(c?.result, 'incomplete');
});

test('an out-of-fragment scenario is not covered', (t) => {
  if (!lakeAvailable()) { t.skip(NO_LAKE); return; }
  const text = fs.readFileSync(path.join(HERE, '..', 'fixtures', 'behaviour-order', 'workload.jsonc'), 'utf8');
  const project = new Project({ name: 'behaviour-workload', specText: text, layoutText: null });
  assert.ok(project.model, 'the fixture parses');
  assert.throws(() => proveScenario(project.model, 'driven'), /not covered by the calculus/);
});

test('a scenario that sends over a link is explored to a verdict', (t) => {
  if (!lakeAvailable()) { t.skip(NO_LAKE); return; }
  const text = fs.readFileSync(path.join(HERE, '..', 'fixtures', 'behaviour-order', 'linked.jsonc'), 'utf8');
  const project = new Project({ name: 'behaviour-linked', specText: text, layoutText: null });
  assert.ok(project.model, 'the fixture parses');
  assert.equal(claimOf(proveScenario(project.model, 'linked'), 'sender-stays')?.result, 'holds');
});

test('a variable set from a draw is explored over every outcome', (t) => {
  if (!lakeAvailable()) { t.skip(NO_LAKE); return; }
  const c = claimOf(proveScenario(orderModel(), 'sampled'), 'sampler-small');
  assert.equal(c?.result, 'holds');
});

// WG-5682: model checking on the behaviour calculus (tests/fixtures/liveness).
const LIVE = path.join(HERE, '..', 'fixtures', 'liveness', 'spec.jsonc');

function liveModel() {
  const project = new Project({ name: 'liveness', specText: fs.readFileSync(LIVE, 'utf8'), layoutText: null });
  assert.ok(project.model, 'the fixture parses');
  return project.model;
}

// The invariant of the eight-client scenario holds with 256 states and no faults.
// @evidence explorer-counts-calculus-states
test('eight independent clients explore exactly 256 states', (t) => {
  if (!lakeAvailable()) { t.skip(NO_LAKE); return; }
  const out = proveScenario(liveModel(), 'eight-clients');
  assert.deepEqual(out.faults, [], 'explored with no faults');
  const c = claimOf(out, 'clients-in-their-states');
  assert.equal(c?.result, 'holds');
  assert.equal(c.states, 256, 'the reachable configurations are the 2^8 subsets of delivered entries');
});

// The counter's invariant is incomplete with reason bound and is not described as holding for every reachable configuration.
// @evidence explorer-incomplete-says-why
test('a counter to 100 with an invariant at 50 and bound 20 is incomplete for its bound and never holds', (t) => {
  if (!lakeAvailable()) { t.skip(NO_LAKE); return; }
  const c = claimOf(proveScenario(liveModel(), 'count-to-100', { bound: 20 }), 'counter-at-most-50');
  assert.equal(c?.result, 'incomplete');
  assert.equal(c.reason, 'bound');
  assert.doesNotMatch(c.explanation, /for every reachable configuration/);
});

// The certificate of b.y == 0 is accepted; with its first state removed, Lean refuses the file.
// @evidence prove-invariants-certified
test('a holds result carries a closed-set certificate Lean accepts and Lean refuses it without one of its states', (t) => {
  if (!lakeAvailable()) { t.skip(NO_LAKE); return; }
  // The F4 fixture of the foundations (machines a and b on one event, tests/fixtures/behaviour-order).
  const c = claimOf(proveScenario(orderModel(), 'order-ab'), 'ab-b-stays-zero');
  assert.equal(c?.result, 'holds');
  assert.ok(c.certificate, 'the result names its certificate');
  assert.match(c.certificate.theorem, /ab-b-stays-zero-invariant/);
  const file = path.join(FORMAL, c.file.replace(/^formal\//, ''));
  const text = fs.readFileSync(file, 'utf8');
  assert.match(text, /theorem «ab-b-stays-zero-certificate» : checkClosed \(Core\.Behav\.Exec\.enum orderAbSys\) visited \(V2\.ProveLive\.invP inputText "b\.y == 0"\) = true/);
  assert.match(text, /checkClosed_sound \(Core\.Behav\.Exec\.enum orderAbSys\) visited _ «ab-b-stays-zero-certificate»/);
  // Remove the first state of `visited` (the initial state) and check the altered file.
  const lines = text.split('\n');
  const at = lines.indexOf('def visited : List Core.Behav.State := [');
  assert.ok(at >= 0 && lines[at + 1].startsWith('  Core.Behav.State.'), 'one state per line');
  assert.ok(lines[at + 2].startsWith('  Core.Behav.State.'), 'the certificate has more than one state');
  lines.splice(at + 1, 1);
  const altered = path.join(path.dirname(file), 'order-ab-altered.lean');
  fs.writeFileSync(altered, lines.join('\n'), 'utf8');
  try {
    const check = spawnSync('lake', ['env', 'lean', ...nativeLibOptions(), path.relative(FORMAL, altered)], { cwd: FORMAL, encoding: 'utf8', windowsHide: true, maxBuffer: 1 << 28 });
    assert.notEqual(check.status, 0, 'Lean refuses the certificate without one of its states');
    assert.match(`${check.stdout}${check.stderr}`, /ab-b-stays-zero-certificate|native_decide/);
  } finally {
    fs.rmSync(altered, { force: true });
  }
});

// The FG claim reads violated: lasso off -> on -> off; the GF claim reads holds under weak fairness of turn-on, with turn-on-fair as its open assumption.
// @evidence prove-liveness-under-fairness
test('the F4 blinker: FG on is violated by a lasso and GF on holds under weak fairness of turn-on', (t) => {
  if (!lakeAvailable()) { t.skip(NO_LAKE); return; }
  const out = proveScenario(liveModel(), 'blink-f4');
  const fg = claimOf(out, 'blinker-fg-on');
  assert.equal(fg?.result, 'violated');
  assert.match(fg.verdictText, /^violated: lasso off → on → off/);
  const gf = claimOf(out, 'blinker-gf-on');
  assert.equal(gf?.result, 'proved');
  assert.equal(gf.verdictText, 'holds under weak fairness of turn-on');
  assert.deepEqual(gf.openAssumptions, ['turn-on-fair'], 'the fairness assumption is cited');
});

// The waiter's GF claim is violated by a lasso flagged zeno, never proved.
// @evidence prove-zeno-lasso-not-proved
test('a zero-delay self-loop gives a Zeno lasso and its liveness claims are not proved', (t) => {
  if (!lakeAvailable()) { t.skip(NO_LAKE); return; }
  const c = claimOf(proveScenario(liveModel(), 'zeno'), 'waiter-finishes-often');
  assert.notEqual(c?.result, 'proved');
  assert.equal(c.result, 'violated');
  assert.equal(c.lasso.zeno, true, 'the lasso does not advance time');
  assert.match(c.verdictText, /Zeno lasso/);
});

test('a pool acquire is explored to a verdict whose closed-set certificate, world included, Lean accepts', (t) => {
  if (!lakeAvailable()) { t.skip(NO_LAKE); return; }
  // WG-5683: the certificate's states carry the world (resource states, request ids, acting faults)
  // and the entries' kinds; one that dropped them named states the calculus never reaches, and
  // Lean refused it.
  const text = fs.readFileSync(path.join(HERE, '..', 'fixtures', 'behaviour-order', 'pool-acquire.jsonc'), 'utf8');
  const project = new Project({ name: 'behaviour-pool', specText: text, layoutText: null });
  assert.ok(project.model, 'the fixture parses');
  const out = proveScenario(project.model, 'pool-acquire', { module: true });
  // The kernel-only module is not written: `decide` does not reduce settling in the kernel.
  assert.equal(out.module?.written, false);
  assert.match(out.module.note, /resources/);
  const c = claimOf(out, 'pool-one-holder');
  assert.equal(c?.result, 'holds');
  assert.ok(c.certificate, 'the result names its certificate');
  const file = path.join(FORMAL, c.file.replace(/^formal\//, ''));
  assert.match(fs.readFileSync(file, 'utf8'), /world := \{ res := \[\{ capacity := 1, holds := \[\{ owner := /);
});
