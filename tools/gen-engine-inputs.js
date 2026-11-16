#!/usr/bin/env node
// Seeded generator of random valid engine inputs (format exegra-sim-input, version 1), for differential
// checking of the Rust engine against the Lean formal semantics (tools/differential.js). Node-only when
// run as a command; the generator itself is pure.
//
//   node tools/gen-engine-inputs.js [--v2] [--seed <n>] [--count <n>] [--out <dir>]
//
// With --v2, version-2 inputs for the WG-4664 constructs (generateInputV2).
//
// Prints the construct coverage of the generated inputs; with --out, writes each input as
// <dir>/input-<seed>-<i>.json.
//
// "Valid" means the engine accepts the input (no creation refusal): ids are distinct across events,
// behaviors, faults and the scenario, every step and injected event is an event, every active fault
// exists. Inside that, every construct of the language is generated, including the ones a validated
// model cannot contain (an effect without "to", a set of a name that is not a variable, an emit of a
// name that is not an event, a malformed effect, an expression that does not parse) and expressions that
// fail at run time (type errors, division and modulo by zero, unknown references, a guard that is not a
// boolean). Sizes are bounded so runs stay small: at most 4 behaviors of at most 4 states and 6
// transitions, at most 6 input steps, step limits mostly below 40.

import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

/**
 * mulberry32: a small deterministic generator of floats in [0, 1).
 * @param {number} seed
 */
export function createRng(seed) {
  let a = seed >>> 0;
  const next = () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
  return {
    next,
    /** @param {number} n integer in [0, n) */
    int: (n) => Math.floor(next() * n),
    /** @param {number} p */
    chance: (p) => next() < p,
    /** @template T @param {T[]} xs @returns {T} */
    pick: (xs) => xs[Math.floor(next() * xs.length)],
  };
}

/** @typedef {ReturnType<typeof createRng>} Rng */
/** @typedef {Record<string, number>} Coverage */

/** @param {Coverage} cov @param {string} key @param {number} [by] */
const count = (cov, key, by = 1) => { cov[key] = (cov[key] ?? 0) + by; };

/** Number literals as they may appear in expressions (no sign, no exponent). */
const NUM_LITERALS = ['0', '1', '2', '3', '5', '7', '10', '100', '0.5', '0.1', '0.2', '2.25', '1.75', '2.50', '007', '123456789012'];
/** JSON numbers for payloads, variables and literals. */
const JSON_NUMBERS = [0, 1, 2, 3, 4, 7, 10, 42, 100, 150, -3, 0.5, 0.1, 2.25, -1.5, 1e-7, 123456.5, 1e21, 9007199254740993];
const STRINGS = ['a', 'ab', 'x y', '', 'open', 'é', 'big', 'small'];
const JSON_STRINGS = ['a', 'ab', 'x y', '', 'say "hi"', 'tab\there', 'é ü', 'line\nbreak', 'back\\slash'];
const PAYLOAD_FIELDS = ['amount', 'label', 'flag', 'obj', 'n'];
const MALFORMED_EXPRESSIONS = ['a +', '(a', 'a b', "'abc", 'a = b', '1 2.50', 'x.', ')', '', 'a # b', 'event.', '1 +* 2', '!', '(1 + 2'];

/**
 * A random JSON value of bounded depth.
 * @param {Rng} r @param {number} depth
 * @returns {any}
 */
function jsonValue(r, depth = 0) {
  const k = r.int(depth > 1 ? 4 : 7);
  if (k === 0) return r.pick(JSON_NUMBERS);
  if (k === 1) return r.pick(JSON_STRINGS);
  if (k === 2) return r.chance(0.5);
  if (k === 3) return null;
  if (k === 4) return Array.from({ length: r.int(3) }, () => jsonValue(r, depth + 1));
  /** @type {Record<string, any>} */
  const o = {};
  for (let i = r.int(3); i > 0; i--) o[r.pick(['b', 'a', '1', '0', 'k', '10'])] = jsonValue(r, depth + 1);
  return o;
}

/**
 * A payload object for an input step or an injected event.
 * @param {Rng} r @param {Coverage} cov
 */
function payloadObject(r, cov) {
  /** @type {Record<string, any>} */
  const p = {};
  if (r.chance(0.6)) p.amount = r.pick([0, 50, 99, 100, 150, 500, 2.5, -1]);
  if (r.chance(0.4)) p.label = r.pick(STRINGS);
  if (r.chance(0.3)) p.flag = r.chance(0.5);
  if (r.chance(0.15)) { p.obj = jsonValue(r, 1); count(cov, 'payload.compound'); }
  if (r.chance(0.1)) { p.n = null; count(cov, 'payload.null'); }
  return p;
}

/**
 * The expression generator for one transition's scope.
 * @param {Rng} r @param {Coverage} cov
 * @param {{ownVars: string[], others: {id: string, vars: string[]}[], fields: string[]}} scope
 */
function expressionGenerator(r, cov, scope) {
  /** @param {string} op */
  const op = (op) => count(cov, `expr.op ${op}`);
  /** A reference, mostly to something that exists. */
  const ref = () => {
    const k = r.int(10);
    if (k <= 2 && scope.ownVars.length) { count(cov, 'expr.ref own variable'); return r.pick(scope.ownVars); }
    if (k === 3) { count(cov, 'expr.ref time'); return 'time'; }
    if (k <= 5) { count(cov, 'expr.ref event field'); return `event.${r.pick(scope.fields)}`; }
    if (k <= 7 && scope.others.length) {
      const b = r.pick(scope.others);
      if (r.chance(0.4) || !b.vars.length) { count(cov, 'expr.ref machine state'); return `${b.id}.state`; }
      count(cov, 'expr.ref machine variable');
      return `${b.id}.${r.pick(b.vars)}`;
    }
    if (k === 8) { count(cov, 'expr.ref unknown'); return r.pick(['missing', 'event.nope', 'a.b.c', 'bh-9.state', 'nobody.x']); }
    count(cov, 'expr.ref own variable');
    return scope.ownVars.length ? r.pick(scope.ownVars) : 'time';
  };
  /** @param {number} depth @returns {string} */
  const num = (depth) => {
    const k = r.int(depth > 2 ? 3 : 9);
    if (k === 0) { count(cov, 'expr.literal number'); return r.pick(NUM_LITERALS); }
    if (k === 1) return ref();
    if (k === 2) { count(cov, 'expr.literal number'); return r.pick(['1', '2', '10']); }
    if (k === 3) { op('unary -'); return `-${num(depth + 1)}`; }
    if (k === 4) { op('()'); return `(${num(depth + 1)})`; }
    const o = r.pick(['+', '-', '*', '/', '%', '+', '-', '*']);
    op(o);
    // Division and modulo by zero now and then.
    const rhs = (o === '/' || o === '%') && r.chance(0.25) ? (count(cov, 'expr.zero divisor'), r.pick(['0', '(1 - 1)', '-0'])) : num(depth + 1);
    return `${num(depth + 1)} ${o} ${rhs}`;
  };
  /** @param {number} depth @returns {string} */
  const str = (depth) => {
    const k = r.int(depth > 2 ? 2 : 4);
    if (k === 0) { count(cov, 'expr.literal string'); const s = r.pick(STRINGS); return r.chance(0.5) ? `'${s}'` : `"${s}"`; }
    if (k === 1) return ref();
    op('+ strings');
    return `${str(depth + 1)} + ${str(depth + 1)}`;
  };
  /** @param {number} depth @returns {string} */
  const bool = (depth) => {
    const k = r.int(depth > 2 ? 4 : 12);
    if (k === 0) { count(cov, 'expr.literal boolean'); return r.pick(['true', 'false']); }
    if (k === 1) return ref();
    if (k <= 3) {
      const o = r.pick(['<', '<=', '>', '>=']);
      op(o);
      return `${num(depth + 1)} ${o} ${num(depth + 1)}`;
    }
    if (k === 4) { op('!'); return `!${r.chance(0.5) ? `(${bool(depth + 1)})` : bool(depth + 1)}`; }
    if (k <= 6) {
      const o = r.pick(['==', '!=']);
      op(o);
      const side = () => r.pick([num, str, bool, any])(depth + 1);
      return `${side()} ${o} ${side()}`;
    }
    if (k === 7) { op('()'); return `(${bool(depth + 1)})`; }
    const o = r.pick(['&&', '||', '=>']);
    op(o);
    // Short-circuiting over a right side that would fail.
    if (r.chance(0.2)) {
      count(cov, 'expr.short-circuit over error');
      const bad = r.pick(['1 / 0 > 1', 'missing', '5', "'x'", 'event.nope == 1']);
      return `${o === '||' ? 'true' : 'false'} ${o} ${bad}`;
    }
    return `${bool(depth + 1)} ${o} ${bool(depth + 1)}`;
  };
  /** Anything, including null and ill-typed mixtures. @param {number} depth @returns {string} */
  const any = (depth) => {
    const k = r.int(8);
    if (k === 0) { count(cov, 'expr.literal null'); return 'null'; }
    if (k === 1) return ref();
    if (k === 2) {
      // A deliberate type error.
      count(cov, 'expr.type mixture');
      const o = r.pick(['+', '-', '<', '&&', '*']);
      op(o);
      return `${r.pick([str, bool, num])(depth + 1)} ${o} ${r.pick([str, bool, num])(depth + 1)}`;
    }
    return r.pick([num, str, bool])(depth + 1);
  };
  return {
    /** A guard: usually boolean, sometimes not (a guard that is not a boolean), rarely unparseable. */
    guard() {
      if (r.chance(0.03)) { count(cov, 'expr.parse error'); return r.pick(MALFORMED_EXPRESSIONS); }
      if (r.chance(0.04)) { count(cov, 'guard.not boolean candidate'); return any(1); }
      return bool(0);
    },
    /** An effect value expression of any type. */
    value() {
      if (r.chance(0.02)) { count(cov, 'expr.parse error'); return r.pick(MALFORMED_EXPRESSIONS); }
      return r.pick([num, num, str, bool, any])(0);
    },
  };
}

/**
 * Generate one engine input.
 * @param {Rng} r
 * @param {Coverage} [cov] construct counts, added to
 * @returns {any}
 */
export function generateInput(r, cov = {}) {
  count(cov, 'inputs');
  const eventIds = Array.from({ length: 2 + r.int(4) }, (_, i) => `ev-${String.fromCharCode(97 + i)}`);
  // Events declared but never delivered, and names that are not events (emitted: a run-time error).
  const notEvents = ['ev-ghost'];

  const nBehaviors = 1 + r.int(4);
  /** @type {{id: string, states: string[], vars: string[]}[]} */
  const shapes = [];
  for (let b = 0; b < nBehaviors; b++) {
    const states = Array.from({ length: 2 + r.int(3) }, (_, i) => `b${b}-s${i}`);
    const nVars = r.int(5);
    const names = ['x', 'y', 'n', 'label', 'flag', 'obj', 'time', 'state'];
    /** @type {string[]} */
    const vars = [];
    for (let v = 0; v < nVars; v++) {
      const name = r.pick(names);
      if (!vars.includes(name)) vars.push(name);
    }
    shapes.push({ id: `bh-${b}`, states, vars });
  }

  /** @type {string[]} */
  const transitionIds = [];
  const behaviors = shapes.map((shape, b) => {
    count(cov, 'behaviors');
    count(cov, 'states', shape.states.length);
    const others = shapes.filter((s) => s.id !== shape.id).map((s) => ({ id: s.id, vars: s.vars }));
    const gen = expressionGenerator(r, cov, { ownVars: shape.vars, others, fields: PAYLOAD_FIELDS });
    const variables = shape.vars.map((name) => {
      count(cov, 'variables');
      /** @type {any} */
      const v = { name };
      const k = r.int(10);
      if (k === 0) { count(cov, 'variable without initial'); return v; }
      if (k <= 4) v.initial = r.pick([0, 1, 2, 5, 10, 0.5]);
      else if (k === 5) v.initial = r.pick(STRINGS);
      else if (k === 6) v.initial = r.chance(0.5);
      else if (k === 7) v.initial = null;
      else { v.initial = jsonValue(r, 1); count(cov, 'variable compound initial'); }
      return v;
    });
    const nTransitions = 1 + r.int(6);
    const transitions = [];
    for (let t = 0; t < nTransitions; t++) {
      count(cov, 'transitions');
      const id = `t${b}-${t}`;
      transitionIds.push(id);
      /** @type {any[]} */
      const effects = [];
      for (let e = r.int(4); e > 0; e--) {
        let k = r.int(40);
        // A behavior without variables mostly emits; a set of a name that is not a variable stays rare.
        if (k <= 19 && !shape.vars.length && !r.chance(0.1)) k = 20;
        if (k <= 19) {
          const variable = shape.vars.length && !r.chance(0.03) ? r.pick(shape.vars) : (count(cov, 'effect.set not a variable'), 'nope');
          if (r.chance(0.03)) { count(cov, 'effect.set without to'); effects.push({ set: variable }); continue; }
          const lit = r.int(10);
          if (lit === 0) { count(cov, 'effect.set literal'); effects.push({ set: variable, to: jsonValue(r, 1) }); }
          else if (lit === 1) { count(cov, 'effect.set literal compound'); effects.push({ set: variable, to: r.chance(0.5) ? { k: [1, 'x'], a: 'event.amount' } : [1, { b: 2 }] }); }
          else { count(cov, 'effect.set expression'); effects.push({ set: variable, to: gen.value() }); }
        } else if (k <= 36) {
          count(cov, 'effect.emit');
          const event = r.chance(0.04) ? (count(cov, 'effect.emit not an event'), r.pick(notEvents)) : r.pick(eventIds);
          /** @type {any} */
          const fx = { emit: event };
          const a = r.int(6);
          if (a === 0) count(cov, 'effect.emit after absent');
          else if (a === 1) { fx.after = 0; count(cov, 'effect.emit after 0'); }
          else if (a === 2) { fx.after = null; count(cov, 'effect.emit after null'); }
          else if (a === 3) { fx.after = r.pick([0.5, 1.25]); count(cov, 'effect.emit after fractional'); }
          else { fx.after = 1 + r.int(4); count(cov, 'effect.emit after positive'); }
          if (r.chance(0.7)) {
            /** @type {Record<string, any>} */
            const payload = {};
            for (let p = r.int(4); p > 0; p--) {
              const key = r.pick(['amount', 'label', 'flag', 'obj', '1', '0', 'n']);
              const lk = r.int(6);
              if (lk === 0) { payload[key] = jsonValue(r, 1); count(cov, 'effect.emit payload literal'); }
              else { payload[key] = gen.value(); count(cov, 'effect.emit payload expression'); }
            }
            if (Object.keys(payload).some((x) => /^\d+$/.test(x))) count(cov, 'effect.emit payload index keys');
            fx.payload = payload;
          } else if (r.chance(0.3)) { fx.payload = null; count(cov, 'effect.emit payload null'); }
          effects.push(fx);
        } else if (k === 37) {
          count(cov, 'effect.malformed');
          effects.push(r.pick([{}, { other: 1 }, 'set', null, 3]));
        } else {
          // `set` of an own variable from another machine's state or an identity comparison.
          count(cov, 'effect.set expression');
          if (shape.vars.length) {
            const v = r.pick(shape.vars);
            const w = r.pick(shape.vars);
            count(cov, 'expr.identity comparison');
            effects.push({ set: r.pick(shape.vars), to: r.pick([`${v} == ${w}`, `${v} != ${v}`, 'event.obj == event.obj', `event.obj == ${v}`]) });
          }
        }
      }
      /** @type {any} */
      const tr = { id, from: r.pick(shape.states), to: r.pick(shape.states), on: r.pick(eventIds), effects };
      const gk = r.int(10);
      if (gk <= 2) { tr.guard = null; count(cov, 'guard absent'); }
      else if (gk === 3) { count(cov, 'guard omitted'); }
      else { tr.guard = gen.guard(); count(cov, 'guard expression'); }
      const fo = r.int(10);
      if (fo === 0) { tr.faultOnly = true; count(cov, 'transition faultOnly'); } else tr.faultOnly = false;
      transitions.push(tr);
    }
    /** @type {any} */
    const out = { id: shape.id, initial: shape.states[0], states: shape.states, variables, transitions };
    if (r.chance(0.8)) out.subject = r.pick(['comp-a', 'comp-b', shape.id === 'bh-0' ? 'ev-a' : 'comp-c']);
    return out;
  });

  // Faults.
  /** @type {any[]} */
  const faults = [];
  for (let f = r.int(5); f > 0; f--) {
    const id = `f-${faults.length}`;
    const kind = r.pick(['drop-event', 'delay-event', 'enable-transition', 'disable-transition', 'inject-event']);
    /** @type {any} */
    const fault = { id, kind };
    if (kind === 'drop-event' || kind === 'delay-event') {
      fault.event = r.pick(eventIds);
      const o = r.int(5);
      if (o <= 1) { fault.occurrence = 1 + r.int(3); count(cov, 'fault occurrence'); }
      else if (o === 2) { fault.occurrence = null; count(cov, 'fault occurrence null'); }
      if (kind === 'delay-event') fault.by = r.pick([1, 2, 3, 0, 0.5, 5]);
    } else if (kind === 'inject-event') {
      fault.event = r.pick(eventIds);
      fault.at = r.pick([0, 1, 2, 3, 7, 1.5]);
      if (r.chance(0.6)) fault.payload = payloadObject(r, cov);
    } else {
      fault.transition = transitionIds.length && r.chance(0.9) ? r.pick(transitionIds) : 't-none';
    }
    faults.push(fault);
  }
  const active = faults.filter(() => r.chance(0.8)).map((f) => f.id);
  if (active.length && r.chance(0.15)) { active.push(active[0]); count(cov, 'scenario.faults repeated'); }

  // Input steps: some simultaneous, listed out of time order.
  const steps = [];
  /** @type {number[]} */
  const times = [];
  for (let s = 1 + r.int(6); s > 0; s--) {
    const at = r.chance(0.3) && times.length ? r.pick(times) : r.pick([0, 1, 2, 3, 4, 5, 8, 0.5]);
    times.push(at);
    /** @type {any} */
    const st = { at, event: r.pick(eventIds) };
    const pk = r.int(5);
    if (pk <= 2) st.payload = payloadObject(r, cov);
    else if (pk === 3) st.payload = {};
    steps.push(st);
  }
  count(cov, 'input steps', steps.length);
  if (new Set(times).size < times.length) count(cov, 'steps simultaneous');
  if (times.some((t, i) => i > 0 && t < times[i - 1])) count(cov, 'steps out of time order');

  const activeFaults = faults.filter((f) => active.includes(f.id));
  for (const f of activeFaults) count(cov, `fault ${f.kind}`);

  /** @type {any} */
  const scenario = { id: 'scenario-gen', steps, faults: active };
  const lk = r.int(12);
  // The default limit (1000) only where nothing emits, so the queue cannot grow with every step.
  const emits = behaviors.some((b) => b.transitions.some((/** @type {any} */ t) => t.effects.some((/** @type {any} */ fx) => fx && typeof fx === 'object' && 'emit' in fx)));
  if (lk === 0 && !emits) count(cov, 'stepLimit absent (1000)');
  else if (lk === 0) { scenario.stepLimit = 40; count(cov, 'stepLimit small'); }
  else if (lk === 1) { scenario.stepLimit = r.pick([0, -1, 1]); count(cov, 'stepLimit at most 1'); }
  else if (lk === 2) { scenario.stepLimit = r.pick([2.5, 3.2]); count(cov, 'stepLimit fractional'); }
  else { scenario.stepLimit = 2 + r.int(38); count(cov, 'stepLimit small'); }
  if (!active.length && r.chance(0.5)) delete scenario.faults;

  return {
    format: 'exegra-sim-input',
    version: 1,
    scenario,
    behaviors,
    events: [...eventIds, 'ev-unused'].map((id) => ({ id })),
    faults: activeFaults,
  };
}

/** An integer time from a generated (possibly fractional or negative) one. @param {any} x */
const intTime = (x) => (typeof x === 'number' ? Math.max(0, Math.ceil(x)) : x);

/**
 * A random integer distribution (format 2).
 * @param {Rng} r @param {Coverage} cov @param {string} what
 */
function distribution(r, cov, what) {
  const k = r.int(6);
  if (k === 0) { count(cov, `${what} integer`); return r.int(6); }
  if (k === 1) { count(cov, `${what} fixed`); return { kind: 'fixed', value: r.int(6) }; }
  if (k <= 3) { const lo = r.int(4); count(cov, `${what} uniform`); return { kind: 'uniform', lo, hi: lo + r.int(8) }; }
  if (k === 4) { count(cov, `${what} table`); return { kind: 'table', points: [[0, 1], [2 ** 31, 3 + r.int(4)], [2 ** 32, 10 + r.int(20)]] }; }
  count(cov, `${what} choice`);
  return { kind: 'choice', values: Array.from({ length: 1 + r.int(3) }, () => r.int(9)) };
}

/**
 * Generate one version-2 engine input covering the WG-4664 constructs: integer time in a unit,
 * counted and keyed instances with routes, aggregates, resources with classes, bounds, overflow and
 * demand factors, use, acquire and release, sampled delays, demands and sets, replies, targeted steps
 * and seeds. It starts from a version-1 input of generateInput, with its times made integers.
 * @param {Rng} r
 * @param {Coverage} [cov]
 * @returns {any}
 */
export function generateInputV2(r, cov = {}) {
  // Hyphen-free behavior and state ids, so aggregates such as `bh0.count.b0s1` parse.
  const input = JSON.parse(JSON.stringify(generateInput(r, cov)).replace(/bh-(\d)/g, 'bh$1').replace(/b(\d)-s(\d)/g, 'b$1s$2'));
  count(cov, 'v2 inputs');
  input.version = 2;
  input.time = r.pick([{ unit: 'tick', perSecond: null }, { unit: 'us', perSecond: 1000000 }, { unit: 'ms', perSecond: 1000 }]);
  const sc = input.scenario;
  for (const st of sc.steps) st.at = intTime(st.at);
  for (const f of input.faults) {
    if ('by' in f) f.by = intTime(f.by);
    if ('at' in f) f.at = intTime(f.at);
    if (f.kind === 'inject-event' && r.chance(0.9)) f.payload = { ...(f.payload ?? {}), label: 'a' };
  }
  if (typeof sc.stepLimit === 'number') sc.stepLimit = Math.max(1, Math.ceil(sc.stepLimit));
  const k = r.int(10);
  if (k < 9) { sc.seed = r.pick(['42', '0', '1234567', '18446744073709551615']); count(cov, 'v2 seed'); }
  else if (r.chance(0.3)) { sc.seed = r.pick(['042', '-1', 'x', '18446744073709551616']); count(cov, 'v2 seed malformed'); }
  else count(cov, 'v2 no seed');

  const eventIds = input.events.map((/** @type {any} */ e) => e.id).filter((/** @type {string} */ e) => e !== 'ev-unused');
  // Resources.
  /** @type {any[]} */
  const resources = [];
  for (let i = r.chance(0.85) ? 1 + r.int(2) : 0; i > 0; i--) {
    const id = `res${resources.length}`;
    const nClasses = 1 + r.int(2);
    const capacity = 1 + r.int(3);
    const classes = Array.from({ length: nClasses }, (_, c) => {
      /** @type {any} */
      const cl = { id: `c${c}`, priority: r.int(3) - 1, reserved: 0, limit: null, queueBound: null, maxWait: null };
      if (nClasses > 1 && c === 0 && capacity > 1 && r.chance(0.5)) { cl.reserved = 1; count(cov, 'v2 class reserved'); }
      if (r.chance(0.3)) { cl.limit = 1 + r.int(2); count(cov, 'v2 class limit'); }
      if (r.chance(0.4)) { cl.queueBound = r.int(3); count(cov, 'v2 class queueBound'); }
      if (r.chance(0.3)) { cl.maxWait = 1 + r.int(5); count(cov, 'v2 class maxWait'); }
      return cl;
    });
    const df = r.int(6);
    /** @type {any} */
    const demandFactor = df === 0 ? [[0, 1, 1], [2, 3, 2]] : df === 1 ? { usl: { alpha: [1, 10], beta: [1, 100] } } : null;
    if (demandFactor) count(cov, `v2 demandFactor ${Array.isArray(demandFactor) ? 'table' : 'usl'}`);
    const res = {
      id, kind: r.pick(['cpu', 'io', 'pool', 'connection', 'threads']), capacity,
      discipline: r.pick(['fifo', 'priority']), queueBound: r.chance(0.4) ? r.int(4) : null,
      overflow: r.pick(['refuse', 'drop', 'shed-oldest']), demandFactor, classes,
    };
    count(cov, `v2 resource ${res.discipline} ${res.overflow}`);
    resources.push(res);
  }
  if (resources.length) input.resources = resources;

  // Instances and routes.
  /** @type {any[]} */
  const routes = [];
  for (const b of input.behaviors) {
    const ik = r.int(6);
    if (ik <= 1) { b.instances = { count: 1 + r.int(3) }; count(cov, 'v2 instances counted'); }
    else if (ik === 2) { b.instances = { key: 'label', max: 1 + r.int(4) }; count(cov, 'v2 instances keyed'); }
    for (const ev of eventIds) {
      if (b.instances?.key) {
        if (r.chance(0.7)) { routes.push({ event: ev, behavior: b.id, by: 'key', field: 'label' }); count(cov, 'v2 route key keyed'); }
        continue;
      }
      if (!r.chance(0.3)) continue;
      const by = r.pick(['key', 'round-robin', 'random', 'any', 'least-busy']);
      /** @type {any} */
      const route = { event: ev, behavior: b.id, by };
      if (by === 'key') route.field = 'label';
      if (by === 'least-busy') { if (!resources.length) continue; route.resource = r.pick(resources).id; }
      routes.push(route);
      count(cov, `v2 route ${by}`);
    }
  }
  if (routes.length) input.routes = routes;
  // Keyed behaviors receive labels: give steps one more often.
  for (const st of sc.steps) {
    if (r.chance(0.97)) st.payload = { ...(st.payload ?? {}), label: r.pick(['a', 'b', 'c', 1]) };
    if (r.chance(0.1)) {
      const b = r.pick(input.behaviors);
      st.target = { behavior: b.id, instance: b.instances?.key ? r.pick(['a', 'b']) : 0 };
      count(cov, 'v2 step target');
    }
  }

  // Effects and expressions. The version-1 generator's run-time errors are thinned out, so that
  // runs reach the resource constructs.
  for (const b of input.behaviors) {
    for (const t of b.transitions) {
      if (r.chance(0.6)) delete t.guard;
      t.effects = t.effects.filter((/** @type {any} */ fx) => (fx && typeof fx === 'object' && ('set' in fx || 'emit' in fx)) || r.chance(0.1));
      const site = (/** @type {string} */ what) => count(cov, `v2 ${what}`);
      for (const fx of t.effects) {
        if (fx && typeof fx === 'object' && 'emit' in fx) {
          if (typeof fx.after === 'number') fx.after = intTime(fx.after);
          if (r.chance(0.3)) fx.after = distribution(r, cov, 'v2 emit after');
          if (r.chance(0.1)) { fx.target = 'reply'; site('emit reply'); }
          if (r.chance(0.95)) fx.payload = { ...(fx.payload && typeof fx.payload === 'object' ? fx.payload : {}), label: { a: 'a', b: 'b' }[r.pick(['a', 'b'])] };
        }
        if (fx && typeof fx === 'object' && 'set' in fx && typeof fx.to === 'string' && r.chance(0.6)) fx.to = r.pick(['time', '1', 'instance']);
        if (fx && typeof fx === 'object' && 'set' in fx && r.chance(0.1)) fx.to = { sample: distribution(r, cov, 'v2 set sample') };
        if (fx && typeof fx === 'object' && 'emit' in fx && fx.payload && typeof fx.payload === 'object') {
          for (const key of Object.keys(fx.payload)) if (typeof fx.payload[key] === 'string' && r.chance(0.6)) fx.payload[key] = r.pick([1, 'time', 'x']);
        }
      }
      if (resources.length) {
        for (let e = r.chance(0.7) ? 1 + r.int(2) : 0; e > 0; e--) {
          const res = r.pick(resources);
          const cls = res.classes.length > 1 || r.chance(0.5) ? r.pick(res.classes).id : undefined;
          const kk = r.int(3);
          /** @type {any} */
          let fx;
          if (kk === 0) { fx = { use: res.id, demand: distribution(r, cov, 'v2 use demand'), then: r.pick(eventIds) }; site('effect use'); }
          else if (kk === 1) { fx = { acquire: res.id, then: r.pick(eventIds) }; site('effect acquire'); }
          else { fx = { release: res.id }; site('effect release'); }
          if (cls !== undefined) fx.class = cls;
          if (r.chance(0.3)) {
            const ci = cls === undefined ? 0 : res.classes.findIndex((/** @type {any} */ c) => c.id === cls);
            const others = res.classes.reduce((/** @type {number} */ a, /** @type {any} */ c, /** @type {number} */ j) => a + (j === ci ? 0 : c.reserved), 0);
            const most = Math.min(res.classes[ci].limit ?? res.capacity, res.capacity - others);
            fx.units = r.chance(0.05) ? most + 1 : 1 + r.int(Math.max(1, most));
          }
          if (kk < 2 && r.chance(0.6)) fx.refused = r.pick(eventIds);
          if (kk < 2 && r.chance(0.5)) fx.payload = { amount: 'event.amount', tag: r.pick(STRINGS) };
          t.effects.splice(r.int(t.effects.length + 1), 0, fx);
        }
      }
      if (r.chance(0.25)) {
        const other = r.pick(input.behaviors);
        const g = r.pick([
          `${other.id}.count.${other.initial} >= 0`, `${other.id}.instances.count > 0`, 'instance == 0',
          `${other.id}.sum.x >= 0`, `${other.id}.max.n == null`, `${other.id}.state == "${other.initial}"`,
          ...resources.map((x) => `${x.id}.inUse < ${x.capacity}`), ...resources.map((x) => `${x.id}.waiting.c0 == 0`),
        ]);
        t.guard = typeof t.guard === 'string' && r.chance(0.5) ? `(${t.guard}) || ${g}` : g;
        site('guard aggregate or resource');
      }
    }
  }
  return input;
}

/**
 * A version-2 input centred on resources: workers that take requests by use or acquire, wait,
 * are granted or refused, release and finish, under every discipline, overflow and route kind.
 * @param {Rng} r @param {Coverage} cov
 * @returns {any}
 */
function generateResourceInput(r, cov) {
  count(cov, 'v2 focused inputs');
  const resources = Array.from({ length: 1 + r.int(2) }, (_, i) => {
    const capacity = 1 + r.int(3);
    const two = r.chance(0.5);
    const classes = [
      { id: 'hi', priority: 1, reserved: two && capacity > 1 && r.chance(0.5) ? 1 : 0, limit: r.chance(0.3) ? 1 : null, queueBound: r.chance(0.4) ? r.int(3) : null, maxWait: r.chance(0.4) ? 1 + r.int(6) : null },
      ...(two ? [{ id: 'lo', priority: 0, reserved: 0, limit: r.chance(0.3) ? 1 : null, queueBound: r.chance(0.4) ? r.int(3) : null, maxWait: r.chance(0.4) ? 1 + r.int(6) : null }] : []),
    ];
    const res = {
      id: `pool${i}`, kind: 'pool', capacity, discipline: r.pick(['fifo', 'priority']),
      queueBound: r.chance(0.5) ? r.int(4) : null, overflow: r.pick(['refuse', 'drop', 'shed-oldest']),
      demandFactor: r.pick([null, null, [[0, 1, 1], [2, 3, 2]], { usl: { alpha: [1, 10], beta: [1, 100] } }]), classes,
    };
    count(cov, `v2 focused resource ${res.discipline} ${res.overflow}`);
    return res;
  });
  const events = ['req', 'done', 'no', 'got', 'tick'];
  const behaviors = Array.from({ length: 1 + r.int(2) }, (_, b) => {
    const id = `worker${b}`;
    const res = r.pick(resources);
    const cls = res.classes.length > 1 ? r.pick(res.classes).id : (r.chance(0.5) ? 'hi' : undefined);
    const take = r.chance(0.5)
      ? { use: res.id, demand: distribution(r, cov, 'v2 use demand'), then: 'done', refused: 'no', payload: { k: 'event.label' } }
      : { acquire: res.id, then: 'got', refused: 'no' };
    if (cls) /** @type {any} */ (take).class = cls;
    const rel = { release: res.id, ...(cls ? { class: cls } : {}) };
    const transitions = [
      { id: `take${b}`, from: 'idle', to: 'busy', on: 'req', effects: [take, { set: 'n', to: 'n + 1' }] },
      { id: `fin${b}`, from: 'busy', to: 'idle', on: 'done', effects: [] },
      { id: `rej${b}`, from: 'busy', to: 'idle', on: 'no', effects: [{ set: 'refused', to: 'refused + 1' }] },
      { id: `got${b}`, from: 'busy', to: 'busy', on: 'got', effects: [{ emit: 'done', after: distribution(r, cov, 'v2 emit after') }, ...(r.chance(0.9) ? [rel] : [])] },
      { id: `tick${b}`, from: 'idle', to: 'idle', on: 'tick', guard: r.pick([`${res.id}.inUse <= ${res.capacity}`, `${res.id}.waiting.hi >= 0`, `worker0.count.idle >= 0`, 'instance == 0', `worker0.sum.n >= 0`]), effects: [{ set: 'n', to: { sample: distribution(r, cov, 'v2 set sample') } }] },
      { id: `busytick${b}`, from: 'busy', to: 'busy', on: 'tick', effects: [{ emit: 'no', after: 1, ...(r.chance(0.1) ? { target: 'reply' } : {}) }] },
    ];
    const ik = r.int(3);
    /** @type {any} */
    const out = { id, initial: 'idle', states: ['idle', 'busy'], variables: [{ name: 'n', initial: 0 }, { name: 'refused', initial: 0 }], transitions };
    if (ik === 0) out.instances = { count: 1 + r.int(3) };
    else if (ik === 1) out.instances = { key: 'label', max: 1 + r.int(4) };
    count(cov, `v2 focused instances ${ik === 0 ? 'counted' : ik === 1 ? 'keyed' : 'single'}`);
    return out;
  });
  /** @type {any[]} */
  const routes = [];
  for (const b of behaviors) {
    if (b.instances?.key) { routes.push({ event: 'req', behavior: b.id, by: 'key', field: 'label' }); continue; }
    if (!r.chance(0.8)) continue;
    const by = r.pick(['key', 'round-robin', 'random', 'any', 'least-busy']);
    /** @type {any} */
    const route = { event: 'req', behavior: b.id, by };
    if (by === 'key') route.field = 'label';
    if (by === 'least-busy') route.resource = r.pick(resources).id;
    routes.push(route);
    count(cov, `v2 focused route ${by}`);
  }
  const steps = Array.from({ length: 3 + r.int(10) }, () => ({ at: r.int(12), event: r.pick(['req', 'req', 'req', 'tick']), payload: { label: r.pick(['a', 'b', 'c']) } }));
  return {
    format: 'exegra-sim-input', version: 2, time: { unit: 'us', perSecond: 1000000 },
    events: events.map((id) => ({ id })), behaviors, routes, resources, faults: [],
    scenario: { id: 'focused', seed: r.pick(['42', '7', '1234567']), steps, faults: [], stepLimit: 60 },
  };
}

/**
 * Generate `count` version-2 inputs from a seed, alternating generateInputV2 and the resource-centred
 * generateResourceInput (a stream of its own, so version-1 inputs of the same
 * seed are unchanged).
 * @param {number} seed @param {number} n
 * @returns {{inputs: any[], coverage: Coverage}}
 */
export function generateInputsV2(seed, n) {
  const r = createRng(seed ^ 0x5eed2);
  /** @type {Coverage} */
  const coverage = {};
  const inputs = [];
  for (let i = 0; i < n; i++) inputs.push(i % 2 ? generateResourceInput(r, coverage) : generateInputV2(r, coverage));
  return { inputs, coverage };
}

/**
 * Generate `count` inputs from a seed. The same seed and count always give the same inputs.
 * @param {number} seed @param {number} n
 * @returns {{inputs: any[], coverage: Coverage}}
 */
export function generateInputs(seed, n) {
  const r = createRng(seed);
  /** @type {Coverage} */
  const coverage = {};
  const inputs = [];
  for (let i = 0; i < n; i++) inputs.push(generateInput(r, coverage));
  return { inputs, coverage };
}

/** @param {Coverage} cov @returns {string} */
export function formatCoverage(cov) {
  return Object.keys(cov).sort().map((k) => `  ${k}: ${cov[k]}`).join('\n');
}

/** @param {string[]} argv */
function main(argv) {
  let seed = 1;
  let n = 100;
  /** @type {string|undefined} */
  let out;
  let v2 = false;
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    const v = argv[i + 1];
    if (a === '--v2') v2 = true;
    else if (a === '--seed' && v !== undefined) { seed = Number(v); i++; }
    else if (a === '--count' && v !== undefined) { n = Number(v); i++; }
    else if (a === '--out' && v !== undefined) { out = path.resolve(v); i++; }
    else { process.stderr.write('Usage: node tools/gen-engine-inputs.js [--v2] [--seed <n>] [--count <n>] [--out <dir>]\n'); return 2; }
  }
  if (!Number.isInteger(seed) || !Number.isInteger(n) || n < 0) { process.stderr.write('--seed and --count must be integers\n'); return 2; }
  const { inputs, coverage } = v2 ? generateInputsV2(seed, n) : generateInputs(seed, n);
  if (out !== undefined) {
    fs.mkdirSync(out, { recursive: true });
    inputs.forEach((input, i) => fs.writeFileSync(path.join(/** @type {string} */ (out), `input-${seed}-${i}.json`), `${JSON.stringify(input, null, 1)}\n`));
  }
  process.stdout.write(`gen-engine-inputs: seed ${seed}, ${n} inputs${out ? `, written to ${out}` : ''}\ncoverage:\n${formatCoverage(coverage)}\n`);
  return 0;
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) process.exitCode = main(process.argv.slice(2));
