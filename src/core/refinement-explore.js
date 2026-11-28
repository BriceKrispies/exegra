// Refinement checked over every execution of a scenario, not only the engine's trace (WG-5685, criterion 10;
// WG-4852).
//
// The engine runs a scenario in one order: entries of equal time are delivered in the order they were queued.
// Any other order of simultaneous entries is an execution too (the behaviour calculus delivers any entry of
// minimal time, docs/simulation.md). This module explores them: from the initial configuration it delivers, at
// every node, each pending entry of minimal time (the scenario's own steps and the events the behaviors emitted),
// one at a time, with the step semantics of src/core/replay.js (the engine step without faults), and checks every
// step it reaches with checkRefinementTrace. Configurations already explored are not explored again.
//
// Results:
//   failure    a reachable step fails the refinement; the counterexample is the path to it (its delivery order);
//   complete   every reachable step was checked and none failed;
//   incomplete the exploration did not cover every execution: it hit its state cap or the scenario's step limit,
//              or the scenario has what the explorer does not enumerate (fault masks, draws of sampled delays,
//              timer cancellations, counted or keyed instances, resources, workloads). An incomplete exploration
//              is never reported verified.

import { engineInput } from './engine.js';
import { createReplay } from './replay.js';
import { checkRefinementTrace } from './refinement.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */

/** The most configurations one exploration visits. */
export const DEFAULT_STATE_CAP = 5000;

const KNOWN_INPUT_KEYS = new Set(['format', 'version', 'scenario', 'behaviors', 'events', 'faults', 'time']);

/**
 * What the explorer cannot enumerate in a scenario's engine input; null when it can enumerate everything.
 * @param {any} input
 * @returns {string|null}
 */
export function unexplorable(input) {
  const extra = Object.keys(input).filter((k) => !KNOWN_INPUT_KEYS.has(k) && input[k] && !(Array.isArray(input[k]) && !input[k].length) && !(typeof input[k] === 'object' && !Array.isArray(input[k]) && !Object.keys(input[k]).length));
  if (extra.length) return `the engine input has ${extra.join(', ')}, which the explorer does not model`;
  if (Array.isArray(input.scenario?.faults) && input.scenario.faults.length) return `the scenario runs faults (${input.scenario.faults.join(', ')}), whose masks the explorer does not enumerate`;
  for (const b of input.behaviors ?? []) {
    if (b.instances) return `behavior "${b.id}" has instances, which the explorer does not enumerate`;
    for (const t of b.transitions ?? []) for (const fx of t.effects ?? []) {
      if (!fx || typeof fx !== 'object') continue;
      if ('cancel' in fx) return `transition "${t.id}" cancels a timer, which the explorer does not model`;
      if ('set' in fx) { if (fx.to && typeof fx.to === 'object') return `transition "${t.id}" sets "${fx.set}" to a sampled value, whose draws the explorer does not enumerate`; continue; }
      if (typeof fx.emit !== 'string') return `transition "${t.id}" has an effect the explorer does not model`;
      if (fx.after !== undefined && typeof fx.after !== 'number' && !(fx.after && fx.after.kind === 'fixed' && typeof fx.after.value === 'number')) return `transition "${t.id}" emits "${fx.emit}" after a sampled delay, whose draws the explorer does not enumerate`;
      if (fx.fanout === true || 'via' in fx) return `transition "${t.id}" emits over a fan-out or a link, which the explorer does not model`;
    }
  }
  return null;
}

/**
 * @typedef {{seq:number, time:number, event:string, payload:Record<string, any>, external:boolean}} Entry
 * @typedef {{status:'failure', failure: any, order: string[], states:number, steps:number}
 *   | {status:'complete', states:number, steps:number}
 *   | {status:'incomplete', reason:string, states:number, steps:number}} ExploreResult
 */

/**
 * Explore every delivery order of a scenario and check every step of `impl` against its model.
 * @param {Model} model @param {Entity} impl @param {string} scenarioId
 * @param {{stateCap?: number}} [opts]
 * @returns {ExploreResult}
 */
export function exploreRefinement(model, impl, scenarioId, opts = {}) {
  return exploreExecutions(model, scenarioId, (trace) => {
    const res = checkRefinementTrace(model, impl, trace, scenarioId);
    if (res.failure) return { failure: res.failure };
    if (res.unsupported) return { unsupported: res.unsupported };
    return null;
  }, opts);
}

/**
 * Explore every delivery order of a scenario. `check` is called with the trace of each path the exploration
 * extends (initial configuration and steps, the last step new) and returns a failure, an unsupported reason, or
 * null when the path is fine; the first failure ends the exploration.
 * @param {Model} model @param {string} scenarioId
 * @param {(trace: {initial: any, steps: any[]}) => ({failure: any}|{unsupported: string}|null)} check
 * @param {{stateCap?: number}} [opts]
 * @returns {ExploreResult}
 */
export function exploreExecutions(model, scenarioId, check, opts = {}) {
  const cap = opts.stateCap ?? DEFAULT_STATE_CAP;
  const input = engineInput(model, scenarioId, []);
  const why = unexplorable(input);
  if (why) return { status: 'incomplete', reason: `Not every execution was explored: ${why}.`, states: 0, steps: 0 };
  const stepLimit = input.scenario.stepLimit ?? 1000;
  /** @type {Entry[]} */
  const externals = (input.scenario.steps ?? []).map((/** @type {any} */ s, /** @type {number} */ i) => ({ seq: i, time: s.at, event: s.event, payload: s.payload ?? {}, external: true }));

  /**
   * Replay a delivery order from the start. The replay's clock is the recorded sequence number, so each entry is
   * delivered with its scheduled time as that number.
   * @param {Entry[]} order
   */
  const run = (order) => {
    const r = createReplay(model, { scenarioId, bound: Number.MAX_SAFE_INTEGER });
    for (const e of order) r.consume({ seq: e.time, id: e.event, payload: e.payload });
    return r;
  };
  /** The entries pending after a delivery order: undelivered scenario steps and the events emitted and not delivered. @param {Entry[]} order @param {any} r */
  const pendingAfter = (order, r) => {
    const done = new Set(order.filter((e) => e.external).map((e) => e.seq));
    const trace = r.trace();
    /** @type {Entry[]} */
    const internal = (trace.final.pending ?? []).map((/** @type {any} */ p) => ({ seq: p.seq, time: p.time, event: p.event, payload: p.payload, external: false }));
    return [...externals.filter((e) => !done.has(e.seq)), ...internal];
  };
  /** A configuration: the machines and the pending entries, as a multiset. @param {any} r @param {Entry[]} pend */
  const keyOf = (r, pend) => JSON.stringify([r.trace().final.machines, pend.map((e) => JSON.stringify([e.time, e.event, e.payload, e.external ? e.seq : -1])).sort()]);

  const seen = new Set();
  let steps = 0;
  /** @type {Entry[][]} */
  const stack = [[]];
  while (stack.length) {
    const order = /** @type {Entry[]} */ (stack.pop());
    const r = run(order);
    const trace = r.trace();
    if (order.length) {
      steps++;
      const last = trace.steps[trace.steps.length - 1];
      const err = last.divergences.find((/** @type {any} */ d) => d.kind === 'error');
      if (err) return { status: 'incomplete', reason: `The execution delivering ${order.map((e) => e.event).join(', ')} ends in an error (${err.explanation}), so the executions after it were not run.`, states: seen.size, steps };
      const res = check({ initial: trace.initial, steps: trace.steps });
      if (res && 'failure' in res) return { status: 'failure', failure: res.failure, order: order.map((e) => e.event), states: seen.size, steps };
      if (res && 'unsupported' in res) return { status: 'incomplete', reason: `Not every execution was checked: ${res.unsupported}`, states: seen.size, steps };
    }
    const pend = pendingAfter(order, r);
    const key = keyOf(r, pend);
    if (seen.has(key)) continue;
    seen.add(key);
    if (seen.size > cap) return { status: 'incomplete', reason: `The exploration reached its cap of ${cap} configurations before covering every execution.`, states: seen.size, steps };
    if (!pend.length) continue;
    if (order.length >= stepLimit) return { status: 'incomplete', reason: `An execution reached the scenario's step limit of ${stepLimit} steps with entries still pending, so later steps were not explored.`, states: seen.size, steps };
    const t = Math.min(...pend.map((e) => e.time));
    // Each distinct entry of minimal time is a choice; equal entries lead to the same configuration.
    const choices = new Map();
    for (const e of pend) if (e.time === t) {
      const k = JSON.stringify([e.event, e.payload, e.external ? e.seq : -1]);
      if (!choices.has(k)) choices.set(k, e);
    }
    for (const e of [...choices.values()].reverse()) stack.push([...order, e]);
  }
  return { status: 'complete', states: seen.size, steps };
}
