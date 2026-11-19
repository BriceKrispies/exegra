// Replay of a recorded stream of real events through the behaviors of a scenario.
//
// A running Exegra records the events it really produces (src/app/traffic-recorder.js). This module
// checks such a stream against the self-model: the behaviors that the scenario names (in Exegra's own
// specification, `live-session`) are executed with the step semantics of the engine
// (docs/simulation.md, "Handling the head", phase 1 choice and phase 2 effects, expressions of
// src/core/expr.js), but the events delivered are the recorded ones, one at a time, in recorded order.
// The events the model emits are not queued for delivery: they become predictions, which a later
// recorded event must match.
//
// Why not the engine itself: the engine runs a whole scenario to quiescence from its input and
// delivers events with equal time in the order they were queued. A real run interleaves independent
// chains (a network answer, a file-watch notice, a claim evaluation) in whatever order they happen, so
// replaying it needs (1) one delivery at a time, driven from outside, and (2) any interleaving of the
// predicted events that respects causality (an event can only be matched after the delivery that
// predicted it), which is the same relaxation `exegra prove` explores for simultaneous events. The
// checker is therefore a pure incremental reimplementation of one engine step, without faults.
//
// Divergences (each reported under the claim real-runs-replay-through-self-model):
//   unknown-event   the recorded event is not an event of the model;
//   unpredicted     the event is one the model emits, but no pending prediction matches it;
//   not-allowed     a predicted (internal) event arrived and no behavior that consumes it accepted it
//                   in its current state;
//   payload         a recorded payload value differs from the predicted one;
//   missing         a prediction was not matched within `bound` recorded events (or by the end of a
//                   closed stream);
//   error           an expression of the model failed on the recorded payload.
// Calibration: a variable whose declared initial value stands for the environment at the start of
// the stream (a hash of a file on disk, a stored preference) and that no transition has written yet
// takes the recorded value the first time a prediction that reads it is compared. That is reported on
// the step, not as a divergence.
//
// Pure and deterministic: no clock (time is the recorded sequence number), no I/O.

import { simulationInput } from './sim-input.js';
import { evaluate, parseExpr } from './expr.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./sim-input.js').InputBehavior} InputBehavior */

export const REPLAY_CLAIM = 'real-runs-replay-through-self-model';
export const REPLAY_SCENARIO = 'live-session';
/** A prediction not matched within this many later recorded events is missing. */
export const DEFAULT_BOUND = 200;

/**
 * @typedef {{seq:number, id:string, payload?:Record<string, any>, inferred?:boolean}} RecordedEvent
 * @typedef {{kind:'unknown-event'|'unpredicted'|'not-allowed'|'payload'|'missing'|'error', stepIndex:number, seq:number, event:string, explanation:string, behavior?:string, transition?:string, field?:string}} Divergence
 * @typedef {{seq:number, time:number, event:string, payload:Record<string, any>, source:{kind:'transition', transition:string, behavior:string}, stepIndex:number, bindings:Record<string, string[]>, literals:string[]}} Prediction
 */

/** @template T @param {T} v @returns {T} */
const copy = (v) => (v === undefined ? v : JSON.parse(JSON.stringify(v)));
/** The declared types a behavior's expressions are evaluated with (its `types` in the engine input). @param {any} b */
const typesOf = (b) => (/** @type {string[]} */ path) => (b.types && Object.hasOwn(b.types, path.join('.')) ? b.types[path.join('.')] : undefined);
/** @param {unknown} v */
const scalar = (v) => v === null || typeof v === 'string' || typeof v === 'number' || typeof v === 'boolean';

/**
 * Start a replay of the behaviors of `scenarioId` (default live-session).
 * @param {Model} model
 * @param {{scenarioId?: string, bound?: number}} [opts]
 */
export function createReplay(model, opts = {}) {
  const scenarioId = opts.scenarioId ?? REPLAY_SCENARIO;
  const bound = opts.bound ?? DEFAULT_BOUND;
  const input = simulationInput(model, scenarioId, []);
  /** @type {InputBehavior[]} */
  const behaviors = input.behaviors;
  const eventIds = new Set(input.events.map((e) => e.id));
  /** Events some transition of the run emits (internal), and events some transition consumes. */
  const emitters = new Map();
  const consumers = new Map();
  for (const b of behaviors) for (const t of b.transitions) {
    if (t.faultOnly) continue;
    if (!consumers.has(t.on)) consumers.set(t.on, new Set());
    consumers.get(t.on).add(b.id);
    for (const fx of t.effects) if (fx && typeof fx.emit === 'string') {
      if (!emitters.has(fx.emit)) emitters.set(fx.emit, new Set());
      emitters.get(fx.emit).add(b.id);
    }
  }
  /** Correlation fields: the event's declared correlation, and requestId. Never compared, only matched. */
  const correlationOf = (/** @type {string} */ id) => {
    const e = model.entities.get(id);
    const c = typeof e?.data?.correlation === 'string' ? e.data.correlation : null;
    return c ? [c, 'requestId'] : ['requestId'];
  };

  /** @type {Record<string, {state:string, vars:Record<string, any>}>} */
  let machines = {};
  for (const b of behaviors) {
    machines[b.id] = { state: b.initial, vars: Object.fromEntries(b.variables.map((v) => [v.name, copy(v.initial)])) };
  }
  const initialMachines = copy(machines);
  /** Variables still at their declared initial value: "<behavior>\u0000<name>". */
  const uncalibrated = new Set(behaviors.flatMap((b) => b.variables.map((v) => `${b.id}\u0000${v.name}`)));

  /** @type {Prediction[]} */
  let pending = [];
  /** @type {any[]} */
  const steps = [];
  /** @type {Divergence[]} */
  const divergences = [];
  let predictionSeq = 0;
  let time = 0;
  let finished = false;

  const configOf = () => ({
    time,
    machines: copy(machines),
    pending: pending.map((p) => ({ seq: p.seq, time: p.time, event: p.event, payload: copy(p.payload), source: { ...p.source } })),
  });
  const initial = { time: 0, machines: initialMachines, pending: [] };

  /**
   * The value of a reference path for a behavior, reading `cfg`.
   * @param {Record<string, {state:string, vars:Record<string, any>}>} cfg @param {string} bid @param {Record<string, any>} payload
   */
  const resolver = (cfg, bid, payload) => (/** @type {string[]} */ path) => {
    if (path.length === 1 && path[0] === 'time') return time;
    if (path[0] === 'event') return path.length === 2 ? payload[path[1]] : undefined;
    if (path.length === 1) return cfg[bid]?.vars[path[0]];
    if (path.length === 2 && cfg[path[0]]) return path[1] === 'state' ? cfg[path[0]].state : cfg[path[0]].vars[path[1]];
    return undefined;
  };

  /** The variable an expression is exactly a reference to, as [behavior, name], or null. @param {string} src @param {string} bid */
  const varRef = (src, bid) => {
    const r = parseExpr(src);
    if (!r.ok || r.ast.t !== 'ref') return null;
    const p = r.ast.path;
    if (p.length === 1 && p[0] !== 'time' && p[0] in (machines[bid]?.vars ?? {})) return [bid, p[0]];
    if (p.length === 2 && machines[p[0]] && p[1] !== 'state' && p[1] in machines[p[0]].vars) return [p[0], p[1]];
    return null;
  };

  /** @param {Divergence} d */
  const diverge = (d) => { divergences.push(d); return d; };

  /**
   * The best pending prediction for a recorded event: same event, matching correlation when both carry it, oldest first.
   * @param {RecordedEvent} ev
   */
  function findPrediction(ev) {
    const keys = correlationOf(ev.id);
    const payload = ev.payload ?? {};
    const same = pending.filter((p) => p.event === ev.id);
    if (!same.length) return null;
    const exact = same.find((p) => keys.some((k) => k in payload && k in p.payload && p.payload[k] === payload[k]));
    if (exact) return exact;
    // Otherwise the prediction whose payload agrees with the recorded one on the most scalar fields; the oldest on a tie.
    let best = same[0];
    let bestScore = -1;
    for (const p of same) {
      let score = 0;
      for (const [k, v] of Object.entries(p.payload)) if (scalar(v) && k in payload && payload[k] === v) score++;
      if (score > bestScore) { best = p; bestScore = score; }
    }
    return best;
  }

  /**
   * Deliver one recorded event.
   * @param {RecordedEvent} ev
   */
  function consume(ev) {
    const index = steps.length;
    time = ev.seq;
    const payload = copy(ev.payload ?? {});
    /** @type {Divergence[]} */
    const here = [];
    /** @type {{behavior:string, variable:string, value:any}[]} */
    const calibrated = [];
    /** @type {any} */
    let source = { kind: 'recorded', ...(ev.inferred ? { inferred: true } : {}) };

    if (!eventIds.has(ev.id)) {
      here.push(diverge({ kind: 'unknown-event', stepIndex: index, seq: ev.seq, event: ev.id, explanation: `"${ev.id}" is not an event of the specification: the self-model has no name for something the running application did.` }));
      return record(index, ev, payload, source, [], [], [], here, calibrated);
    }

    const internal = emitters.has(ev.id);
    if (internal) {
      const p = findPrediction(ev);
      if (!p) {
        const by = [...emitters.get(ev.id)].join(', ');
        here.push(diverge({ kind: 'unpredicted', stepIndex: index, seq: ev.seq, event: ev.id, explanation: `${ev.id} happened, but the self-model does not predict it here: no transition of ${by} emitted it since it was last matched.` }));
      } else {
        pending = pending.filter((x) => x !== p);
        source = { ...p.source };
        const skip = correlationOf(ev.id);
        for (const [k, want] of Object.entries(p.payload)) {
          if (skip.includes(k) || p.literals.includes(k) || !(k in payload) || !scalar(want) || !scalar(payload[k]) || want === payload[k]) continue;
          const bind = p.bindings[k];
          const key = bind ? `${bind[0]}\u0000${bind[1]}` : null;
          if (key && uncalibrated.has(key)) {
            uncalibrated.delete(key);
            machines[bind[0]].vars[bind[1]] = copy(payload[k]);
            calibrated.push({ behavior: bind[0], variable: bind[1], value: copy(payload[k]) });
            continue;
          }
          here.push(diverge({ kind: 'payload', stepIndex: index, seq: ev.seq, event: ev.id, field: k, behavior: p.source.behavior, transition: p.source.transition, explanation: `${ev.id}.${k} is ${JSON.stringify(payload[k])}, but transition ${p.source.transition} predicted ${JSON.stringify(want)}.` }));
        }
      }
    }

    // Phase 1: choice, reading the configuration from before the step.
    const before = machines;
    /** @type {{b: InputBehavior, t: any}[]} */
    const winners = [];
    /** @type {any[]} */
    const ignored = [];
    try {
      for (const b of behaviors) {
        const m = before[b.id];
        /** @type {string[]} */
        const considered = [];
        /** @type {any} */
        let won = null;
        let guardFalse = false;
        for (const t of b.transitions) {
          if (t.from !== m.state || t.on !== ev.id || t.faultOnly) continue;
          considered.push(t.id);
          if (t.guard !== null) {
            const g = evaluate(t.guard, resolver(before, b.id, payload), typesOf(b));
            if (typeof g !== 'boolean') throw new Error(`Guard "${t.guard}" of transition "${t.id}" did not evaluate to a boolean.`);
            if (!g) { guardFalse = true; continue; }
          }
          won = t;
          break;
        }
        if (won) winners.push({ b, t: won });
        else ignored.push({ behavior: b.id, reason: guardFalse ? 'guard-false' : 'no-transition', considered });
      }

      // Phase 2: effects on the next configuration, behaviors in scenario order.
      const next = copy(before);
      /** @type {any[]} */
      const fired = [];
      /** @type {Prediction[]} */
      const born = [];
      for (const { b, t } of winners) {
        const sets = [];
        const emitted = [];
        for (const fx of t.effects) {
          const val = (/** @type {any} */ v) => (typeof v === 'string' ? evaluate(v, resolver(next, b.id, payload), typesOf(b)) : copy(v));
          if (typeof fx.set === 'string') {
            const beforeVal = next[b.id].vars[fx.set];
            const after = val(fx.to);
            next[b.id].vars[fx.set] = after;
            uncalibrated.delete(`${b.id}\u0000${fx.set}`);
            sets.push({ variable: fx.set, before: beforeVal, after: copy(after) });
          } else if (typeof fx.emit === 'string') {
            /** @type {Record<string, any>} */
            const out = {};
            /** @type {Record<string, string[]>} */
            const bindings = {};
            /** Fields the transition gives as a number literal: stand-ins for counts the model does not track. @type {string[]} */
            const literals = [];
            for (const [k, v] of Object.entries(fx.payload ?? {})) {
              if (typeof v === 'number') literals.push(k);
              out[k] = val(v);
              const ref = typeof v === 'string' ? varRef(v, b.id) : null;
              if (ref) bindings[k] = ref;
            }
            const pr = { seq: predictionSeq++, time: time + (fx.after ?? 0), event: fx.emit, payload: out, source: { kind: /** @type {'transition'} */ ('transition'), transition: t.id, behavior: b.id }, stepIndex: index, bindings, literals };
            born.push(pr);
            emitted.push({ event: fx.emit, time: pr.time, seq: pr.seq, payload: copy(out) });
          }
        }
        next[b.id].state = t.to;
        fired.push({ behavior: b.id, transition: t.id, from: t.from, to: t.to, guard: t.guard, sets, emitted });
      }
      machines = next;
      pending.push(...born);

      if (internal && !fired.length && consumers.has(ev.id)) {
        const states = [...consumers.get(ev.id)].map((bid) => `${bid} in ${machines[bid].state}`).join(', ');
        here.push(diverge({ kind: 'not-allowed', stepIndex: index, seq: ev.seq, event: ev.id, explanation: `${ev.id} happened, but the self-model does not allow it at this point: ${states} accepts it in no transition.` }));
      }
      expire(index);
      return record(index, ev, payload, source, fired, ignored, winners, here, calibrated);
    } catch (e) {
      here.push(diverge({ kind: 'error', stepIndex: index, seq: ev.seq, event: ev.id, explanation: `The self-model could not process ${ev.id}: ${/** @type {Error} */ (e).message}` }));
      expire(index);
      return record(index, ev, payload, source, [], [], [], here, calibrated);
    }
  }

  /** Predictions older than the bound are missing. @param {number} index */
  function expire(index) {
    const late = pending.filter((p) => index - p.stepIndex > bound);
    if (!late.length) return;
    pending = pending.filter((p) => index - p.stepIndex <= bound);
    for (const p of late) missing(p, index, `within ${bound} recorded events`);
  }

  /** @param {Prediction} p @param {number} index @param {string} when */
  function missing(p, index, when) {
    const d = diverge({ kind: 'missing', stepIndex: p.stepIndex, seq: p.time, event: p.event, behavior: p.source.behavior, transition: p.source.transition, explanation: `Transition ${p.source.transition} predicted ${p.event} at step #${p.stepIndex}, but it did not happen ${when}.` });
    const at = steps[p.stepIndex];
    if (at) at.divergences.push(d);
    void index;
  }

  /**
   * @param {number} index @param {RecordedEvent} ev @param {Record<string, any>} payload @param {any} source
   * @param {any[]} fired @param {any[]} ignored @param {any[]} winners @param {Divergence[]} here @param {any[]} calibrated
   */
  function record(index, ev, payload, source, fired, ignored, winners, here, calibrated) {
    /** @type {string[]} */
    const responsible = [];
    const add = (/** @type {string} */ id) => { if (id && !responsible.includes(id)) responsible.push(id); };
    if (eventIds.has(ev.id)) add(ev.id);
    for (const f of fired) {
      add(f.transition); add(f.behavior);
      const b = behaviors.find((x) => x.id === f.behavior);
      if (b?.subject) add(b.subject);
    }
    void winners;
    const step = { index, time: ev.seq, kind: 'deliver', event: { id: ev.id, payload, seq: ev.seq, source }, fired, ignored, faults: [], responsible, config: configOf(), divergences: here, calibrated };
    steps.push(step);
    return step;
  }

  return {
    scenarioId,
    bound,
    initial,
    steps,
    divergences,
    consume,
    /** The predictions still waiting for their event. */
    get pending() { return pending.map((p) => ({ event: p.event, payload: copy(p.payload), source: { ...p.source }, stepIndex: p.stepIndex })); },
    /** Close the stream: every outstanding prediction is missing. */
    finish() {
      if (finished) return;
      finished = true;
      const left = pending;
      pending = [];
      for (const p of left) missing(p, steps.length, 'before the recorded stream ended');
    },
    /** The replay as a trace (src/core/engine.js Trace shape); outcome running while the stream is open. */
    trace() {
      return { scenarioId, faults: [], initial, steps: steps.slice(), outcome: finished ? 'quiescent' : 'running', final: steps.length ? steps[steps.length - 1].config : initial };
    },
  };
}

/**
 * Replay a whole recorded stream. `closed` marks the stream as ended, so outstanding predictions are missing.
 * @param {Model} model @param {RecordedEvent[]} events
 * @param {{scenarioId?: string, bound?: number, closed?: boolean}} [opts]
 */
export function replayStream(model, events, opts = {}) {
  const r = createReplay(model, opts);
  for (const ev of events) r.consume(ev);
  if (opts.closed) r.finish();
  return { trace: r.trace(), divergences: r.divergences.slice(), pending: r.pending };
}

/**
 * The divergences of a replay as failed checks of the claim real-runs-replay-through-self-model (or one
 * passing check when there are none), in the shape checkTrace returns.
 * @param {Model} model @param {Divergence[]} divergences @param {number} stepCount
 */
export function replayChecks(model, divergences, stepCount) {
  const claimId = model.entities.get(REPLAY_CLAIM)?.kind === 'claim' ? REPLAY_CLAIM : 'replay';
  if (!divergences.length) {
    return [{ claimId, holds: true, automatic: true, check: 'replay', explanation: `${stepCount} recorded event${stepCount === 1 ? '' : 's'} replayed through the self-model without a divergence.` }];
  }
  return divergences.map((d) => ({ claimId, holds: false, automatic: true, check: 'replay', divergence: d.kind, stepIndex: d.stepIndex, explanation: `${d.kind}: ${d.explanation}` }));
}
