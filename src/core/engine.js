// The simulation engine facade: the one place the rest of Exegra touches the engine.
//
// The engine is the Lean core (formal/), compiled to WebAssembly and called through the call boundary
// of src/core/lean.js as the registered function "engine.run": the dispatch the native `exegra-lean`
// runs. A version-2 input the elaborator accepts runs on the scheduler of the behaviour calculus
// (formal/Exegra/Format2B.lean, traceOfB), one outside the calculus's fragment on the legacy format-2
// interpreter (its trace says "semantics": "legacy"), and a version-1 input is refused (format 1 was
// removed, WG-5681). That function is the implementation Exegra.Impl, proved equal to the definition
// on every input (Exegra.Impl.runAnyValue_eq). It reads one engine input (format "exegra-sim-input")
// and returns one trace. The engine input of a scenario is derived in Lean too (engineInput, the
// registered function "engine.input", Exegra.Lower.engineInput, WG-5683): the shell sends the model's
// entities and the scenario, never an input it built itself. Semantics: docs/module-contracts.md, section
// "Simulation"; formats: docs/simulation.md, "Engine input and trace format". The Rust engine
// (engine/) is no longer run here: it stays as a differential oracle in the tests.
//
// Loading. In Node, initEngine() is synchronous and runEngine() loads the core on first use when
// nobody called initEngine(). In the browser (and in a Web Worker) initEngine() is asynchronous and
// must be awaited before the first run.

import { callText, initLean, leanReady } from './lean.js';

/** @typedef {import('./types.js').Model} Model */
/**
 * @typedef {{id:string, from:string, to:string, on:string, guard:string|null, effects:any[], faultOnly:boolean}} InputTransition
 * @typedef {{id:string, subject:string, initial:string, types?:Record<string, string>, variables:{name:string, initial:any}[], states:string[], transitions:InputTransition[]}} InputBehavior
 * @typedef {{id:string, kind:string, event?:string, transition?:string, occurrence?:number, by?:number, at?:number, payload?:Record<string, any>}} InputFault
 * @typedef {{format:'exegra-sim-input', version:2, time?:{unit:string, perSecond:number|null},
 *   scenario:{id:string, steps:{at:number, event:string, payload:Record<string, any>}[], faults:string[], stepLimit:number},
 *   behaviors:InputBehavior[], events:{id:string}[], faults:InputFault[], resources?:{id:string}[]}} SimulationInput
 */

/** The engine input format's name. */
export const SIM_INPUT_FORMAT = 'exegra-sim-input';

/** The entity kinds the lowering reads (Exegra.Lower.engineInput). */
const LOWERED_KINDS = new Set(['scenario', 'behavior', 'transition', 'state', 'event', 'fault', 'workload', 'resource', 'link',
  'requestClass', 'quotaPool', 'quota', 'type', 'system']);

/**
 * The model as the lowering of one scenario reads it: the entities of the kinds it reads, `{id, kind,
 * owner, data}`, in the model's order (an entity added to `model.entities` alone counts too). Only the
 * scenario itself, the behaviors it lists with their states and transitions, and the faults, workloads
 * and quota pools it names (and the faults `faults` names) are sent of their kinds: the lowering reads no other
 * entity of those kinds, and a name that is missing is refused with the same message as a name of the
 * wrong kind. This keeps the request small: the Lean core parses it on every call.
 * @param {Model} model @param {string} scenarioId @param {string[]} [faults]
 */
function loweringModel(model, scenarioId, faults) {
  const sdata = /** @type {any} */ (model.entities.get(scenarioId)?.data) ?? {};
  const named = (/** @type {any} */ v) => new Set(Array.isArray(v) ? v.filter((x) => typeof x === 'string') : []);
  const behaviors = named(sdata.behaviors);
  /** @type {Record<string, Set<string>>} */
  const wanted = { scenario: new Set([scenarioId]), behavior: behaviors, fault: new Set([...named(faults), ...named(sdata.faults)]), workload: named(sdata.workloads), quotaPool: named(sdata.pools) };
  /** @type {{id:string, kind:string, owner:string|null, data:any}[]} */
  const entities = [];
  for (const e of model.entities.values()) {
    if (!LOWERED_KINDS.has(e.kind)) continue;
    if (e.kind in wanted && !wanted[e.kind].has(e.id)) continue;
    if ((e.kind === 'state' || e.kind === 'transition') && !(e.owner !== null && behaviors.has(e.owner))) continue;
    entities.push({ id: e.id, kind: e.kind, owner: e.owner, data: loweredData(e.kind, e.data) });
  }
  return { entities };
}

/** Top-level members of an entity the lowering never reads (prose). */
const PROSE = new Set(['name', 'description', 'notes', 'rationale']);

/**
 * The part of an entity's data the lowering reads: the prose members are left out, an event keeps only
 * its payload, a state nothing (its id is all that is read), and a behavior not its nested states and
 * transitions (the lowering reads them as their own entities). Nested values are kept whole.
 * @param {string} kind @param {any} data
 */
function loweredData(kind, data) {
  if (!data || typeof data !== 'object' || Array.isArray(data)) return data;
  if (kind === 'state') return {};
  if (kind === 'event') return 'payload' in data ? { payload: data.payload } : {};
  /** @type {Record<string, any>} */
  const out = {};
  for (const k of Object.keys(data)) {
    if (PROSE.has(k)) continue;
    if (kind === 'behavior' && (k === 'states' || k === 'transitions')) continue;
    out[k] = data[k];
  }
  return out;
}

/** @param {Model} model @param {string} scenarioId @param {string[]} [faults] */
function loweringArgs(model, scenarioId, faults) {
  return JSON.stringify({ model: loweringModel(model, scenarioId, faults), scenario: scenarioId, ...(faults ? { faults } : {}) });
}

/**
 * The engine inputs derived lately, by the text of their lowering request: a request is the whole of
 * what the lowering reads, so an equal request has an equal answer, and claim evaluation, which derives
 * the input of one scenario for many claims, asks the Lean core once. At most `LOWERED_CACHE_SIZE`
 * entries, the least recently used dropped first.
 * @type {Map<string, {ok: true, text: string} | {ok: false, error: string}>}
 */
const lowered = new Map();
const LOWERED_CACHE_SIZE = 64;

/**
 * The engine input of a scenario as JSON text, or the lowering's refusal.
 * @param {Model} model @param {string} scenarioId @param {string[]} [faults]
 * @returns {{ok: true, text: string} | {ok: false, error: string}}
 */
function engineInputText(model, scenarioId, faults) {
  const request = loweringArgs(model, scenarioId, faults);
  const hit = lowered.get(request);
  if (hit) {
    lowered.delete(request);
    lowered.set(request, hit);
    return hit;
  }
  const r = callText('engine.input', request);
  const answer = r.ok ? { ok: /** @type {true} */ (true), text: r.text } : { ok: /** @type {false} */ (false), error: r.error };
  lowered.set(request, answer);
  if (lowered.size > LOWERED_CACHE_SIZE) lowered.delete(/** @type {string} */ (lowered.keys().next().value));
  return answer;
}

/**
 * The engine input of one scenario run, derived in Lean (Exegra.Lower.engineInput). `faults`, when
 * given, replaces the scenario's own fault list. Throws, with the lowering's message, for a scenario,
 * behavior, event, fault, workload or quota pool that does not exist and for a malformed unit, rate or
 * distribution, before any engine runs. Synchronous after initEngine().
 * @param {Model} model
 * @param {string} scenarioId
 * @param {string[]} [faults]
 * @returns {SimulationInput}
 */
export function engineInput(model, scenarioId, faults) {
  const r = engineInputText(model, scenarioId, faults);
  if (!r.ok) throw new Error(r.error);
  return JSON.parse(r.text);
}

/**
 * @typedef {{seq:number, time:number, event:string, payload:Record<string, any>, source:any}} Pending
 * @typedef {{machines: Record<string, {state:string, vars:Record<string, any>}>, time:number, pending: Pending[]}} Configuration
 * @typedef {{index:number, time:number, kind:'deliver'|'drop'|'delay', event:{id:string, payload:Record<string, any>, seq:number, source:any},
 *   fired: {behavior:string, transition:string, from:string, to:string, guard:string|null,
 *           sets:{variable:string, before:any, after:any}[], emitted:{event:string, time:number, seq:number, payload:Record<string, any>}[]}[],
 *   ignored: {behavior:string, reason:'no-transition'|'guard-false'|'disabled', considered:string[]}[],
 *   faults: {fault:string, effect:'dropped'|'delayed'|'enabled'|'disabled'|'injected'}[],
 *   responsible: string[], config: Configuration, error?: {message:string}}} TraceStep
 * @typedef {'running'|'quiescent'|'step-limit'|'error'} Outcome
 * @typedef {{scenarioId:string, faults:string[], initial:Configuration, steps:TraceStep[], outcome:Outcome, final:Configuration}} Trace
 * @typedef {{scenarioId:string, faults:string[], initial:Configuration, config:Configuration, steps:TraceStep[],
 *   outcome:Outcome, step:() => TraceStep|null, run:() => Trace, reset:() => void, trace:() => Trace}} Simulation
 */

/**
 * Load the engine. In Node the work is done before this returns (the promise is already settled);
 * in a browser or worker the returned promise must be awaited. Calling it again is harmless.
 * @returns {Promise<void>}
 */
export function initEngine() {
  return initLean();
}

/** Whether the engine is loaded and runEngine can be called. */
export function engineReady() {
  return leanReady();
}

/**
 * Run an engine input given as JSON text and return the trace as JSON text. Synchronous.
 * Throws an Error with the engine's message when the engine refuses the input.
 * @param {string} inputText
 * @returns {string}
 */
export function runEngineText(inputText) {
  const r = callText('engine.run', inputText);
  if (!r.ok) throw new Error(r.error);
  return r.text;
}

/**
 * Run an engine input and return the parsed trace. Synchronous after initEngine().
 * @param {SimulationInput|string} input  the input, or its JSON text
 * @returns {Trace}
 */
export function runEngine(input) {
  return JSON.parse(runEngineText(typeof input === 'string' ? input : JSON.stringify(input)));
}

/**
 * Run a scenario of a model to completion. `opts.faults` replaces the scenario's own fault list.
 * Throws for a scenario, behavior, event or fault that does not exist (engineInput); a run that
 * fails part-way is recorded in the trace with outcome "error".
 * @param {Model} model
 * @param {string} scenarioId
 * @param {{faults?: string[]}} [opts]
 * @returns {Trace}
 */
export function runScenario(model, scenarioId, opts) {
  const r = engineInputText(model, scenarioId, opts?.faults);
  if (!r.ok) throw new Error(r.error);
  return JSON.parse(runEngineText(r.text));
}

/**
 * A stepwise view of a finished trace: `steps` holds the steps revealed so far, `step()` reveals the
 * next one, `run()` reveals the rest, `reset()` hides them all again. `outcome` is "running" while
 * steps remain hidden and the trace's own outcome once all are revealed; `config` is the
 * configuration after the last revealed step. The trace itself is never changed.
 * @param {Trace} trace
 * @returns {Simulation}
 */
export function createTraceCursor(trace) {
  const all = trace.steps;
  /** @type {Simulation} */
  const sim = {
    scenarioId: trace.scenarioId,
    faults: trace.faults.slice(),
    initial: trace.initial,
    config: trace.initial,
    steps: [],
    outcome: 'running',
    step,
    run,
    reset,
    trace: snapshot,
  };
  const sync = () => {
    const n = sim.steps.length;
    sim.outcome = n < all.length ? 'running' : trace.outcome;
    sim.config = n === all.length ? trace.final : n === 0 ? trace.initial : all[n - 1].config;
  };
  /** @returns {TraceStep|null} */
  function step() {
    const n = sim.steps.length;
    if (n >= all.length) return null;
    sim.steps.push(all[n]);
    sync();
    return all[n];
  }
  /** @returns {Trace} */
  function run() {
    for (let n = sim.steps.length; n < all.length; n++) sim.steps.push(all[n]);
    sync();
    return snapshot();
  }
  function reset() {
    sim.steps = [];
    sync();
  }
  /** @returns {Trace} */
  function snapshot() {
    // Every trace is version 2 (WG-5681): the fields beside the steps (version, timeUnit, seed,
    // initialDraws, truncated, semantics, ...) are the trace's own; stepsTaken counts the revealed steps.
    /** @type {any} */
    const out = { ...trace, scenarioId: sim.scenarioId, faults: sim.faults.slice(), initial: sim.initial, steps: sim.steps.slice(), outcome: sim.outcome, final: sim.config };
    if ('stepsTaken' in trace) out.stepsTaken = sim.steps.length;
    return out;
  }
  sync();
  return sim;
}

/**
 * Run a scenario and return a stepwise view of its trace (createTraceCursor).
 * @param {Model} model
 * @param {string} scenarioId
 * @param {{faults?: string[]}} [opts]
 * @returns {Simulation}
 */
export function createSimulation(model, scenarioId, opts) {
  return createTraceCursor(runScenario(model, scenarioId, opts));
}
