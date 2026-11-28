// The simulation engine facade: the one place the rest of Exegra touches the engine.
//
// The engine is the Lean core (formal/), compiled to WebAssembly and called through the call boundary
// of src/core/lean.js as the registered function "engine.run": the dispatch the native `exegra-lean`
// runs. A version-2 input the elaborator accepts runs on the scheduler of the behaviour calculus
// (formal/Exegra/Format2B.lean, traceOfB), one outside the calculus's fragment on the legacy format-2
// interpreter (its trace says "semantics": "legacy"), and a version-1 input is refused (format 1 was
// removed, WG-5681). That function is the implementation Exegra.Impl, proved equal to the definition
// on every input (Exegra.Impl.runAnyValue_eq). It reads one engine input (sim-input.js, format
// "exegra-sim-input") and returns one trace. Semantics: docs/module-contracts.md, section
// "Simulation"; formats: docs/simulation.md, "Engine input and trace format". The Rust engine
// (engine/) is no longer run here: it stays as a differential oracle in the tests.
//
// Loading. In Node, initEngine() is synchronous and runEngine() loads the core on first use when
// nobody called initEngine(). In the browser (and in a Web Worker) initEngine() is asynchronous and
// must be awaited before the first run.

import { simulationInput } from './sim-input.js';
import { callText, initLean, leanReady } from './lean.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./sim-input.js').SimulationInput} SimulationInput */

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
 * Throws for a scenario, behavior, event or fault that does not exist (sim-input.js); a run that
 * fails part-way is recorded in the trace with outcome "error".
 * @param {Model} model
 * @param {string} scenarioId
 * @param {{faults?: string[]}} [opts]
 * @returns {Trace}
 */
export function runScenario(model, scenarioId, opts) {
  return runEngine(simulationInput(model, scenarioId, opts?.faults));
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
