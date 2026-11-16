// Runs engine inputs off the main thread, in the Web Worker of engine-worker.js, so a long
// simulation never blocks the page. One run at a time: starting a run while another is still
// executing terminates that worker (its result would be discarded anyway) and starts a fresh one.
// Where no worker can be started, a run falls back to the main-thread engine (src/core/engine.js),
// which the application has already loaded.

import { runEngine } from '../core/engine.js';

/** @typedef {import('../core/engine.js').Trace} Trace */
/** @typedef {import('../core/sim-input.js').SimulationInput} SimulationInput */

/**
 * @typedef {{run: (input: SimulationInput) => Promise<Trace>, dispose: () => void}} EngineRunner
 */

/** @returns {EngineRunner} */
export function createEngineRunner() {
  /** @type {Worker|null} */
  let worker = null;
  let workerFailed = typeof Worker === 'undefined';
  let seq = 0;
  /** @type {Map<number, {resolve: (t: Trace) => void, reject: (e: Error) => void, input: SimulationInput}>} */
  const waiting = new Map();

  /** A run on the main thread, after the current task so the "running" state is shown first. @param {SimulationInput} input */
  const onMainThread = (input) => new Promise((resolve, reject) => {
    setTimeout(() => {
      try { resolve(runEngine(input)); } catch (e) { reject(e instanceof Error ? e : new Error(String(e))); }
    }, 0);
  });

  function start() {
    if (worker || workerFailed) return;
    try {
      worker = new Worker(new URL('./engine-worker.js', import.meta.url), { type: 'module' });
    } catch {
      workerFailed = true;
      return;
    }
    worker.onmessage = (/** @type {MessageEvent} */ e) => {
      const { id, ok, trace, error } = e.data ?? {};
      const job = waiting.get(id);
      if (!job) return;
      waiting.delete(id);
      if (ok) {
        try { job.resolve(JSON.parse(trace)); } catch (err) { job.reject(/** @type {Error} */ (err)); }
      } else job.reject(new Error(error));
    };
    // The worker itself could not run (its module failed to load): use the main thread from now on.
    worker.onerror = (/** @type {ErrorEvent} */ e) => {
      e.preventDefault?.();
      worker?.terminate();
      worker = null;
      workerFailed = true;
      const jobs = [...waiting.values()];
      waiting.clear();
      for (const job of jobs) onMainThread(job.input).then(job.resolve, job.reject);
    };
  }

  function stop() {
    worker?.terminate();
    worker = null;
    waiting.clear(); // their promises never settle; the session discards stale runs by token
  }

  start();

  return {
    run(input) {
      if (waiting.size) stop();
      start();
      if (!worker) return onMainThread(input);
      const id = ++seq;
      const w = worker;
      return new Promise((resolve, reject) => {
        waiting.set(id, { resolve, reject, input });
        w.postMessage({ id, input: JSON.stringify(input) });
      });
    },
    dispose() {
      stop();
      workerFailed = true;
    },
  };
}
