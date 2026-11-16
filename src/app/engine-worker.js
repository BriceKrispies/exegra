// Web Worker that runs the simulation engine off the main thread. It loads the same WebAssembly
// module as the page, through src/core/engine.js.
//
// Message in:  {id, input}            input is the engine input as JSON text
// Message out: {id, ok: true, trace}  trace is the trace as JSON text
//              {id, ok: false, error} the engine refused the input, or could not be loaded

import { initEngine, runEngineText } from '../core/engine.js';

const ready = initEngine();
ready.catch(() => { /* reported with the first run */ });

self.onmessage = async (/** @type {MessageEvent} */ e) => {
  const { id, input } = e.data ?? {};
  try {
    await ready;
    self.postMessage({ id, ok: true, trace: runEngineText(input) });
  } catch (err) {
    self.postMessage({ id, ok: false, error: err instanceof Error ? err.message : String(err) });
  }
};
