// The Rust simulation engine (engine/exegra-engine) compiled to WebAssembly, bound by wasm-bindgen into
// src/engine/pkg/ (`npm run build:engine`). Node-only. It is no longer the engine Exegra runs
// (src/core/engine.js runs the Lean core); it stays as an independent implementation the tests
// compare the Lean engine against (tests/core/conformance.test.js), next to the native binaries
// (tools/differential.js).

import fs from 'node:fs';
import { createRequire } from 'node:module';

const WASM_URL = new URL('../src/engine/pkg/exegra_engine_wasm_bg.wasm', import.meta.url);
const GLUE = '../src/engine/pkg/exegra_engine_wasm.js';

/** @type {{run_input: (input: string) => string}|null} */
let glue = null;

/** Whether the Rust WebAssembly engine is built. */
export function rustEngineBuilt() {
  return fs.existsSync(WASM_URL);
}

/**
 * Run an engine input text on the Rust WebAssembly engine; returns the trace text, or throws with
 * the engine's refusal.
 * @param {string} inputText
 * @returns {string}
 */
export function runRustEngineText(inputText) {
  if (!glue) {
    const g = createRequire(import.meta.url)(GLUE);
    g.initSync({ module: fs.readFileSync(WASM_URL) });
    glue = g;
  }
  try {
    return /** @type {{run_input: (input: string) => string}} */ (glue).run_input(inputText);
  } catch (e) {
    throw new Error(e instanceof Error ? e.message : String(e));
  }
}
