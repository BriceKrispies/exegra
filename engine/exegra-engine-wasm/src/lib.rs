//! WebAssembly build of Exegra's simulation engine: one export over
//! [`exegra_engine::run_input`], text in and text out.
//!
//! `run_input` takes the engine input JSON (format `exegra-sim-input`) and returns the trace
//! JSON. A refusal (input that is not JSON, not an engine input, or names something that does
//! not exist) is returned as `Err(JsError)`, which the generated JavaScript glue throws as an
//! `Error` carrying the engine's message. A run that fails part-way is not a refusal: the trace
//! records it with outcome `error`.
//!
//! The JavaScript side is `src/core/engine.js`; `npm run build:engine` builds this crate for
//! `wasm32-unknown-unknown` and runs `wasm-bindgen --target web` into `src/engine/pkg/`.

use wasm_bindgen::prelude::*;

/// Run an engine input to completion and return the trace as JSON text.
#[wasm_bindgen]
pub fn run_input(input: &str) -> Result<String, JsError> {
    exegra_engine::run_input(input).map_err(|message| JsError::new(&message))
}
