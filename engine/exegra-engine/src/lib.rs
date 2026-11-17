//! Exegra's simulation engine: a deterministic discrete-event simulation of the state machines
//! a scenario names. It reads one engine input (format `exegra-sim-input`, version 1) and
//! returns one trace, exactly as the golden conformance suite in `tests/conformance/` records
//! (the goldens were recorded with the former JavaScript engine, `src/core/sim.js`).
//!
//! - [`value`]: JSON-like values with JavaScript semantics (doubles, property order, identity).
//! - [`expr`]: the expression language (`src/core/expr.js`).
//! - [`input`]: the engine input (`src/core/sim-input.js`).
//! - [`trace`]: configurations, steps and traces, and their JSON form.
//! - [`engine`]: the simulation (ported from the former `src/core/sim.js`).
//! - [`random`], [`v2`]: format 2 (WG-4664): seeded streams, instances and resources.
//!
//! [`run_input`] is the whole engine as one text-to-text function, so a host (the native binary,
//! the WebAssembly crate `exegra-engine-wasm`) is a thin layer over it.

#![forbid(unsafe_code)]

pub mod engine;
pub mod expr;
pub mod input;
pub mod random;
pub mod trace;
pub mod v2;
pub mod value;
pub mod workload;

pub use engine::{EngineSource, Simulation};
pub use input::SimInput;
pub use trace::Trace;

/// Run an engine input to completion. Returns the trace as JSON text, or the refusal message
/// for input that is not JSON, not an engine input, or names something that does not exist.
/// Failures during the run are not refusals: they are recorded in the trace (outcome `error`).
pub fn run_input(input_json: &str) -> Result<String, String> {
    let text = input_json.strip_prefix('\u{feff}').unwrap_or(input_json);
    let value = value::parse_json(text)?;
    // Version 2 (WG-4664) is run by its own semantics; every other input as before.
    if let Some(root) = value.as_object() {
        if root.get("format").and_then(value::Value::as_str) == Some("exegra-sim-input")
            && matches!(root.get("version"), Some(value::Value::Number(x)) if *x == 2.0)
        {
            return v2::run(root);
        }
    }
    let input = SimInput::from_value(&value)?;
    let trace = engine::run(&input)?;
    Ok(trace.to_json())
}
