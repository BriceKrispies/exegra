//! Exegra's simulation engine, kept as a differential oracle of the Lean engine: a deterministic
//! discrete-event simulation of the state machines a scenario names. It reads one engine input
//! (format `exegra-sim-input`, version 2) and returns one trace, exactly as the golden conformance
//! suite in `tests/conformance/` records. Format 1 was removed (WG-5681).
//!
//! - [`value`]: JSON-like values with JavaScript semantics (doubles, property order, identity).
//! - [`expr`]: the expression language (`src/core/expr.js`).
//! - [`random`], [`workload`], [`v2`]: format 2: seeded streams, instances, resources, workloads.
//!
//! [`run_input`] is the whole engine as one text-to-text function, so a host (the native binary,
//! the WebAssembly crate `exegra-engine-wasm`) is a thin layer over it.

#![forbid(unsafe_code)]

pub mod expr;
pub mod random;
pub mod v2;
pub mod value;
pub mod workload;

/// The refusal of a version-1 engine input (formal/Exegra/Format2B.lean, `formatOneGone`).
pub const FORMAT_ONE_GONE: &str =
    "Version 1 engine inputs are no longer run: format 1 was removed (WG-5681); derive a version-2 input.";

/// The refusal of JSON that is not an engine input (formal/Exegra/Format2B.lean, `notAnInput`).
pub const NOT_AN_INPUT: &str =
    "Not an engine input: \"format\" must be \"exegra-sim-input\" and \"version\" 2.";

/// Run an engine input to completion. Returns the trace as JSON text, or the refusal message
/// for input that is not JSON, not a version-2 engine input, or names something that does not
/// exist. Failures during the run are not refusals: they are recorded in the trace (outcome
/// `error`).
pub fn run_input(input_json: &str) -> Result<String, String> {
    let text = input_json.strip_prefix('\u{feff}').unwrap_or(input_json);
    let value = value::parse_json(text)?;
    let Some(root) = value.as_object() else {
        return Err(NOT_AN_INPUT.to_string());
    };
    if root.get("format").and_then(value::Value::as_str) != Some("exegra-sim-input") {
        return Err(NOT_AN_INPUT.to_string());
    }
    match root.get("version") {
        Some(value::Value::Number(x)) if *x == 2.0 => v2::run(root),
        Some(value::Value::Number(_)) => Err(FORMAT_ONE_GONE.to_string()),
        _ => Err(NOT_AN_INPUT.to_string()),
    }
}
