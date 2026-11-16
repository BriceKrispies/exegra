# Exegra simulation engine (Rust)

Exegra's simulation engine, and its only one: the library crate `exegra-engine` with the native binary `exegra-sim`,
and `exegra-engine-wasm`, the same library compiled to WebAssembly for the browser and Node. It reads one engine input
(format `exegra-sim-input`, version 1) and returns one trace, and is judged only by the golden conformance suite in
`tests/conformance/` (see `docs/simulation.md`, "Engine input and trace format"). The goldens were recorded with the
JavaScript engine this crate replaced; they stay as committed and are the reference.

## WebAssembly

`exegra-engine-wasm` is a `cdylib` with one export, `run_input(input: &str) -> Result<String, JsError>`: the engine
input JSON in, the trace JSON out. A refusal is an `Err(JsError)`, which the generated glue throws as a JavaScript
`Error` with the engine's message. Its `wasm-bindgen` dependency is pinned to `=0.2.122`, the version of the
`wasm-bindgen` CLI that generates the glue; the two must match.

From the repository root:

```sh
npm run build:engine
```

runs `cargo build --release --target wasm32-unknown-unknown -p exegra-engine-wasm` here and then
`wasm-bindgen --target web --out-dir src/engine/pkg` on the result (`tools/build-engine.js`). `src/core/engine.js`
loads `src/engine/pkg/` (synchronously in Node, asynchronously in a page or a Web Worker) and is the only module that
touches it.

## Native build

From this directory, with the MSVC toolchain:

```sh
cargo build --release
```

The binary is `target/release/exegra-sim` (`exegra-sim.exe` on Windows). It reads the input JSON on stdin and writes
the trace JSON on stdout. Input that cannot be run (not JSON, not an engine input, a scenario, behavior, event or
fault that does not exist) exits with status 1 and a message on stderr. A run that fails part-way is not a refusal:
the trace records it with outcome `error`.

The library's entry point is `exegra_engine::run_input(input_json: &str) -> Result<String, String>`, text in and text
out, so a host such as a WebAssembly wrapper is a thin layer over it.

Unit tests for the expression language and the value model sit next to the code (`cargo test`).

## Conformance

From the repository root:

```sh
node tools/conformance.js                                          # the WebAssembly engine, in-process
node tools/conformance.js --engine "engine/target/release/exegra-sim"   # the native binary
```

`tests/core/conformance.test.js` runs both: the WebAssembly engine always, the native binary when it is built.

The runner starts the binary once per golden, compares the parsed trace with the golden as JSON values (key order is
ignored, numbers compare as doubles) and reports the first difference of each mismatch. `--filter <text>` limits the
run to goldens whose `<source>/<name>` contains the text.

## Layout

The crate was ported from the JavaScript engine `src/core/sim.js`, since removed. The table maps what it had to what
the crate has.

| Former JavaScript | Rust | What |
|---|---|---|
| `src/core/expr.js`: `tokenize`, `parseExpr` | `src/expr.rs`: `tokenize`, `parse_expr` | Tokenizer and parser; the same grammar, precedence and parse error messages. |
| `src/core/expr.js`: `evalExpr`, `requireType`, `evaluate`, `exprRefs` | `src/expr.rs`: `eval_expr`, `require_type`, `evaluate`, `expr_refs` | Evaluator with double arithmetic, strict equality, short-circuiting and the same error messages. |
| `src/core/sim-input.js`: `sourceOf`, the input typedefs | `src/input.rs`: `SimInput::from_value`; `src/engine.rs`: `EngineSource` | The engine input, its format and version checks, and the entity view the engine reads. |
| `runInput` (formerly in `src/core/sim-input.js`) | `src/lib.rs`: `run_input`; `src/engine.rs`: `run` | Run an input to completion. |
| `src/core/sim.js`: `createSimulation` | `src/engine.rs`: `Simulation::new` | Creation checks, the initial configuration and the initial queue. |
| `src/core/sim.js`: `step`, `commit`, `responsibleOf`, `insertPending`, `resolverFor`, `guardHolds`, `valueOf` | `src/engine.rs`: `Simulation::step`, `deliver`, `commit`, `responsible_of`, `insert_pending`, `resolve`, `guard_holds`, `value_of` | One step: drop, delay, or delivery in two phases. |
| `src/core/sim.js`: `run`, `reset`, `trace` | `src/engine.rs`: `Simulation::run`, `reset`, `trace` | Run control and the trace. |
| `src/core/sim.js`: `deepCopy` | `src/value.rs`: `Value::deep_copy`; `src/trace.rs`: `Configuration::deep_copy` | Copies at the same points as the reference engine. |
| `src/core/sim.js`: `Configuration`, `TraceStep`, `Trace` typedefs | `src/trace.rs` | Trace records and their JSON form. |
| JavaScript values, `JSON.parse`, `JSON.stringify` | `src/value.rs` | Doubles, property order, reference identity of arrays and objects, `undefined`. |

## Matching JavaScript

- Numbers are doubles throughout. Input numbers are parsed to the nearest double (`serde_json` with
  `float_roundtrip`), and written as JavaScript writes them (shortest round-trip digits; integral values without a
  fraction).
- Objects keep JavaScript's property order (array-index keys first), so payload entries are evaluated in the order
  `Object.entries` gives.
- `==` on arrays and objects is reference identity, as `===` is: values are reference-counted, and copies are made
  exactly where the JavaScript engine called `deepCopy`.
- A field of the wrong JSON type in the input is refused rather than coerced; a validated model never produces one.
