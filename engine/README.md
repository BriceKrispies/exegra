# Exegra simulation engine (Rust)

The Rust oracle of Exegra's engine: the library crate `exegra-engine` with the native binary `exegra-sim`, and
`exegra-engine-wasm`, the same library compiled to WebAssembly. Exegra runs the Lean engine (`formal/`); this crate is
kept as an independent implementation that `tools/differential.js` compares with it. It reads one engine input
(format `exegra-sim-input`, version 2) and returns one trace, and is judged by the golden conformance suite in
`tests/conformance/` (see `docs/simulation.md`, "Engine input and trace format"). A version-1 input is refused:
format 1 was removed (WG-5681).

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

| Module | What |
|---|---|
| `src/value.rs` | JSON-like values with JavaScript semantics: doubles, property order, reference identity, `undefined`. |
| `src/expr.rs` | The expression language: tokenizer, parser, evaluator, and the integer rules of the behaviour calculus's fragment (`eval_expr_mode`). |
| `src/random.rs`, `src/workload.rs` | Seeded streams and workloads of format 2. |
| `src/v2.rs` | Format 2: decoding, instances, routes, resources, links, timers, faults, the run and the trace. Reads of other machines and aggregates see the start of the step; an input in the calculus's fragment computes with integers. |
| `src/lib.rs` | `run_input`: the format and version check, then `v2::run`. |

## Matching JavaScript

- Numbers are doubles throughout. Input numbers are parsed to the nearest double (`serde_json` with
  `float_roundtrip`), and written as JavaScript writes them (shortest round-trip digits; integral values without a
  fraction).
- Objects keep JavaScript's property order (array-index keys first), so payload entries are evaluated in the order
  `Object.entries` gives.
- `==` on arrays and objects is reference identity, as `===` is: values are reference-counted, and copies are made
  exactly where the JavaScript engine called `deepCopy`.
- A field of the wrong JSON type in the input is refused rather than coerced; a validated model never produces one.
