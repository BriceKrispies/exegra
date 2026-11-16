# Simulation conformance suite

What a simulation engine is judged by: for each golden, the engine reads `<name>.input.json` (the engine input, see "Engine input and trace format" in `docs/simulation.md`) and must produce exactly `<name>.trace.json`. A Rust engine, or any other, is accepted when it reproduces every golden.

- `fixture/spec.jsonc`: a small specification, validated like any other (`node cli/exegra.js validate --project fixture --specs tests/conformance`), written to exercise every construct the engine implements.
- `goldens/<source>/<name>.input.json` and `.trace.json`: the recorded runs. Sources: `fixture` (the specification above), `exegra` (`specs/exegra/spec.jsonc`) and `multiplayer` (`tests/fixtures/multiplayer/spec.jsonc`). The names are `<scenario>` (the scenario with its own declared faults), `<scenario>--none` (no faults, when the scenario declares any) and `<scenario>--<fault>` (that one fault, when the scenario declares more than one).
- The goldens were recorded with the former JavaScript engine and are the reference the Rust engine is judged against. `node tools/record-goldens.js` writes goldens that do not exist yet with the current engine (`src/core/engine.js`) and refuses to overwrite an existing one, listing every existing golden the engine no longer reproduces; `node tools/record-goldens.js --force` rewrites them all (deterministic: two runs give identical files). Use `--force` only when the simulation semantics are meant to change, or a specification above changed, and review the diff.
- `node tools/conformance.js` checks the WebAssembly engine (through `src/core/engine.js`; build it with `npm run build:engine`) against every golden, from the input file alone. `node tools/conformance.js --engine "<command>"` starts the command once per golden, writes the input JSON to its stdin and reads the trace JSON from its stdout. Every mismatch is reported with the golden, the first differing step index and the JSON path of the first differing field; the exit code is non-zero on any mismatch or error. `--filter <text>` limits the goldens to those whose `<source>/<name>` contains the text.
- The Lean formal semantics (`formal/`, see "Formal semantics" in `docs/simulation.md`) is the definition the goldens and the engine are judged by: `tests/core/formal-semantics.test.js` checks its executable `exegra-lean` against every golden, and `tools/differential.js` compares it with the native engine on the goldens and on generated inputs.
- `tests/core/conformance.test.js` runs the WebAssembly engine against the goldens from the model and from the input alone, runs the native binary `engine/target/release/exegra-sim` against them when it is built (skipped with a message otherwise), and checks that the runner reports a difference at the right step and path.

## Constructs covered by the fixture

All goldens named below are in `goldens/fixture/`; a name with `--` is a variant of the scenario before it.

| Construct | Golden showing it |
|---|---|
| Guard over payload fields (`event.amount >= 100`) | `core-flow` (steps 0, 6, 10, 13) |
| Guard over another machine's variable and state (`ledger-machine.balance`, `ledger-machine.state`), and over `time` | `core-flow` (step 4, `gw-tick`) |
| `set` effects, including `before`/`after`, string concatenation, unary minus and a later effect reading an earlier `set` | `core-flow` (`led-credit`, `led-freeze`, `gw-tick`) |
| `emit` effects with `after` 0 and above, evaluated payload entries, literal payload entries (string expression, nested object and array copied as is) | `core-flow` (`gw-submit-large`, `gw-submit-small`, `led-credit`) |
| Transitions tried in declaration order, first match wins, guard false falls through to the next | `core-flow` (`gw-submit-large` against `gw-submit-small`) |
| `ignored` with reason `no-transition`, and `considered` ids | `core-flow` (step 17, frozen ledger) |
| `ignored` with reason `guard-false` | `core-flow` (step 11, `led-credit` and `led-freeze` both false) |
| An event no behavior handles | `unhandled-event`, `simultaneous-events` (step 1) |
| Simultaneous events: equal times ordered by sequence, input steps listed out of time order, an emitted event at the same time as queued ones | `simultaneous-events` |
| A run with no input: no steps, `quiescent` | `empty-run` |
| Fault `drop-event` with an `occurrence` | `faults-drop` (`drop-first-submit`) |
| Fault `drop-event` without an `occurrence`, and two drop faults on one step | `faults-drop` (`drop-all-tick`, `drop-second-tick` at step 6) |
| Drop acts before delay when both match | `faults-combined` (step 0) |
| Fault `delay-event`, with an `occurrence` | `faults-delay` (`delay-first-submit`, step 0) |
| Fault `delay-event` without an `occurrence`, and a delayed event delayed again by another fault, but never twice by the same one | `faults-delay` (`delay-tick-3`, `delay-tick-2`, steps 4 to 10) |
| Fault `enable-transition` with a `faultOnly` transition (`enabled` record, tried before the transition it competes with) | `fault-enable-transition`; the same run without the fault, where the transition is not considered, is `fault-enable-transition--none` |
| Fault `disable-transition`: skipped and the next transition fires, `disabled` recorded although another fired | `fault-disable-guard-true` (step 2) |
| Fault `disable-transition`: no other transition, `ignored` with reason `disabled` | `fault-disable-sole` (step 3) |
| A disable fault whose transition has a false guard records nothing (the guard is evaluated first) | `fault-disable-guard-false` (step 2) |
| Fault `inject-event`, source `fault`, `injected` record | `fault-inject` (step 5) |
| Several fault kinds in one run | `faults-combined` |
| The step limit stops a run with events pending | `step-limit-reached` (`step-limit`) |
| The queue empties exactly on the last permitted step (`quiescent`, not `step-limit`) | `step-limit-exact` |
| No `maxSteps`: the default limit 1000 appears in the input | `default-step-limit` |
| A guard that is not a boolean stops the run | `error-guard-not-boolean` |
| Type error | `error-type` |
| Division by zero | `error-division-by-zero` (after a successful step, with an event left pending) |
| Modulo by zero | `error-modulo-by-zero` |
| Unknown reference, in a guard | `error-unknown-reference-guard` |
| Unknown reference, in an effect after an earlier effect set a variable (nothing of the step is kept) | `error-unknown-reference-effect` |
| The same guard with the payload field present | `payload-field-present` |
| Every operator, precedence, associativity of `=>`, short-circuiting, string concatenation, strict equality across types, `null`, a number that is not exact (`0.1 + 0.2`), `time` in an effect | `expression-showcase` |

The `exegra` and `multiplayer` goldens (the shipped self-specification and the multiplayer example) are larger runs; they show the engine on specifications written by hand, including the faults that change a verdict (`early-ack`, `validation-fails`, `disk-changed-externally`).

## Not covered

- Parse errors in expressions, `set` of a name that is not a variable, an `emit` of a name that is not an event, an effect that is neither `set` nor `emit`, and an effect without `to`: a validated specification cannot contain them, so no golden can.
- Creation errors (an input naming a scenario, behavior, event or fault that does not exist): they are refusals, not traces.
- Results that are not finite numbers: JSON cannot carry them.
