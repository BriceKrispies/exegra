# Simulation

The simulation engine executes the state machines (`behavior` entities) that a `scenario` names. It is the Lean 4 semantics in `formal/` itself (see [Formal semantics](#formal-semantics)), the definition of the behavior language and the code its theorems are about: compiled to WebAssembly it runs in the browser and in Node behind the facade `src/core/engine.js`, called as the function `engine.run` through the Lean call boundary (`src/core/lean.js`, `formal/Exegra/Api.lean`), and the native binary `exegra-lean` runs the same C from the command line. It is pure and deterministic: no clock, no randomness, no I/O, and no host-language evaluation. The binding interface is in [module-contracts.md](module-contracts.md). The Rust crate `engine/exegra-engine`, which was the engine until WG-4792, stays as a differential oracle: the tests compare it with the Lean engine as WebAssembly and as the native `exegra-sim`.

## Building and loading the engine

`npm run build:formal-wasm` (`tools/build-formal-wasm.js`) builds the Lean core into `src/engine/lean/` (`exegra-lean.mjs`, `exegra-lean.wasm`, `build-info.json`; generated, not committed) from pinned inputs: the Lean toolchain of `formal/lean-toolchain` (`lake build` emits the C of every Exegra module; the toolchain's `lean -c` emits the C of the 792 Init/Std modules that `Exegra.Api` imports), the Lean runtime sources at the toolchain's tag (verified by commit) with `formal/wasm/patches/*.patch` applied, libuv v1.48.0 (verified by commit), and emscripten 7.0.0 (emsdk at a pinned commit). The target is wasm64 (Memory64) only, so the C the 64-bit compiler emits runs under the assumptions it was generated for; Memory64 runs in Node 24, Chrome 133+ and Firefox 134+, and **stable Safari is not supported until it ships Memory64** (decision 2026-11-18). Downloads and checkout-independent objects are cached in `%LOCALAPPDATA%\exegra\cache\formal-wasm` (Windows), `$XDG_CACHE_HOME/exegra/formal-wasm` or `~/.cache/exegra/formal-wasm` (`EXEGRA_CACHE_DIR` overrides, `EMSDK` names an existing emsdk of the pinned version); the Exegra objects live in `formal/.lake/wasm/`. Parallelism is `--jobs N` or `EXEGRA_BUILD_JOBS`, default 3. A rebuild after a change to `formal/` recompiles only the changed Exegra modules and relinks. `npm run dev`, `build`, `test`, `test:browser`, `generate` and `verify` run it first, after `npm run build:engine`, which still builds the Rust engine into `src/engine/pkg/` for the tests that compare against it.

**Cost.** The Lean engine is about ten times slower than the Rust engine it replaced. Measured 2026-11-18 (Node 24, Windows 10, mean of 50 runs after a warm-up): `live-session` (93 KB input) 20.5 ms against 1.95 ms for the Rust WebAssembly engine, `app-start-and-open` (64 KB) 23.7 ms against 2.4 ms; loading and initializing the module takes about 120 ms once per process. The module is 2.8 MB of wasm. The gated queueing and pool fixtures (`EXEGRA_FIXTURES=1`, hundreds of long runs) use the native `exegra-lean`, compiled from the same C, when it is built. The first build from an empty cache took 22 minutes with 3 jobs on the development machine (most of it generating and compiling the C of 792 Init/Std modules, cached afterwards); a build with nothing changed takes about 9 s (`lake build` and the up-to-date check).

`src/core/engine.js` is the one place the rest of Exegra touches the engine:

- `initEngine()` loads the Lean core (`initLean()` of `src/core/lean.js`). In Node it is synchronous (the module bytes are read with `node:fs`, reached through `process.getBuiltinModule`, and the emscripten loader, built for synchronous instantiation, is `require`d), and `runEngine` loads the core on first use if nobody called it. In a page or a worker it is asynchronous and must be awaited; the application awaits it before opening a project (`src/app/main.js`).
- `runEngine(input)` runs an engine input and returns the parsed trace; `runEngineText` takes and returns JSON text. A refusal throws an `Error` with the engine's message.
- `runScenario(model, id, {faults})` derives the input with `simulationInput` and runs it.
- `createTraceCursor(trace)` (and `createSimulation(model, id, {faults})`, which runs the scenario first) is a stepwise view of a finished trace: `step()`, `run()`, `reset()`, `steps`, `outcome`, `config`, `trace()`.

If the core is not built, `initEngine` and `runEngine` throw a message that says to run `npm run build:formal-wasm`; claim checks over scenarios then report that the scenario could not be run.

## Model of execution

A scenario lists behaviors, timed input `steps` (`at`, `event`, optional `payload`) and optionally active `faults` and `maxSteps` (default 1000). A simulation holds:

- a **configuration**: logical `time`, one machine per behavior (`state` and `vars`, initialised from `initial` and `variables`), and a `pending` queue;
- the queue, ordered by `(time, seq)`. `seq` grows monotonically, so events with equal time are delivered in the order they were scheduled. The scenario's input steps are queued first, in declaration order, then events injected by faults.

Each **step** takes the head of the queue, sets `time` to its time and delivers it. Time is logical ticks only. A step is one of three kinds:

| Kind | When | Effect |
|---|---|---|
| `drop` | a matching `drop-event` fault | The event is discarded and nothing fires. |
| `delay` | a matching `delay-event` fault that has not yet delayed this entry | The event is re-queued `by` ticks later, once per fault. |
| `deliver` | otherwise | Each behavior chooses a transition; effects run. |

**Delivery has two phases.** Phase 1 reads the configuration as it was at the start of the step. For every behavior in scenario order, the first transition in declaration order whose `from` equals the machine's state, whose `on` equals the event, and whose guard is true, wins. A `faultOnly` transition is eligible only when an `enable-transition` fault targets it; a transition targeted by a `disable-transition` fault is skipped, and remembered as the reason when nothing else fires. Phase 2 runs the winners' effects behavior by behavior, writing to the next configuration: `set` assigns a variable, `emit` queues an event at `time + after` with an evaluated payload. A transition then moves its machine to its `to` state. Behaviors with no winner are recorded in `ignored` with a reason: `no-transition`, `guard-false` or `disabled`. Declaration order is therefore part of the model: swapping two enabled, unguarded transitions on one event and state changes which fires. `exegra validate` warns about such a pair (`transition.order-decides`) and a trace claim's scope names the pair when it decided a verdict ([claims-and-evidence.md](claims-and-evidence.md)).

A guard must evaluate to a boolean. Any evaluation error is recorded on the step (`error.message`), the step is not committed to the configuration and the run ends with outcome `error`.

**Outcome** of a run: `running` while events are pending, `quiescent` when the queue is empty, `step-limit` when `maxSteps` steps were taken with events still pending, `error` after a failed step.

## Faults

| Kind | Parameters | Meaning |
|---|---|---|
| `drop-event` | `event`, optional `occurrence` | Deliveries of the event are lost. `occurrence` counts delivery attempts (1-based); omitted means every one. |
| `delay-event` | `event`, `by`, optional `occurrence` | The event arrives `by` logical ticks late. |
| `enable-transition` | `transition` | A `faultOnly` transition becomes available (a defect to exhibit). |
| `disable-transition` | `transition` | A transition cannot fire. |
| `inject-event` | `event`, `at`, optional `payload` | An event nobody sent is queued at time `at`. |
| `duplicate-event` | `event`, optional `by`, optional `occurrence` | Format 2. The event is delivered, and delivered again `by` later (default 0): an at-least-once message redelivered ([semantics.md](semantics.md#faults-the-runtime-can-produce)). |
| `lose-event` | `event`, optional `occurrence` | Format 2. As `drop-event`, recorded `lost`: an at-most-once message lost between its sender's commit and dispatch. |
| `retry-event` | `event`, `attempts`, optional `occurrence` | Format 2. As `delay-event`, by the retry backoff after `attempts` failed dispatches (`system.generation.retry`), recorded `retried`. |

Faults come from the scenario's own `faults` list, or from the list the caller passes (`runScenario(model, id, {faults})`), which replaces it. The UI, `exegra simulate --faults a,b` and claim checks all use that parameter. Each step records which faults acted and how (`dropped`, `delayed`, `enabled`, `disabled`, `injected`; format 2 also `duplicated`, `lost`, `retried`).

## Traces

`runScenario(model, id, {faults})` returns a `Trace`: scenario id, faults, `initial` configuration, `steps`, `outcome` and `final`. A step records its index, time, kind, the event (id, payload, source: scenario step, fault or transition), the transitions that `fired` (with `sets` before and after, and `emitted` events), `ignored`, `faults`, the entities `responsible` for the step, and the full configuration after it. Traces are deep-copied snapshots: later steps never change earlier ones. `exegra trace <id> --out file.json` writes a trace as stable JSON.

The engine always runs a scenario to the end. A finished trace can then be stepped, reset, or revealed to the end through `createTraceCursor`; stepping one event at a time gives the same trace as `run()`, and identical inputs give deep-equal traces (tests in `tests/core/sim.test.js`).

## Engine input and trace format

A simulation engine is judged by two JSON documents, both **format version 2** (format 1 was removed, WG-5681): the *engine input*, which `src/core/sim-input.js` derives from a validated model for one scenario and fault set, and the *trace* the engine must return. The golden conformance suite in `tests/conformance/` pins both for every scenario of three specifications; `node tools/conformance.js` checks an engine against it (see `tests/conformance/README.md`). An engine is accepted when it reproduces every golden trace from the matching input, and nothing else is read.

Conventions for both documents:

- They are JSON. The order of keys in an object has no meaning (the goldens are written with sorted keys, one space of indent and a final newline, only so that they diff well). **The order of elements in an array is part of the format**, wherever the text below says so.
- Numbers are JSON numbers, compared as numbers (`3` and `3.0` are equal). An input the behaviour calculus covers holds only integers, and its arithmetic is exact integer arithmetic with the rules of [semantics.md](semantics.md#values-numbers-and-time): an untyped result outside `-(2^53 - 1) .. 2^53 - 1` and an untyped `/` with a remainder are errors, and a number that is not an integer is refused. An input outside the calculus runs the legacy interpreter (its trace says `"semantics": "legacy"`), whose untyped arithmetic is that of doubles, so `0.1 + 0.2` is `0.30000000000000004` there; a result that is not finite cannot be written as JSON and is outside the contract.
- Strings are compared code unit by code unit; there are no escapes in expression string literals.
- Every value in a trace is a copy: later steps never change earlier ones, and no two places share a value. Values a trace holds are `boolean`, `number` or `string`, or the JSON value that an effect's non-string literal `to` or `payload` entry copies verbatim.

### Engine input

`simulationInput(model, scenarioId, faults?)` returns the input. `faults`, when given, replaces the scenario's own fault list, as `runScenario(model, id, {faults})` does. The input is all the engine ever reads: `runScenario` is `runEngine(simulationInput(...))`, so running from a model and running from a committed input file are the same path.

| Field | Meaning |
|---|---|
| `format` | The string `"exegra-sim-input"`. |
| `version` | The number `1`. An engine refuses any other value. |
| `scenario.id` | The scenario's id; it becomes the trace's `scenarioId`. |
| `scenario.steps` | The scenario's input events in declaration order: `{at, event, payload}`. `at` is the logical time, `event` an id from `events`, `payload` an object (`{}` when the scenario gave none). Payload values are literals: they are never evaluated, even when a string. The array order is the scheduling order, not time order. |
| `scenario.faults` | The active fault ids, in order, without repeats. Each is declared in `faults`. |
| `scenario.stepLimit` | The step limit: the scenario's `maxSteps`, or `1000` when it has none. |
| `behaviors` | The behaviors the scenario runs, **in scenario order** (this is the order of every per-behavior loop in a step). |
| `behaviors[].id` | The behavior's id; the key of its machine in a configuration. |
| `behaviors[].subject` | The component the behavior describes. Only used to build `responsible`. |
| `behaviors[].initial` | The initial state id. |
| `behaviors[].variables` | `{name, initial}` in declaration order. `initial` is a literal copied into the initial configuration. |
| `behaviors[].types` | Optional, implementation-level behaviors only: `{path: type}`, the declared type of each reference the behavior's expressions read (`time`, variables, `event.<field>`), lowered to `u8` … `i64`, `option` or another name (untyped). Integer types make arithmetic checked; an absent `option` reads as `null` ([semantics.md](semantics.md#values-numbers-and-time)). The Rust engine ignores it. |
| `behaviors[].states` | The ids of the behavior's states. Informational: the engine does not read it, and no trace contains it. |
| `behaviors[].transitions` | The behavior's transitions in **declaration order** (the order in which they are tried): `{id, from, to, on, guard, effects, faultOnly}`. |
| `transitions[].guard` | The guard expression as a string, or `null` when there is none. |
| `transitions[].effects` | The effects, in order. `{set, to}` assigns the variable `set` the value of `to`. `{emit, after?, payload?}` queues the event `emit`, `after` logical ticks (default `0`) later, with `payload` (an object, default `{}`). For `to` and for each top-level value of an emit `payload`: a string is an expression, any other JSON value a literal (a nested object or array is copied as it is; its strings are not evaluated). |
| `transitions[].faultOnly` | `true` when the transition may only fire while an `enable-transition` fault targets it. |
| `events` | Every event id of the model, as `{id}`. The engine only checks that an event named by a step, an emit effect or an injected fault is in this list. |
| `faults` | The active faults, in `scenario.faults` order: `{id, kind, ...}` with the fields of the kind that the engine reads: `event` (`drop-event`, `delay-event`, `inject-event`), `transition` (`enable-transition`, `disable-transition`), `occurrence` (optional; `drop-event`, `delay-event`), `by` (`delay-event`), `at` and `payload` (`inject-event`; payload optional). |

The input holds nothing else: no names, descriptions, variable types, projections or layout. Two calls of `simulationInput` on the same model give identical documents.

### Trace

A trace is what `runScenario(model, id, {faults})` and `runEngine(input)` return, what `exegra_engine::run_input` returns as text, and what `exegra-sim` writes.

| Field | Meaning |
|---|---|
| `scenarioId` | The scenario's id. |
| `faults` | The active fault ids, in order, without repeats (`scenario.faults` of the input). |
| `initial` | The configuration before the first step. |
| `steps` | One entry per step taken, in order; see below. Empty when nothing was queued. |
| `outcome` | `quiescent`, `step-limit` or `error`. (`running` exists only on a stepwise view whose steps are not all revealed yet.) |
| `final` | The configuration after the last step; for `error`, the configuration before the failing step. |

**Configuration**: `{time, machines, pending}`.

- `time`: the logical time of the last delivered event, `0` initially.
- `machines`: one entry per behavior, keyed by behavior id: `{state, vars}`, with `state` a state id and `vars` an object from variable name to value. Initially the behavior's `initial` and the variables' `initial` values.
- `pending`: the queue, ordered by `(time, seq)`; each entry is `{seq, time, event, payload, source}`. `seq` is the number assigned when the entry was queued, and `source` records where it came from:
  - `{kind: 'scenario', step: i}`: input step `i` of `scenario.steps`;
  - `{kind: 'fault', fault}`: an `inject-event` fault;
  - `{kind: 'transition', transition, behavior}`: an `emit` effect (the ids of the transition and of its behavior).

**Queue and sequence numbers.** Initially the scenario's steps are queued in array order with `seq` `0, 1, 2, ...`, then the active `inject-event` faults in `faults` order with the next numbers (an injected event's time is the fault's `at`, a step's the step's `at`). An entry is inserted after every entry whose time is less than or equal to its own, so entries with equal times are delivered in the order they were queued. Every later entry gets the next number: a delayed copy of an event, and each `emit` in the order the effects run (behaviors in scenario order, effects in declaration order). Numbers are never reused.

**Step.** A step takes the first queue entry (the *head*), sets the configuration time to the head's time and handles it. Fields:

| Field | Meaning |
|---|---|
| `index` | Position in `steps`, from `0`. |
| `time` | The head's time. |
| `kind` | `deliver`, `drop` or `delay` (see below). |
| `event` | `{id, payload, seq, source}`: the head's own fields. |
| `fired` | Transitions that fired, at most one per behavior, in scenario order; empty for `drop`, `delay` and a failed step. Each is `{behavior, transition, from, to, guard, sets, emitted}`. `guard` is the guard string or `null`. `sets` lists `{variable, before, after}` in effect order, one per `set` effect (also when the value did not change). `emitted` lists `{event, time, seq, payload}` in effect order: the queue entries the `emit` effects created. |
| `ignored` | The behaviors with no firing transition, in scenario order: `{behavior, reason, considered}`. `considered` lists the ids of the transitions that matched the state and the event and were eligible, in declaration order (a `faultOnly` transition that no active fault enables is not eligible). `reason` is `disabled` when a transition would have fired but a `disable-transition` fault stopped it, else `guard-false` when a considered transition's guard was false, else `no-transition`. Empty for `drop`, `delay` and a failed step. |
| `faults` | The faults that acted in this step, `{fault, effect}` in the order they acted. `effect` is `dropped`, `delayed`, `injected` (first, when the head came from an `inject-event` fault), `disabled` (one entry per disabling fault of a transition whose guard held, in the order the transitions were tried, also when another transition then fired) or `enabled` (the enabling faults of a `faultOnly` transition that fired, after the `disabled` entries of the same behavior). |
| `responsible` | Ids that explain the step, without repeats, in this order: the event id; for each fired transition its id, its behavior's id and its behavior's `subject`; then the ids of the faults in `faults`. |
| `config` | The configuration after the step (for a failed step, see Errors). |
| `error` | Present only on a failed step: `{message}`. |

**Handling the head.** The *attempt* number of an event is how many entries with that event id the run has taken from the queue so far, counting this one (a delayed event counts again each time it is taken; a failed step counts too). In this order:

1. **Drop.** If any `drop-event` fault has the head's event and either no `occurrence` or an `occurrence` equal to the attempt number, the step is `drop`: the entry is discarded, every such fault is recorded as `dropped` (in `faults` order), and nothing else happens.
2. **Delay.** Otherwise the first `delay-event` fault (in `faults` order) that matches in the same way and has not already delayed this entry or one it was copied from makes the step `delay`: a copy of the entry is queued at `time + by` with a new `seq` and the same event, payload and `source`, and the fault is recorded as `delayed`. The copy remembers every fault that delayed it or its ancestors, so each fault delays an event at most once, but several faults can delay it in turn.
3. **Deliver.** Otherwise the step is `deliver`, in two phases.
   - *Phase 1, choice.* For each behavior in scenario order, its transitions are tried in declaration order, reading the configuration as it was before the step. A transition is skipped unless `from` equals the machine's state and `on` equals the event. If it is `faultOnly` and no active `enable-transition` fault targets it, it is skipped. Otherwise it is *considered*. Its guard (if any) is evaluated with the head's payload and time; if false, the transition is skipped (reason `guard-false`). If a `disable-transition` fault targets it, it is skipped too (reason `disabled`, one `disabled` record per such fault). Otherwise it wins and the behavior's scan stops. A behavior without a winner gets an `ignored` entry.
   - *Phase 2, effects.* For each winner, in scenario order, the effects run in order on the **next** configuration, which behaviors share. A `set` replaces the variable's value and records `before` and `after`. An `emit` queues an entry at `head.time + after` with the evaluated payload and source `{kind: 'transition', ...}`. Expressions read the next configuration as it is at that moment, so a later effect sees an earlier `set`, and a later behavior sees the variables **and the state** that an earlier winner already wrote (a behavior's state is written after its own effects). After its effects the machine moves to the transition's `to` state.

**Expression scope.** A reference is a dotted path. `time` is the head's time (the same in guards and effects). A bare name is a variable of the transition's own behavior. `event.<field>` is a field of the delivered payload. `<behaviorId>.state` is the state id of a behavior of the run, and `<behaviorId>.<name>` one of its variables. Anything else, and any name with no value, is an unknown reference. Guards read the configuration from before the step, effects the next configuration (above). The expression language is that of `src/core/expr.js`:

- Literals: numbers (`12`, `0.5`; no sign and no exponent), strings in `'` or `"` (the text up to the next matching quote, no escapes), `true`, `false`, `null`. Names may contain inner hyphens (`ledger-machine.balance`), so a binary minus needs spaces around it (`a - b`); `-a` and `a - -b` are fine.
- Precedence, lowest first: `=>` (right-associative), `||`, `&&`, `==` `!=`, `<` `<=` `>` `>=`, `+` `-`, `*` `/` `%`, unary `!` `-`. All binary operators except `=>` are left-associative. Parentheses group.
- `==` and `!=` are strict equality of any two values (values of different types are never equal; two `null` are equal). `<` `<=` `>` `>=` `-` `*` `/` `%` and unary `-` need numbers; `+` needs two numbers or two strings (concatenation); `!` and the operands of `&&` `||` `=>` need booleans. `/` and `%` by `0` are errors; `%` is the remainder of doubles with the sign of the dividend.
- `&&`, `||` and `=>` short-circuit: the right operand is not evaluated, and not type-checked, when the left one decides (`false && x`, `true || x`, `false => x`).
- A guard must evaluate to a boolean.

**Errors.** A failure while handling a delivery (an expression error, or one of the cases below) does not abort the program: the step is recorded with `kind: 'deliver'`, the head's `index`, `time` and `event`, `fired`, `ignored` and `faults` empty, `responsible` equal to `[event id]`, `error: {message}`, and `config` equal to the configuration **before** the step (the failed head is still in `pending` and `time` is unchanged, so nothing the step started is kept). The run ends with outcome `error` and `final` is that same configuration. The messages are part of the contract, since they are compared:

| Source | `message` |
|---|---|
| Wrong type | `Operator "<op>" needs a <boolean or number>, got <null, boolean, number, string or object>` (`<op>` is the operator; `!` and `-` for the unary ones) |
| Division | `Division by zero` (for `/` and `%`) |
| Unknown reference | `Unknown reference "<path>"` (the dotted path) |
| Guard type | `Guard "<guard>" of transition "<id>" did not evaluate to a boolean.` |
| `set` of a name that is not a variable | `Effect sets "<name>", which is not a variable of "<behavior>".` |
| Effect without a value | `Effect has no value.` |
| `emit` of a name that is not an event | `Effect emits "<name>", which is not an event.` |
| Effect that is neither `set` nor `emit` | `Malformed effect in transition "<id>".` |
| Expression that does not parse | `Expression "<source>": <parser message>`; parser messages: `Unterminated string literal`, `Unexpected character '<c>'`, `Unexpected end of expression`, `Unexpected "<token>"`, `Expected a name after "."`, `Expected ")"` |

A validated model cannot produce the last five rows; the first four are what the conformance fixture exercises.

**Outcome and the step limit.** After each committed step the outcome is `quiescent` when the queue is empty, otherwise `step-limit` when the number of steps taken has reached `stepLimit`, otherwise the run goes on. So a run that empties the queue on exactly the last permitted step is `quiescent`, and a `step-limit` run always has entries in `final.pending`. A failed step ends the run as `error` whatever the limit. A run whose queue is empty to begin with has no steps and is `quiescent`. Drop and delay steps count as steps. (A limit of `0` or less still takes one step if anything is queued.)

**Creation errors.** An input that names a scenario that is not one, a behavior that is not one, an event that is not an event (in a step or an `inject-event` fault) or a fault that is not one is not a trace: `simulationInput` refuses it before any engine runs (`Scenario "<id>" lists "<b>", which is not a behavior.` and its siblings in `src/core/sim-input.js`), and the engine refuses such an input too. The goldens contain none, since the specifications they come from validate.

## Formal semantics

**The Lean semantics in `formal/` is the definition of the behavior language.** The prose above, the goldens and the Rust engine describe the same language; where they disagree, the Lean definition decides. It is a Lake project (toolchain pinned in `formal/lean-toolchain`, Lean's standard library only, no Mathlib):

| Module | Defines |
|---|---|
| `formal/Exegra/Number.lean` | Correctly rounded decimal-to-double conversion, `fmod` (the `%` of doubles), and JavaScript's number-to-string. |
| `formal/Exegra/Value.lean` | Values (IEEE `Float`, string, boolean, null, arrays, objects with JavaScript property order), strict equality, `typeof`, and object identity: arrays and objects carry an identity, a deep copy gives fresh ones, so `==` on them is reference identity as in the engine. |
| `formal/Exegra/Json.lean` | JSON reading and writing with `JSON.parse` and `JSON.stringify` semantics (property order kept, numbers rounded once). |
| `formal/Exegra/Expr.lean` | The expression language: tokenizer, parser and evaluator with the engine's error texts and order of evaluation. |
| `formal/Exegra/Input.lean`, `Trace.lean` | What the version-2 input and trace share with the removed format 1: variable declarations, fault occurrences, decoding helpers, the records of a fired transition, an ignored behaviour and a fault. |
| `formal/Exegra/Format2.lean` | The version-2 input and trace, their decoding and encoding with the engine's refusals, and the legacy interpreter `V2.traceOf`, which runs every construct of format 2. |
| `formal/Exegra/Core/Behav.lean`, `BehavExec.lean` | The behaviour calculus: typed systems, configurations, the step relation `Step` and `Sys.lts`, and the deterministic scheduler `Exec.step` with its draws; the theorems about them (below). |
| `formal/Exegra/Core/BehavRename.lean`, `BehavCheck.lean` | Renaming of machines, and the calculus explorer `exploreB` with the temporal forms and their monitors. |
| `formal/Exegra/Elab.lean` | The elaborator from a version-2 input to the calculus ([Elaboration](#elaboration-into-the-behaviour-calculus)). |
| `formal/Exegra/Format2B.lean` | The dispatch: `traceOfB`, the fold of `Exec.step` written as a version-2 trace, and `V2.runInput`, which runs `traceOfB` for an elaborated input and the legacy interpreter for an input outside the fragment; `Exegra.runAnyValue`, which refuses version 1. |
| `formal/Exegra/Impl/` | The implementation the application runs, proved equal to the definition (below): `Json.lean` (an in-place JSON writer), `Semantics.lean` (the definition with that writer) and `Refinement.lean` (the refinement theorems). |
| `formal/Exegra/Search.lean`, `ProveB.lean` | The generic breadth-first search, and what `exegra prove` needs: claim invariants over calculus states, the temporal check over the product with a monitor, the verdicts a generated proof file states, and the `explore` and `temporal` protocols (see [Exhaustive exploration in Lean](#exhaustive-exploration-in-lean-exegra-prove)). |
| `formal/Main.lean` | `exegra-lean`: one engine input JSON on stdin, one trace JSON on stdout, refusals on stderr with exit status 1, the protocol of `exegra-sim`. `exegra-lean --legacy` runs the legacy interpreter whatever the elaborator says, `exegra-lean elab` prints the elaborator's verdict, and `exegra-lean explore` and `temporal` read an exploration request instead. |

Places where the engine's order of evaluation or of checks decides an observable result are marked `ORDER` in the Lean sources; places where the engine's behavior looks accidental and is mirrored on purpose are marked `MIRRORED`.

**Proved properties** (no `sorry`, no `admit`, no axiom of its own; `#guard_msgs` checks in each file fail the build if a theorem depends on anything beyond `propext`, `Classical.choice` and `Quot.sound`). They are about the behaviour calculus, so they hold of every run of an elaborated input and of none on the legacy interpreter:

- determinism: `Exec.step` is a function, so a state has one scheduled successor, and `Exec.step_sound` makes each committed step a step of `Sys.lts`;
- at most one transition fires per machine in a step (`winners_nodup`), and the order of the winners changes nothing but which error is reported (`phase2_perm`), since every machine reads the others at the start of the step;
- every run of an elaborated input stops: whatever `V2.runInput` returns is the trace of `traceOfB`, whose outcome is not `running` and which has at most `stepLimit` steps (`V2.runB_terminates`), and every state of that run is reachable in `Sys.lts` (`V2.runB_reach`);
- a failed step keeps nothing (`Exec.step_failed`), and the error state is deadlocked.

**Definition and implementation.** The files above define the engine; what the application runs (`engine.run`, and `exegra-lean`) is `Exegra.Impl.runAnyValue` in `formal/Exegra/Impl/`, which is the definition with traces written by a JSON writer that appends to one string. `Exegra.Impl.runAnyValue_eq : ∀ v, Impl.runAnyValue v = Exegra.runAnyValue v` (and `runAny_eq` on text) rests on `JsonOut.write'_eq`, with only the standard axioms, and the implementation uses no `implemented_by`, `extern` or `csimp` of its own, so every theorem about the definition holds of what runs. The legacy interpreter parses each expression at every evaluation (WG-4798), and `Json.parse` is still a partial definition (WG-4797).

**Building and checking.** `npm run build:formal` runs `lake build` in `formal/` (needs elan; the toolchain installs itself from `lean-toolchain`); it type-checks the semantics and the proofs and builds `formal/.lake/build/bin/exegra-lean`. `formal/.lake/` is build output, ignored by git and outside the traceability surface. Then:

- `node tools/conformance.js --engine "<path of exegra-lean>"` checks the Lean semantics against the goldens (`formal/.lake/build/bin/exegra-lean`, `formal\.lake\build\bin\exegra-lean.exe` on Windows);
- `node tools/differential.js --goldens --seed <n> --count <n>` runs every golden input, `<n>` inputs in the integer fragment of the calculus and `<n>` inputs of every format-2 construct generated from the seed by `tools/gen-engine-inputs.js` through the native Rust engine (`cargo build --release` in `engine/`) and `exegra-lean`, compares the traces as the conformance runner does, prints the construct coverage of the generated inputs and of the traces, saves every mismatching input under `test-results/differential/` and exits non-zero on any mismatch. `node tools/gen-engine-inputs.js --seed <n> --count <n> [--out <dir>]` prints (and writes) the generated inputs alone. `node tools/differential.js --calculus --seed <n> --count <n>` runs every golden, every version-2 fixture and `<n>` integer-fragment inputs through `exegra-lean` and `exegra-lean --legacy` (and the Rust engine when built) and requires the calculus path to give the legacy trace, except the differences `tests/conformance/expected-differences.json` lists; `--lift` compares every golden with its version-1 trace at the base commit of `tests/conformance/golden-changes.json`;
- `tests/proofs/formal-semantics.test.js` builds `formal/` and checks the proofs, checks `exegra-lean` against the goldens, and runs the differential check, and the calculus check, on the goldens and on seed 4685 with 150 inputs. Each part skips with a message when `lake` or a binary is missing.

**Changing the language.** An engine change that alters behavior is made against the definition first: change the calculus or the legacy interpreter in Lean (and the proofs, if they no longer build), then the Rust engine, then re-record the goldens on purpose (`node tools/record-goldens.js --force`) and run the differential check until the engine, the goldens and the semantics agree.

### Elaboration into the behaviour calculus

`formal/Exegra/Elab.lean` maps a format-2 engine input into the typed behaviour calculus of `formal/Exegra/Core/Behav.lean` (`Elab.elab`, at the call boundary `engine.elab`, and `exegra-lean elab`). An input is accepted, or refused as one of three kinds:

- `outOfFragment`: it uses resources, links, workloads, keyed instances, routes, measured outputs, `sample` effects, option types or resource faults, which the calculus does not cover;
- `illTyped`: an unknown event or variable, a guard that is not Boolean, an operator on the wrong sorts (`text - 1`, `1 == '1'`), or one of the decisions below;
- `notInteger`: a number that is not an integer in a literal, an initial value or a payload.

Machines are the instances of the behaviours, behaviours in input order and the instances of a counted behaviour in index order, the order phase 1 visits them. Expressions are parsed once and resolved to scoped references; a reference to nothing (an unknown name, a behaviour with several instances read as one) evaluates to an error in the step that reads it, as in format 2. Objects, arrays and `null` are constants of their own sort, compared by structure. `elab_wf` proves that an accepted input elaborates to a well-formed system. On the goldens, every input is accepted except those listed in `tests/conformance/expected-refusals.json` (`tests/core/formal-elab.test.js`).

The five behaviours of WG-4688 are decided as follows; each has a test in `tests/core/formal-elab.test.js`.

- **A repeated behaviour id is refused** (`illTyped`). Format 2 scanned such a behaviour twice in phase 1 and reported the second scan as if it were another machine; a behaviour id names one behaviour.
- **An id declared both as an event and as a behaviour, fault or scenario is refused** (`illTyped`). Format 2 resolved such an id by the order of its lookups, so the same text meant different things in a guard and in an emit.
- **`set a` to an object value copies the value.** Values are immutable in the calculus, so `a` and `b` are equal from the next step on: guards and effects both see `a == b` true. The legacy interpreter copies as well (`Value.copy`).
- **A negative `after` or `by` is refused** when the input is decoded ("must be an integer in [0, …]"). A delay into the past would reorder the queue behind the current time.
- **A variable named `time` or `state` is refused** (`illTyped`). `time` reads the step's time and `b.state` a machine's control state; a variable of either name would be shadowed in one reading and not in the other.

## Exhaustive exploration in Lean (`exegra prove`)

A simulation is one run. `exegra prove <scenario> --project <p> [--bound N] [--max-states N] [--steps]` checks a scenario's state invariants and temporal claims on every run the scenario admits in the behaviour calculus, with an explorer whose soundness is proved in Lean (`formal/Exegra/Core/BehavCheck.lean`, `formal/Exegra/ProveB.lean`), and reports per claim either *verified by Lean for every reachable configuration*, a real counterexample run, or *incomplete*. A scenario whose input the elaborator does not accept is not explored: one outside the calculus's fragment is reported *not covered by the calculus*, an ill-typed or non-integer one with the refusal.

**What the explorer varies.** Exactly three things, through the calculus's successor function `Exec.successors`, which is sound and complete for the step relation `Sys.lts` (`successors_sound`, `successors_complete`):

- **Delivery order among minimal-time entries.** Any pending entry whose time is the least pending time may be delivered next.
- **The whole-run fault mask.** Each fault the scenario lists acts in the run or does not, chosen once at the start (a mask over its faults, fixed for the run, `mask_const`). A fault with an `occurrence` therefore fires at that occurrence or not at all, one without fires at every match or never, and an `inject-event` fault queues its event or not. Every subset is explored; the all-true mask is the scenario's own fault set.
- **Draw outcomes up to the cap.** Every value of the support of each sampled delay is tried. A support larger than `drawCap` (1000 values) is not enumerated: the claim is reported `incomplete`, never `holds` (`successorsUpTo_eq` proves that below the cap the capped enumeration is the full one).

**What `N` counts.** `N` is the number of distinct **calculus states** the search visited: a fault mask and a configuration of machines (control state and variables), the pending entries and the time. A calculus state holds no sequence numbers, object identities, stream counters or step count, so two runs that reach the same machines and queue by different routes count once. Failed steps lead to the error state, which has no successor and violates every invariant.

**What is proved** (no `sorry`, no `admit`, no axiom of our own; `#guard_msgs` pins each theorem to `propext`, `Classical.choice` and `Quot.sound`):

| Theorem | Statement |
|---|---|
| `explore_holds_invariant` | `exploreB sys P bound cap = .holds n` → `(Sys.lts sys).Invariant (fun s => s.ok ∧ P s)`: with no bound, since `holds` is returned only on an empty frontier. |
| `explore_cex_real` | `exploreB sys P bound cap = .counterexample p` → the invariant is refuted, and `p.picks` replays through the successor function from an initial state to a state where `s.ok ∧ P s` fails. A replay through the successor function is a run of `Sys.lts` by `successors_sound`. |
| `verdictOf_holds` | A `holds` verdict of a generated proof file gives that invariant for the calculus system of the embedded input text. |
| `monitor_sound` | On every finite run ending in a deadlocked state, the monitor of each temporal form (`never`, `precedes`, `eventually`, response within a time bound) accepts exactly the runs that satisfy the form. |
| `tcheckB_holds`, `tcheckB_cex` | A `holds` of the temporal check covers every reachable node of the product of the calculus with the monitor; a counterexample is a real path of the product to a violating node. |

The explorer is a breadth-first search (`Gen.search`, `formal/Exegra/Search.lean`) with a `Std.HashSet` of visited states. It is total: its recursion is on the depth (at most `bound` layers), and it stops with `incomplete n` when the visited set would grow past `maxStates` or a path is cut off by the bound. `incomplete` claims nothing.

**From a specification to a theorem.** `exegra prove` (`tools/prove.js`, with the pure part in `src/core/proof-export.js`):

1. builds the scenario's engine input exactly as `simulate` does, and collects the `state-invariant`, `never`, `precedes` and `eventually` claims that list the scenario and refer only to its behaviors. A claim expression reads the configuration as the trace check does: `time`, `<behavior>.state`, `<behavior>.<variable>`. It holds when it evaluates to `true`; an evaluation error counts as a violation;
2. runs `lake build` in `formal/` and `exegra-lean explore` and `temporal`, the compiled explorer, to find each claim's result;
3. writes `formal/generated/<scenario>.lean` (ignored by git). It holds the engine input text and per claim `theorem «<claim>» : V2.ProveB.verdictOf inputText "<expr>" bound maxStates = <result>` (or `tverdictOf` with the claim's form for a temporal claim);
4. checks the file with `lake env lean`, loading the modules' native shared libraries (`precompileModules` in `formal/lakefile.toml`), and reads the axioms of every theorem from `#print axioms`. A claim is reported only when Lean accepted its theorem.

**What is trusted.** Each theorem is discharged by `native_decide`. In Lean 4.35 this adds one auxiliary axiom per theorem (named `<theorem>._native.native_decide.ax_…`), which asserts that the compiled code evaluated the statement to `true`. The result's `axioms` lists them, and `trusted` says so: the Lean compiler, the C compiler it uses and the Lean runtime are trusted for the evaluation, while the meaning of the result is proved with standard axioms only. The theorem is about the embedded input text, which `verdictOf` decodes and elaborates itself. Kernel evaluation (`decide`) does not apply: the visited set hashes states with `String.hash` and `mixHash`, which are opaque to the kernel.

**Output.** Each claim gets `method: "lean-exhaustive"`, `result` (`holds`, `counterexample`, `incomplete`, or `not-supported`/`not-evaluable` for claims it cannot explore), `bound`, `states` (N), `axioms`, `trusted`, `theorem` and `file`. A counterexample carries the active faults, the delivery choices, a step list in the form simulate uses, with `[delivered ahead of k earlier simultaneous entries]` where the order differs from the scripted one, and the request-log lines of its contract events (`src/core/contract-trace.js`). With `--steps` it also carries the step records. The default bound is the scenario's step bound (`max 1 ⌈maxSteps⌉`); a larger `--bound` is capped there, since no run of the scenario takes more steps. The default state budget is 200000.

On the fixture `tests/fixtures/race` (two clients increment a counter), the read-modify-write store's scripted run passes its trace check, but `exegra prove lost-update-race --specs tests/fixtures --project race` reports:

```
"result": "counterexample",
"explanation": "A run of 10 steps violates the invariant. Invariant `racy-store.value == racy-store.writes` is false after step 9: racy-store.value = 1, racy-store.writes = 2. The scenario declares no faults.",
"stepList": [
  "#0 t=0 deliver go-b [delivered ahead of 1 earlier simultaneous entry] → client-b-flow: b-start",
  "#1 t=0 deliver prepare-b [delivered ahead of 1 earlier simultaneous entry] → client-b-flow: b-prepare",
  ...
  "#7 t=0 deliver value-b → client-b-flow: b-write",
  "#8 t=0 deliver write-b [delivered ahead of 1 earlier simultaneous entry] → racy-store: racy-write-b",
  "#9 t=0 deliver write-a → racy-store: racy-write-a"
]
```

and the atomic store (`atomic-increments`, with its lost-write fault on and off) holds for every reachable configuration (N = 106 calculus states). `tests/proofs/formal-explore.test.js` runs both and skips, with a message, when `lake` is not on the PATH.

**Relation to the Rust explorer.** The Rust explorer of the assurance chain (WG-4650) is for state spaces too large for this one; it will be checked differentially against the Lean explorer, as the Rust engine is checked against the Lean engine. The unbounded proof of an invariant, by induction over the step relation, is WG-4686.

## In the application

The *Simulation* panel loads a scenario, toggles faults (a change restarts the run), and steps, steps back, plays, resets or runs to the end; while a scenario is loaded the docked transport (above the navigation on a phone, floating over the scene from 768 px) steps back, plays or pauses, steps and runs to the end without the panel open. Loading a scenario, or changing its faults, runs it once to the end in a Web Worker (`src/app/engine-worker.js`, driven by `src/app/engine-runner.js`) that loads the same WebAssembly module, so a long run never blocks the page; the panel shows *Running…* and the transport *running…* until the trace arrives, and a new load cancels a run still in progress. The trace's recorded steps then form the cursor (`createTraceCursor`): stepping forward reveals the next recorded step, stepping back moves the cursor back, and the timeline, the step counter and the outcome show only the steps revealed so far, exactly as when the run was computed step by step. Claim evaluation still runs scenarios synchronously on the main thread. The timeline lists each step with its event and the transitions that fired; a step has a detail view with variables changed, events emitted, ignored behaviors and faults acted. In a view of the `behavior` projection (for example *Edit flow behavior* in the `exegra` project), visited and active states and transitions are marked, and the fired entities are briefly pulsed in the scene.

**Messages in the structural view.** Each step is also shown as a message travelling through the component diagram (`src/core/flows.js`, drawn by the renderer). The sender is read from the trace: the subject of the behavior whose transition emitted the event, or *outside* for a scenario input or an injected fault. The receivers are the subjects of the behaviors that fired a transition on it. A marker labelled with the event's name then travels to each receiver:

- along the drawn edge between the two components, backwards along it for a reply;
- dropping in from above for a request from outside;
- straight, and labelled *not drawn in this view*, when a relationship connects the two components but the current view hides it (for example a `calls` relationship in a view filtered to data-flow kinds);
- straight, in the violation colour and labelled *no declared relationship*, when no relationship connects them at all;
- upwards and fading, labelled *dropped*, when a fault drops the event after it leaves its sender.

A collapsed subsystem stands for its members, and a message between two members of one collapsed subsystem pulses that node. The step detail in the panel states the same thing in words (*Message: save-requested: Application session → Workspace service (1 without a declared relationship)*). So a behavior model that sends messages along paths the structure does not declare is visible at the step where it happens. The self-specification's own `visual-edit-flow` shows one: its session sends `save-requested` straight to the workspace service, while the declared path runs through the persistence client and the dev-server plugin.

**Live claim checks.** `checkTrace` evaluates every invariant and temporal claim that lists the loaded scenario (and whose behaviors the scenario runs) against the steps seen so far. A claim that cannot yet be decided is reported as *undecided*, not as violated:

- a `state-invariant` that is false at a step, a `precedes` whose `then` occurs without an earlier `first`, and a `never` whose forbidden occurrence happens are **violated** at that step, permanently;
- an `eventually` that has not yet seen its occurrence (or final state) is **undecided** while the run is unfinished, and is violated only once the run is quiescent;
- a check whose expression cannot be evaluated is undecided with the reason;
- a `state-invariant` that is an implication whose antecedent was never true on a finished trace is undecided, because the implication was never exercised;
- only claims that list the loaded scenario in `evaluate.scenarios` are checked against its trace.

This is what the shipped self-specification shows. Load the scenario `visual-edit-flow` and tick the fault `disk-changed-externally`: the workspace machine takes the faulty transition `workspace-detect-conflict`, nothing is written, and the claim `file-matches-model-after-save` (`workspace-flow.persistedRevision == transaction-flow.revision && session-flow.saveState == 'saved'` at quiescence) is violated. The scenario `edit-with-disk-conflict` lists that fault itself; its claims `conflict-never-overwrites` and `conflict-is-flagged` are about that run. The scenario `rejected-edit` runs with `validation-fails` and its claims state that nothing commits, refreshes or is written.

The command-processing example with an early-acknowledgement fault is a test fixture, `tests/fixtures/multiplayer/spec.jsonc`: scenario `command-happy-path` with the fault `early-ack` makes the claim `ack-implies-durable` (`worker-flow.acked => database-flow.durable`) false at the step where `command-accepted` fires `worker-ack-early`. The browser test *simulation steps through the trace; early-ack fault violates the invariant* in `tests/browser/exegra.spec.js` runs it through the user interface.

## Contract events in a trace

An event that names a `contract` and a `role` (see [model-and-format.md](model-and-format.md#contract-events)) makes the trace read like a request log. Nothing changes in the engine, the Lean semantics, the goldens or the engine input: the checks and the log read the finished trace (`src/core/contract-trace.js`).

**Automatic checks.** `checkTrace` adds, for every delivered step whose event is a contract event, checks that need no claim. Each violation is a failed check of the scenario carrying its step index (the claim id is `trace-contract-conformance` in Exegra's own specification): a payload value that does not fit its declared type, a request that lacks an input that is not optional, a payload field the contract does not declare, an error `code` that is not among the contract's errors, and a response or error that answers no earlier unanswered request of the same contract. A response is matched to the earliest unanswered request, or to the one whose `correlation` field holds the same value when the event declares one. A trace with contract events and no violation gets one passing check. Dropped and delayed steps are not deliveries and are not checked. A scenario without contract events gets no such check, so existing results are unchanged. `exegra simulate` lists the checks under `checks`; the simulator panel shows them in the Checks section, with the step to jump to.

**Request log.** `requestLog(model, trace)` turns the contract events of a trace into lines: a request is `→ <method path | operation | event name> {payload}` (the contract's `binding` when present), a response `← ok {payload}`, an error `← refused <code> {rest of payload}`; a dropped step is prefixed `✕ lost`. `exegra simulate` returns them as `result.requestLog` (`#<step> t=<time> <line>`), and the simulator panel shows them as the Requests section, one jump target of at least 44 px per line, dimmed while the step is still to come. Exegra's own scenario `write-with-stale-base-hash` runs the contract `write-file` between the persistence client and the development server:

```
#1 t=0 → POST /__exegra/write {name: "exegra", file: "spec", text: "spec text of revision 2", baseHash: "h1"}
#2 t=0 ← refused conflict {current: "h2"}
#3 t=0 → POST /__exegra/write {name: "exegra", file: "spec", text: "spec text of revision 2", baseHash: "h2"}
#4 t=0 ← ok {ok: true, hash: "h3"}
```

## Live mode: Exegra's own run, replayed through its specification

The simulator panel has two sources: a declared scenario, and **Live**. Live shows the events the running application is producing right now, replayed through its own specification, on the components responsible for them.

**Recording.** `src/app/traffic-recorder.js` keeps a bounded stream (the last 5000 events) of real events named by the event ids of `specs/exegra/spec.jsonc`. Each event has a logical sequence number `seq`, which is the only time the replay and the claim evaluator see; the wall-clock time `at` stays in the application layer for display. The producers sit where the event descriptions say: `src/app/main.js` (page load, engine load, camera), `src/app/session.js` (project list, open and read, commits and their cause, saves and their answers, external changes, claim evaluation, simulator controls, preference writes), `src/app/engine-runner.js` (worker messages), `src/persist/client.js` (requests and change notices), `src/ui/toolbar.js`, `src/ui/realisation-panel.js` and `src/ui/layout.js`. Texts and bundles are recorded as their sha-256 (`src/core/sha256.js`, equal to the workspace's hash), as the specification represents them. A store write that leaves the model's abstraction of the store unchanged (the selection and view of `exegra.session`, whether the explorer is open in `exegra.layout`) is a stutter step and is not recorded.

**The development server's events.** A request that carries `x-exegra-request-id` (the `requestId` of the contract events, from `traffic.nextRequestId()`) gets the server's own events back in the `x-exegra-trace` header of its answer: the workspace events (`ws-read`, `ws-write`, `disk-file-replaced`, ...) and the answer event (`write-file-ok`, `write-file-conflict`, ...), stamped with that id, in the order the server produced them. The change stream sends `ws-watch` and, before each `change`, `ws-change` and `file-change-notice-sent` as `trace` messages. For a notice whose hash the server did not write, it infers the external edit (`disk-edited-externally`, `disk-file-replaced`, or `ws-write-recorded` for `evidence/results.json`) and marks those events `inferred`.

**Replay.** `src/core/replay.js` executes the behaviors of the scenario `live-session` with the step semantics of the engine (phase 1 choice, phase 2 effects, the expression language and the engine input of `simulationInput`), but delivers the recorded events one at a time in recorded order with their recorded payloads. The events the model emits are kept as predictions instead of being queued: a recorded event that some transition of the scenario emits must match a pending prediction (by correlation field or `requestId` when both carry it, else the prediction whose payload agrees best, else the oldest). Any interleaving of predictions that respects causality is accepted, because a real run interleaves independent chains (an HTTP answer, a file-watch notice, a claim evaluation) in whatever order they happen. The engine itself is not driven: it runs a scenario to quiescence and delivers simultaneous events in queue order, so it cannot be fed one external event at a time.

A **divergence** is reported, under the claim `real-runs-replay-through-self-model`, at its step:

| Kind | Meaning |
|---|---|
| `unknown-event` | The event is not an event of the specification. |
| `unpredicted` | The model emits this event, but no pending prediction matches it here. |
| `not-allowed` | A predicted event arrived and no behavior that consumes it accepts it in its current state. |
| `payload` | A recorded scalar payload value differs from the predicted one. Correlation fields, values the transition gives as number literals (stand-ins for counts the model does not track), arrays and objects are not compared. |
| `missing` | A prediction was not matched within 200 recorded events, or by the end of a closed stream. |
| `error` | An expression of the model failed on the recorded payload. |

A variable that no transition has written since the stream started and whose declared initial value stands for the environment (a file's hash on disk, a stored preference) is **calibrated** from the first recorded value a prediction compares it with; the step lists it.

The replay returns a trace of the usual shape (steps with `fired`, `ignored`, `responsible`, `config` whose `pending` are the predictions awaited, plus `divergences` and `calibrated`), so `checkTrace`, `requestLog`, the panel, the message flows and the pulses read it as they read a simulated trace.

**In the panel.** Press *Live* next to the scenario select. The status line counts the real events replayed, the divergences and the predictions awaited; the timeline lists the recorded events with their logical time and the wall-clock time since the first (display only), marks inferred events and divergences, and follows the newest event unless you step back; *Predicted, not yet seen* lists the predictions awaited; the step column shows the step's message, fired transitions, calibrations and divergences; the Divergences section lists all of them with a jump to their step; the Requests section is the request log of the real traffic. Each new burst of events pulses its responsible components in the scene and draws the newest message. A semantic edit of the open specification replays the kept stream through the new model. Live needs a specification that declares `live-session` (Exegra's own or a copy of it).

Limits: the stream is in memory only (WG-4780); a write the server made for another tab reaches this tab as an unpredicted notice (WG-4781); command-line runs are not recorded; the divergences a longer session still shows are listed in the unknowns of `self-model-replay` (WG-4782).

## What a simulation establishes

A simulation shows what the **specified machines** do for **one input sequence and one fault set**. It can show a concrete failing trace, which is a real counterexample to the specified model, and a passing run shows the property held on that run.

It does not establish:

- that a property holds for other inputs, fault sets, interleavings or timing. `exegra prove` (above) covers other orders of simultaneous events and subsets of the scenario's faults within a bound, for state invariants. Nothing covers other inputs or timings, and there is no probabilistic or stochastic evaluation yet (planned: [resources, workloads and performance](#planned-resources-workloads-and-performance-wg-4664-wg-4715));
- that the code behaves like the machines. The machines are hand-written abstractions; the correspondence is neither generated nor checked (assumption `machines-abstract-the-code`);
- anything about real time. Ticks are logical; `delay-event` by `3` is three ticks, not three milliseconds;
- concurrency semantics beyond the model: within a step, behaviors all read the configuration from the start of the step, and delivery order for equal times is scheduling order.

The claim method that uses simulation, `state-invariant`, `precedes`, `eventually` and `never`, states these limits in each result's `scope`, and also runs each declared negative (a listed scenario with extra faults) and requires it to violate the claim before reporting `verified`. `prove` does not explore negatives in Lean. See [claims-and-evidence.md](claims-and-evidence.md). The simulator's recorded limitations are in `simulation-engine`'s `unknowns` and `system.notes` in `specs/exegra/spec.jsonc`.

## Planned: resources, workloads and performance (WG-4664, WG-4715)

**Status: largely implemented at the engine-input level (WG-4664, WG-4715, WG-4729).** Defined in `formal/Exegra/Format2.lean`, `Resource.lean`, `Workload.lean` and `Random.lean`, run by both `exegra-lean` and the Rust engine (`engine/exegra-engine/src/v2.rs`, `workload.rs`) and checked differentially on generated version-2 inputs (`tools/differential.js`, which generates resource, workload, closed and population, link and timer, and fault inputs): integer time units; counted and keyed instances with routes and aggregates; resources (`use`, `acquire`, `release`, classes, bounds, overflow, demand factors); SplitMix64 streams; open workloads (constant and Poisson processes, phases, ramps, repetition, batches, clients, payload generators, `maxArrivals`), closed workloads (think, start offsets, replies, client timeouts) and population workloads (keyed client instances with targeted start entries), with address groups; links (transfer at a bandwidth through a FIFO queue, propagation latency, ordered links, queue bounds, fan-out) and timers (`timer`, `cancel`); the resource faults `set-capacity`, `set-class-limit`, `collapse-classes`, `scale-demand` and `replace-demand`, untimed or windowed through `fault-edge` steps, and windows on the format-1 fault kinds; request classes with the request lifecycle, and the measured outputs of [Measured outputs](#measured-outputs) that the engines report (`metrics`: resources, request classes with response time, outcomes and legitimate refusals, transition firings, and series buckets). The integer lowering of distributions is `src/core/distributions.js`; the statistics and the metric-bound runner over engine inputs are `src/core/metric-stats.js` and `src/core/metric-claims.js`. `lift_agrees` was removed with format 1 (WG-5681); the goldens' move to version 2 is checked against `tests/conformance/golden-changes.json` (`tools/differential.js --lift`). **Not yet** (refused when present, or not derived): `crash-instance` and incarnations, meters, prices and the cost metric, `waiting-time` per class and resource signals per series bucket, the determinism theorem over seeds, calibration, sensitivity and revision binding (`asOf` is only recorded), and exploration of version-2 inputs (WG-4741). A specification's resources, links, workloads, request classes and format-2 scenarios derive version 2 through `simulationInput` (`src/core/sim-input.js`; see [Specification-level form](#specification-level-form)), and the `metric-bound` claim method is registered (`src/core/claim-methods.js`) and evaluated by `src/core/claims.js`. This section is the normative definition that the Lean semantics in `formal/` and then the Rust engine follow. The planned components (`resource-model`, `workload-model`, `performance-metrics`, `metric-claims`), the contracts `engine-input-v2` and `trace-v2` and the planned claims are in `specs/exegra/spec.jsonc`. Where this text and the Lean definition disagree, the Lean definition decides, as for format 1.

Why: today one injected event stands for a burst of traffic and one tick for a second, so a denial-of-service model can only count abstract events. Format 2 lets a model state request rates, pool capacities, service times and latencies, and lets a claim say "p99 of the database leg of a move ≤ 30 ms under a page-read flood", evaluated over seeded runs with a stated confidence.

**What such a result is.** A metric claim that holds says the *model*, with its *assumed* parameters, meets the target under the stated workload. It never reads verified and is never counted as supported by evidence (status `model-holds`, [Claims over metrics](#claims-over-metrics)); it becomes a statement about a system only through calibration against recorded load runs ([Calibration](#calibration-and-sensitivity)). Its job is to find designs that cannot work and to rank designs, before load runs measure the one that is built.

### Principles

1. **Engine arithmetic is on unbounded natural numbers, except the expression language.** Time, durations, capacities, sizes, bandwidths, random draws, sampled values, counters and every measured output are natural numbers in the semantics (Lean `Nat`), bounded by the input limits of [Integers and bounds](#integers-and-bounds). Lean compares them decidably, and Rust and Lean agree bit for bit without reasoning about rounding modes or `libm`. In the behaviour calculus the expression language computes on integers as well ([semantics.md](semantics.md#values-numbers-and-time)); only the legacy interpreter, for inputs outside the calculus, keeps IEEE doubles in expressions.
2. **Probability is computed outside the semantics; the engine reads tables.** Continuous distributions are lowered to integer inverse-CDF tables by `simulationInput`, with an integer algorithm ([Lowering](#lowering-distributions)), and written into the engine input.
3. **Nondeterminism and probability are different things.** A `choice` (and a route `by: "any"`) is nondeterministic: the explorer enumerates it. Every other draw is probabilistic: it is only ever sampled, and results that depend on it are statistical, never verified.
4. **Format 1 is gone.** Every input is version 2 (WG-5681); the goldens recorded under format 1 were moved to version 2, and every change is listed in `tests/conformance/golden-changes.json` ([Backward compatibility](#backward-compatibility)).

### Integers and bounds

Every integer of a version-2 input is checked against a bound when the input is read (refusal `Field "<path>" must be an integer in [<lo>, <hi>].`):

| Quantity | Bound |
|---|---|
| times, durations, `horizon`, `warmup`, `stopAt`, `x` of every distribution table, `fixed` and `uniform` values | `[0, 2^53)` |
| `x` of `unitExponential` (scale 2^−64) | `[0, 2^72)` |
| `scenario.stepLimit` (`maxSteps` in the specification) | `[1, 2^53)` |
| capacities, units, `reserved`, `limit`, `queueBound`, instance `count` and `max`, populations, client counts, `maxArrivals` | `[0, 2^32)` (capacity and units at least 1) |
| sizes (bytes) | `[0, 2^40)` |
| bandwidth (bytes per second) | `[1, 2^40)` |
| rate numerators and denominators, factor numerators and denominators, USL `alpha` and `beta` numerators and denominators, weights | `[0, 2^32)` (denominators at least 1); a sum of weights below `2^53` |
| table `u` | `[0, 2^32]` |
| seed | `[0, 2^64)`, a decimal string without sign, spaces or leading zeros |

With these bounds every product the semantics forms below fits in 128 bits (the largest are `r · span` < 2^117, the service time `d · f · s` < 2^117 with each factor reduced as stated in [Resources](#resources), and the table interpolation `(u − u_i) · (x_{i+1} − x_i)` < 2^85), except two computations that the Rust engine does with a big-integer type (and Lean with `Nat`): the next Poisson arrival time, whose exact rationals combine rates, times and an exponential sample (several hundred bits), and a USL demand factor evaluated at an occupancy. The lowering of distributions in `simulationInput` runs on unbounded `BigInt` and has no width limit; only its outputs are bounded. **A value the run computes that leaves its bound** (a time or an accumulated metric reaching 2^53, a counter reaching 2^53) is a failed step with the message `Value <what> exceeds 2^53.`, where `<what>` names it (`time`, `metric <name>`, `counter <name>`). Values of the expression language (variables, payload fields) are doubles as in format 1 and are not bounded; only the engine's integers are.

### Time

**Decision: time stays discrete, as a natural number of a declared base unit.** The input declares `time.unit`, one of `tick`, `s`, `ms`, `us`, `ns`; `perSecond` follows from it (`null`, 1, 10^3, 10^6, 10^9). **The recommended unit for performance models is `us`** (integer microseconds): 2^53 µs is about 285 years, and service times of queries and RPCs are tens of microseconds and up. `ns` exists for fast links (2^53 ns is about 104 days), `ms` and `s` for coarse models, `tick` for models with no physical time; a model in unit `tick` may not use rates, bandwidths or anything that needs `perSecond` (validation error, and refusal `Unit tick has no rate; "<path>" needs one.`).

Rejected: **rational time** (denominators of sums of sampled durations grow without bound and nothing a performance model states needs finer than a nanosecond) and **floating-point time** (Lean's `Float` is opaque to the kernel, and accumulating durations in doubles makes the order of events depend on rounding, while the explorer needs "simultaneous" to be exact).

**Rounding.** A duration written in the specification is converted to the base unit exactly; a value that is not a whole number of base units (`0.5 us` with base `us`) is a validation error. A duration the engine computes is rounded as stated where it is defined: transfer times up, table interpolation down, demand scaling up, all on exact integers.

**The expression language** reads `time` as an integer (the legacy interpreter converts it to a double, exact below 2^53).

**Models without a time unit.** A model that uses no construct of this section derives a version-2 input in unit `tick` with no seed: the logical ticks of the removed format 1, now integers (the golden that had `after: 3.5` was edited to an integer and re-recorded, as `tests/conformance/golden-changes.json` records).

### Instances

A behavior may run as several instances, each with its own machine:

- `instances: {count: N}`: instances `0 … N-1`, created at the start.
- `instances: {key: "<field>", max: M}`: *keyed* instances, one per distinct value of a payload field, created in the initial state with initial variables on the first entry routed to that key. Creating instance `M + 1` is a failed step: `Behavior "<b>" would exceed <M> instances.`
- No `instances`: exactly one instance, numbered `0`, whose machine key is the behavior id.

A population workload ([Workloads](#workloads)) creates its client instances at the start of the run, which takes precedence over creation on first routing; validation requires `max` to be at least the sum of the counts of the populations on that behavior.

**Machine keys.** Otherwise each instance is `<behavior>#<k>`: `k` is the index for a counted behavior, and for a keyed one the canonical JSON text of the key value, quotes included, so the string `"1"` (`limiter#"1"`) and the number `1` (`limiter#1`) are different instances. The behavior part ends at the first `#`, since ids cannot contain one (they are lower-case words joined by hyphens), so a `#` inside a key value is harmless.

**Addressing.** A queue entry may carry `target: {behavior, instance, incarnation}` (one instance of one behavior) and `from: {behavior, instance, incarnation}` (the emitting instance and its incarnation, [Faults](#faults-in-format-2); absent for scenario steps, faults and workload arrivals). For each behavior an entry does not target, the instances that see it are fixed by a *route* `{event, behavior, by, field?, resource?}` when the entry is **first taken as head**, at its scheduled time (a delayed copy keeps that decision):

| `by` | Instances |
|---|---|
| no route (broadcast) | counted: every instance in index order (the only behavior for one instance); keyed: every existing instance in creation order, none if none exists yet |
| `key` | keyed behavior: the instance `payload[field]`, created if missing; counted: index `fnv1a64(json(payload[field])) mod N`, where `json` is the canonical JSON writer of `formal/Exegra/Json.lean` (`JSON.stringify` semantics, numbers formatted as JavaScript's number-to-string of `formal/Exegra/Number.lean`, so `1`, `1.0` and `1e0` all hash as `1`) and FNV-1a 64 runs over its UTF-8 bytes |
| `round-robin` | counted only: `c mod N`, `c` the route's counter, which then increments |
| `random` | counted only: `uniformInt(0, N − 1)` from stream `route:<event>:<behavior>` (sampled) |
| `any` | counted only, nondeterministic: the explorer enumerates every instance; simulation draws `uniformInt(0, N − 1)` from the stream `route:<event>:<behavior>`, or takes instance `0` when the scenario has no seed |
| `least-busy` | counted only: the instance with the fewest units held in `resource` plus requests it has waiting on `resource`, read from the configuration at the start of the step; ties go to the lowest index |

**Down instances** (crashed, [Faults](#faults-in-format-2)) are skipped by `round-robin` (it takes the `(c mod u)`-th instance that is up, `u` their number), `random`, `any` and `least-busy`, so a crashed instance, which holds nothing, does not attract traffic; when none is up, the entry reaches no instance of that behavior. `key` routes are not redirected: an entry whose key maps to a down instance is dropped for it, as a sticky route would be.

A `key` route whose `payload[field]` is missing is a failed step: `Route of "<event>" to "<behavior>" needs payload field "<field>".` A route naming a keyed behavior with any `by` other than `key` or a broadcast is a validation error. An emit effect with `target: "reply"` addresses the instance in the `from` of the entry being delivered, **with that entry's recorded incarnation**: if the requester crashed and restarted in between, the reply is stale and never reaches the new incarnation. **Only entries created by a transition's `emit` effect carry `from`**, and so do their delayed copies and link deliveries. Scenario steps, injected faults, arrivals, closed issues, population `start` entries, timer firings, resource events (`then`, `refused`, `service-done`, `wait-timeout`), fault edges and `notify` carry none; a `reply` while delivering one of them is a failed step: `Effect replies to "<event>", which has no requester.` (the validator warns where it can see it statically).

**When recipients are decided.** Targeted entries (an explicit `target` from an emit, a `reply`, a timer, a resource's `then` or `refused`) name their instance and its incarnation **when created**, since they answer a particular incarnation; a scenario step's `target`, which answers nobody, takes the incarnation current when it is first taken as head. Routed entries are decided **when first taken as head**: the route's instance, the route counter, any route draw and the chosen instance's incarnation, all from the start-of-step configuration; a delayed copy keeps the decision. So `least-busy` reads the load when the entry is delivered, and an arrival routed to an instance that restarted before its delivery is not stale. **Broadcasts are evaluated at delivery**: every instance that is up when the entry is delivered, in index order (keyed: creation order), including an instance restarted after the entry was created and a keyed instance created since. Broadcasts carry no epoch on purpose: a broadcast stands for a fact announced to whoever is listening when it arrives. The routed instances are stored on the entry as `routes: {<behavior>: instance}`; route counters are part of the configuration (`routeCounters`) and of the explorer's state.

**In a step**, phase 1 visits behaviors in scenario order and, within a behavior, its addressed instances in index order (keyed instances in creation order). Each instance fires at most one transition. A behavior routed to no instance gets one `ignored` entry with reason `no-instance`.

**Aggregates over instances** are three-part references, readable wherever a cross-behavior reference is (guards and effects alike read the start-of-step configuration): `<behavior>.count.<state>` (instances in that state), `<behavior>.sum.<var>`, `<behavior>.min.<var>`, `<behavior>.max.<var>` (over the instances that are **up**, in index or creation order: a down instance is excluded from every aggregate, `<behavior>.count.<state>` and `<behavior>.instances.count` included; `min` and `max` of no instance are `null`; a non-number is a failed step `Aggregate "<path>" needs numbers, got <type>.`) and `<behavior>.instances.count`. A two-part reference `<behavior>.<name>` to a behavior with more than one instance is a failed step, `Reference "<path>" is ambiguous: "<behavior>" has <n> instances.`, and a validation error where it is visible statically.

### Expression scope in format 2

What an expression reads, and when:

- **Variables, states and aggregates**: a machine's own variables are read in its guards from before the step, and in its effects from the next configuration as it is being written (a later effect sees an earlier `set`). **Other machines and aggregates are read from the start of the step**, in guards and effects alike (snapshot reads, WG-5681), so no machine sees another's writes of the same step and the order of the winners decides nothing but which error is reported.
- **Everything new is read from the start of the step**, in guards and effects alike: `<resource>.inUse`, `<resource>.waiting`, `<resource>.inUse.<class>`, `<resource>.waiting.<class>`, `<meter>.value` and `<meter>.count`, and `least-busy` routing. Resource effects (`use`, `acquire`, `release`) are *recorded* in phase 2 and *applied* when the step settles, after all effects, so no expression of a step sees them.
- `instance`: the firing instance's index (a number) or key (a string).

**Reserved in format 2** (a validation error, and a refusal of the input): a variable named `instance`; a behavior, resource, meter, link or workload id that equals another of these; and the second parts `count`, `sum`, `min`, `max`, `instances` of a reference to a behavior with `instances` declared, used as a variable name of that behavior.

### Resources

A resource is a pool of identical units: CPU cores, I/O channels, connections, pool slots, worker threads. The input declares, per resource:

| Field | Type | Meaning |
|---|---|---|
| `id` | string | |
| `kind` | `cpu` \| `io` \| `pool` \| `connection` \| `threads` | Informational (labels and overlays); the semantics is the same. |
| `capacity` | integer ≥ 1 | Units. |
| `discipline` | `fifo` \| `priority` | Order of service among waiting requests. |
| `queueBound` | integer or `null` | Bound on all waiting requests (`null`: unbounded). |
| `overflow` | `refuse` \| `drop` \| `shed-oldest` | What happens to a request beyond a bound. |
| `demandFactor` | step table, `{usl: {alpha, beta}}` or `null` | Load-dependent service demand, below. |
| `classes` | list | Request classes (a resource with none gets one class `default`). |
| `classes[].id`, `priority` | string, integer | Higher priority is served first under `priority`; ignored under `fifo`. |
| `classes[].reserved` | integer ≥ 0 | Units only this class may use. Σ reserved ≤ capacity, and `reserved ≤ limit` when the class has a limit. |
| `classes[].limit` | integer ≥ 1 or `null` | Most units the class may hold at once (a bulkhead). |
| `classes[].queueBound` | integer or `null` | Bound on this class's waiting requests. |
| `classes[].maxWait` | duration or `null` | A request waiting longer is refused with reason `timeout`. |

**Effects.** Recorded in phase 2 in effect order, applied when the step settles:

- `{use: <resource>, class?, units?, demand: <dist>, then: <event>, refused?: <event>, payload?}`: acquire `units`, hold them for a service time, release them, then emit `then` to the requesting instance. CPU work, an I/O, a query.
- `{acquire: <resource>, class?, units?, then: <event>, refused?: <event>, payload?}`: hold units across several transitions; `then` is emitted, targeted at the requester, when they are granted.
- `{release: <resource>, class?, units?}`: release units the instance holds in that class (default class: the resource's only class, else a validation error when the class is omitted). **Holdings are tracked per (instance, resource, class).** Releasing more than the instance holds there is a failed step: `Instance "<key>" releases <n> units of "<r>" class "<c>" but holds <m>.`

`units` is a literal integer (default 1), so it can be checked statically: a request with `units > min(limit(class), capacity − Σ_{other classes} reserved)` could never be granted and is a validation error (`Class "<c>" of "<r>" can never grant <n> units.`), checked again after the fault mask is applied ([Faults](#faults-in-format-2)).

The `then` and `refused` events carry the effect's evaluated `payload` plus `resource`, `class`, `waited` and, for `use`, `served`; `refused` also carries `reason`: `bound`, `shed`, `timeout` or `crash`.

**Service demand.** `demand` is a distribution of service time in base units. The service time of a grant is `ceil(d · f · s)`, with `d` the draw, `f` the demand factor and `s` the combined `scale-demand` factor (1 when none), computed exactly and rounded up once. The combined factor is the product of the active factors reduced to lowest terms; a numerator or denominator of 2^32 or more is a failed step (`Value demand scale of "<r>" exceeds 2^32.`), and a service time of 2^53 or more is one too (`Value service time of "<r>" exceeds 2^53.`). `demand` and `scale-demand` are evaluated at the grant, against the faults active at that time; a request already in service keeps its service time. The service time is fixed at the grant and does not change while the request is served.

**Load-dependent demand.** `demandFactor` is a step table `[[n, num, den], ...]` with `n` strictly increasing from 0: the factor for an occupancy `o` is `num/den` of the last row with `n ≤ o`. The occupancy at a grant is the units held at the resource after the grant, by every class and by `use` and `acquire` alike, plus every request still waiting at it at that point of the grant loop, including requests that the bounds step of the same settling will then remove (grants come first, so this is what a grant sees). The factor is evaluated once, at the grant, and fixed for that request's service; a later change of occupancy does not stretch or shrink a service already granted (a limitation, listed in [What it still does not represent](#what-it-still-does-not-represent)). For USL parameters `n` is this occupancy, the concurrency at the resource (in service plus waiting), and calibration fits α and β against load runs measured with the same notion of concurrency. A table is a step function: beyond its last row the last factor holds. Alternatively the resource carries Universal Scalability Law parameters `{usl: {alpha, beta}}`, each an exact rational `[num, den]` in the input, and the factor is **evaluated exactly at the grant**, `f(n) = 1 + alpha·(n − 1) + beta·n·(n − 1)` for the occupancy `n ≥ 1` (the granted request counts), with no table and no cut-off. This is how a single-writer database whose throughput falls as concurrency grows (a constraint on database concurrency) is stated; its parameters come from calibration ([Calibration](#calibration-and-sensitivity)).

**Settling.** After phase 2 of a delivery, and after every internal step, each resource the step touched is settled, in input order of resources:

1. *Release.* Recorded releases are applied in effect order.
2. *Enqueue.* Recorded requests are appended to their class queue in creation order, with `since = now`; a `wait-timeout` entry is created at `now + maxWait` when the class has one.
3. *Grant.* Repeat: the next request is the head of the eligible class chosen first by (priority descending, then the head's `since`, then its `seq`) under `priority`, or the oldest eligible head by (`since`, `seq`) under `fifo`. A class is eligible when its head's units fit: `held(class) + units ≤ limit(class)` and `units ≤ free − Σ_{other classes k} max(0, reserved(k) − held(k))`. Within a class service is strictly FIFO; an ineligible class does not block other classes. A grant removes the request and its `wait-timeout` entry, adds the units to the requester's holding, records `waited = now − since`, and either draws the demand and creates `service-done` at `now + service time` (`use`) or emits `then` at `now` (`acquire`). Stop when no class is eligible.
4. *Bounds*, in this order: each class with a `queueBound`, in declaration order, then the resource's `queueBound`. While a bound is exceeded, one request is removed:
   - `refuse`: the newest waiting request (largest `since`, then `seq`) of that class, or for the resource bound of all classes; it gets its `refused` event at `now` with reason `bound`;
   - `drop`: the same request, with no event (recorded as `dropped`);
   - `shed-oldest`: for a class bound, the oldest waiting request of that class; for the resource bound, under `fifo` the oldest waiting request overall, under `priority` the oldest of the lowest-priority class that has one; it gets `refused` with reason `shed`.

Grants happen before bounds are checked, so a request served at once never counts against a bound. A `service-done` step releases the units, emits `then` (targeted at the requester, at `now`) and settles. A `wait-timeout` step removes the request, emits `refused` with reason `timeout` and settles. **Every path that removes a waiting request (a grant, a refusal or drop at a bound, a shed, a crash) deletes its `wait-timeout` entry in the same step**, so a `wait-timeout` step always finds its request still waiting. An orphaned entry therefore cannot occur in the semantics; were an implementation to take one, the step would change and record nothing, and the differential check would report the difference.

**Invariants**, to be proved in Lean of the step: for every resource, class and configuration, `held(class) ≤ limit(class)`, `Σ held ≤ capacity` (while no timed `set-capacity` has lowered it; see below), `waiting(class) ≤ queueBound(class)` and `Σ waiting ≤ queueBound` after each settled step, and every request is in exactly one of waiting, held, refused, dropped or completed. **Deadlock freedom is not guaranteed**: two instances that each hold one resource and wait for the other's deadlock, as they would in the system; a claim can ask the explorer to look for it (`never` an outcome where requests wait with nothing in service), and the queue-length metrics show it in a simulation.

### Workloads

A workload generates queue entries from outside the behaviors. Each arrival is an event entry with source `{kind: "arrival", workload, n, client}`, `n` its number in the workload from 0, and payload fields added to its generated payload: `request` = `"<workload>#<n>"`, and when the workload has clients, `client` and `address` (names configurable with `requestField`, `clientField`, `addressField`). **A `horizon` is required** in every scenario with a workload, with `warmup < horizon`; arrivals at or after the horizon are not created.

**Open workloads** (`kind: "open"`), each for one event:

- `process`: `poisson` or `constant`.
- `phases`: a list of `{from, until, rate}`, times in base units, `rate` a rate `{num, den}` per second or a ramp `{from: {num, den}, to: {num, den}}`. Consecutive phases make a step; `repeat: <period>` repeats the list (on/off bursts); outside every phase there are no arrivals. A constant process may not ramp.
- `batch`: optional distribution of the number of arrivals at one instant, default `fixed 1`; at least 1 (a `fixed` batch below 1 is a validation error, a drawn size below 1 counts as 1).
- `clients`: optional `{count: U, pick: "uniform" | "round-robin", addresses?: {groupSize: <dist>}}`, `pick` defaulting to `uniform`; `round-robin` gives arrival entry `n` (the workload's entries counted from 0) client `n mod U`. `client` is `"<w>:<k>"`. With `addresses`, users are grouped onto addresses at the start of the run: address `a` gets a group size `g_a` drawn from stream `groups:<w>` (at least 1), users `k` in order fill address 0, then 1, and so on, until all `U` users have one (a drawn size below 1 counts as 1); `address` is `"<w>@<a>"`. Without `addresses`, `address` equals `client`.
- `legitimate`: `true` or `false`, used by the false-positive metric.
- `maxArrivals`: optional cap on arrival **entries**; an instant that would pass it is created with only the remaining entries, and no instant follows (required for exploration, [Exploration](#exploration-and-sampling)).
- `payload`: per field, a literal, `{sample: <dist>}`, `{choose: [values], weights: [integers]}`, or `{counter: true}` (the value of `n`).

**When and in what order arrivals are made.** A workload keeps one future *arrival instant* in the queue. An instant at scheduled time `t_n` consists of `b` entries with consecutive `seq` and the same time. Computing an instant draws, in this order, which is also its order in `steps[].draws`: its time (`arrival:<w>`, Poisson only), the batch size `b` (`batch:<w>`, when `batch` is not fixed), then for each of its `b` entries in order the client (`client:<w>`, for `pick: uniform`) and the payload fields in declaration order (`payload:<w>:<field>`). When the **first** entry of an instant is taken as the head of a step, the next instant is computed and created before anything else happens in the step (drop, delay or delivery), so its sequence numbers precede every number the step creates. Only the original first entry carries the mark `first`; a delayed copy does not keep it. In addition each workload keeps `created`, the number of instants it has created, and instant `n + 1` is created only when `created = n + 1`, so it is created exactly once whatever faults do to the entries of instant `n`. **`t_{n+1}` is computed from the scheduled `t_n`**, never from the time the entry was delivered, so a delay fault does not move the arrival process. **Start of the run.** After the format-1 initial entries (the scenario's steps, then injected faults), initial entries are created in this order: the `fault-edge` entries of windowed faults, in `faults` order (each fault's `at` edge, then its `until` edge); then each workload in input order, with its initial entries: an open workload's first instant; a closed workload's first issue per client, in client order; a population's `start` entries per client, in client order. Draws made at the start (groups, start offsets, first instants) are recorded in the trace's top-level `initialDraws`, in the shape of `steps[].draws`.

- *phases*: each phase has `from < until`; phases are sorted by `from` and do not overlap (`until` of one ≤ `from` of the next); with `repeat`, the period is at least the last `until`, and repetition `m` shifts every phase by `m · repeat`. A rate counts **instants**: with a `batch` other than 1 the offered request rate is the rate times the mean batch size. Anything else is a validation error.
- *constant*: in a phase (or a repetition of it) of rate `a/b` per second starting at `from`, instant `j = 0, 1, …` of that phase is at `from + floor(j · perSecond · b / a)`, while that is before `until` and before the horizon; `j` starts again at 0 in every phase and every repetition. A phase with rate 0 has no arrivals.
- *poisson*: one draw per arrival instant, **by inverting the integrated rate; there is no thinning and no rejection loop**, so no valid input can reach a cap. `E` is a unit-mean exponential sample: the input's pinned table `unitExponential` ([Lowering](#lowering-distributions)) sampled with a draw from stream `arrival:<w>`, an integer at scale 2^−64. In a phase whose rate is `r(t) = r0 + g·(t − from)` per second (`g = 0` for a constant rate), the next instant after `t_n` (or after the phase's `from`, for its first arrival) is `t_n + s`, where `s` solves `ρ·s + γ·s²/2 = E`, with `ρ = r(t_n) / perSecond` and `γ = g / perSecond` per base unit, all exact rationals, and `s` rounded to the nearest integer (half up):
  - `γ = 0`: `s = round(E / ρ)`;
  - `γ > 0`: `s = round((−ρ + √(ρ² + 2γE)) / γ)`;
  - `γ < 0`: when `ρ² + 2γE < 0` the mass left in the phase is below `E` and the phase has no further arrival; otherwise `s = round((ρ − √(ρ² + 2γE)) / |γ|)`.

  The terms are brought to one integer denominator, and `round((A ± √B) / C)` for integers `A`, `B ≥ 0`, `C > 0` is computed exactly: `⌊(2A + C + isqrt(4B)) / (2C)⌋` for `+`, and `⌊(2A + C − ⌈√(4B)⌉) / (2C)⌋` for `−`, with `isqrt` the integer square root, `⌈√x⌉ = isqrt(x − 1) + 1` for `x > 0` and `⌈√0⌉ = 0` (adding a fraction below 1 to an integer numerator never changes such a floor). If `t_n + s` is at or after the phase's `until`, or at or after the horizon, the draw is spent, no instant is created, and the next phase starts afresh at its `from` with a new draw (exact for a memoryless process); past the horizon nothing more is drawn. A phase with `r0 = r1 = 0` has no arrivals and draws nothing; a ramp from 0 is handled by the quadratic directly (`ρ = 0`). Rounding each interarrival to the nearest base unit, rather than down, keeps the rate unbiased. Every `arrival` draw, a spent one included, appears in `steps[].draws` of the step that computes the instant, in the order drawn. An interarrival can round to 0 (at a mean of 100 base units, about 0.5% of them), which puts two instants at the same time; that is harmless: they are delivered in `seq` order, and the explorer may swap them.
- *minimum interarrival*: in an open workload, constant or Poisson (closed and population workloads have no rate), a phase whose mean interarrival at its largest rate, `perSecond / max(r0, r1)`, is below 100 base units is a validation error and a refusal (`Phase <i> of workload "<w>" has a mean interarrival below 100 base units; use a finer unit.`), which keeps the rounding of `s` within 0.5% of the mean.

**Closed workloads** (`kind: "closed"`): `population: N` clients, each issuing `event` (with `client` = `"<w>:<c>"` and `request` = `"<w>#<n>"`, `n` counting the issues of the whole workload in issue order), waiting for the delivery of the `reply` event whose `request` field equals its request id, then thinking for a draw from `think` (stream `think:<w>`) before issuing again; `start` (default `fixed 0`, stream `start:<w>`, drawn for clients in order at the start) offsets each client's first issue. With `timeout`, a client whose reply has not been delivered `timeout` after issuing gives up: the request ends with outcome `timeout` (never censored), a reply delivered later is ignored by the workload and by the metrics, and the client thinks and issues again. A closed client issues at most one request at a time. **Measurement**: a closed population measures each request from its issue, which is correct for that population, but the population throttles itself when the system slows, so a closed workload cannot represent offered load and is not the model of a flood or of open internet traffic; use an open workload for offered-load claims (and see coordinated omission in [What it still does not represent](#what-it-still-does-not-represent)).

**Population workloads** (`kind: "population"`): the clients are instances of a behavior, so they can retry, back off, reconnect and keep state. `{behavior, count: N, start: {event, at: <dist>}, clients?}` creates the keyed instances `"<w>:<k>"` of `behavior` (keyed on `client`) and delivers `start` to each at a time drawn from `at` (stream `start:<w>`, clients in order); everything after that is the behavior's own transitions, timers and emits. Request ids are the behavior's to make (for example `instance + '#' + attempts`). `legitimate` (default `true`) applies to every request whose start entry was emitted by one of its client instances. Retry amplification and reconnect storms are modelled this way.

### Links, payload size and bandwidth

A *link* is declared on a relationship of the model and lowered to `{id, from, to, latency?, bandwidth?, queueBound?, ordered?, fanout?}`: `from` and `to` are component ids, `bandwidth` bytes per second, `latency` a distribution in base units. An emit effect with `via: <link>` and `size: <expr | dist>` (bytes) is sent over the link; a size that is not an integer in `[0, 2^40)` is a failed step (`Size of emit "<event>" must be an integer in [0, 2^40), got <value>.`):

1. *Transfer.* The message joins the link's FIFO transfer queue (one per link; with `fanout`, one per receiver). One message is transmitted at a time per queue; its transfer time is `ceil(size · perSecond / bandwidth)`. Contention is waiting in that queue (store and forward). Beyond `queueBound` the newest message is lost (`link-lost`, no event). On a link that is not `ordered`, a message of size 0, and every message on a link without bandwidth, skips the transfer stage and goes straight to propagation, so it can overtake messages still in transfer. On an `ordered` link with bandwidth, a message of size 0 joins the transfer queue with a transfer time of 0, so it cannot overtake.
2. *Propagation.* At the `link-done` step of a transfer, in this order: a latency is drawn (stream `latency:<link>`); the delivery entry is created at `now + latency`, routed like any entry when it is first taken as head (an explicit `target`, including `reply`, was fixed at the send); then the next message in the queue starts its transfer (its `link-done` entry is created).

Latencies are independent draws, so **messages on a link can overtake each other**, as datagrams can. A link with `ordered: true` delivers in send order: a message's delivery time is `max(now + latency, previous delivery time on that link and receiver)`, which models an ordered stream without its retransmission dynamics.

**Fan-out.** An emit with `fanout: true` over a link to a behavior with instances creates one message per instance (index or creation order), each targeted at its instance and queued in that receiver's own transfer queue with its own `queueBound`; overflow on a fan-out link drops the **oldest waiting** message of that receiver (a realtime stream keeps the newest state); the message in transfer is never dropped. Each receiver queue has the link's full bandwidth: the sender's total egress is not shared among receivers, a limitation listed in [What it still does not represent](#what-it-still-does-not-represent). This is the minimal model of realtime fan-out with per-receiver buffers (realtime fan-out under a per-receiver buffer constraint).

An emit with `via` must not also have `after` (validation error). `simulationInput` derives `via` when exactly one link connects the emitting behavior's subject to the subjects of the behaviors with a transition on the event, and otherwise requires the specification to name the link.

### Latency, timeouts and timers

**Distributions** in the input, all over integers. A draw `r` is an unsigned 64-bit value from a stream:

| `kind` | Fields | Sample |
|---|---|---|
| `fixed` | `value` | `value`, no draw |
| `uniform` | `lo ≤ hi` | `uniformInt(lo, hi)` |
| `table` | `points: [[u, x], ...]`, `u` strictly increasing from `0` to `2^32`, `x` non-decreasing | `u* = r >> 32`; for the segment `u_i ≤ u* < u_{i+1}`: `x_i + floor((u* − u_i) · (x_{i+1} − x_i) / (u_{i+1} − u_i))` |
| `choice` | `values` | simulation: `values[uniformInt(0, len − 1)]`, or `values[0]` when the scenario has no seed; exploration: every value is a successor, and no draw happens |

**`uniformInt(lo, hi)`** = `lo + ((r · (hi − lo + 1)) >> 64)`, the product exact (below 2^117). Its bias is at most `(hi − lo + 1) / 2^64` per value, accepted for determinism without rejection loops. **Categorical `choose`** with integer weights `w_0 … w_{m−1}`, `W = Σ w_i ≥ 1`: `v = uniformInt(0, W − 1)` and the value is the first `i` with `w_0 + … + w_i > v`.

#### Lowering distributions

`simulationInput` lowers what a specification writes to `table`, `uniform` or `fixed`. Every step below is integer arithmetic on `BigInt`, specified to the bit, so every implementation and every JavaScript engine derives the same input; no `Math` function and no `Number` arithmetic is used.

**Pinned tables.** The standard grid is `u = k · 2^22` for `k = 0 … 1023`, then `2^32 − 2^(32−j)` for `j = 11 … 31`, then `2^32` (1,046 points). For a grid point with `u > 0` let `p = u / 2^32`, except `p = 1 − 2^−33` at `u = 2^32`. Two tables hold, at scale 2^−64, the correctly rounded (half to even) values of the unit-mean exponential quantile `−ln(1 − p)` and of the standard normal quantile `Φ⁻¹(p)`. **They are defined by the integer algorithms below**, which anyone can rerun; both were checked to give the correctly rounded value at every one of the 1,045 points against an 80-digit computation (no scaled value lies within 3.9 × 10⁻⁴ of a rounding tie, and the algorithms' errors are far smaller).

- `Qexp(u) = round_half_even(−ln_fp(y) / 2^32)`, with `y = (2^32 − u) << 64` (that is `1 − p` at scale `S`), and `y = 2^63` at `u = 2^32`.
- `Qnorm(u)`: the smallest integer `m` with `Φ_W((2m + 1) << 127) ≥ p · W`, found by bisection over `[−8 · 2^64, 8 · 2^64]`, where `W = 2^192`, `(2m + 1) << 127` is `(m + ½) / 2^64` at scale `W`, `p · W` is exact, and `Φ_W(x)`, for `x` at scale `W`, is:
  - `a = |x|`, `a2 = ⌊a · a / W⌋`; `term = a`, `total = 0`, `n = 0`; repeat `total = total + term`, `n = n + 1`, `term = ⌊term · a2 / (W · (2n + 1))⌋` until `term = 0` (this is `Σ a^(2n+1) / (2n+1)!!`, all terms positive);
  - `dens = ⌊ISQ2PI_W · exp_W(−⌊a2 / 2⌋) / W⌋`, where `exp_W` is `exp_fp` with `S` replaced by `W` and `LN2` by `LN2_W`;
  - `half = ⌊dens · total / W⌋`; `Φ_W(x) = W/2 + half` for `x ≥ 0`, else `W/2 − half`.

  Constants at scale `W`: `LN2_W = round(ln 2 · W) = 4350955369971217654477563090224794165364344896676135745070` and `ISQ2PI_W = round(W / √(2π)) = 2504201280626952864894549311249338563268063356138482501337`.

`unitExponential` in the engine input is the table `[[u, Qexp(u)]]` with `[0, 0]` first, included when a workload is Poisson; its `x` reach 2^69 and are bounded by 2^72. Since a JSON number holds integers exactly only below 2^53, each `u` and `x` of this table is written as a JSON number when below 2^53 and otherwise as a decimal string (digits only, no sign, no leading zeros); a reader accepts either form for every entry, and refuses anything else with `Field "unitExponential[<i>][<j>]" must be an integer in [0, <hi>].` **Hash.** The canonical text of the tables is one ASCII line per grid point with `u > 0`, in grid order, `<u> <Qexp(u)> <Qnorm(u)>\n` (decimal integers, a minus sign for negatives, single spaces, a final newline, no other characters); its SHA-256 is `a23cd2a9566c106701375d5cf75ef982b8db6f3e52c199c47e6239649c840950`. **This replaces an approximation of Φ⁻¹** such as AS 241 (PPND16, accurate to about 10⁻¹⁶, so its last bits at scale 2^−64 would be approximation error, and its coefficients would have to be pinned too).

**Fixed-point arithmetic.** Scale `S = 2^96`. `⌊a / b⌋` is floor division (toward −∞) for `b > 0`; `x << k` and `x >> k` are `x · 2^k` and `⌊x / 2^k⌋`. Constants: `LN2 = round(ln 2 · S) = 54916777467707473351141471128` and `Z99 = round(Φ⁻¹(0.99) · S) = 184312267429221101812985515261`.

- `exp_fp(x)`, for `x` at scale `S`, of either sign: `k = ⌊x / LN2⌋` and `r = x − k·LN2`, so `0 ≤ r < LN2`; then `t = S`, `s = 0`, `n = 0`, and repeat `s = s + t`, `n = n + 1`, `t = ⌊t · r / (n · S)⌋` until `t = 0`; the result is `s << k` for `k ≥ 0`, else `s >> −k`.
- `ln_fp(y)`, for `y > 0` at scale `S`: `k = bitlength(y) − 97`; `m = y << −k` if `k < 0`, else `y >> k`, so `S ≤ m < 2S`; `s = ⌊(m − S) · S / (m + S)⌋` and `s2 = ⌊s · s / S⌋`; then `t = s`, `acc = 0`, `j = 0`, and repeat `acc = acc + ⌊t / (2j + 1)⌋`, `j = j + 1`, `t = ⌊t · s2 / S⌋` until `t = 0`; the result is `2·acc + k·LN2`.
- Every multiplication is exact, every division is the floor stated, each series is evaluated term by term in the order written (no Horner rearrangement), and a series stops exactly when its next term is 0. Checks: `exp_fp(LN2) = 2^97` and `ln_fp(2^97) = LN2` exactly, and `ln_fp(round(e · S)) = S − 16`.

**Families.**

- `exponential {mean}`, the mean `a/b` base units: `x(u) = round_half_even(a · Qexp(u) / (b · 2^64))`, `x(0) = 0`.
- `lognormal {median: M, p99: P}` (base units, `M ≥ 1`, `M < P ≤ 10^6 · M`): `σ = ⌊ln_fp(⌊P · S / M⌋) · S / Z99⌋`. `lognormal {median: M, sigma}`: `σ = ⌊sigma · S⌋`, from the exact decimal. `σ` must be at most `8 · S` (sigma ≤ 8; validation error otherwise). Then for `u > 0`, `z = Qnorm(u) << 32` and `x(u) = round_half_even(M · exp_fp(⌊σ · z / S⌋) / S)`; `x(0) = 0`.
- **A lowered table with any `x` of 2^53 base units or more is a lowering error** (`Distribution "<path>" lowers to values of 2^53 base units or more.`), for every family.
- `empirical {samples}`: the samples converted exactly to base units and sorted, `s_1 ≤ … ≤ s_n`, on the standard grid: `x(0) = s_1`, and for `u > 0` the nearest-rank sample `s_max(1, ⌈u · n / 2^32⌉)` (so `s_n` at `u = 2^32`).
- `empirical {quantiles: [[p, x], ...]}`, `p` exact decimals strictly increasing from `0` to `1` and `x` non-decreasing: the table is these points, with `u = round_half_even(p · 2^32)`, refused if two coincide; not the grid.
- `uniform {lo, hi}` stays `uniform`; `constant` becomes `fixed`.

**Reference outputs**, to be reproduced bit for bit by the implementation's tests:

| Value | Integer |
|---|---|
| `Qexp` at `k = 1` / `512` / `1023` | 18023200333324837 / 12786308645202655660 / 127863086452026556598 |
| `Qexp` at `u = 2^32 − 2` (`j = 31`) / at `u = 2^32` | 396375568001282325453 / 421948185291687636773 |
| `Qnorm` at `k = 1` / `512` / `1023` | −57134530012947273077 / 0 / 57134530012947273077 |
| `Qnorm` at `u = 2^32 − 2` / at `u = 2^32` | 112908024744873384702 / 116914684648236608820 |
| `σ` of `lognormal {median: 1000, p99: 4000}` | 47212867929608158508829714117 (about 0.59591) |
| its `x` at `k = 1` / `512` / `1023` / `u = 2^32` | 158 / 1000 / 6332 / 43678 |
| `exponential {mean: 1250}`: `x` at `k = 512` / `1023` / `u = 2^32` | 866 / 8664 / 28592 |

**Bias of a table.** The mean of a `table` distribution is computed exactly from its points (the trapezoid sum over segments, less the floor of the interpolation), so fixtures state the exact figure rather than an estimate. The trapezoid mean of `Qexp` exceeds 1 by `1.18 × 10⁻⁴` (relative), and the table stops at `33 · ln 2 ≈ 22.9` means.

**Timeouts** come in four forms: a resource class's `maxWait`, a closed client's `timeout`, a population client's own timers, and *timers* on any instance:

- `{timer: <name>, after: <duration | dist>, emit: <event>, payload?}` sets a named timer on the firing instance. A timer is identified by the stable id `<machine key>/<name>`, stored on its entry as `timer`; setting a timer removes every queued entry with that id, then creates the new one. `{cancel: <name>}` removes every queued entry with that id.
- A timer firing is an event entry with source `{kind: "timer", behavior, instance, timer}`, targeted at that instance and delivered like any event. **Faults act on it like on any event**: `drop-event` can lose it, and `delay-event` can delay it; the delayed copy keeps the timer id, so a later `cancel` or re-set still removes it.

### Faults in format 2

The fault kinds of the removed format 1 are kept. A fault may also carry a window `{at, until?}`: it acts only on heads whose time is in `[at, until)`. New kinds:

| Kind | Parameters | Meaning |
|---|---|---|
| `scale-demand` | `resource`, `num`, `den` | Service times of grants on the resource are multiplied by `num/den`, rounded up. |
| `set-capacity` | `resource`, `capacity` | Without a window, the capacity from time 0; with a window, from `at` (and back at `until`). |
| `set-class-limit` | `resource`, `class`, `limit` | A class's limit, likewise. |
| `collapse-classes` | `resource` | The resource behaves as one `fifo` class with no reservation, no class limit and no class bound (the resource bound stays). |
| `replace-demand` | `behavior`, `transition`, `effect`, `demand` | The `use` effect at that index draws from `demand` instead: a scenario variant written as a fault (M/D/1 against M/M/1). |
| `crash-instance` | `behavior`, `instance`, `at`, `restartAfter?`, `notify?` | The instance stops at `at` and restarts after `restartAfter` with its state lost. |

**Validity after the fault mask.** The static checks of resources (Σ reserved ≤ capacity, grantable units) are repeated for every fault mask the scenario admits, with untimed `set-capacity` and `set-class-limit` applied; a mask that breaks them is refused for that run (`Fault "<f>" leaves "<r>" with reserved units above capacity.`), and the explorer reports such masks as refused, not explored.

**Timed faults and their edges.** A windowed fault that changes a resource (`set-capacity`, `set-class-limit`, `collapse-classes`, `scale-demand`) creates internal `fault-edge` entries at `at` and `until`; a `fault-edge` step applies the change and settles the resource. **Lowering capacity mid-run never preempts**: units held above the new capacity stay held until released, no grant happens while `Σ held ≥ capacity`, and the utilisation denominator follows the capacity in effect ([Measured outputs](#measured-outputs)). `collapse-classes` mid-run moves every waiting request into the single FIFO queue in (`since`, `seq`) order.

**Overlapping faults.** "Input order" is the order of the input's `faults` list (the scenario's active faults). The value in effect is a function of the set of faults active on that target, recomputed at every `fault-edge`: for `set-capacity`, `set-class-limit` (per class) and `replace-demand`, the last active fault in `faults` order, else the declared value; for `scale-demand`, the product of every active factor; for `collapse-classes`, collapsed while any is active. When a collapse ends, every waiting request returns to the queue of its own class in (`since`, `seq`) order, and bounds are enforced at that settling. During a collapse every request keeps its declared class for `maxWait` (its timeout entry is unchanged) and for metrics; the collapse changes only the order of service, eligibility and bounds.

**`crash-instance`** (the timed, per-instance form of WG-4704's crash-restart primitive; defined here once, and WG-4704's explorer adds the choice of *when*). It acts at `at`; a `window` is not allowed on it (refusal: use `restartAfter`), and `restartAfter`, a duration or a distribution, says when it comes back. Each instance has an **incarnation**, 0 when created and incremented at each crash. Every queue entry addressed to an instance or acting for it records the incarnation it was created for: targeted events (`then`, `refused`, replies, timers, targeted link deliveries) from their creation, routed entries (per routed behavior) from the moment they are first taken as head, and the `service-done` and `wait-timeout` entries of its requests. At the `fault-edge` at `at`, in this order:

1. the instance is marked down and its incarnation incremented;
2. its timers are removed from the queue;
3. its waiting requests are removed with their `wait-timeout` entries (recorded `refused`, reason `crash`, no event);
4. its requests in service are ended, their `service-done` entries removed and their units released (recorded `released`, reason `crash`), and units it holds by `acquire` are released;
5. when `restartAfter` is set, it is drawn now (stream `restart:<fault>`, if a distribution) and a restart `fault-edge` is created at `at + restartAfter`;
6. the `notify` event, if any, is created at `now` with payload `{behavior, instance}`, broadcast;
7. the touched resources are settled.

**Details.**

- For a keyed behavior, `instance` is the key value (a JSON value). A crash of an instance that does not exist (a key not created yet, an index out of range) or that is already down does nothing and is recorded as `crashed` with nothing removed; it creates no restart edge.
- A restart edge records the incarnation it restores (the one set by its crash); it restarts the instance only if the instance is down at that incarnation, and is a no-op otherwise. So overlapping crashes of one instance cannot restart it early.
- `random` and `any` routes over the up instances: with `u ≥ 1` up, the instance is the `uniformInt(0, u − 1)`-th of them in index order; `round-robin` takes the `(c mod u)`-th and then increments `c`; with none up the entry reaches no instance of that behavior and `c` does not move.
- Only the copy for the affected behavior is dropped. A targeted entry (one behavior) whose instance is down or stale is a `drop` step, recorded `crashed` or `stale`. For a **routed** entry the behaviors whose routed instance is down or stale get an `ignored` entry with reason `crashed` or `stale`, and the other behaviors receive it normally. A **broadcast** skips down instances without an `ignored` entry.
- When every instance of a behavior is down, broadcasts and routes reach none of them and the behavior gets one `ignored` entry with reason `no-instance`.

An entry whose recorded incarnation differs from the instance's current one is **stale**: taken as the head, it is handled as above (an `acquire`'s `then` already queued, a reply, a link delivery, a timer created before the crash). **An entry created for the old incarnation never reaches the new one**: when client C calls S, crashes and restarts, S's reply carries C's old incarnation and is dropped as stale; broadcasts, which name no incarnation, reach whichever instances are up when delivered. While down, the instance is skipped by broadcasts (no `ignored` entry), and an entry routed or targeted to it is dropped (`crashed`). At the restart edge it is up again in its initial state with its initial variables (state lost). Closed-workload clients are not instances and are not affected.

Correlated failures (several instances, a resource and a link together) are written as several faults with windows. The explorer chooses whether each fault acts, not when ([Exploration](#exploration-and-sampling)).

### Randomness

**Generator: SplitMix64, as a family of independent streams.** Every draw belongs to a named stream. The stream key is `k = mix64(seed XOR fnv1a64(name))`, where `fnv1a64` is 64-bit FNV-1a (offset basis `0xCBF29CE484222325`, prime `0x100000001B3`) over the UTF-8 bytes of the name. The `i`-th draw of a stream (from `i = 0`) is `mix64(k + (i + 1) · 0x9E3779B97F4A7C15)`, wrapping, where

```
mix64(z): z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9
          z = (z ^ (z >> 27)) * 0x94D049BB133111EB
          return z ^ (z >> 31)                       (all mod 2^64)
```

So each stream is exactly Vigna's reference `splitmix64` seeded with `k`, and its published outputs are test vectors for both implementations.

Why: it needs only 64-bit wrapping addition, multiplication, xor and shifts, which Lean's `UInt64` and Rust's `u64::wrapping_*` define identically; it passes BigCrush; its state is one counter per stream, so explorer states stay small; and since a draw is addressed by (stream, index), adding a workload or a transition never shifts another stream's values. Rejected: xoshiro256\*\* and PCG (sequential state; independent streams need jump functions or 128-bit multiplication), the Mersenne Twister (2.5 KB of state per stream in every explorer state), ChaCha or Philox (several times the code and proof surface for no need in a simulator), platform generators (not portable).

**Stream names.** Parts are joined with `:`; ids cannot contain `:`, so names are unambiguous. `<effect>` is the 0-based index of the effect in its transition's `effects`.

| Stream | Draws, and when |
|---|---|
| `arrival:<w>` | one per Poisson instant, when the instant before it is taken (or at the start, for the first) |
| `batch:<w>`, `client:<w>`, `payload:<w>:<field>` | per instant / per entry, when the instant is created (order above) |
| `groups:<w>` | per address, at the start of the run |
| `think:<w>`, `start:<w>` | per think time; per client at the start |
| `route:<event>:<behavior>` | per entry routed `random` or `any` (simulation), when first taken as head |
| `size:<behavior>:<transition>:<effect>` | per emit whose `size` is a distribution, when the effect runs |
| `demand:<behavior>:<transition>:<effect>` | per grant of that `use`, at the grant |
| `latency:<link>` | per message, at `link-done` (or at the send when there is no transfer stage) |
| `after:<behavior>:<transition>:<effect>` | per `emit` or `timer` whose delay is a distribution, when the effect runs |
| `sample:<behavior>:<transition>:<effect>` | per `set` with `{sample: <dist>}` |
| `restart:<fault>` | per crash with a `restartAfter` distribution, at the crash |
| `choice` sites | a `choice` in simulation draws from the stream of its site; in exploration it does not draw and the counter does not move |

`fixed` distributions draw nothing. A stream's counter is part of the configuration (`streams`, keyed by name, absent while 0). Because a step is a total function of the configuration, including counters, **the same input, seed and fault set give the same trace and metrics** (claim `simulation-seeded-runs-reproducible`, to be proved in Lean with the seed as an argument of the run). An input that has a sampled site and no seed is refused: `Input samples "<stream>" but declares no seed.` A scenario whose only random sites are `choice` values needs no seed.

**Sequence numbers.** `seq` increments every time an entry is created, including entries later removed (wait-timeouts at a grant, replaced timers, shed requests' entries); removed numbers are never reused.

**Seeds of a set of runs.** Run `r` (from 0) of a claim with base seed `s` uses seed `mix64(s + (r + 1) · 0x9E3779B97F4A7C15)`, the addition and multiplication wrapping mod 2^64, the `r`-th output of SplitMix64 seeded with `s`, so that adjacent runs do not use adjacent seeds.

### Exploration and sampling

**As built (WG-5681).** `exegra prove` explores the behaviour calculus ([Exhaustive exploration in Lean](#exhaustive-exploration-in-lean-exegra-prove)): it varies the delivery order among minimal-time entries, the whole-run fault mask and every outcome of each sampled delay up to a support of 1000 values (a larger support makes the result `incomplete`). A scenario that uses a construct outside the calculus (resources, links, workloads, keyed instances, routes) is reported not covered and is not explored. The decision below is the plan for those constructs.

**Decision: `exegra prove` explores every nondeterministic choice with the sampled draws fixed by a seed, enumerates `choice` values and `any` routes, and never enumerates probabilistic outcomes.** For a scenario with those constructs the successor relation gains:

- the existing choices: order of simultaneous entries, now including `service-done`, `wait-timeout`, `link-done`, `fault-edge`, closed-client timeouts and timer entries; and the fault mask, including the new kinds;
- one successor per value of a `choice` and per instance of an `any` route.

**Ties.** An arrival and a `service-done` at the same time are delivered in `seq` order by the simulator; the explorer delivers them in both orders, as any simultaneous entries.

Sampled draws come from the seed's streams, whose counters are part of the explored state. `prove` takes `--seed <s>` (repeatable; default the scenario's `seed`). **For a seeded model, the seed comes first in the result**: *under seed s only: holds on all N configurations reachable within the bound*, one theorem per seed. **The verified criterion, stated once.** A result may be shown as verified only when the engine input contains **no distribution other than `fixed` or `choice` anywhere**, and **no element that draws**: no Poisson process, no `batch`, `think`, closed `start`, population `start.at`, emit `size` or `after`, timer delay or `restartAfter` other than `fixed` or `choice`, no client `pick: uniform`, no `groups`, no `choose` or `sample` payload field, and no `random` route. The check is static, on the input; `choice` values and `any` routes are enumerated. Otherwise the result names the seeds and is never shown as verified.

**Performance scenarios and the explorer.** A scenario with workloads is explorable only with an explicit short `horizon` and a `maxArrivals` on every workload; without them `prove` refuses, and with them `incomplete` (the state budget ran out) is the expected result for anything but a handful of arrivals. Keyed populations are beyond reach: an edge rate limiter keyed on 15,000 clients has a state per client, and is checked by simulation and metric claims, not by exploration. The explorer cannot search *when* a timed fault acts under a fixed seed; it chooses only whether (WG-4704 adds timing as a choice), and every result on a scenario with windowed faults carries the scope "fault times fixed as declared".

Rejected alternatives: refusing stochastic models (it would lose the check that pool protocols, timeouts and leases are safe under every interleaving), and enumerating bounded discrete distributions (probability treated as nondeterminism; the branching explodes after a handful of arrivals; a model that wants every outcome explored says `choice`).

### Scenario, horizon and outcome

A format-2 scenario adds `seed`, `horizon` (required with workloads), `warmup` (default 0, `warmup < horizon`), `stopAt` (optional, `≥ horizon`: entries later than it are never taken) and `output` (`trace` or `metrics`). The run continues after the horizon until the queue is empty, the step limit, an error, or `stopAt`; outcome `stopped` means the head's time exceeded `stopAt`. Steps of every kind count against `stepLimit` (`maxSteps` in the specification).

**Truncation.** A run is *truncated* when it ended `step-limit` or `error`, or `stopped` while a measured request was still open. A truncated run reports its metrics, marked `truncated: true`, and **never satisfies a metric claim**. Signals are taken as constant from the last step to the end of the window.

### Request lifecycle

Every rule about requests (their samples, sample counts, bucket power, derived metrics, `approx`, `relativeTo` and calibration) follows from this section and refers to it.

**Request classes.** `{id, start: {event, workload?}, key, ends: [{event, outcome}]}`, with `outcome` one of `ok`, `refused`, `timeout`, `error`. A boundary class is derived from a contract with a `correlation` field: its request event starts, its response event ends `ok`, its error event ends `error`.

**States.** A request is *started*, then either *ended* with exactly one outcome, or *censored* when the run ends first. A request never ends twice and never restarts.

**Start.** A request of class C starts at the step in which an entry carrying C's start event (from C's workload, if one is named) is **first taken as head**, whatever that step then does to it. Its key is the entry's `payload[key]`; its start time is the entry's `scheduledAt` (the time it was first queued for, kept by delayed copies). A delayed copy taken later belongs to the same request: every delayed copy carries `copyOf`, the sequence number of the original entry (kept by copies of copies), so a copy is told from the original even when the delay is 0 and the copy is taken at the same time; only an entry without `copyOf` can start a request. An entry with no `key` field starts no request (counted as `unkeyed`); an entry whose key is that of a started, unended request of C starts none (counted as `duplicate`).

**Lost starts.** The start entry must be *handled*: taken in a `deliver` step in which at least one transition fires on it. When the step that takes the start entry, or after delays its last copy, does not handle it, the request **ends at once with outcome `error`** at that step's time:

| What happens to the start entry | Step | Request |
|---|---|---|
| a `drop-event` fault drops it | `drop` | ends `error` |
| its target is down (`crashed`) or its incarnation is old (`stale`) | `drop` | ends `error` |
| delivered, but every behavior ignores it (`no-transition`, `guard-false`, `disabled`, `no-instance`, `crashed`, `stale`) | `deliver` | ends `error` |
| a `delay-event` fault delays it | `delay` | started; the copy decides |
| the step fails (an expression error) | failed | the run ends `error` and is truncated; the request is censored |

**End.** A started request ends at the first step that **delivers** an end event of its class whose `payload[key]` equals its key, with that end's outcome. *Delivered* means the entry is the head of a `deliver` step that does not fail, whether or not a transition fires: an end event often goes to the outside, where no behavior listens. An end entry that is dropped, delayed, crashed or stale is not delivered and ends nothing; a later end still can. Besides end events, a request ends only when a closed client's `timeout` fires (outcome `timeout`; a later reply is ignored). Refusals, timeouts and errors inside the model end a request only through end events the class declares, so a class lists the model's `refused` and timeout events among its ends. End entries for an ended request are ignored (counted as `lateEnds`). A request not ended when the run ends is censored.

**Into the metrics.**

- *Measured* requests are the started requests whose start time lies in the window (W, a claim's window, or a bucket).
- *Samples*: an `ok` request gives `end − start`; a `refused`, `timeout` or `error` request, and a censored one, gives **+∞**. A mean over samples that include +∞ is undefined. A claim restricted to `outcomes: ["ok"]` reports how many requests it left out.
- *Sample count* `n`: the measured requests. A lost, refused or unanswered request still counts, so `n` is fixed once the start entries have been taken.
- *Who starts the class* decides what an underpowered statistic means. A class is **open-started** when every start entry of it comes from an open workload: then `n` depends only on the arrivals, and an underpowered run is left out, an underpowered or empty bucket is skipped. Otherwise (a closed or population workload, or start events emitted by behaviors) `n` depends on how the system behaved, and an underpowered run **does not satisfy**, an underpowered or empty bucket **does not satisfy** in every derived metric.
- *Waiting time* at a resource: one sample per request enqueued in the window, `waited` for a grant and +∞ for a request removed without one (refused, shed, dropped, timed out, crashed); its count is the requests enqueued.
- The metrics also report `unkeyed`, `duplicate` and `lateEnds` per class, and, per outcome, how many requests ended that way and how many were censored.

### Meters

A meter is a windowed measurement that behaviors can read, which is what a load-shedding ladder or an adaptive limiter needs. Declared as `{id, of, measure, window, q?}`:

- `of`: a request class (with an optional outcome set), an event (deliveries), a resource class (refusals by reason) or a transition (firings);
- `measure`: `count`, `rate` (count per second), `ratio` (count of the outcome set over all ends of the class), or `quantile` (`q`, of response times of the class's requests that ended in the window);
- `window`: a duration `w`. At a step whose head has time `t`, the meter covers what happened at times in `(t − w, t]` **before** this step (the start-of-step configuration).

`<meter>.value` is the measure as a double: `count` exactly; `rate` and `ratio` as the IEEE division of two integers below 2^53 (correctly rounded in both Lean and Rust); `quantile` by nearest rank, `null` when empty. `<meter>.count` is the number of observations. `window` is at least 1 base unit. A window with no observation gives `count` 0, `rate` 0, and `value` `null` for `ratio` and `quantile`; a `ratio` whose denominator is 0 is `null`. A `quantile` meter includes the +∞ samples of requests that ended without `ok`; when the rank falls on one, `value` is `null` and `<meter>.infinite` is `true`. Reading `null` in arithmetic or a comparison is a failed step, as in format 1, so a guard tests `<meter>.count` first. The configuration keeps, per meter, the observations inside its window (bounded by the window and the rates).

### Measured outputs

Metrics are a **pure function of the run**, defined in Lean over the step sequence and computed by the engine (so `output: "metrics"` gives the same numbers as the full trace), checked differentially. Every number is an integer or a pair of integers; decimals are formed by the consumer.

**Window and attribution.** `W = [warmup, horizon)`. **Every metric about a request is attributed by its start time**: a request is *measured* when its start is in W, whenever it ends. Waiting times are attributed by the request's `since`. Signals (units held, requests waiting, transfers in progress, capacity) are piecewise constant between steps; the value in effect at `warmup` is the one after the last step at or before `warmup` (the initial configuration's if none), and the last value holds until `horizon`. The integral over W is an exact integer.

**Requests** are defined in [Request lifecycle](#request-lifecycle): when they start and end, their outcomes, their samples and their counts. Every request metric below is computed from that section's samples.

| Metric kind | Per run, reported | `count` | `ratio` | `mean` | `p<q>`, `max` |
|---|---|---|---|---|---|
| `response-time` (class) | count, sum and max of finite samples, number of +∞, quantiles | measured requests | finite / measured | sum / count over finite samples, **undefined if any sample is +∞** | nearest rank over all samples |
| `outcomes` (class, optional outcome set) | count per outcome, censored | requests in the set | in set / measured | — | — |
| `throughput` (class) | measured requests ended `ok`, and `|W|` | that count | count · perSecond / `|W|` (per second) | — | — |
| `utilisation` (resource or class) | `busy` = ∫ held, `capacityTime` = ∫ capacity | — | busy / capacityTime | — | max held |
| `queue-length` (resource or class) | ∫ waiting, `|W|`, max within W | — | ∫ waiting / `|W|` | same as ratio | max |
| `waiting-time` (resource or class) | per request enqueued in W: `waited` for a grant, +∞ for a request removed without one | requests enqueued | — | sum / count, undefined with a +∞ sample | nearest rank |
| `refusals` (resource or class) | by reason and `dropped` | refusals | refusals / requests | — | — |
| `false-positives` (class) | measured requests of `legitimate` workloads that ended `refused` | that count | refused / measured legitimate | — | — |
| `transitions` (transition) | firings in W | firings | — | — | — |
| `link` | ∫ transfers, bytes, lost | messages | busy / `|W|` | — | — |
| `cost` | Σ counted quantity × price ([Cost](#cost)) | cost | — | — | — |

A statistic not marked for a kind is a validation error.

**Percentiles.** For `p = a/b` (an exact decimal such as `"0.99"`) over `n ≥ 1` values sorted ascending with +∞ last: the value at rank `max(1, ceil(a · n / b))` (nearest rank). +∞ is reported as `null` with `infinite: true`; `n = 0` as `null` with `empty: true`. Nearest rank is an observed value, needs only integers, and is the order statistic the confidence method reasons about.

**Time series and phases.** With `series: {bucket: b}`, `horizon − warmup` must be a multiple of `b` (a validation error otherwise), so there is no partial bucket; bucket `i` is `[warmup + i·b, warmup + (i + 1)·b)`. Each metric is reported per bucket, requests attributed by start time and signals integrated over the bucket (denominator `b`). A bucket statistic is `null` when the bucket is empty or underpowered. What a `null` bucket means depends on who starts the class ([Request lifecycle](#request-lifecycle)):

- for an **open-started** class, a `null` bucket is **skipped** (it reflects arrivals, not the system), and results report how many were skipped;
- for any other class, and for every `time-to-recover`, a `null` bucket **does not satisfy**.

Two derived metrics read the series, with `after` on the bucket grid (a validation error otherwise); **their value is the duration `t − after`**:

- `time-to-first {metric, op, bound, after}`: `t` is the start of the first bucket starting at or after `after` whose statistic is non-null and satisfies the condition (skipping or failing `null` buckets as above); `null` if none.
- `time-to-recover {metric, op, bound, after, hold}`: `t` is the earliest bucket start `≥ after` such that the buckets whose **start** lies in `[t, t + hold]` all lie inside `[warmup, horizon)` and **every one of them is non-null and satisfies the condition**; `null` if none.

A `null` derived metric fails any bound on it. **Series aggregates**: a claim may take `{over: "buckets", aggregate: "max" | "min" | "mean"}` of a bucketed statistic within its window (the busiest second of `transitions`, for example). For an open-started class (and for counts, which are never `null`) the aggregate is over the non-null buckets and is `null` when every bucket is; for any other class a `null` bucket makes the aggregate `null`, which does not satisfy. A claim may be scoped to a sub-window `{from, until}` on the grid, or to a workload phase (`<workload>.<phase index>`), which replaces W for that claim.

#### Cost

A *price* is `{id, counts, price, currency, source, date}`: `counts` names a counted quantity (deliveries of an event, ends of a class with an outcome, bytes over a link, unit-time held of a resource, instance-time of a behavior), `price` an exact rational `{num, den}` (each below 2^32) of `currency` per counted unit, with its source and date. The counted units are: one delivery, one ended request, one byte, one unit of a resource held for one second, one instance up for one second (held and up times are integrated in base units and divided by `perSecond`). The `cost` metric is Σ quantity × price over W, an exact rational reduced to lowest terms, per price and in total, and per bucket in a series. Prices are kept apart from components in a price profile; the cost aspect (WG-4669) owns the profiles and the money reports, and reads these metrics.

### Claims over metrics

A new claim method, `metric-bound` (kind `measured`):

| Parameter | Meaning |
|---|---|
| `scenarios` | Scenarios whose runs are measured (each is evaluated separately; all must hold). |
| `metric` | `{kind, of, statistic, outcomes?, window?}` from the table above. |
| `op`, `bound` | `<=`, `<`, `>=` or `>`, and the bound with its unit (`"30 ms"`, `"0.8"`, `"100/s"`). |
| `approx` | Instead of `op`: `{value, tolerance}` (relative), for agreement with an analytic result. |
| `window` | Optional `{from, until}` on the grid or a phase `<workload>.<index>`: the claim's window, replacing W. |
| `relativeTo` | `{metric, window?}`: another metric of the same run, with its own window (default the claim's): the per-run statistic is the exact ratio of `metric` to it, compared with `bound` (a number); `null` or a zero denominator does not satisfy. |
| `fraction` | β, the fraction of runs whose statistic must satisfy the bound. Default `0.95`. |
| `confidence` | 1 − α. Default `0.95`. |
| `runs` | N. At least the smallest N with `β^N ≤ α`, compared exactly as rationals (59 for the defaults), or validation reports an error: the claim could never hold. |
| `seed` | Base seed; run seeds as in [Randomness](#randomness). |
| `negatives` | `{scenario, faults}` pairs under which the claim must **fail** at the same confidence (as trace claims' negatives, WG-4711). `scenario` is one of the claim's scenarios, or a *variant*: a scenario declaring `variantOf` one of them, for a twin no fault can express. |
| `controlNegatives` | `{scenario, faults}` pairs, each a twin's faults on a control scenario, under which the claim must **hold**. |
| `calibratedBy` | Calibrations the model must pass ([Calibration](#calibration-and-sensitivity)). |

**Method: an exact binomial test on independent runs (distribution-free, order-statistic form).** Within one run, response times are autocorrelated, so pooling them as independent samples would overstate confidence. Runs with distinct seeds draw from disjoint streams, so their per-run statistics `T_1 … T_N` are independent and identically distributed (assumption `seeded-streams-independent`). Let `k` be the number of runs whose `T_r` satisfies the bound; a run whose statistic is undefined or +∞ against an upper bound, or a truncated run, does not; an underpowered run is left out (below). With β = a/b exact:

- **holds** when `P[Bin(N, β) ≥ k] ≤ α`;
- **fails** when `P[Bin(N, β) ≤ k] ≤ α`;
- **inconclusive** otherwise.

Both tails are exact rationals (`BigInt`), with no floating point and no randomness. This is the one-sided Clopper-Pearson bound written as a test. **What it means in practice, at the defaults with N = 59**: *holds* needs all 59 runs to pass (`0.95^59 = 0.0485`); a single failing run gives *inconclusive*; *fails* needs 7 or more failing runs (52 or fewer passes: `P[Bin(59, 0.95) ≤ 52] = 0.027`, while 53 passes give 0.074). More runs make one failure affordable: the result says how many runs would decide an inconclusive one.

**Run count policy.** N is fixed before the runs and never extended after seeing results: stopping when the result looks good would void the confidence. The default is 59 at 95%/95%, a screening count that holds only with no failing run. A claim expected to hold despite an occasional failing run declares more: 93 runs allow one failure (and fail at 9 or more), 150 allow two (fail at 13 or more), 300 allow eight (fail at 22 or more). The fixtures use 59.

**Sample counts and underpowered runs.** Samples and their count `n` are those of [Request lifecycle](#request-lifecycle). A statistic is *underpowered* when a quantile `q` has `n · (1 − q) < 30`, a mean has `n < 30`, or a ratio of counts (outcomes, refusals, false positives) with bound `b` has a denominator `d` with `d · min(b, 1 − b) < 30` (fewer than 30 expected on the rarer side, so a false-positive ratio ≤ 0.001 needs 30,000 requests). Throughput, utilisation, queue length, `max` and `count` are never underpowered; validation warns that a `max` grows with `n`.

- For an **open-started** class an underpowered run is **left out**, neither a pass nor a fail. For any other class it **does not satisfy the bound**, so a collapse can never turn `fails` into `inconclusive`. Open-startedness is computed from the engine input (`openStartedClass`, `src/core/metric-claims.js`), never assumed: the class's named workload is open, or, with none named, an open workload issues its start event and no closed or population workload, behavior `emit` or `then`, scenario step or injected fault can. A run with `duplicate` starts is never left out either, since a stalled system with keys drawn from a small pool lowers `n`.
- The test runs on the `N'` runs not left out, with the thresholds for `N'`. At the defaults `holds` needs `N' ≥ 59` with every run passing, so with N = 59 a single run left out makes `holds` impossible; with N = 93 and one run left out, `holds` needs all 92 (91 of 92 gives 0.052). `fails` stays reachable: with `N' = 58` it needs 51 or fewer passes, with `N' = 55`, 48 or fewer.
- A `relativeTo` run is underpowered when either of its two metrics is.

**Validation refuses** a quantile, mean or ratio claim on an open-started class whose expected sample count, from the open workloads' declared rates over the claim's window, is below the rule (`Claim "<c>" expects <n> samples on its rarer side; at least 30 are needed.`), and for a series claim it applies the rule **per bucket** (`Bucket <b> of claim "<c>" expects <n> samples beyond its quantile; use a longer bucket.`): a p99 per bucket of 1 s needs 3,000 requests per second. For other classes it warns.

**`approx`.** It uses the `N'` runs kept by the rules above and is `inconclusive` when any run is truncated. With `T_(1) ≤ … ≤ T_(N')`, the interval `[T_(j), T_(N'+1−j)]` with the largest `j` such that `P[j ≤ Bin(N', 1/2) ≤ N' − j] ≥ 1 − α` covers the **median** of the per-run statistic with probability at least 1 − α (the sign test over the `N'` runs kept, not the `N` declared; for `N' = 59` it is `[T_(22), T_(38)]`, coverage 0.964). No such `j` exists below `N' = 6` at α = 0.05, and then the result is `inconclusive`. This assumes independent runs and a continuous distribution of `T` (ties make it conservative). The claim holds when the interval lies inside `[v(1 − tol), v(1 + tol)]`, fails when it is disjoint from it, and is inconclusive otherwise. **The median of per-run means is not the analytic mean**: the per-run mean of a finite run is biased by the warm-up and its distribution is skewed, so the median sits slightly below the mean; long horizons shrink the gap, and the fixtures state the measured gap next to the tolerance.

Rejected: the bootstrap (asymptotic only, poor at extreme quantiles from few runs, and it needs its own resampling randomness); normal-theory intervals (assume a shape tail latencies do not have); pooled within-run percentiles (not independent).

**Verdict and status.** A metric claim is **never** shown as verified, and its positive result is **never counted as supported by evidence**. The results are:

| Result | Status | Shown as |
|---|---|---|
| holds | `model-holds` | *holds in the model at 95% confidence over 59 runs (59/59); parameters assumed* |
| fails | `violated` | *fails in the model at 95% confidence over 59 runs (50/59)*, with the worst run's seed, replayable as a trace |
| inconclusive | `inconclusive` | *inconclusive over 59 runs (58/59); about N runs would decide it* |

`model-holds` is a new status, distinct from `supported` and `verified`, always carrying the scope "model only; parameters as stated" and the qualifier `unvalidated` until calibration passes, or `extrapolated` when a scenario lies outside the validated envelope. The vocabulary is coordinated with WG-4703's honest verdicts, which this follows. Every result carries `runs`, the seeds, `k`, β, the confidence, the minimum, median and maximum of `T_r`, per-run sample, +∞, underpowered and truncated counts, `N'`, and the window. A claim that holds while one of its negatives does not fail, or one of its control negatives does not hold, is `inconclusive` (vacuous, or failing for a reason other than the stated one).

#### Calibration and sensitivity

- **A recorded load run is evidence**: an `evidence` entity of kind `load-run` with its date, an expiry date, the system version it ran, and the component revisions it binds to (the semantic hash of each component it measured, as the specification recorded it), the workload it drove (offered rate per class, mix, clients, instance counts, payload sizes, active faults), the capacities, its warm-up and window, and what it measured (p50 and p99 per class, utilisation per resource, the knee: the offered rate at which p99 crossed a stated value), with each repeat's values when it was repeated. Its percentiles use the convention of the model: every request that was refused, timed out or failed counts as +∞; a load run whose percentiles leave them out says so and cannot calibrate a percentile.
- **Dates and revisions.** A claim evaluation takes an `asOf` date as input and records it in its result; evidence whose expiry is before `asOf` validates nothing. The wall clock is never read. Evidence whose bound component revisions differ from the current specification's validates nothing either.
- **Calibration** `{id, scenario, fit, holdout, tolerance, runs}`, `runs` the number of model runs per hold-out run (default 59). `fit` names the load runs used to set `to-be-measured` parameters (USL `alpha` and `beta`, for example); `holdout` names other load runs, never used for fitting (validation error otherwise). For each hold-out run the model is run with that run's workload, capacities, warm-up and window (validation requires them equal), over seeded runs at the claim's confidence. For each compared statistic:
  - the **band** is `[m(1 − tol), m(1 + tol)]` for a single measurement `m`, and `[min_i m_i · (1 − tol), max_i m_i · (1 + tol)]` over repeats `m_1 … m_r`;
  - the model side is the sign-test interval of the median of the per-run statistic over the `N'` runs not left out (underpowered runs are left out as in a claim). It needs `N'` at least the smallest N with `2^(1−N) ≤ α` (6 at α = 0.05, 8 at α = 0.01); with fewer, or with any truncated run, the calibration does not pass;
  - the statistic passes when the interval lies inside the band.

  A calibration passes when every compared statistic of every hold-out run does.
- **Margin.** It is taken at the rank the test uses. Let `k` be the smallest number of passes out of `N'` for which the test reads `holds`. For an upper bound `B ≠ 0`, with the per-run statistics sorted ascending, `T*` is the one at rank `k` and the margin is `(B − T*) / B` (at `N' = 59`, `k = 59`: the largest run); for a lower bound, sorted descending, likewise with `(T* − B) / B`. For `B = 0` the margin is undefined and the claim reads `unvalidated` with that reason. A `relativeTo` or time-to claim has an `op` and a `bound` and uses the same rule on its statistic. For `approx {value: v, tolerance}` with interval `[lo, hi]`, the margin is `min((v(1 + tol) − hi) / v, (lo − v(1 − tol)) / v)`. A calibration whose tolerance on the claim's statistic exceeds the margin cannot validate the claim.
- **`unvalidated`.** A metric claim reads `unvalidated` when it names no calibration, when one fails, when its evidence has expired at `asOf` or is bound to another component revision, or when a tolerance exceeds its margin.
- **Operating envelope.** The tested points are the parameter vectors of the passing hold-out runs, over: offered rate per class (for a phased workload, two coordinates: the time-average of the declared rate over the window, and its peak), capacities, mix, instance counts, payload sizes, and the set of active faults. A claim's scenario is inside when its fault set equals that of some tested points and its other coordinates lie in the convex hull of those points, decided by a linear program solved in exact rational arithmetic (points with another fault set are not used); otherwise the result is flagged `extrapolated`. With fewer tested points than coordinates the hull is degenerate and little is inside: that is intended.
- **Sensitivity.** Every parameter tagged `assumed` or `to-be-measured` declares a `range`, from its source (a requirement's tolerance, the spread a vendor states) or from the calibration's uncertainty; a metric claim that uses a parameter without one is a validation error. Each parameter is varied alone to both ends of its range; it is *flagged* when an end flips the verdict or moves `T*` by more than half the margin. Every pair of flagged parameters is then varied together at the four corners. The result lists first the parameters and pairs that flip the verdict.

### Engine input and trace format version 2

**Engine input**, `format: "exegra-sim-input"`, `version: 2`. The fields of the removed version 1 keep their meaning, with times and durations integers of the base unit. New and changed fields:

| Field | Type | Meaning |
|---|---|---|
| `version` | `2` | |
| `time` | `{unit, perSecond}` | `unit` ∈ `tick`, `s`, `ms`, `us`, `ns`. |
| `scenario.seed` | decimal string or `null` | Unsigned 64-bit seed; required when anything samples. |
| `scenario.horizon`, `warmup`, `stopAt` | integer or `null` | Horizon required with workloads; `warmup < horizon ≤ stopAt`. |
| `scenario.output` | `"trace"` \| `"metrics"` | Default `"trace"`. |
| `scenario.steps[].target` | `{behavior, instance}` | Optional. |
| `behaviors[].instances` | `{count}` \| `{key, max}` | Optional. |
| `transitions[].effects` | list | Adds: `emit` with `after` an integer or a distribution, `target: "reply"`, `via`, `size`, `fanout`; `use`, `acquire`, `release` (with `class`); `timer`, `cancel`; `set` with `to: {sample: <dist>}`. |
| `routes` | `[{event, behavior, by, field?, resource?}]` | `by` ∈ `key`, `round-robin`, `random`, `any`, `least-busy`. |
| `resources` | `[{id, kind, capacity, discipline, queueBound, overflow, demandFactor, classes}]` | |
| `links` | `[{id, from, to, latency, bandwidth, queueBound, ordered, fanout}]` | |
| `workloads` | `[{id, kind, ...}]` | Open: `event`, `process`, `phases`, `repeat`, `batch`, `clients`, `legitimate`, `maxArrivals`, `payload`. Closed: `event`, `population`, `think`, `start`, `reply`, `timeout`, `payload`, `legitimate`. Population: `behavior`, `count`, `start`, `clients`, `legitimate`. |
| `unitExponential` | `[[u, x]]` | The pinned unit-mean exponential table, when a workload is Poisson. |
| `requests` | `[{id, start, key, ends}]` | Request classes. |
| `meters` | `[{id, of, measure, window, q}]` | |
| `prices` | `[{id, counts, price: {num, den}, currency}]` | Exact rational prices per counted unit; source and date stay in the specification. |
| `metrics` | `{quantiles, series}` | Quantiles as exact decimals (default 0.5, 0.9, 0.99); optional series bucket. |
| `faults[]` | | Optional `window {at, until}` (not on `crash-instance`); adds kinds `scale-demand`, `set-capacity`, `set-class-limit`, `collapse-classes`, `replace-demand`, `crash-instance`. |
| distributions | `{kind: fixed \| uniform \| table \| choice, ...}` | |

Refusals, in this order after those of the fields version 1 had: an unknown time unit; an integer out of its bound (`Field "<path>" must be an integer in [<lo>, <hi>].`); a malformed seed; a reserved name; an unknown id in a route, resource, link, workload, request class, meter, price or fault; a malformed table; a phase below 100 base units of mean interarrival; a rate or bandwidth under unit `tick`; reserved units above capacity or above a class limit, or a request that can never be granted; a `window` on `crash-instance`; a population larger than its behavior's `max`; a sampled site with no seed; `via` together with `after`; workloads without a horizon, or `warmup ≥ horizon`, or `stopAt < horizon`.

**Refusals as built.** Beyond the refusals of the fields version 1 had, both engines refuse with these messages (Format2.lean is the reference): `Unknown time unit "<u>".`; `Field "<path>" must be an integer in [<lo>, <hi>].`; `Field "scenario.seed" must be a decimal string in [0, 18446744073709551615].`; `Id "<x>" is reserved: it names more than one element.`; `Variable "<name>" of "<b>" is reserved.`; `Route names "<x>", which is not an event.` (or a behavior, or a resource); `Route of "<e>" to keyed "<b>" must be by key.`; `Effect uses "<r>", which is not a resource.`; `Effect names no class of "<r>".`; `Effect sends over "<l>", which is not a link.`; `<effect>: "via" cannot be combined with "after".`; `Class "<c>" of "<r>" can never grant <n> units.`; `Resource "<r>" reserves more units than its capacity.`; `Class "<c>" of "<r>" reserves more units than its limit.`; `Fault "<f>": inject-event takes no window.`; `Fault "<f>" has an empty window.`; `Fault "<f>" names no use effect.`; `Fault "<f>" names "<r>", which is not a resource.`; `Fault "<f>" names no class of "<r>".`; `Fault "<f>" leaves "<r>" with reserved units above capacity.` (or `above a class limit.`); `<what>: fault kind "crash-instance" is not implemented (WG-4664).`; `Unit tick has no rate.`, `Unit tick has no rate; "workloads[<i>]" needs one.` and `...; "links[<i>]" needs one.`; `Workload "<w>" generates "<e>", which is not an event.`; `Workload "<w>" waits for "<e>", which is not an event.`; `Workload "<w>" has a timeout that reaches 2^53 after the horizon.`; `Workload "<w>" names "<b>", which is not a keyed behavior.`; `Population of "<b>" exceeds its max of <M> instances.`; `Workload "<w>" has malformed phases.`; `Phase <i> of workload "<w>" has a mean interarrival below 100 base units; use a finer unit.`; `Workload "<w>" has a batch below 1.`; `Input field "unitExponential" is required by a Poisson workload.`; `Request class "<c>": outcome must be ok, refused, timeout or error.`; `Request class "<c>" starts on "<e>", which is not an event.` (or `ends on`); `Request class "<c>" names "<w>", which is not a workload.`; `Input samples "<stream>" but declares no seed.`; `Scenario "<s>" has workloads but no horizon.`; `Scenario "<s>" measures outputs but has no horizon.`; `Scenario warmup must be below its horizon.`; `Scenario stopAt must be at least its horizon.`; `Metrics series bucket must divide the window.`; and `Input field "<k>" is not implemented by this engine (WG-4715).` for `meters` and `prices`. Failed steps add `Size of emit "<e>" must be an integer in [0, 2^40), got <value>.` (`<value>` a number as JavaScript writes it, else the type name) and `Value demand scale of "<r>" exceeds 2^32.`

**Trace**, version 2 (a version-1 input is refused; a trace of the legacy interpreter adds `"semantics": "legacy"`):

| Field | Meaning |
|---|---|
| `version`, `timeUnit`, `seed` | `2`, and copied from the input. |
| `initialDraws` | The draws made at the start of the run, in order, as `{stream, index, value}`. |
| configurations | As in the removed version 1, plus `resources` (per resource: held per (instance, class), waiting per class as `[{request, requester, units, since, seq}]`, current capacity and limits), `links` (per queue: in transfer, waiting), `timers` (timer id ↦ entry seq), `workloads` (next instant, issued; closed: per client its outstanding request and state; groups), `meters` (observations in window), `routeCounters`, `streams` (counters), `down` (crashed instances), `incarnations` and the instance machines; every pending entry carries `scheduledAt` and, when addressed to an instance, its `incarnation`. |
| `steps[].kind` | Adds `service-done`, `wait-timeout`, `link-done`, `fault-edge`, `client-timeout`. |
| `steps[].event` | Adds `target`, `from`, `routes`, `timer` when present; `source` kinds add `arrival {workload, n, client}`, `timer {behavior, instance, timer}`, `resource {resource, request, outcome}`, `link {link, message}`, `fault {fault}` for edges. |
| `steps[].fired[]`, `steps[].ignored[]` | Add `instance`; `ignored` reason adds `no-instance`. |
| `steps[].resources` | In order: `{resource, class, request, action, at, waited?, served?, reason?}`, `action` ∈ `enqueued`, `granted`, `completed`, `released`, `refused`, `shed`, `dropped`, `timed-out`. |
| `steps[].draws` | `{stream, index, value}` per draw, in order (`value` a decimal string). |
| `steps[].faults[]` | Adds effects `scaled`, `capacity`, `limit`, `collapsed`, `replaced`, `crashed`, `stale`, `restarted`. |
| `outcome` | Adds `stopped`; `truncated` is reported beside it. |
| `metrics` | The measured outputs, when the input declares request classes or asks for metrics. |

**`metrics` as built** (present when the input declares request classes or `metrics`, or asks for `output: "metrics"`): `window {from, until}`; `requests`, per class, `{measured, outcomes {ok, refused, timeout, error, censored}, responseTime {count, finite, infinite, sum, max, quantiles}, legitimate {measured, refused}, unkeyed, duplicate, lateEnds, window}` over the measured requests (start in the window); `transitions`, firings in the window per `<behavior>.<transition>`; `resources`, per resource, `{utilisation {busy, capacityTime, max}, queueLength {integral, window, max}, waitingTime {count, finite, infinite, sum, max, quantiles}}`; and with `metrics.series {bucket}`, `series {bucket, buckets: [{from, until, requests, transitions}]}`. Every quantile is `{value}`, `{value: null, infinite: true}` or `{value: null, empty: true}`. Throughput, the outcome ratio and the false-positive ratio are formed from these counts by the claim runner (`src/core/metric-claims.js`). Step records add `links` (`{link, queue, message, action, at, size}`, action `started`, `queued`, `lost`, `transferred` or `propagated`), and pending entries add `timer` and `copyOf`.

With `output: "metrics"` the trace holds `version`, `scenarioId`, `faults`, `seed`, `timeUnit`, `stepsTaken`, `outcome`, `truncated`, `final` and `metrics`, and no `steps`.

#### Backward compatibility

Format 1 was removed (WG-5681), and with it the lift theorem `lift_agrees`, which had stayed unproved. What replaces them:

- Every golden under `tests/conformance/goldens` is version 2. `tests/conformance/golden-changes.json` names the base commit at which they were version 1 and classifies every golden that changed since: its input lifted (unit `tick`, no seed) with its trace equal to the version-1 trace once the version-2 fields are removed, re-recorded inputs whose traces are equal under that removal, traces removed because the calculus refuses the input, and edited inputs. `tests/core/conformance.test.js` recomputes the classes from git and fails on any golden that changed without an entry; `node tools/differential.js --lift` prints the same comparison.
- `simulationInput` derives a version-2 input for every specification: unit `tick` for one without a time unit or a format-2 construct.
- A version-1 input is refused by the Lean engine and the Rust oracle alike (`formatOneGone`).

### Specification-level form

**Units.** Durations: `"<decimal> <unit>"` with `ns`, `us`, `ms`, `s`, `min`, `h`. Rates: `"<decimal>/<unit>"` with `s`, `min`, `h`. Sizes: `"<decimal> <unit>"` with `B`, `kB`, `MB`, `GB` (powers of 1000) and `KiB`, `MiB`, `GiB` (powers of 1024). Bandwidth: `"<decimal> <unit>"` with `bit/s`, `kbit/s`, `Mbit/s`, `Gbit/s`, `B/s`, `kB/s`, `MB/s`, `GB/s`. Decimals are exact (`"0.1 ms"` is one tenth of a millisecond, never a double). **Every load parameter carries `source`**: `{kind: "requirement" | "measurement" | "assumed" | "to-be-measured", ref?, date?}` (claim `load-parameters-sourced`).

The pool-under-flood fixture ([Fixtures](#fixtures)) as a specification writes it (behaviors abbreviated to the transitions that matter):

```jsonc
{
  "simulation": { "timeUnit": "us" },
  "resources": [
    { "id": "db-pool", "kind": "pool", "capacity": 20, "discipline": "priority", "overflow": "refuse", "queueBound": 200,
      "source": { "kind": "assumed", "ref": "the persistence specification states no pool size" },
      "classes": [
        { "id": "money", "priority": 3, "reserved": 2, "maxWait": "200 ms" },
        { "id": "moves", "priority": 2, "reserved": 6, "maxWait": "200 ms" },
        { "id": "page-reads", "priority": 1, "limit": 3, "queueBound": 50, "maxWait": "100 ms" }
      ] },
    { "id": "db-io", "kind": "io", "capacity": 4, "discipline": "fifo",
      "demandFactor": { "usl": { "alpha": "0.03", "beta": "0.001" } },
      "source": { "kind": "to-be-measured" } }
  ],
  "behaviors": [
    { "id": "host-flow", "subject": "c-match-host", "instances": { "count": 4 }, "initial": "idle",
      "transitions": [
        { "id": "host-take-move", "from": "idle", "to": "idle", "on": "move-requested",
          "effects": [{ "acquire": "db-pool", "class": "moves", "then": "move-connection", "refused": "move-refused",
                        "payload": { "request": "event.request" } }] },
        { "id": "host-commit", "from": "idle", "to": "idle", "on": "move-connection",
          "effects": [{ "use": "db-io", "demand": { "lognormal": { "median": "1 ms", "p99": "4 ms" }, "source": { "kind": "assumed" } },
                        "then": "move-written", "payload": { "request": "event.request" } }] },
        { "id": "host-ack", "from": "idle", "to": "idle", "on": "move-written",
          "effects": [{ "release": "db-pool", "class": "moves" }, { "emit": "move-acked", "payload": { "request": "event.request" } }] }
      ] }
    // api-flow: the same three steps for page reads on class page-reads, demand lognormal median 10 ms, p99 60 ms
  ],
  "routes": [{ "event": "move-requested", "behavior": "host-flow", "by": "key", "field": "match" }],
  "workloads": [
    { "id": "moves", "kind": "open", "event": "move-requested", "process": "poisson", "rate": "400/s",
      "clients": { "count": 1000 }, "payload": { "match": { "choose": ["m1", "m2", "m3", "m4"], "weights": [1, 1, 1, 1] } },
      "legitimate": true, "source": { "kind": "assumed", "ref": "K-2: 1,000 players; 0.4 moves per player per second assumed" } },
    { "id": "page-reads", "kind": "open", "event": "page-requested", "process": "poisson",
      "phases": [{ "from": "0 s", "until": "20 s", "rate": "200/s" }, { "from": "20 s", "until": "60 s", "rate": "5000/s" },
                 { "from": "60 s", "until": "70 s", "rate": "200/s" }],
      "clients": { "count": 10000 }, "legitimate": false, "source": { "kind": "assumed" } },
    { "id": "page-reads-normal", "kind": "open", "event": "page-requested", "process": "poisson", "rate": "200/s",
      "clients": { "count": 5000 }, "legitimate": true, "source": { "kind": "assumed" } }
  ],
  "requestClasses": [
    { "id": "move-db-leg", "start": { "event": "move-requested" }, "key": "request",
      "ends": [{ "event": "move-acked", "outcome": "ok" }, { "event": "move-refused", "outcome": "refused" }] }
  ],
  "faults": [
    { "id": "pool-classes-collapsed", "kind": "collapse-classes", "resource": "db-pool" },
    { "id": "page-read-limit-raised", "kind": "set-class-limit", "resource": "db-pool", "class": "page-reads", "limit": 12 }
  ],
  "scenarios": [
    { "id": "page-read-flood", "behaviors": ["host-flow", "api-flow"], "workloads": ["moves", "page-reads"],
      "seed": "4715", "warmup": "10 s", "horizon": "70 s", "stopAt": "80 s", "maxSteps": 20000000 },
    { "id": "page-read-normal", "behaviors": ["host-flow", "api-flow"], "workloads": ["moves", "page-reads-normal"],
      "seed": "4715", "warmup": "10 s", "horizon": "70 s", "stopAt": "80 s", "maxSteps": 20000000 }
  ],
  "claims": [
    { "id": "pool-classes-protect-move-db-leg", "kind": "measured",
      "statement": "The p99 of the modelled database leg of a move stays within 30 ms (an assumed share of K-32's 250 ms) under the page-read flood.",
      "evaluate": { "method": "metric-bound", "scenarios": ["page-read-flood", "page-read-normal"],
        "metric": { "kind": "response-time", "of": "move-db-leg", "statistic": "p99" }, "op": "<=", "bound": "30 ms",
        "window": { "from": "20 s", "until": "60 s" },
        "fraction": "0.95", "confidence": "0.95", "runs": 59, "seed": "4715",
        "negatives": [{ "scenario": "page-read-flood", "faults": ["pool-classes-collapsed"] },
                      { "scenario": "page-read-flood", "faults": ["page-read-limit-raised"] }],
        "controlNegatives": [{ "scenario": "page-read-normal", "faults": ["pool-classes-collapsed"] },
                             { "scenario": "page-read-normal", "faults": ["page-read-limit-raised"] }] } }
  ]
}
```

**As built** (`src/core/sim-input.js`, `simulationInputV2`): a scenario derives version 2 when it names `workloads`, a `seed` or a `horizon`, or one of its behaviors has `instances` or a format-2 effect; the time unit is the scenario's `timeUnit` (default `us`), and routes, `metrics` and `output` are scenario fields; resources, links, workloads and request classes are the sections `resources`, `links`, `workloads` and `requestClasses`. Durations, rates, sizes and bandwidths are converted exactly (a duration that is not a whole number of base units is refused), a workload with `rate` and no `phases` runs at that rate from 0 to the horizon, and distributions are lowered as in [Lowering](#lowering-distributions). The validator checks format-2 effects (resources, classes, events, links) and that a metric claim has enough runs to ever hold; the other first-draft rules below are not all built yet. A metric-bound claim (`src/core/claim-methods.js`) is evaluated by `src/core/claims.js` on the WebAssembly engine.

**Validator refusals for common first drafts** (errors unless marked): a duration without a unit, or with `timeUnit` undeclared; a duration that is not a whole number of base units; a rate without `/s`, `/min` or `/h`; a workload in a scenario without `horizon`; `warmup ≥ horizon` or `stopAt < horizon`; `use`, `acquire` or `release` of an undeclared resource or class, or `release` without `class` on a resource with several; units that can never be granted; Σ reserved > capacity; a `key` route whose field the event does not declare; a two-part reference to a multi-instance behavior; a metric claim with fewer runs than can ever hold; a request class whose start or end events nobody emits; a statistic the metric kind does not have; a log-normal with `p99 < median`; a load parameter without `source`; a scenario with sampled sites and no seed; (warning) a quantile claim whose expected sample count beyond the quantile is under 30; (warning) a workload whose event no behavior of the scenario consumes.

### Fixtures

Each fixture is a small specification under `tests/fixtures/` with its claims and negatives; every number is tagged `requirement`, `assumed` or `to-be-measured`.

**Base, control and twins.** Each fixture with a load event (a flood, a slowdown, a crash, an attack) has a **base** scenario with the event, a **control** scenario without it, and **twins**, each the base with one fault. The claim lists base and control as its scenarios and must hold in both; each twin must fail; and each twin's fault applied to the control must still hold (a control negative that must *not* fail), so that a twin fails because the defect meets the load event, not because of the fault alone. If the base does not hold, the claim is `violated` and the twins prove nothing: the fixture's parameters are wrong and are corrected, never its claim weakened. The queueing-theory fixtures have no load event and no control. All fixtures use 59 runs. Every twin is a fault (including `replace-demand`) or, where no fault can express it, a *variant* scenario declaring `variantOf` the base.

**What a fixture result is.** Fixture parameters are adjusted until the base holds, so a fixture result tests the engine, the metrics and the claim method (that the twin fails for its stated reason), and is **not evidence about any system**.

**As built so far.** The fixtures are stated at the engine-input level under `tests/fixtures/queueing/` (distributions written as `{lower: <family>}` and lowered by `src/core/distributions.js`), and their twins are faults of the base input. `tests/core/queueing-fixtures.test.js` evaluates the M/M/1 claims (`mm1.json`: warm-up 10 s, horizon 90 s; twins `set-capacity 2` and `replace-demand` with a constant 1 ms service); recorded 2026-11-17: utilisation interval [0.7967, 0.8009], mean wait [3910.6, 4032.3] µs, both `model-holds`, and both twins fail. `tests/core/pool-fixture.test.js` evaluates the pool fixture (`pool-flood.json`, scaled so a run stays short: moves 1,000/s with a commit I/O of median 0.4 ms and p99 1.6 ms, page reads 50/s with a flood of 5,000/s from 2 s to 6 s, the claim window being the flood, `warmup` 2 s, `horizon` 6 s; control: page reads at 50/s throughout). Runs only with EXEGRA_FIXTURES=1 (354 runs; measured 2026-11-18 at 98 s on the native engine after WG-4774, down from about 15 minutes). Recorded 2026-11-17: model-holds. Per-run p99 of the move leg: base holds 59/59 (spread 2987 / 3433 / 4630 us), control holds 59/59 (1584 / 1802 / 2376 us); the twin collapse-classes fails 0/59 (every run +inf: moves are refused at the shared queue), the twin page-read limit 12 fails 0/59 (70839 / 83599 / 105493 us: moves wait behind page reads on the shared I/O channels); both twin faults hold on the control (59/59; spreads up to 21768 and 13969 us). A model result on assumed parameters, not evidence about any system. **Runtime.** Measured 2026-11-18 after WG-4774, a format-2 step costs about 1.9 µs on the native engine for M/M/1 and about 4.6 µs for the pool base (copy-on-write configuration, shared ids), and the M/M/1 test shares the base runs between its two claims (177 runs): both run only with `EXEGRA_FIXTURES=1`, outside the routine suite: the M/M/1 fixtures take 78 s and the pool fixture 98 s on the native engine (WG-4774), which together exceed the routine suite budget.

**Queueing theory** (claims `metrics-reproduce-mm1-utilisation`, `metrics-reproduce-mm1-mean-wait`, `metrics-reproduce-mm2-erlang-c`). One Poisson workload, one resource, FIFO, unbounded, exponential demand of mean 1 ms, unit `us`, warm-up 20 s, horizon 220 s, `approx` claims at 95% confidence over 59 runs.
- M/M/1, λ = 800/s, μ = 1000/s: utilisation 0.8 within 2%. **Twin**: `set-capacity 2` (utilisation 0.4) must fail it.
- M/M/1 mean wait in queue `ρ / (μ − λ) = 4 ms` within 5%. **Twin**: `replace-demand` with a fixed 1 ms service (M/D/1, mean wait 2 ms by Pollaczek-Khinchine) must fail it.
- M/M/2, λ = 1600/s: Erlang C gives `C(2, 1.6) = 6.4 / 9 ≈ 0.711` and mean wait `C / (2μ − λ) ≈ 1.78 ms`, within 5%. **Twin**: the variant `mm2-split` (two resources of capacity 1, fed by a `random` route: random splitting of a Poisson stream gives two Poisson streams of 800/s, so two M/M/1 queues with mean wait 4 ms; a `round-robin` split would give Erlang-2 arrivals, E2/M/1, with a mean wait of about 2.84 ms) must fail it, which shows the multi-server grant is not two queues.

**Database pool with classes under a page-read flood** (the acceptance example of WG-4715; claim `pool-classes-protect-move-db-leg-under-flood`). The fragment above: base `page-read-flood`, control `page-read-normal`, the claim scoped to the flood window 20–60 s (about 16,000 moves per run, 160 beyond the p99). The point it makes: **class reservation protects the pool but does not isolate the shared resource behind it**.
- `db-pool`: 20 connections (assumed); classes money (reserved 2), moves (reserved 6), page-reads (limit 3, bound 50); all assumed, since the specification the fixture is modelled on states no pool numbers.
- `db-io`: 4 I/O channels behind the pool, FIFO, USL α = 0.03, β = 0.001 (to be measured). Every query holds a connection while it uses `db-io`.
- Demand: a move's commit I/O log-normal, median 1 ms, p99 4 ms (assumed; K-26's 10 ms p99 database round trip is the order of magnitude); a page read's I/O median 10 ms, p99 60 ms (assumed).
- Load: moves 400/s over 1,000 clients (assumed from K-2); page reads 200/s, flood 5,000/s over 10,000 clients from 20 s to 60 s (assumed).
- **Budget.** K-32 is 250 ms at p99 for a commit acknowledgement, end to end: client to edge, edge to host (K-4: 5 ms p99 added), host processing, the database commit (pool wait, I/O, synchronous replication), and the acknowledgement back. **The model covers only the database leg** (pool wait and `db-io` time, request class `move-db-leg`); it assigns that leg an assumed 30 ms of the 250 ms. Replication, the network legs and host processing are not modelled; the claim is named for the leg, not for K-32.
- **Why it should hold, and why it is near the edge.** With page reads limited to 3 connections, at most 3 of the 4 channels serve page reads, and moves (about 400/s × 1.2 ms ≈ 0.5 of a channel) keep one channel and part-time use of others. Raising the page-read limit to 4 leaves moves no channel of their own; the sensitivity report is expected to show the verdict flipping on that limit and on the page-read I/O demand.
- **Twin A**, `collapse-classes` on `db-pool`: one FIFO queue; the flood fills the 20 connections and the 200-request queue, moves wait behind page reads or are refused (+∞), and the claim must fail.
- **Twin B**, `set-class-limit page-reads 12`: moves still have 6 reserved connections, but 12 page reads queue on 4 I/O channels and moves wait behind them in the `db-io` FIFO; the claim must fail. This is the twin that shows reservations do not isolate downstream resources.

**Load-shedding ladder** (claim `ladder-reacts-without-flapping`). A `ladder` behavior reads a meter of refused page reads per second over 5 s; it rises one rung when the rate exceeds 1,000/s and lowers it when the rate is under 200/s for a hold of 10 s (a timer); rung 1 makes the edge shed anonymous page reads. Claims over the flood: `time-to-first` rung 1 within 10 s of the flood start; at most 4 rung transitions during the flood (`transitions` count); `time-to-recover` within 30 s after it. **Twin**: equal rise and lift thresholds and no hold (a `faultOnly` transition enabled) flap, giving more than 20 transitions.

**Retry amplification** (claim `retry-budget-bounds-amplification`). A population of 2,000 client behaviors; each request has a 500 ms timer and retries on timeout. A windowed `scale-demand ×5` on `db-io` from 20 s to 30 s slows the database. Claim, in the ratio form: the busiest second of queries reaching the pool during the slowdown (`transitions` of the pool-acquire transition, buckets of 1 s, aggregate `max` over 20–30 s), `relativeTo` the mean per second over 10–20 s (aggregate `mean`), is at most 1.5, with a retry budget (a client retries only while its token bucket allows, 10% of its requests). **Twin**: the unbudgeted retry transition (`faultOnly`, enabled) amplifies the rate beyond 3× and the claim fails.

**Reconnect storm** (claim `reconnect-stagger-bounds-handshake-wait`). 4,000 population clients connected to 4 `host` instances (routed by `key` on the match); `crash-instance host#0` at 30 s with `notify: connection-reset` and `restartAfter` 2 s; its about 1,000 clients reconnect, to the hosts that are up, after a timer drawn uniformly from 0 to 5 s, and a reconnect is a `use host-cpu` with the TLS handshake as its demand (this is how TLS handshake CPU is represented). Claim: the p90 waiting time on `host-cpu` in the window 30–40 s is at most 200 ms (about 1,000 handshakes per run, 100 beyond the p90; a p99 would rest on 10 and be underpowered). Control: no crash. **Twin**: an immediate reconnect transition (stagger 0) fails it.

**Address limiter** (claims `address-limiter-acts`, `address-limiter-false-positives-bounded`). Legitimate users: 5,000 at 0.2 requests per second, grouped onto addresses with a group-size distribution that puts most users alone and some behind large shared addresses (assumed: up to 50 users behind a campus or carrier NAT, 10 requests per second, inside the limit); attack: 50 addresses at 100/s each. A keyed limiter behavior on `address` admits 20 requests per second per address. Claims: the attack's refused ratio ≥ 0.9 (the limiter acts) and the legitimate `false-positives` ratio ≤ 0.001. **Twins**, as variants of the base with the limiter's limit variable initialised differently: a limit of 1,000 per second per address fails the first; a limit of 2 per second fails the second.

**Holding across a downstream wait** (claim `bulkhead-keeps-static-served-under-db-slowdown`). An `api-worker` thread pool (16 threads) is held while a request calls the database (`acquire`, then `use db-io`, then `release`); static requests need a thread and no database. A windowed `scale-demand ×10` on `db-io` from 20 s to 40 s. With a class `db-calls` limited to 8 threads and a `maxWait`, the p99 of static requests (200 per second, so about 4,000 in the window and 40 beyond the p99) in that window stays ≤ 50 ms. **Twin**: `collapse-classes` on `api-worker` lets database calls hold all 16 threads, static requests starve, and the claim fails: the cascading collapse that credit-based backpressure would prevent.

### What it still does not represent

| Not represented | What covers it instead | Follow-up |
|---|---|---|
| Packet-level networking: packets, MTU, loss and retransmission, congestion windows, slow start, head-of-line blocking in TCP; packet-rate floods (a SYN flood of millions of packets per second needs `ns` and a step per packet, beyond any step budget) | Load runs on the real network path; measured latency distributions as `empirical` tables; an aggregated (fluid) mode for packet-rate floods | WG-4718 |
| Kernel and NIC queues, SYN backlog, connection tracking tables, file-descriptor limits | Can be approximated as resources with bounds; their real limits come from load runs and provider documentation | — |
| Provider throttling (API rate limits, burst credits of managed services) | A resource or a keyed limiter behavior with stated limits, sourced from the provider profile; real behaviour from load runs | — |
| CDN behaviour under attack (cache hit ratio, origin shielding, provider filtering) | A modelled hit ratio as an assumed parameter; the provider's protection is a declared capability with its conformance row (an open question about provider protection) | — |
| CPU caches and buffer-pool effects (hit ratios changing with load) | A load-dependent `demandFactor` calibrated from load runs | — |
| Processor sharing, CPU scheduling, preemption, frequency scaling | CPU is a FCFS multi-server station | WG-4719 |
| Garbage collection pauses, JIT warm-up, allocator behaviour | Measured service-time distributions that include them | — |
| Lock contention and database internals (row locks, MVCC, vacuum, checkpoint I/O) | `demandFactor` (USL) fitted to load runs; database load tests at production size (the runs a database-capacity constraint asks for) | — |
| Shared thread pools and head-of-line blocking inside one process (an event loop blocked by one slow handler) | A `threads` resource models a pool; blocking inside one thread of control is not represented; profiling and load runs | — |
| Noisy neighbours on shared hosts | A windowed `scale-demand` fault as a stated scenario; measurement on the provider | — |
| Autoscaling policies and cold start | **Static sweeps over `count` and `capacity` are the K-3 method**; a windowed `set-capacity` models a step change | WG-4720 |
| Matchmaking `gather` (wait until N compatible requests, then start together) | Writable with a behavior that counts and releases, but not as a primitive with metrics | WG-4721 |
| Credit-based backpressure across components | The hold-across fixture shows the failure it prevents; timeouts and bulkheads are representable | WG-4722 |
| Coordinated omission in the real measurements the model is compared against | The model measures open workloads from scheduled arrival; load generators must record intended send times | — |
| Clock skew, diurnal load, time-of-day effects | One global integer clock; phases only as declared; production monitors (WG-4680) | — |
| Synchronous replication latency (part of K-32's commit acknowledgement) | Not in the pool fixture's database leg; representable as a `use` on a replication link or resource with a measured latency distribution once measured | — |
| Memory per session, fuel and other non-time budgets | No memory resource kind: a pool of units can stand for memory slots, but allocation size, fragmentation and out-of-memory behaviour are not modelled; measured in load runs | — |
| Slowloris-style long-lived connections | Representable as `acquire` held for a long sampled time on a connection pool; the attacker's adaptive pacing is not | — |
| Attacker address rotation over time | Client and address identities are fixed per run; rotation needs phases of separate workloads | — |
| Detection noise and operator response time | Ladder and limiter behaviors react to meters exactly; noisy detection, alert delay and human response are not modelled beyond explicit timers | — |
| Egress bandwidth cost of an attack | The cost metric counts bytes over links when links carry sizes; provider egress pricing tiers are outside it (WG-4669) | WG-4669 |
| The sender's total egress on fan-out | Each fan-out receiver queue has the link's full bandwidth; the sender NIC limit is not shared among them | — |
| Service demand that changes during service | `demandFactor` is fixed at the grant; a request already in service is not slowed by later contention | — |
| Rare events beyond the runs taken | 59 runs bound the 95th percentile of a per-run statistic, not one-in-a-million events; chaos campaigns (WG-4667), game days | — |
| Exploring *when* faults act | The explorer chooses whether a fault acts; timing as a choice is WG-4704 | WG-4704 |
| That the model's machines behave like the code | Assumption `machines-abstract-the-code`; implementation refinement (WG-4679) | — |

### Order of the work

By dependency. Each step is defined in Lean before the Rust engine implements it, then checked differentially:

1. **Generator and distributions**: SplitMix64 streams, FNV-1a, `uniformInt`, `table`, categorical choice, reference test vectors. Depends on nothing. In parallel, the pinned quantile tables and the integer **lowering** of distributions in `simulationInput`, with the reference outputs as tests.
2. **Input and trace version 2** (decoders, bounds, refusals, encoders) and **integer time with instances, routes, aggregates and timers**, with the determinism property over seeds. Needs 1.
3. **Resources**: effects, settling, grants, bounds, timeouts, `demandFactor`, resource faults, timed fault edges, `crash-instance`, with the invariants proved. Needs 2.
4. **Links**: transfer, propagation, ordered links, fan-out. Needs 2.
5. **Workloads**: open (phases, inversion of the integrated rate, batches, clients, groups), closed, population. Needs 1 and 2.
6. **Meters and metrics**, series, cost, `output: "metrics"`. Needs 3, 4, 5.
7. **Exploration** of version-2 inputs. Needs 2–5.
8. **Specification vocabulary, validator rules, version-2 goldens and the version-2 input generator.** The vocabulary and validator can start after 1; goldens need 2–6.
9. **Metric claims**: the method, the binomial and sign tests, negatives, `model-holds`, underpowered and truncated runs, the ratio form, calibration and sensitivity. Needs 6 and 8, and WG-4703's status vocabulary.
10. **Calibration and sensitivity**: load-run evidence with expiry, fit and hold-out runs, tolerance against margin, envelopes, one-at-a-time and pairwise variation over declared ranges. Needs 9.
11. **Fixtures**: queueing theory first (it validates 3, 5 and 6), then the pool, ladder, retry, reconnect, limiter and hold-across fixtures. Needs 9 (and 10 for calibrated claims).

### Open questions

- **Status vocabulary.** `model-holds` is proposed here; WG-4703 settles the final names and how the inspector shows them.
- **Meter state size.** A meter keeps the observations in its window; at high rates over long windows this grows. A bucketed approximation would change the semantics, so it is not adopted yet.
- **Default runs and confidence** beyond the 59-run minimum, and whether the tool should suggest N from a pilot run.
- **Warm-up detection.** `warmup` is declared; no stationarity test is defined.
- **Explorer state size** with stream counters, meters and resource queues; whether to abstract counters of streams a claim cannot observe.

## Roadmap: accurate simulation as far as it goes

The aim is simulation as accurate as the specification allows: excessive load, chaos (an instance dies, the network partitions), the cost of running the system, and a depth that goes as far as the specification says something. The plan is recorded in Exegra's own specification: six components marked `not-implemented` (`simulation-aspect-registry`, `refinement-checker`, `chaos-aspect`, `load-aspect`, `cost-aspect`, `simulation-overlays`) and sixteen claims that stay *not evaluated* until recorded evidence supports them. Workgraph task WG-4663 and its children hold the work, in dependency order:

1. **Core** (WG-4664): time units, instances, resources with capacity and service time, seeded randomness, and the trace format as a contract other engines are judged by (the shared fields specified above under "Engine input and trace format" and pinned by `tests/conformance/`; format 2 specified under "Planned: resources, workloads and performance"). Workloads, bandwidth, latency, timeouts, measured outputs and claims over them (WG-4715) build on it, in the same section.
2. **Aspects** (WG-4665): a registry like the projection and claim-method registries. An aspect brings the vocabulary it reads, the state it adds, hooks into the core, metrics, claim methods and overlays. Specifications name aspects, with versions and parameters, as data; specification text is never executed.
3. **Depth** (WG-4666): a component may have an abstract behavior and children that refine it. A run chooses the level per region, following the view's collapse state, and the refinement checker reports where a refined trace leaves what the abstract behavior allows, so deep and shallow models cannot drift apart.
4. **Chaos** (WG-4667), **load** (WG-4668, validated against queueing theory) and **cost** (WG-4669, prices sourced and dated, from a price profile kept apart from components).
5. **Statistical claims and result ranges** (WG-4670): percentiles, availability and cost ceilings over seeded sweeps, reported as spreads with their basis, never as single figures and never as verified.
6. **Overlays** (WG-4671) on the component view. **A faster engine** (WG-4672) was done: the Rust engine replaced the JavaScript engine everywhere. Since 2026-11-18 the Lean engine (WebAssembly) runs in its place, and the Rust engine is the differential oracle.

Results are only as accurate as their parameters, so every load and cost parameter names its source: a requirement, a dated price sheet, a measurement, or an explicit assumption.

## The assurance chain

The aim is to be able to deploy a system specified well enough and be highly confident, within a stated fault model, that it is durable, highly available, recovers from failure, rolls back without loss and deploys blue-green. Confidence comes from closing the links between specification, code, cloud and reality, each with the strongest method that fits it, not from simulation detail alone. Exegra's specification records each step as a planned component with a claim; Workgraph holds the work (children of WG-4663), in dependency order:

1. **Fault model** (WG-4676): environments, failure modes with sourced rates and durations, and fault models with concurrency bounds as specification entities; every behavioral or reliability claim names the fault model it holds under.
2. **Exhaustive exploration** (WG-4650): every interleaving and every combination of the fault model's failure modes within stated bounds, in the Rust engine, for the protocols where bugs hide (leases and fencing, failover, outbox, cutover, rollback, migrations, revocation timing), with shortest counterexamples.
3. **Deployment model** (WG-4677): environments, versions, blue and green slots, health gates, cutover, rollback and expand/contract migrations as entities and behaviors, model-checked under the fault model.
4. **Generated infrastructure** (WG-4678): infrastructure per provider profile, the pipeline's state machine and boundary contract tests generated from the specification, with the output verified against the deployment model (a finite, declarative target where verified generation is tractable).
5. **Real code against the model** (WG-4679): the system's code run in its own deterministic simulator with faults from the fault model, its traces checked against the model at the boundaries (refinement).
6. **Reality** (WG-4680): game days on the generated infrastructure and production monitors generated from claims, recorded as evidence, with observed failure rates replacing assumed ones.

What this gives is high confidence scoped to the fault model, backed by proof where the core is small, exhaustive checking where protocols are finite, simulation of the real code, and measurement in reality. It does not give certainty: failures outside the fault model remain, and the model says where that boundary is.
