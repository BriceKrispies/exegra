# Refinement theory and implementation conformance: assessment

Team: refinement theory and implementation conformance. Read-only review. Lean, the CLI and the test suites
could not run here. Two demonstrations ran under node against the pure JS modules:
`scratchpad/demo/refines-ignore.mjs` and `scratchpad/demo/replay-blind.mjs`, both under
demos/

## 1. Verdict

- **Spec to code:** Today the only links between the spec and running code are file-path existence, test names, and event-id instrumentation placed by hand. No relation defines what it means for code to implement a behavior, so nothing establishes guarantee 7 (implementation conformance).
- **Refinement in Lean:** No refinement relation exists in Lean, either between two specs or between a spec and a machine. `Impl/Refinement.lean` proves that the optimised interpreter and the reference interpreter are equal functions. The JS `refines` check works per trace, misses ignored inputs, and reimplements the semantics outside Lean.
- **Can it be evolved?** Yes, but only by adding foundations, not by patching. A refinement relation and its preservation theorems have to be written in Lean over `Semantics.step`. The JS checkers (`refinement.js`, `replay.js`) would then become clients of Lean or be replaced. Evidence has to be bound to code revisions.
- **What to keep:** the trace format, the proof style of `Impl/Refinement`, the traffic recorder and replay design, and the honest scope texts. All are good substrate.

## 2. Fundamental limitations

**L1. No semantic relation between spec and code. BLOCKS-OBJECTIVE. DEMONSTRATED (traced through every check; the browser suite was not executed).**
`tools/traceability.js:89-126` checks only that the declared module paths exist and that every file under
`src/ cli/ tools/` is claimed. The scanned surface (`SCAN_DIRS`, line 28) excludes `formal/` and `engine/`, so a new Lean or Rust file that no component claims is never reported. The self-spec says outright that "the scenario state machines in this file are hand-maintained abstractions of the code: the correspondence ... is not generated and not checked" (`specs/exegra/spec.jsonc:18`; assumption `machines-abstract-the-code`, `:14641`).

*Counterexample (a code change that breaks specified behavior while every check passes):* in `src/app/main.js:102`, change `sessionStorage.setItem(cameraKey(), camera)` to `sessionStorage.setItem(cameraKey(), '')`. Coming back to a view then restores nothing (`saved` is falsy at line 92, so the code records `camera-none`). Each check is unaffected:
- `validate`: the spec is unchanged.
- `traceability`: the same files.
- `tests/core/runtime-data-complete.test.js:44`: it matches the needle `sessionStorage.setItem(cameraKey()` textually, and the needle is still there.
- `tests/core/replay.test.js`: it replays a committed recorded stream, not the live code.
- `tests/browser/live.spec.js`: it asserts zero divergences only for open/edit/save. The view switch is "for the record, not asserted" (line 120).
- No test reads `exegra.camera.*`.

So `camera-restored-per-view` ("Coming back to a view restores the camera the user left it with", `spec.jsonc:17105`) stays **"Verified within the stated model and assumptions"** (`generated/claims-report.md:3267`).

Worse, this is not hypothetical. `spec.jsonc:2241` (WG-4782) records that the real camera memory already diverges from the model on view switch, and on claims-on-commit and engine-worker termination. The claim reads Verified anyway.

**L2. The `refines` check accepts implementations that silently refuse inputs the model must handle. BLOCKS-OBJECTIVE (for guarantee 6). DEMONSTRATED (ran under node).**
`src/core/refinement.js:241-252` iterates only over `step.fired`. The engine records the steps it ignores (`step.ignored` with `reason: no-transition`; see the goldens, e.g. `tests/conformance/goldens/fixture/faults-delay--delay-tick-2.trace.json`), but the checker never reads them. Each fired step is checked from `map(impl config)`, and an input that I ignores is never compared with what A would do.

*Counterexample:* the lease fixture of `tests/core/refinement.test.js:19-75` itself. Its `li-renewing` state declares `ignores: ['release']`, while the model's `lm-held` accepts `release` when `event.client == holder`. I ran `checkRefinementTrace` on the engine-format trace of `acquire(a)@0, renew@1, release(a)@2, renewed@3, acquire(b)@4`. Result: `failure: null, unsupported: null, checkedSteps: 3, movingSteps: 1`, which `evaluateRefines` turns into **verified** (`src/core/claims.js:997`). On the same inputs the model frees the lease and grants it to b. The implementation keeps a forever and never grants b.

What the check actually defines is partial correctness of fired steps. It has no input-enabledness or alternating-simulation condition and preserves no liveness or response property. A deadlocked implementation that takes one correct step "refines" anything. Further holes:
- Cancels are not compared (`refinement.js:349`), so an implementation that never cancels a timer passes.
- Fan-out, link and resource effects yield `unsupported` (`:140-146`).
- Model and "implementation" are both machines in the same spec (`validate.js:184-199`). No code is involved; the docs admit as much (`docs/claims-and-evidence.md:102`, "anything about generated or hand-written code").

**L3. Lean has no refinement theory. BLOCKS-OBJECTIVE. ARGUED.**
`formal/Exegra/Impl/Refinement.lean` proves `Impl.runAnyValue v = Exegra.runAnyValue v` (and `runAny_eq`) by a chain of `*_compile` lemmas: an optimised interpreter, which caches parses through `Thunk` and uses `evalFast`, is extensionally equal to the reference interpreter. That is program equivalence of two Lean functions, i.e. compiler-optimisation correctness. It is not a simulation between specs, and not a relation between a behavior and an implementation machine. For format 2, "Format 2 otherwise runs the definition (`V2.traceOf`) unchanged" (`Impl/Semantics.lean`, header), so `runInputV2_eq` covers only the JSON writer.

The only inter-level relation stated in Lean, `Lift.lift_agrees` (v1 against v2), is `sorry` (`Lift.lean:128-136`, honestly pinned).

Two further limits narrow the coverage of `runAny_eq`:
- `runAny_eq` ranges "over every input text", but parsing goes through `partial def` parsers (`Json.lean:32-182`), which are opaque to proofs. Both sides call the same parser, so the theorem is true but says nothing about what a text means.
- The spec-to-engine-input lowering (distributions, pools, retry delays, faults) is JS (`src/core/sim-input.js:124-`). "The engine the application runs equals the definition" therefore covers only what happens after an unverified JS translation.

`refinement.js` (the model step: guard order, effects) and `replay.js` (a "pure incremental reimplementation of one engine step", header) are two more JS step semantics. Neither is proved or even differentially tested against Lean: `tests/core/replay.test.js` does not import the engine. Each violates "Lean is the sole authority".

**L4. Evidence is not bound to the code it describes. BLOCKS-OBJECTIVE (for change impact). DEMONSTRATED (by reading data and code).**
`specs/exegra/evidence/results.json` has keys `results`, `traceability` and `theorems` only. It carries no tree stamp, commit or spec hash. All 609 results are `"obtained": "reused"` and `"outcome": "pass"`. Freshness is checked only when results are recorded (`cli/outcomes.js:58`, `staleReason`). At read time `evaluateEvidenceClaim` does `void recorded` (`claims.js:515-516`), so after any code edit every evidence-based claim stays "supported" until someone reruns verify. Three weaker paths also exist:
- Author-entered non-test evidence alone yields **supported** (`claims.js:533-546`).
- For a method in `meta.verificationMethods`, a hand-written `results.json` entry `claims.<id>.outcome = "pass"` makes the claim **supported** even when it has no evidence entity (`claims.js:255-271`).
- `lean-theorem` claims become **proved** from the `theorems` block of the same JSON file (`claims.js:369-407`).

Test references can be whole files (26 of 616 refs). Nothing checks that a referenced test exercises the claim's subject. There is no dependency from evidence to modules, so change impact cannot say which evidence a code edit invalidates.

**L5. The runtime replay is partial and has blind spots its claim denies. LIMITS. DEMONSTRATED (ran under node).**
`src/core/replay.js` is the closest thing to trace conformance (see section 6). In `replay-blind.mjs` the model is: client `idle -open-> ready -save-requested/emit write-intent{file,text,base}-> saving -saved-> ready`, `ready -close-> idle`; server `write-intent/emit saved{file}`. The recorded stream drops `text` from `write-intent`, sends a `base` hash the model never held, then delivers `save-requested` after `close`, when no behavior accepts it. Result: **`divergences: []`**. The three causes:
- Fields missing from the recording are skipped (`replay.js:189`, `!(k in payload) ... continue`).
- The first mismatch on a variable-bound field is silently "calibrated" (`:191-197`).
- `not-allowed` is raised only for internal (emitted) events (`:287`), so a refused external event is invisible.

Non-scalar fields and number-literal fields are never compared. Instrumentation records intent before the effect happens: the `camera-saved` description says it is recorded "just before sessionStorage.setItem" (`spec.jsonc:7019`, `main.js:101-102`). The recorded trace is therefore the code's own testimony.

**L6. "Conformance" is self-regression. MINOR. ARGUED.** The goldens are recorded by the engine under test (`tools/record-goldens.js:2`). `machine-coverage.js` measures spec machines in spec scenarios, not code; `docs/coverage.md:6` is honest about this.

## 3. Overclaims

1. **`camera-restored-per-view` and every behavioral claim about Exegra built on model machines show "Verified".** The statement is about the application, the evidence is about a hand-written machine, and a known divergence already exists (L1). The assumption is listed, but the status label overstates it.
2. **`refines` reports `verified`** (`claims.js:997`) for a check over hand-written scenario traces, in conflict with AGENTS.md's "verified only for what it established by checking the model itself" and with the explorer/trace distinction. The `scope` text is honest; the status is not.
3. **`real-runs-replay-through-self-model`** (`spec.jsonc:16958`) states that "every divergence ... a payload value that differs" is reported. The demo shows an absent field and a calibrated differing value both go unreported, as does an external event the model refuses. The calibration is documented in the module header, not in the claim.
4. **`engine-run-refines-definition`** uses the word "refines" for function equality restricted to the post-lowering Lean part. The statement is accurate, but the name invites the reading "the implementation is verified".
5. **"implementation-level machine" and "shipped"** (`realisation.js`, `machine-coverage.js:42-46`) name spec machines whose owning component is not `not-implemented`. Nothing ties them to code that exists.
6. **`tools/conformance.js` and "conformance goldens"** are regression against the engine's own output.

## 4. What to preserve

- **The trace format.** Steps carry `fired` (from, to, guard, `sets`, `emitted` with times) and `ignored` with a reason. It is exactly the observation a simulation or ioco checker needs.
- **The `refinement` mapping schema.** `states`, `variables` as expressions over I, `transitions` with `null` stutters, and `timeScale`, together with validation that the mapping is total (`validate.js:184-200`). This is a sound abstraction-function interface: α on states, data refinement on variables, a transition map with stuttering. Keep it; move the check into Lean and add the missing conditions.
- **The proof style of `Impl/Refinement.lean`.** Lemma-per-function equivalence, `#guard_msgs` pins on `#print axioms`, and no `implemented_by`/`extern`. This is the template for proving a generated or optimised machine equal to its definition.
- **The traffic recorder** (`src/app/traffic-recorder.js`): logical `seq`, `requestId` correlation, wall-clock time stripped before reaching the core. **The replay's** prediction and causal matching with a bound: the right shape for a runtime monitor.
- **Status taxonomy, explicit assumptions and honest scope strings**, e.g. the explanations in `evaluateRefines` and `docs/claims-and-evidence.md:102`. **`tools/tree-stamp.js`** is the right primitive for binding evidence. **Realisation roots with JUnit** are a usable structural/interface conformance stage.

## 5. Architectural decisions that prevent the objective

1. **"Implementation" is another machine in the spec.** No artifact stands for code. Replace with an implementation model extracted or generated from code (or typed adapters), related to spec behaviors by a Lean-defined relation.
2. **Semantic checks written in JS** (`refinement.js`, `replay.js`, `sim-input.js`). Replace with Lean functions (`Semantics.step` with external delivery; a simulation checker) plus equality or soundness theorems. The JS becomes a shell.
3. **Evidence as unauthenticated mutable JSON keyed by id.** Replace with entries carrying `{treeStamp, specSemanticHash, refHash, modulesTouched}`, produced only by verify. Make staleness a read-time status.
4. **Hand-placed instrumentation that names spec events and records before the effect.** Replace with events emitted at effect-commit points, generated from the spec (as the telemetry rules already sketch, `src/core/telemetry.js`). Divergence then means behavior, not testimony.
5. **Refinement defined as a per-trace check.** Replace with a relation on labeled transition systems that has theorems. Trace checks become the "tested" tier.

## 6. Highest-leverage foundational changes (dependency-ordered)

1. **A Lean refinement theory over `Semantics.step`.** Behaviors as I/O LTSs; abstraction α (states plus variable expressions); forward simulation with stuttering; an **input condition**: every input A accepts in α(c) is accepted by I from c, or is in a declared refusal set; output matching. Theorems: `sim_trace_inclusion` and `sim_preserves_safety` for `state-invariant`, `never` and `precedes`, plus response/liveness preservation under stated fairness.
   *Done when* both theorems exist with pinned axioms, and the lease scenario from `refines-ignore.mjs` is refused by the Lean checker.
2. **A decidable Lean checker `checkSim` over the explored state space** (reuse `Explore.lean`/`Search.lean`) with a soundness theorem `checkSim_sound : checkSim A I α = ok → Sim A I α`. `refines` reports `verified` only from it, and per-trace results become `supported`/tested.
   *Done when* `refinement.js` is a thin caller, and the existing violated cases of `refinement.test.js` plus the ignored-input case fail through Lean.
3. **Evidence binding and change impact.** Every result carries a tree stamp, the spec semantic hash and the modules it depends on (traceability gives the file-level map). At read time, a mismatch makes the status `stale`, never `supported`. Remove the path where a JSON-only `claims` entry yields `supported`, or require a signature from verify.
   *Done when* editing `src/app/main.js` flips the evidence-based camera and replay claims to stale without rerunning anything.
4. **A Lean runtime monitor.** Move replay to Lean as `monitorStep` and prove it equal to `step` under a delivery chosen from outside. Define divergence completely: missing fields, refused external events, and calibration only for variables declared `environment`.
   *Done when* `replay-blind.mjs` yields three divergences, and a differential test of replay against the engine passes on the goldens.
5. **A staged conformance framework that reuses what exists:**
   - structural: `traceability.js` and realisation roots, including `formal/` and `engine/`;
   - interface: `contract-trace.js`, `codegen-model.js` types and telemetry line formats;
   - transition: the scenarios that `cover-machines --write` generates, run as tests against code through roots;
   - trace and monitoring: the recorder and the Lean monitor;
   - static: the `readiness*` rules;
   - verified refinement: the proof style of `Impl/Refinement` applied to generated machines;
   - generation: readiness plus a codegen equality theorem.

   *Done when* each stage has a claim method whose status names its tier, and the camera mutant from L1 is caught at the trace stage.

## 7. Predictions about other teams

- Some will report "refinement is proved in Lean" from `Impl/Refinement.lean`/`runAnyValue_eq`. It is interpreter-optimisation equivalence and says nothing about specs or code (L3).
- Some will read `refines`, "implementation-level" and "shipped" as spec-to-code conformance. Both sides are spec machines.
- The simulation team may count the traffic replay as runtime verification or simulation fidelity. It is incomplete (L5), reimplements the step in JS, and its input is code testimony recorded before effects.
- The Lean team may miss that every theorem about `runInput` sits downstream of JS lowering (`sim-input.js`) and an opaque `partial` JSON parser. "For every input text" is weaker than it sounds.
- Evidence and claims reviewers may treat the `pass` entries in `results.json` as current. They carry no revision binding, and `theorems`/`claims` entries in the same file are trusted as written.
- Several teams will over-criticise the docs. The scope texts are mostly scrupulous (e.g. `claims-and-evidence.md:102`, `spec.jsonc:18`). The defects are status labels (Verified, verified, "every divergence") and missing foundations, not concealment.
