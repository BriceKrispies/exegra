# Claims and evidence

The rule of `src/core/claims.js`: never confuse *declared* with *true*. A claim is a statement with an explicit evaluation method. A result says what was checked, and the status is derived from what was checked, not from the claim existing.

## Claims

```jsonc
{
  "id": "no-direct-client-to-database",
  "kind": "structural",
  "statement": "The web client has no direct relationship to the persistent game database.",
  "subjects": ["web-client", "game-database"],
  "assumptions": [],
  "evaluate": { "method": "no-relationship", "from": "web-client", "to": "game-database", "transitive": false }
}
```

`kind` is `structural`, `invariant`, `temporal`, `measured` or `requirement`. A `requirement` is a statement whose verification is carried out outside Exegra (see [External verification methods](#external-verification-methods)). `evaluate.method` must be listed in `claim-methods.js` for that kind, or be a method the specification declares itself, and may carry only that method's parameters; otherwise validation reports `claim.method.kind` or `claim.param.unknown`. An unknown method is only a warning (`claim.method.unsupported`) and the claim stays not evaluated. `assumptions` reference `assumption` entities, conditions accepted without evidence; they are listed in the result and are never checked.

## Fault models

A claim may name a fault model (`faultModel`, an entity of kind `faultModel`, see [model-and-format.md](model-and-format.md#fault-models-and-sources)): the environment and the failure modes it is evaluated under. The result's `scope` then begins with "Under fault model <name> (<n> failure modes; bounds: ...)." followed by the scope the method states, for every method, `external-evidence` and externally verified methods included. For the trace methods (`state-invariant`, `precedes`, `eventually`, `never`) the explanation also says how many of the model's failure modes the listed scenarios inject (through the `realises` of their faults); the others were not exercised. Naming a fault model does not make a claim stronger: it states what the result is scoped to. Failures outside the model are not covered, and the model says where that boundary is. An invariant, temporal or measured claim with no fault model, in a specification that declares one, is reported as the gap `gap.no-fault-model`.

## Methods

| Method | Kinds | Establishes |
|---|---|---|
| `no-relationship` | structural | No relationship (optionally no multi-hop path, `transitive`) from any `from` component to any `to` component. |
| `reachable` | structural | Every `from` component reaches some `to` component along a path of at least one relationship; being a member of the target set is not reaching it. |
| `only-via` | structural | Every directed path from `from` to `to` passes through `via`. |
| `has-port` | structural | Every selected component has a port matching `direction`, `contract`, `name`. |
| `property-defined` | structural | Every selected component has a non-empty value for a property (dot path). Presence only, not correctness. |
| `acyclic` | structural | The graph of the given relationship kinds (default: kinds flagged `dependency`) has no cycle. |
| `data-model` | structural | The listed data rules (`rules`, default all six; optionally only the `records` named and their copies) find nothing on the model's records and copies. Violated with the findings as counterexample; inconclusive when a listed rule has nothing to check. See [model-and-format.md](model-and-format.md#data-model). |
| `state-invariant` | invariant | An expression holds in the initial configuration and after every step of each listed scenario. |
| `precedes` | temporal | In each listed scenario, every occurrence of `then` has an earlier `first`. |
| `eventually` | temporal | In each listed scenario, `occurs` happens, or `expr` holds in the final configuration. |
| `never` | temporal | In each listed scenario, `occurs` never happens. |
| `lean-theorem` | structural, invariant, temporal, requirement | A theorem of the Lean core (`theorem`, fully qualified) states the claim, and Lean checks it: the constant exists and is a theorem, the kernel accepts its proof again (re-added under a fresh name), it depends on no axiom beyond `propext`, `Classical.choice` and `Quot.sound`, and each implementation constant in `about` is a definition that occurs in its statement. See [Lean theorems](#lean-theorems). |
| `implementation-language` | structural | Every selected implemented component (`select`, minus `exclude` taken exactly) records `implementation.language` equal to `language`. Violated with the components that are not, by language, with progress and the task named in `plannedBy`. |
| `external-evidence` | any | Nothing is evaluated. The status comes only from attached evidence. |

A **selector** picks components: an id, an array of ids, or an object (`ids`, `category`, `kind`, `tag`, `trustZone`, `within`, `all`; all present fields must match). Components nested in a selected subsystem are selected. A **matcher** is `{ "event": id }` or `{ "transition": id }`.

### Negatives

Every trace method (`state-invariant`, `precedes`, `eventually`, `never`) takes `negatives`: runs that must **violate** the claim. A negative is one of the claim's own scenarios run with extra faults, `{ "scenario": id, "faults": [ids], "note"?: text }`; the run uses the scenario's own faults plus these. Because it is the same script with something taken away, a violation shows that the protection the claim is about is what makes it hold.

```jsonc
"evaluate": { "method": "state-invariant", "scenarios": ["edit-with-disk-conflict"],
              "expr": "workspace-flow.conflict => workspace-flow.persistedRevision == 1",
              "negatives": [ { "scenario": "edit-with-disk-conflict", "faults": ["conflict-overwrites"] } ] }
```

The fault usually enables a `faultOnly` transition that models a defect the system must not have (here: the workspace writes despite the conflict), or drops, delays, injects or disables something. The validator reports a negative whose scenario is not one of the claim's (`claim.negative.scenario`), whose `faults` is missing or empty or names a fault its scenario already activates (`claim.negative.faults`), or that has another field (`claim.negative.unknown`); an undeclared fault is a reference error. Renaming a scenario or fault rewrites the negatives that name it.

Each result of a trace claim lists its negatives under `negatives`: `scenario`, `faults`, `violated`, the run's `outcome`, the `stepIndex` of the violation and an `explanation`.

## Statuses

| Status | Meaning |
|---|---|
| `proved` | A `lean-theorem` claim: the Lean kernel checked a theorem that states it, with only the standard axioms, about the named Lean definitions. It covers every input, not a list of scenarios. It is about the code that runs to the extent the trusted base holds (the claim's assumptions: the Lean compiler and runtime, emscripten, the JS glue, the WebAssembly engine). |
| `verified` | An evaluator checked the model and found no counterexample, within the stated scope. A trace claim also needs a declared negative, and every one must violate it. |
| `supported` | No evaluation; attached evidence supports the claim. Evidence may be author-entered. |
| `violated` | A counterexample was found, or recorded or declared evidence contradicts the claim. |
| `inconclusive` | Something was checked, but not enough to decide. |
| `not-evaluated` | Nothing was checked: no method, an unsupported method, or `external-evidence` with no evidence. |

Rules that keep the statuses honest:

- **Vacuity is not verification.** A selector that selects nothing, a graph with no relationship of the requested kinds, an unknown relationship kind (a misspelling would pass vacuously), a `precedes` whose `then` never occurs, and a claim that lists no scenario are all `inconclusive`. So are the trace cases that would otherwise pass for want of anything to check: a `state-invariant` that is an implication whose antecedent is never true in a configuration reached by a step of any listed trace, or whose consequent names no state or variable (a constant), a `precedes` whose occurrences are all deliveries from the scenario script (an ordering the script itself dictates; a transition, or an event a transition emitted, must be one of its witnesses), a `state-invariant` over traces that all have zero steps, and a `never` about an event or transition that cannot occur in the scenario (a transition of a behavior the scenario does not run; an event that no transition of its behaviors triggers or emits and that is neither a step event nor injected by a fault).
- **A trace check that cannot fail is not verified.** A trace claim that holds on its scenarios is `verified` only when it declares at least one negative and every negative definitely violates it. With no negative it is `inconclusive` ("declares no negative, so nothing shows this check can fail"); so it is when a negative holds, ends in an error, or is cut off at its step limit before an expected occurrence (an absence in an unfinished run is not a violation). A claim violated on its own scenarios stays `violated`; negatives never soften it.
- **A result says what its verdict rests on.** When the engine took the first of two enabled, unguarded transitions of one behavior on the same event and state because it was declared first, the scope names the pair ("Declaration order decided which transition fired") and says swapping them would change the traces; `validate` warns about such a pair (`transition.order-decides`). A later transition with a guard is not examined for this: whether its guard held is not evaluated. A `never` over an occurrence that only `faultOnly` transitions can produce says so in its scope when no listed scenario enables them: it holds for runs without that fault, and for runs with it only as far as a negative exercises it. An implication that is verified counts as exercised when its antecedent was true after some step; whether its consequent could have been false there is shown only by its negatives.
- **A requirement shows the checks over the behavior model that restate it.** A claim may name a requirement in a `models` property (a vocabulary property of type `ref` to `claim`, as the Strata specification declares). The requirement's result then carries `modelledBy`, the claims that name it with their statuses (listed by `exegra claims`, and in the inspector under "Checked over the behavior model by"). It is information: the requirement's own status does not change. A `models` value that is not a requirement (a claim of kind `requirement`) is the validation error `claim.models-not-requirement`.
- **Trace methods check only the listed scenario traces**, run with the scenario's own faults. Every result's `scope` says so: "This is a check of these traces, not of all possible executions." A scenario that ends in an error or hits its step limit before an expected occurrence cannot establish an absence, and makes the claim `inconclusive`.
- **Evidence can only make a model-evaluated claim worse.** A `verified` result with contradicting evidence (declared `supports: false`, or a recorded `fail`) becomes `violated`.
- **Every result carries a scope, an explanation, the assumptions, the entities involved** and, when violated, a counterexample (a path, a relationship set, or scenario and step). Results are stamped with the semantic hash they were evaluated at.
- **Live checks in the simulator** (`checkTrace`) apply only to claims that list the loaded scenario, and distinguish *undecided* (`pending`) from *violated*: an `eventually` still waiting in an unfinished run is undecided, and so is a vacuous implication on a finished trace. See [simulation.md](simulation.md).

## External verification methods

A specification's `vocabulary.verificationMethods` declares methods that Exegra does not run, for example a property test, a scenario run or a conformance table carried out by another tool ([model-and-format.md](model-and-format.md#meta-model-and-vocabulary)). A claim whose `evaluate.method` names one has no other parameters, gets the evaluator `external:<method>`, and is treated like an `external-evidence` claim: no evidence gives `not-evaluated`, contradicting evidence gives `violated`, a recorded pass or an author-entered item gives `supported`, and untested `test` evidence gives `inconclusive`. It is never `verified`: the result's scope says "Exegra ran nothing" and names the method. The claim kind `requirement` exists for this, and a specification converted from Markdown (a linked project) uses it for every requirement it holds, none of which has evidence, so all are `not-evaluated` ([importing-markdown.md](importing-markdown.md)). `tests/core/vocabulary.test.js` checks that such a claim is never reported as verified by Exegra.

## Lean theorems

A `lean-theorem` claim names a theorem of the Lean core and, optionally, the implementation constants it must be about:

```jsonc
"evaluate": { "method": "lean-theorem", "theorem": "Exegra.runInput_terminates", "about": ["Exegra.runInput"] }
```

Lean does the checking (`tools/lean-theorems.js`, through `lake env lean` in `formal/` on the built library) and reports facts per theorem: whether it exists and is a theorem, whether the kernel accepts its proof again, the axioms it depends on (`Lean.collectAxioms`, what `#print axioms` prints), and for each `about` constant its kind and whether it occurs in the theorem's statement (its type). `exegra verify` records the facts in `evidence/results.json` under `theorems`; `exegra claims` and `exegra evaluate` check again when Lean is installed (`EXEGRA_NO_LEAN=1` skips it) and otherwise use the recorded facts, as the application does. The rule in `src/core/claims.js` turns the facts into a status: `proved` when all hold; `violated` when Lean refuses (no such constant, not a theorem, the kernel rejects the proof, `sorryAx` from `sorry`, `Lean.ofReduceBool` or `Lean.ofReduceNat` from `native_decide`, an axiom of our own, an `about` constant that is missing, is not a definition, or does not occur in the statement); `not-evaluated` with no recorded check. A refused theorem makes `exegra verify` fail unless the claim is expected to be violated.

Requiring the `about` constants in the statement is what makes the theorem about the code: a true theorem that does not mention `Exegra.runInput` says nothing about the engine. What the check does not establish is that the code which runs is those definitions; that is the trusted base, recorded as assumptions of the self-specification (`trusted-lean-kernel`, `trusted-lean-compiler-runtime`, `trusted-emscripten-toolchain`, `trusted-libuv`, `trusted-js-glue`, `trusted-wasm-engine`, `trusted-os-filesystem`, `trusted-js-shell`) and listed by each claim and by the components' `implementation.trusts`.

## Evidence

An `evidence` entity attaches an artifact to a claim: `kind` (`test`, `measurement`, `document`, `review`), `ref`, `supports` (default true; false marks contradicting evidence), `description`, `observed`. Evidence is author-entered and is never a result by itself.

For `external-evidence` claims the status is:

| Attached evidence | Status |
|---|---|
| none | `not-evaluated` |
| any contradicting (declared or recorded `fail`) | `violated` |
| a recorded `pass` of a `test`, or a non-test item | `supported` (the explanation states which part Exegra executed and which is author-entered) |
| only `test` items with no recorded result | `inconclusive` |

`supported` therefore ranges from "Exegra ran this test and it passed" to "someone wrote a document reference". The explanation of each result says which. In the multiplayer test fixture (`tests/fixtures/multiplayer/spec.jsonc`), `ack-latency-objective` is `supported` by a measurement entity marked `illustrative://`, "A placeholder... No such report exists", and the result states that Exegra executed nothing.

## Recorded results

`exegra verify` executes the `test` evidence of a project and writes `specs/<project>/evidence/results.json`, keyed by evidence id:

```jsonc
{ "results": { "ev-roundtrip-core": { "outcome": "pass", "ranAt": "2026-11-14T18:02:54.354Z" } },
  "traceability": { /* module/file comparison */ } }
```

The application and CLI read it when evaluating claims. A `fail` records the last 20 lines of test output. A Node test reference that matches no test (a title pattern that selects nothing) is recorded as a `fail` with the detail "the reference matched no test", not as a pass. Evidence in a realisation root ([verification.md](verification.md#realisation-roots-code-and-tests-in-other-repositories)) is decided from that root's JUnit reports and records `root` and `reports` too; its outcome may also be `not-run` (absent from the report, skipped, errored, or failed for an environmental reason), which counts as no recorded result, never as a pass or a failure. Recorded results are **not bound** to a code or model hash, so a stale result is not detected as stale (a recorded limitation on `recorded-results-file`). Only evidence of kind `test` is executed.

## Concordance results

A linked project may name a results file written by Concordance, a tool that checks a specification against code, with `"concordanceResults"` in its `project.jsonc` (see [model-and-format.md](model-and-format.md)). Each entry of its `claims` (keyed by claim id, only `pass` and `fail` entries) is applied on load as a derived `test` evidence item, `concordance-<claim id>`, that exists only in claim evaluation. A `pass` makes an external-evidence claim `supported` (never `verified`), a `fail` makes it `violated`, and a claim without an entry stays `not-evaluated`. The explanation names the Concordance result with its `detail` and `proofs`. The file is ignored with a warning when it is missing or invalid JSON, when `tool` is not `concordance`, or when its `source` does not name the project's specification; an entry for an id that is not a claim of the specification is ignored with a warning naming the id. `exegra validate` lists these warnings under `concordance`. Nothing else changes: the derived items are never written to `results.json` and are not spec entities. Tests: `tests/core/concordance.test.js`. A `concordanceResults` path that is a directory (or cannot be read for another reason) is the warning `concordance.unreadable` and changes no status; the project still loads. The file watcher observes the results file too and reports a change as a change of the recorded results, so the application re-reads it and re-evaluates the claims. Tests: `tests/core/concordance.test.js`.

## What Exegra can prove, simulate, and only record

| Boundary | What it covers | Examples from `specs/exegra/spec.jsonc` |
|---|---|---|
| **Established by checking the model** | Structure of the declared components, relationships, ports, properties; evaluated exhaustively over the declared graph. | `core-independent-of-ui`, `core-dependencies-acyclic`, `storage-has-owner`. These are exact over *declared* relationships; that the declarations match the real imports is the assumption `relationships-match-imports`. |
| **Checked on traces** | Behavior of the specified state machines on listed scenarios and faults. | `rejected-edit-changes-nothing`, `conflict-never-overwrites`, `commit-only-after-validation`. Valid for the listed traces and for the machines as abstractions of the code. |
| **Needs external evidence** | Anything about the real code, tests, hardware, performance or time. | `simulation-deterministic` (supported by `tests/core/sim.test.js` with a recorded pass), `benchmark-scene-interactive` (`not-evaluated`: no measurement exists and no threshold is defined). |
| **Not evaluable here** | Probabilistic or exhaustive properties. | `ack-probability-bound` in the multiplayer test fixture uses `probabilistic-model-check`, which has no evaluator, so it stays `not-evaluated`. |

Seeded and real violations are kept visible on purpose. The multiplayer test fixture carries `ack-implies-durable-under-early-ack` (behavioral) and `database-reached-only-by-runtime` (structural), both violated by design, and the browser tests rely on them. The shipped `exegra` project carries `edits-only-via-transactions`, violated because Import bypasses the transaction pipeline.

## Integrity rules

A claim is about components, behaviors and traces. A consistency rule over the specification itself (no live entity rests on a superseded decision; a decision closes only what names it as resolver) is an **integrity rule** instead: an entity of the built-in kind `integrityRule`, evaluated on every edit, enforced by `Project.apply` as a ratchet, and proved (`holds`, by reflection) or refuted (from a concrete witness) in Lean by `exegra prove-integrity`. The same rule that vacuity is not verification applies: a rule whose quantifier ranges over nothing is reported vacuous, and every rule of the test fixture must be falsified by a stated mutation. See [integrity-rules.md](integrity-rules.md).

## Where results are shown

The *Verification* tab lists claims by status with scope, explanation, assumptions, evidence (declared versus recorded) and counterexample, and selecting a claim highlights its involved entities in the 3D scene; the `claims` projection draws a claim's entities colour-coded by status. Author-entered evidence is never drawn in a verified or supported colour: an evidence edge that supports is steel and one that contradicts is red. `node cli/exegra.js claims --project <name>` and `evaluate [<claimId>]` print the same results; `generate` writes `claims-report.md` and `.json`. The *Verification* panel shows recorded results loaded with the project and cannot execute tests.
