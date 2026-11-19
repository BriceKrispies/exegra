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

## Requirement realisation

A requirement may state how the system comes to satisfy it, in `realisation`:

- `construction`: generated code guarantees it. Some claim must name the requirement in `models`, or the requirement names at least one cross-cutting construct (a policy, validation, retention, quota, retry or audit) in `realisedBy`; otherwise validation reports `requirement.construction-unmodelled`, always, because a guarantee by construction that neither a check over the model restates nor a construct generates guarantees nothing. See [Model and format](model-and-format.md#cross-cutting-constructs).
- `checked`: hand-written code satisfies it and tests check it, through Concordance.
- `operational`: it is measured on a running deployment (budgets, deployment and operations requirements); no code satisfies it by itself.

When the specification sets `system.generation`, every requirement must state `realisation` (`ready.requirement-realisation-missing`; see [Model and format](model-and-format.md#types-contract-details-and-generation-readiness)). The property does not change how a claim is evaluated.

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
| `refines` | temporal | The implementation behavior `behavior` refines the model behavior it names in `refines`, through its `refinement` mapping, on the traces of its scenarios. See [Refinement](#refinement). |
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

## Refinement

A specification can hold two layers of state machines: abstract **model** behaviors, used for checking, and detailed **implementation** behaviors (`level: "implementation"`), from which code could later be generated. An implementation behavior I says which model behavior A it refines and how its configurations map onto A's:

```jsonc
{ "id": "lease-impl", "level": "implementation", "refines": "lease-model",
  "refinement": {
    "states":      { "li-free": "lm-free", "li-held": "lm-held", "li-renewing": "lm-held" },
    "variables":   { "holder": "owner", "epoch": "gen" },
    "transitions": { "li-acquire": "lm-acquire", "li-renew": null, "li-renewed": null, "li-release": "lm-release" } } }
```

`states` maps every state of I to a state of A; `variables` gives, for every variable of A, an expression of the expression language (`src/core/expr.js`) over I's variables (bare names only); `transitions` maps every transition of I to a transition of A or to `null`, a **stutter**: a step of I that A does not see. The ids inside the mapping are plain strings, not references, so renaming a state or transition does not rewrite them (validation then reports the stale name).

`timeScale` (optional, default 1) is the number of implementation time units per model tick, for a model that counts in ticks refined by an implementation that counts in, say, milliseconds (`"timeScale": 60000` for one-minute ticks). It changes two things and nothing else: wherever the check evaluates a model guard or effect, `time` is the trace time divided by `timeScale`; and a model timer's numeric `after` is multiplied by `timeScale` before it is compared with the implementation's timer. The division is one IEEE 754 double division, as every Exegra number is a double (`src/core/expr.js`, `formal/Exegra/Number.lean`), and model expressions then evaluate in doubles as the engine's do. It is exact whenever the trace time is a multiple of `timeScale` (the quotient is an integer below 2^53), so a boundary that must be decided exactly, such as `time - issuedAt <= 15` at the 15th tick, should fall on such an instant; between multiples the quotient is correctly rounded, not a rational. The mapping expressions, the implementation's own variables and other behaviors read by model expressions are not scaled: a mapping converts implementation quantities itself (for example `"issuedAt": "(expiresAt - 900000) / 60000"`). A `timeScale` that is not a positive number is the error `refinement.time-scale`; `refinement` without `refines` is already `behavior.refinement-without-refines`.

Validation refuses, as errors: a `refines` that names something other than a behavior (`ref.kind`, `ref.unresolved`); a `refines` on a model-level machine, whose `level` is absent or `model` (`behavior.refines-model-level`); refining a behavior that itself refines, since refinement has one level (`behavior.refines-chain`); `refines` without `refinement` (`behavior.refinement-missing`) and the reverse (`behavior.refinement-without-refines`); a key or value that is not a state or transition of the right side, or a mapping expression that reads anything but I's variables (`refinement.unknown-state`, `refinement.unknown-transition`, `refinement.unknown-variable`; a mapping that does not parse is `refinement.expr`); and a state or transition of I, or a variable of A, missing from the mapping (`refinement.unmapped-state`, `refinement.unmapped-transition`, `refinement.unmapped-variable`). A `refines` claim must name one behavior that declares `refines`, and each scenario it lists must run that behavior (`claim.param.value`).

**The check.** `{"method": "refines", "behavior": "<I>", "scenarios"?: [ids]}`, implemented in `src/core/refinement.js`, is a forward simulation with the mapping, evaluated on traces. Write `map(c)` for the model configuration of an I machine `c`: the state `states[c.state]` and, for each variable `v` of A, the value of `variables[v]` on the variables of `c`. The engine runs each scenario (the listed ones, or by default every scenario whose `behaviors` include I) with its own faults, exactly as the trace methods run theirs, and on each trace:

1. **Initial.** For every machine of I in the initial configuration (and for a keyed instance, the configuration it is created with), `map(c).state` is A's `initial`, and each mapped variable equals the `initial` of A's variable.
2. **Steps.** For every transition `t` that a machine of I fires, from `c` (its configuration before the step) to `c'` (after it):
   - if `transitions[t]` is `null`: `map(c).state = map(c').state`, every mapped variable is unchanged, and `t` emits nothing (strict: a stutter has no observable output);
   - otherwise, with `a = transitions[t]`: `a.from = map(c).state`; `a.on` is the delivered event (`t.on`); `a.to = map(c').state`; `a` is not `faultOnly`; and `a` is the transition **A itself would fire**: no transition of A declared before `a` with the same `from` and `on` has a guard that holds, and `a`'s guard holds. Guards and effects of A are evaluated on the mapped variables of `c`, with the step's event payload (`event.<field>`) and time (`time`, the trace time divided by `timeScale`). Applying `a`'s effects in order (a later effect reads an earlier `set`) to the mapped variables of `c` gives exactly the mapped variables of `c'`. The events `t` emits are the events `a` emits, by event id, in the same order and number; for each payload field that `a`'s emit sets, `t`'s emitted payload has that field with a structurally equal value; fields only `t` sets are implementation detail and are not compared. `cancel` effects are not compared; how a delayed emit is compared is under Timers below.
   - **Timers.** A trace step lists the entries a transition queued in `emitted`, emits and timers alike, in effect order. The check tells them apart by the transition's own effects: each `emit` and each `timer` effect queued exactly one entry, in declaration order (a `cancel` queued none); a transition whose effects cannot be matched this way (a fan-out emit, an emit over a link, a resource effect, or a count or event that differs) makes the result inconclusive. An emit is *delayed* when it has an `after` other than 0. A delayed emit and a timer are different things and neither realises the other: a delayed emit goes to its receivers `after` the step, a timer fires its event back at its own machine. So the implementation's emits, delayed or not, are compared with the model's emits, delayed or not, in effect order (reason `emits`): the same events, in order and number, with the payload fields the model sets equal; each emit delayed exactly when the model's is (an emit at once for a delayed one, or the reverse, is a violation); and where the model's `after` is a number, the implementation's emit is delivered at the step's time plus that number times `timeScale` (a duration or a distribution is not compared). A model's `{emit, after}` is therefore realised only by an implementation `{emit, after}` of the same event at the scaled delay; an implementation timer for that event, even with the model's delay, leaves the model's emit unmade and is violated with reason `emits`. A timer the implementation sets is compared only when the model transition sets timers: then the timers must emit the same events, in order and number, with the payload fields the model sets equal, and where the model's `after` is a number the implementation's timer must fire at the step's time plus that number times `timeScale` (reason `timers`). When the model transition sets no timer, the implementation's timers are internal to it and are not compared, and a stutter may set timers but emits nothing, delayed or not. A timer's later firing is a delivery like any other: the transition the implementation fires on it is checked as its own step, against the model transition the mapping names (which is triggered by the same event) or as a stutter.
   - **Other behaviors.** A model guard or effect may read another behavior, `<B>.state` or `<B>.<variable>`, as in the engine. It is read from the same trace: from the machine that ran under the id `B` in the run, or, when none did, from the one machine of the run whose behavior refines `B`, through that behavior's refinement mapping (its `states` for `state`, its `variables` expression for a variable). A guard reads the configuration before the step. An effect reads it as the engine's effects do: the configuration after the step for a machine that fired earlier in the same step (scenario order), and the one before the step otherwise. `<A>.state` and `<A>.<variable>` of the model itself read the mapped state and variables. A behavior with several instances in the run, one that no machine of the run is or refines, one that two machines refine, and a three-part reference (an aggregate) make the result inconclusive.
   - **Instances.** A format-2 trace names the instance of every fired entry, `0` for a behavior without `instances`, while that behavior's machine key is its bare id; the check takes the machine `<I>#<instance>` when the configuration has one and the bare id otherwise.
3. **Verdict.**
   - **violated** at the first failing check, with `counterexample` carrying the `scenario`, the `stepIndex` (`-1` for the initial configuration), a `reason` (`initial-state`, `initial-variables`, `unmapped-transition`, `model-from`, `model-event`, `model-to`, `model-fault-only`, `model-not-chosen`, `model-guard-false`, `post-variables`, `emits`, `timers`, `stutter-state`, `stutter-variables`, `stutter-emits`, `mapping-error`, `model-expression-error`) and `trace`: the steps of I checked so far in that scenario, each `{scenario, stepIndex, machine, event, transition, implFrom, implTo, model, modelFrom, modelTo, ok}`, the last being the failing step with `ok: false`. A mapping expression, or a model guard or effect, that fails to evaluate on a reached configuration (an error of the expression language) is a violation: the mapping is not a function there.
   - **inconclusive** when a scenario cannot be run or ends in an error (the steps before it were checked, but the run did not complete); when a listed scenario does not run I; when a model expression reads something the check does not resolve (see Other behaviors; an aggregate; `instance`), a model transition has a resource effect or a sampled `set`, or an implementation transition's queued entries cannot be told apart (see Timers); when no scenario runs I; and when I fired no transition, or only stutters, in every trace (vacuity is not verification: nothing of A was matched).
   - **verified** otherwise: every initial configuration and every step passed, and at least one step matched a model transition. A run cut off at its step limit is reported as the trace methods report it: the steps it executed were checked, and the scope and explanation say that later steps were not run.

**What a verified result establishes**: on the traces of the listed scenarios, each run with its own faults and the engine's deterministic order of simultaneous events, every step of I maps under the mapping to the step A takes from the mapped configuration, emitted events included. **What it does not establish**: refinement on other inputs, other fault subsets or other delivery orders (the explorer of `formal/Exegra/Explore.lean` returns state-invariant verdicts, not the steps a refinement check needs, so it is not used here); anything after a step limit; that A's environment is the one the other behaviors' models describe (another behavior is read from whatever machine ran under its id or refines it, as it ran); and anything about generated or hand-written code. A `refines` claim takes no `negatives`: unlike a trace property it compares each step with a second machine, and the violated cases of `tests/core/refinement.test.js` show each part of the check failing. The check is JavaScript in the verdict-kernel component `claim-evaluator`, not yet ported to Lean, so `core-logic-in-lean` lists it with that component.

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
