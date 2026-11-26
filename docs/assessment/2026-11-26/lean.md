# Lean theorem proving and proof architecture: assessment

Scope: formal/Exegra/** (12,783 lines, 247 `theorem`s), formal/Main.lean, lakefile.toml, formal/wasm/, tools/prove.js, tools/prove-integrity.js, tools/lean-theorems.js, src/core/proof-export.js, the `lean-theorem` method (src/core/claims.js:363-407), src/core/lean.js. Lean is not installed, so no Lean file was elaborated here. Lean-side conclusions are ARGUED from source. The JS rule findings are DEMONSTRATED by running the rule's own code.

## 1. Verdict

- **Evolve the foundation; do not rewrite it.** The proofs that exist are real. I found no hidden `sorry`, no axiom of the project's own, and no `native_decide`, `implemented_by`, `extern` or `unsafe` in the library. The only `sorry` is `Lift.lift_agrees`, and it is pinned and disclosed. The integrity checker is a genuine kernel-reflection design, with a `Prop` semantics, a least-model meaning and a proved `eval_iff`.
- **What it proves is narrow.** It proves:
  - some structural facts about one executable step function;
  - that an optimized Lean program equals a reference Lean program;
  - soundness of a bounded explorer over that step function.
- **What it has no foundation for:** an abstract semantics, components or contracts, infinite traces or fairness, spec-level refinement, and arithmetic (time is an opaque `Float`).
- **What the objective needs:** guarantee classes 3–6 require a relational, propositional semantics layer above today's executable one, and the claim checker needs real statement binding. Both can be added on top of the current code. The executable definitions, the refinement chain and Integrity.lean should be kept.

## 2. Fundamental limitations and unsound assumptions

**L1. The `lean-theorem` checker does not bind the theorem to the claim. Severity: BLOCKS-OBJECTIVE. Status: DEMONSTRATED.**
- Code: claims.js:371-407, lean-theorems.js:51-73.
- What it checks: the constant exists and is a theorem; the kernel re-accepts it; its axioms are among {propext, Classical.choice, Quot.sound}; and each `about` constant is a `definition` *or `opaque`* that occurs in `ci.type.getUsedConstants`.
- What it never checks: the theorem statement against the claim's prose `statement`. It also never inspects hypotheses or `implemented_by`/`extern` attributes.
- Demonstration: I extracted `evaluateLeanTheorem` verbatim into scratchpad/elt.cjs and fed it the records Lean would emit:
  1. **Tautology.** Claim "every run stops"; theorem `theorem tauto (i : Exegra.SimInput) : Exegra.runInput i = Exegra.runInput i ∧ (2:Nat)^20 = 1048576 := ⟨rfl, by decide⟩` with `about: ["Exegra.runInput"]`. Result: **proved**. This is the repo's own fixture `uses_native_decide` (tests/fixtures/lean-theorem/Refused.lean) with `native_decide` replaced by `decide`. The fixture is refused only because of its axiom, not because its statement is off-topic.
  2. **No `about`.** A claim naming the unrelated `Exegra.Api.registry_names_nodup` with no `about` is **proved**. The explanation merely adds "says nothing about which code it covers".
  3. **`about` names an `opaque` constant.** Result: **proved**. A theorem about an `opaque` constant can say almost nothing about its runtime body. `opaque X : T := impl` with `@[implemented_by]`, or any `partial def` (which compiles to an opaque with `implemented_by`), passes.
- Further vacuous statements that would also pass (ARGUED, same rule): `True ∨ P(runInput)`; and `(h : runInput i = .ok tr) (h2 : tr.steps.length < 0) → …`, whose hypotheses cannot be satisfied.

**L2. Recorded theorem facts are not bound to the sources they were checked against. Severity: LIMITS. Status: DEMONSTRATED.**
- specs/exegra/evidence/results.json `theorems.*` stores only `{found, kind, kernel, axioms, about, lean, checkedAt}`. There is no hash of the theorem's type, of formal/, or of the `.olean`.
- When Lean is absent (the app; every CI without elan; `EXEGRA_NO_LEAN=1`), cli/commands.js:170-181 uses the recorded facts.
- Consequence: weakening `runInput_terminates` to `True` keeps the claim **proved** until someone re-runs with Lean. Admission (cli/admit.js:188) treats lean-theorem claims as decidable from those same records.

**L3. The step semantics is executable only and works on raw data. Severity: BLOCKS-OBJECTIVE for classes 4–6. Status: ARGUED.**
- `step : Env → Config → StepResult` (Semantics.lean) is the only definition of behavior.
  - Guards and effects are stored as source strings (`TransitionIn.guard : Option String`) and are parsed by `parseExpr` *inside* every step.
  - Values are JSON `Value`s, and times and numbers are `Float`.
- Lean's `Float` arithmetic is `@[extern]` opaque over an axiomatized `floatSpec`. No propositional fact about time arithmetic can be proved: not `t ≤ t + d`, not time monotonicity of a run, not a timer firing order.
- Accordingly, Properties.lean (27 theorems) proves only shape facts:
  - fired behaviors are a sublist (`step_fired_sublist`/`nodup`);
  - drop steps fire nothing;
  - failed steps keep nothing;
  - fuel termination (`runInput_terminates`, which is fuel-bounded by construction).
- Three are pure tautologies: `step_deterministic`, `runInput_deterministic`, `runText_deterministic`. Each is function congruence, `h₁.symm.trans h₂` or `h ▸ rfl`.
- The relation `Reachable`/`Succ` (Explore.lean:233-253) is a `Prop`, but it is *defined by* running `step`. There is no independent relational specification for `step` to be checked against.

**L4. Format 2, the engine that carries workloads, resources and metrics, has almost no theorems. Severity: LIMITS. Status: ARGUED.**
- Format2.lean has 3,057 lines and 3 theorems (`makeInstant_arrivals_le`, `endWhere_*`).
- Resource.lean proves per-function bounds (`grantLoop_ok`, `bounds_ok`, …), but no theorem lifts them to runs of `V2.traceOf`.
- `lift_agrees`, which relates format 1 to format 2, is `sorry` (Lift.lean:131-136; pinned by `#guard_msgs` on `sorryAx`).
- The refinement theorem covers format 2 only trivially: `runInputV2_eq` holds because Impl calls `V2.traceOf` unchanged (Impl/Refinement.lean:266).

**L5. `exegra prove` rests on `native_decide`, a per-scenario closed world, and an unverified JS projection. Severity: LIMITS. Status: ARGUED.**
- How the proof is produced (proof-export.js:224-266):
  - The generated file states `explore env (claimInv e) bound maxStates = .holds n := by native_decide`, plus `input_decodes : decodesTo inputText input = true := by native_decide`.
  - The module dynlibs are loaded (prove.js:113-114), so the result is computed by native code.
  - Reflection is not possible: `Json.parse` is `partial` (Json.lean:32-182), `Float` and `String.hash` are opaque, and docs/simulation.md:242 says kernel reduction is infeasible.
- Trusted computing base:
  - Lean compiler, C compiler, runtime, and the `--load-dynlib` shared objects;
  - the per-theorem `._native.native_decide.ax_*` axiom;
  - JS `simulationInput` (sim-input.js), which projects spec → engine input text. That projection is unverified; `input_decodes` only ties the Lean term to that JS output.
- Known divergence between compiled code and the logical model, which matters only under `native_decide`: NaN (simulation.md:242: "the logical model has a single NaN, while compiled code compares bit patterns"). A `native_decide` result over NaN-producing states may therefore not match the logical semantics that `explore_sound` interprets it in.
- The safety theorem itself, `∀ s, Reachable env bound s → claimInv e s.cfg`, is never instantiated in the generated file. It is assembled in prose (proof-export.js:420) from `explore_sound`.
- Nondeterminism covers only the order of equal-time events and subsets of declared faults. Payloads, times and environment inputs are fixed by the scenario.
- Status honesty: these results are reported as `explored`, not `proved`, and `trusted` lists the native axiom.

**L6. Liveness is finite-trace only. Severity: BLOCKS-OBJECTIVE for class 4. Status: ARGUED.**
- `TraceHolds (.eventually …)` (Temporal.lean:78-87) means: the occurrence appears in a finite run ending at quiescence (`CompleteRun`/`Ended`), and the expression holds at the final configuration.
- Runs that hit the step limit make the verdict `incomplete`.
- There are no infinite traces, no fairness assumptions and no ω-regular or LTL semantics. `tverdict_sound` cannot be extended to "progress under fairness" without a new trace model (coinductive or lasso).

**L7. No compositional or contract structure in Lean. Severity: BLOCKS-OBJECTIVE for class 5. Status: ARGUED.**
- `Env` is the closed product of all behaviors of one input. There is no notion of interface, assumption, guarantee or behavior subset with an environment abstraction.
- Spec-level `refines` is JavaScript trace checking (src/core/refinement.js; docs/claims-and-evidence.md:102 says so).

**L8. Kernel recheck versus runtime. Severity: MINOR. Status: ARGUED.**
- lean-theorems.js:57-62 re-adds the proof with `addDecl`. That is redundant with `lake build` but harmless.
- Theorems about runtime behavior ignore resource exhaustion. Stack overflow is a wasm trap, which lean.js reports as an error.
- `call_model_derive_total : ∃ out, call "model.derive" v = .ok out := ⟨_, rfl⟩` holds because `deriveValue` is literally `.ok (…)` (Model.lean:1026-1027). It says nothing about "always returns" at runtime.

## 3. Overclaims

- **Commit 2cfc6af, "Lean engine in the app, proved equal to its definition."** True as stated, read precisely. Impl/Refinement.lean proves `Impl.runAny text = Exegra.runAny text` for all text by a clean chain: `evalC_compile` → `scanC`/`chooseC` → `fireAllC` → `stepC_compile` → `loopC_compile` → `runAnyValue_eq`. The axioms are pinned to the standard three, and no `implemented_by` or `csimp` is involved. But:
  - "definition" means a second Lean program, not a mathematical semantics;
  - for format 2 the equality is identity;
  - for text input both sides share the opaque `partial` `Json.parse`.
  It is a verified optimization (`evalFast`, thunked parses, `write'`), not "the engine is correct".
- **Claim `model-derivation-total`.** "never with an error, and always returns" is backed by a theorem that is true by construction of the wrapper (see L8).
- **Claim scope text (claims.js:376).** It says "establishes the statement about the Lean definitions it names". Nothing checks that the Lean statement is the claim's statement (L1). The claim id and its prose are trusted by convention.
- **"Verified explorer" / "Verified by Lean for all N configurations"** (proof-export.js:420; docs/agent-interface.md:297). Accurate only with all of these qualifiers:
  - native_decide;
  - bounded;
  - one scenario's fixed inputs;
  - the JS-projected engine input.
  The explanation includes bound and faults but not the projection.
- **"Every complete run" (temporal).** "Complete" here means runs that end at quiescence within the step limit, not unbounded behavior.

## 4. What to preserve

- **Integrity.lean.**
  - `Sat`/`Least`, with `Least` defined impredicatively and `least_eq_table` proving that the solved table equals it.
  - `holds_of_eval` and `violated_of_refutes`, discharged by `decide +kernel` with standard axioms only.
  - This is the right pattern: Prop semantics, a Bool checker, a soundness theorem, and kernel reflection. The rest should be built this way.
- **Explore.lean soundness.** `explore_sound` and `explore_counterexample_real`, with `Grow`/`BfsInv` invariants over `Std.HashSet`. These are generic, total, and give `holds` an exact meaning.
- **Impl/Refinement.lean methodology.** Function-by-function simulation lemmas from the optimized code to the reference code, with `#guard_msgs` axiom pins. Reusable for every future fast path.
- **Axiom pins** (`#guard_msgs in #print axioms`) in Resource, Temporal, Hash, Explore and Refinement, including pinning the `sorry` in Lift. This is honest and catches regressions at build time.
- **Status honesty in the checker.** Rejecting native_decide, sorryAx and custom axioms works and is tested. `explored` is kept separate from `proved`.
- **Resource.lean.** Capacity and limit invariants of the grant loop, with real induction proofs over Nat. Good material for a safety layer.

## 5. Architectural decisions that would prevent the objective

1. **Expressions as strings inside the semantics.** Replace them with a typed, pre-elaborated AST in `Env`, plus a proved `parse ∘ print` round trip. Theorems should then quantify over ASTs, with no parser in the loop.
2. **`Float` as the semantic number and time domain.** Make the semantic domain exact: `Int` ticks or `ℚ` for time, and an abstract numeric type for values. Prove that the Float implementation refines it within stated error, or restrict it to integer-valued cases. Otherwise no time property is provable and no kernel decision is possible, so `native_decide` is mandatory.
3. **A single executable step function as the only definition.** Add a relational small-step semantics `Step : Config → Label → Config → Prop` with assumptions (environment and faults) as explicit parameters. Prove `step` sound and complete for it. Explorer, temporal checks and refinement must then target the relation.
4. **A claim binding of "a constant occurs in the type".** Replace it with a statement template per claim method. Lean elaborates the template from the claim's parameters (for example `∀ i, Accepts i → Terminates (Impl.runAny i)`), and the theorem's type must be *definitionally equal* to the elaborated template. Free-form theorems should get a weaker status.
5. **Spec → engine-input projection in JS.** Port `simulationInput` to Lean, or prove a decode-of-projection lemma. Until then, every Lean result about a spec is about a JS artifact.
6. **A closed-world `Env` with finite traces.** Introduce components with interface alphabets, parallel composition, and infinite (coinductive or lasso) traces with fairness. Without these, assume-guarantee reasoning and liveness cannot be stated.

## 6. Highest-leverage changes, in dependency order

1. **Bind lean-theorem claims to statements, and bind records to sources.**
   - Per-method Lean statement templates; check `isDefEq(thm.type, template)`.
   - Refuse `opaque` in `about`, and refuse `about` constants whose transitive closure has `implemented_by`/`extern`.
   - Record a hash of the theorem type and of `formal/` with each check; mark the record stale on mismatch.
   - Done when: the three scratchpad/demo.cjs cases (tautology, no-about, opaque) and a vacuous-hypothesis theorem are refused, and editing a theorem's statement without Lean turns its claim `not-evaluated`.
2. **Exact semantic core.**
   - Typed AST in `Env`; Nat/Int time; `Float` only in a refinement layer.
   - Done when: `theorem run_time_monotone : ∀ i tr, runInput i = .ok tr → tr.steps.Pairwise (·.time ≤ ·.time)` is proved with standard axioms, and the explorer for a small scenario is checked with `decide +kernel`, with no native axiom.
3. **Relational semantics with explicit assumptions.**
   - `Step env A c ℓ c'`, where `A` is the environment/fault assumption set; `step_sound`/`step_complete`; restate `Reachable` over it.
   - Done when: `explore_sound` is re-derived for the relation, and a safety theorem `∀ c, ReachableA env A c → Inv c` is generated as an actual theorem, not prose.
4. **Infinite traces and fairness.**
   - Lasso or coinductive traces, weak and strong fairness predicates, and a sound liveness checker (for example a nested-DFS or SCC lemma) with a soundness theorem.
   - Done when: `tverdict_sound` has a counterpart `∀ trace, Fair trace → Run trace → ◇P` for a fixture.
5. **Composition and refinement in Lean.**
   - Port `refines` to Lean as a forward-simulation relation over `Step`, and add parallel composition with an assume-guarantee rule.
   - Done when: a proved `refines_trans` and an `ag_compose` theorem exist, and `refinement.js` becomes a projection of a Lean verdict.

## 7. Predictions about other teams' errors

- **Taking "proved equal to its definition" as end-to-end correctness, or dismissing it as fake.** Both are wrong. It is a sound optimization-equivalence proof, and it says nothing about whether the definition is right.
- **Calling `exegra prove` results kernel-checked proofs.** They are not: they are native_decide over a JS-produced input. The opposite error is also likely: claiming the repo hides `native_decide` in `proved` claims. It does not, because the lean-theorem checker refuses it and the results are labelled `explored`.
- **Counting 247 theorems as coverage.** Most are lemmas about JSON writers, hashing, `Value.beq`, and the search data structures. Behavioral theorems about runs are about 10, and three are tautologies.
- **Simulation and fidelity teams.** They may assume that the Lean Float semantics equals the IEEE semantics that runs. The NaN divergence is documented, and nothing about Float arithmetic is provable in Lean at all.
- **Claims and integrity teams.** They may miss that the lean-theorem `proved` status depends entirely on the human-chosen theorem name and the `about` list (L1), and on stale-able records (L2).
- **Rust oracle team.** Differential agreement is with the reference Lean definition, which has no independent specification. Agreement there does not establish semantic correctness.
