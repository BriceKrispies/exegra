# Foundations and formal semantics: assessment

Team: mathematical foundations and formal semantics. Everything here comes from reading the source. Lean is not installed, so no theorem was re-checked and nothing was executed. "DEMONSTRATED" means I traced a concrete counterexample through the Lean or JS definitions by hand.

## 1. Verdict

- There is no mathematical account of what a specification means. What exists is a chain of executable steps: JSON text, then the JS model, then JS `sim-input.js`, then the engine-input JSON, then a Lean decoder, then a deterministic Lean interpreter. Nondeterminism is added from outside, and only by `exegra prove`.
- No document states that the semantics is a transition system, LTS or automaton. Neither a model nor a claim is defined as a mathematical object apart from its JSON.
- Some of the Lean can be kept and evolved: the generic search (`Search.lean`), the proof that the implementation equals the definition (`Impl/Refinement.lean`), the integrity logic (`Integrity.lean`), the resource invariants (`Resource.lean`) and the temporal monitors.
- The semantic core cannot be evolved and must be rewritten. That core is the semantic domain (JSON `Value` with `Float` numbers and object identities), the two unrelated formats, the definition written as an interpreter, and the JS mapping from a spec to its semantics.
- Five guarantee classes have no underlying object at all: liveness, compositionality, refinement, conformance and fidelity.

## 2. Fundamental limitations and missing foundations

**F1. No denotation function lives in Lean. Severity: BLOCKS-OBJECTIVE. Status: ARGUED.**
- `Model` (`Model.lean:867-876`) is a list of `Entity {id, kind, data : Value}`, i.e. untyped JSON with ids. Nothing in Lean maps a `Model` to behavior.
- The meaning of a spec's behaviors is computed by JS: `src/core/sim-input.js` (514 lines) builds the engine input from the JS model, not from the Lean model.
- JS also chooses which of two semantics applies: `needsFormat2` at `sim-input.js:320-331` routes the spec to format 1 or format 2.
- So JS defines the function ⟦spec⟧. Lean defines only ⟦engine input⟧.

**F2. Two semantics, unrelated, and every theorem is about the older one. Severity: BLOCKS-OBJECTIVE. Status: ARGUED.**
- Format 1 (`Semantics.lean`) has `Float` time and one machine per behavior.
- Format 2 (`Format2.lean`, 3057 lines) has `Nat` time, instances, routes, timers, links, resources and PRNG draws.
- Their agreement theorem `Lift.lift_agrees` (`Lift.lean:128-136`) is `sorry`. It is pinned as such, which is honest.
- `Properties.lean`, `Explore.lean` and `Temporal.lean` are all about the format-1 `Exegra.step` / `runInput`.
- `exegra prove` decodes only version 1: `Input.lean:237-241` rejects other versions with "this engine reads version 1".
- Format 2 has about three theorems of its own (`makeInstant_arrivals_le`, `endWhere_*`), plus the resource invariants in `Resource.lean`.
- So every construct that needs resources, instances, timers or probability has no exploration and no theorem about runs.

**F3. The definition is an interpreter, not a transition relation, and its runs are finite only. Severity: BLOCKS-OBJECTIVE (liveness). Status: ARGUED.**
- `step : Env → Config → StepResult` (`Semantics.lean:509`) is a function. The step limit is part of the input.
- Nondeterminism lives only in `Explore.lean`. `canPick` and `moveToFront` (`:218-237`) pick among entries with the same time, and `masks` picks a subset of faults.
- Liveness cannot be expressed:
  - There are no infinite traces and no fairness.
  - `Temporal.Form.eventually` (`Temporal.lean:77-87`) means "some step matched, and an expression is true in the final configuration of a finite run". That is a property of where a run ends, not LTL ◇.
  - The temporal forms are only `never`, `precedes` and that `eventually`.
- Time is a priority key on the queue: `Float` in format 1, `Nat` in format 2. There are no clocks, no invariants and no urgency, so there is no timed-automaton reading.

**F4. Composition is ordered, not parallel, and the explorer does not vary the order. Severity: BLOCKS-OBJECTIVE (compositionality). Status: DEMONSTRATED (by trace).**
- In phase 2, each behavior's effects read the shared next configuration:
  - `runEffects` evaluates against `s.next` (`Semantics.lean:324-357`).
  - `resolve` reads `[b, name]` from that view (`:184-197`).
  - `fireAll` runs the behaviors in scenario order (`:371-381`).
  - So a later behavior sees what an earlier one wrote. `docs/simulation.md:146` states this.
- Counterexample:
  - Behavior `a` (variable `x = 0`) has `s0 --e--> s0`, effect `set x = 1`.
  - Behavior `b` (variable `y = 0`) has `t0 --e--> t0`, effect `set y = "a.x"`.
  - The scenario delivers `e` at time 0.
  - With `behaviors: [a, b]`, the run ends with `b.y = 1`. With `[b, a]`, it ends with `b.y = 0`.
  - So the invariant `b.y == 0` is "holds" for one listing and a counterexample for the other. Both listings are the same set of components.
- `canPick` permutes only queue entries, never the order of behaviors within a step.
- The validator warns only about the order of transitions (`validate.js:402`), not about this cross-behavior read.
- So the composition operator is neither commutative nor defined independently of a scenario. Assume-guarantee reasoning has nothing to stand on.

**F5. A closed world, with assumptions that are prose. Severity: BLOCKS-OBJECTIVE (safety under assumptions, consistency). Status: ARGUED.**
- The only environment is one fixed scenario script, with fixed times and payloads.
- A `holds` verdict ranges over fault subsets × tie orders of that one script. Payloads, arrival times and environment behavior are never universally quantified.
- `assumption` is `{statement, rationale}` text (`metamodel.json:487-495`). It has no formal content, so assumptions cannot be conjoined, checked for satisfiability or discharged.

**F6. The explorer silently prunes failed steps. Severity: LIMITS. Status: DEMONSTRATED (by trace).**
- `succOf` returns `none` on `.failed` (`Explore.lean:233-237`), so a failing step simply has no successor.
- Counterexample:
  - A scenario delivers `e` at time 0. The only transition on `e` has the guard `1 / 0 > 0`.
  - `eval` throws "Division by zero" (`Expr.lean`, `.div` case), so `step` returns `.failed` and there are no successors.
  - `explore` therefore reports `holds 1` for any invariant true in the initial state.
  - `proof-export.js` (`proofResults`) prints "Verified by Lean for all 1 configurations reachable within N steps".
- The JS trace evaluator calls the same run `inconclusive` because it ended in an error (`claims.js` trace evaluator). Two meanings of "holds" coexist.
- `bfs` returning `.holds` at depth 0 (`:411-418`) is honestly bounded in `explore_sound`, so that part is fine.

**F7. The semantic domain is JSON with IEEE floats and object identities. Severity: BLOCKS-OBJECTIVE for unbounded proofs. Status: ARGUED.**
- `Value.num : Float` (`Value.lean:21`), and format-1 time is `Float`.
- In the kernel, Lean's `Float` operations are opaque, with no algebraic laws. Any proof that touches guards is therefore `native_decide` on one instance (`proof-export.js:244-260`) and can never be general.
- `Value.eqv` is not reflexive on NaN (`Value.lean:145`). Untyped `1e308*10 - 1e308*10` produces NaN.
- `Value.obj`/`arr` carry a JS identity counter (`nid`), and `step` mirrors reference aliasing on purpose (`Semantics.lean:504-508`, "MIRRORED"). The semantics therefore models JS heap identity.

**F8. Authority runs backwards: the Lean definition mirrors the Rust engine. Severity: LIMITS. Status: ARGUED.**
- `Semantics.lean:4-22` calls the file "the definition the Rust engine is checked against", but says accidental engine behavior is "mirrored on purpose" (MIRRORED, `:38`, `:73`, `:506`). There are 10 ORDER marks.
- So the "normative" semantics was reverse-engineered from an implementation, accidents included.
  - Example: a repeated behavior id is scanned twice per step (`:73`).
- Agreement between Lean and Rust is agreement between a copy and its original. It is not evidence that either is correct.

**F9. Claim kinds mostly have no denotation in Lean. Severity: BLOCKS-OBJECTIVE. Status: ARGUED / DEMONSTRATED.**
- These claims have a meaning in Lean:
  - state invariants: `claimInv`, `Prove.lean:34-42`;
  - three temporal forms: `TraceHolds`, `Temporal.lean:77-95`;
  - integrity formulas: `Integrity.Sat`, `Least`, `eval_iff` (a genuine denotational semantics).
- These exist only as JS evaluators:
  - structural claims: `claims.js:564-571`;
  - `metric-bound`: `metric-claims.js`;
  - `refines`: `refinement.js`, a single-trace step check;
  - the trace methods used for status: `evaluateTraceClaim`, `claims.js:1012+`, with JS `expr.js` and one deterministic trace.
- Counterexample (DEMONSTRATED by trace) showing that JS "verified" and Lean disagree:
  - Scenario steps `a@0` then `b@0`. Behavior `m` has `s0 --a--> s1`, `s0 --b--> bad` and `s1 --b--> s2`. Invariant: `m.state != "bad"`.
  - `runInput` delivers by `seq`, so `a` comes first and the invariant holds on the trace. With a negative, JS reports `verified`.
  - `explore` takes picks `[1]`, delivering `b` first, and finds the counterexample.
- `Integrity.Sat` is defined over `Facts` that JS builds (`src/core/integrity-export.js`), so even the best-founded layer depends on an unverified JS projection of the model.

**F10. Probability and resources. Probability: LIMITS. Resources: preserve. Status: ARGUED.**
- Distributions denote SplitMix64 draws from named seeded streams (`Random.lean`, `Format2.sample`). No probability measure over runs is defined.
- `metric-claims.js` applies exact binomial and sign tests that treat PRNG-seeded runs as i.i.d. samples, from a distribution that is never defined anywhere.
- Resources are given a real semantics (`Resource.lean`): `held ≤ limit` is preserved by grant, release and bounds (`grantLoop_ok`, `bounds_ok`).

## 3. Overclaims

1. **`Api.lean`, docstring of `call_engine_run_spec`.** It calls `Exegra.runAnyValue` "the function the theorems of `Exegra/Properties.lean` are about". In fact those theorems are about `Exegra.runInput` (format 1). The format-2 branch of `runAnyValue` is covered by none of them.
2. **Spec claim `engine-run-terminates-proved` (`spec.jsonc` around line 17527).** The statement covers "every run of an engine input that the engine accepts". The cited theorem `runInput_terminates` covers format 1 only, yet the rationale says it holds "of what runs". Format-2 termination is probably true, since fuel equals `stepLimit ≥ 1` (`Format2.lean:828`), but it is not proved.
3. **Determinism as a "proved property" (`simulation.md:198`, `Properties.lean:24-35`).** `runInput_deterministic` assumes `i₁ = i₂` and concludes equality of results. That is congruence and carries no information. Meanwhile the model's real nondeterminism (tie order, behavior order, faults) sits outside the semantics, so "deterministic" describes the scheduler choice baked into the interpreter, not the model.
4. **`prove` output, "Verified by Lean for all N configurations reachable…".** It omits three things:
   - failed steps are pruned (F6);
   - inputs are fixed by one script (F5);
   - only format-1 scenarios can be explored at all (F2).
5. **The trace-claim status `verified` (`claims-and-evidence.md:109`).** It is the same label used for model-checked results, but it rests on one deterministic trace per scenario. The `prove` explorer can contradict it (F9).
6. **"Semantic hash" (`Model.lean:883`) — MINOR.** It hashes JSON declarations up to presentation, not semantics. Two specs differing only in behavior order hash differently, which is accidentally correct here (F4), and semantically equivalent specs can also hash differently.

## 4. What to preserve

- **`Search.lean` (`Gen.Sys`, `search_sound`, `search_counterexample_real`).** A generic bounded BFS over any finitely-branching system, proved sound and with real counterexamples. It is the right abstraction to point at a future relational LTS.
- **`Impl/Refinement.lean` (`runAnyValue_eq`).** It proves the fast implementation equal to the definition, with no `implemented_by`. This is the template for "Lean is the sole authority" between definition and runtime.
- **`Integrity.lean`.** `Sat` and least-model semantics of stratified programs, a reflective checker with `eval_iff` and `least_eq_table`, and refutation by witness. It is the one genuinely denotational claim logic, and it should become the core of the claim language.
- **`Temporal.lean`.** The monitor/specification agreement proofs (`never_monitor`, `precedes_monitor`) and the product-system construction can be reused for safety automata.
- **`Resource.lean` invariants**, and the integer, checked arithmetic design in `Expr.lean` (`intResult`, `divIn`). The design is right. The carrier (`Float`) is wrong.
- **The `#guard_msgs` axiom pins**, including the honest `sorryAx` pin on `lift_agrees`.

## 5. Architectural decisions that would prevent the objective, and replacements

| Decision | Why it blocks | Replace with |
|---|---|---|
| JSON `Value` (Float, nid identity) as the semantic domain | No algebra in the kernel, NaN, heap identity | A typed value domain (`Int`, `ℚ` or bounded ints, records, lists) indexed by declared types |
| The JS translation spec → engine input, and JS choosing between format 1 and format 2 | JS defines ⟦·⟧ | A Lean elaboration `Model → Core` that Lean owns, run through the wasm boundary |
| The definition written as an executable interpreter, with nondeterminism added outside | No relation to refine or compose; finite runs only | A relational, labelled semantics (`Prop`), with `step` proved to be one scheduler of it |
| Two formats with an unproved lift | Theorems cover the format nobody extends | One core calculus; format 1 becomes sugar, or `lift_agrees` is proved |
| A closed scenario script as the only environment | No "for all inputs", no assumptions | Open automata with input actions; the environment as an automaton or trace set; scenarios as particular environments |
| Ordered synchronous broadcast within a step | Composition is non-commutative | Either snapshot semantics for all reads in phase 2, or explicit interleaving explored as nondeterminism |
| Claims as JS evaluator dispatch | No common satisfaction relation | One Lean claim language with `Sat`; JS evaluators become checkers proved sound or certified per run |
| Lean mirrors Rust ("MIRRORED") | Semantics inherits accidents | Lean is designed first; Rust follows it; MIRRORED items are removed or turned into designed rules |

## 6. Highest-leverage foundational changes, in dependency order

1. **A core calculus with a relational LTS.** Define in Lean `Core` (components, typed variables, events and actions with input, output and internal polarity, transitions, effects) over a typed value domain. Then define `Rel : Core → Conf → Label → Conf → Prop`, with time as an explicit `tick` label over `Nat`.
   - *Done when:* `step_sound` holds: if `step env c = committed r c'` then `Rel ⟦env⟧ c (lbl r) c'`. `choices_complete` holds: every `Rel` step is reachable by some explorer choice, including behavior order or a proved order-independence. `lift_agrees` is proved, or format 1 is deleted. No `Float` appears in `Core`.
2. **Port the elaboration `Model → Core` to Lean** (the work of `sim-input.js`, `needsFormat2` and readiness typing).
   - *Done when:* `engine.run` takes the derived model, `sim-input.js` is deleted, and a theorem relates `Model.derive` diagnostics being empty to elaboration succeeding (well-formed ⇒ elaborates).
3. **Open systems and parallel composition.** Components are I/O automata; scenarios and environments are automata or trace sets; `‖` synchronises on shared actions.
   - *Done when:* `par_comm` and `par_assoc` hold up to (bi)simulation, and the F4 example gives the same verdict for both listings.
4. **Traces, claims and contracts.** Finite and infinite traces with an observation projection `obs`. A Lean claim language (safety and liveness LTL fragment, state predicates, integrity formulas) with `Sat`. Contracts as `(A, G)` trace-property pairs. Refinement as trace inclusion, or simulation, on `obs`.
   - *Done when:* these are proved:
     - `refines_preserves_safety : Refines I A → Sat A φ → Sat I φ`;
     - the assume-guarantee rule `C1 ∧ C2 compatible → (M1 ⊨ C1) → (M2 ⊨ C2) → M1‖M2 ⊨ C1⊗C2`;
     - for liveness, a fairness hypothesis appears explicitly in the theorem's statement.
   - JS `refinement.js` and the trace evaluators become checkers whose verdicts imply `Sat` (proved or certificate-checked).
5. **Probabilistic layer.** `Dist` denotes a PMF, and a model with distributions denotes an MDP (its schedulers being the choices of 1 and 3).
   - *Done when:* a metric claim's statement is a Lean `Prop` about the induced measure. PRNG-as-i.i.d. is an explicit assumption entity on every metric result. A fidelity claim (class 8) states an error bound between that measure and recorded observations through `obs`.

## 7. Predictions about other teams' conclusions

- **"Termination and determinism are proved for the engine."** Others will take this at face value. It is format 1 only, and the determinism theorems are trivial. The meaningful statement (runs of the nondeterministic model) is not in the semantics.
- **Lean–Rust differential agreement as validation.** Testers will count it as independent validation. The Lean definition mirrors Rust by design (F8), so agreement shows two copies match, not that either is correct.
- **"Semantics is in Lean" by line count.** Architecture reviewers will conclude this from about 12.7k lines of Lean. The mapping spec → semantics (`sim-input.js`), the claim semantics (`claims.js`, `refinement.js`, `metric-claims.js`) and a second step implementation (`replay.js`, used for conformance) are JS.
- **Coverage of `prove`.** Verification reviewers may assume it covers resources, instances and timers (format 2). It cannot decode them.
- **"Exhaustive interleavings."** The explorer's equal-time tie orders will be read as exhaustive interleavings. Ordering of behaviors within a step (F4) and payload or time variation (F5) are not explored.
- **Integrity reasoning.** Integrity will likely be underrated as "just lint". `Integrity.lean` is the most rigorous denotational component and should become the template for the claim language. Its gap is that JS builds `Facts`.
- **Statistical claims.** Statistics-minded reviewers may accept the binomial-test claims as sound. The probability space they quantify over is never defined (F10).

## Cross-challenge

### C1. Rewrite or evolve? A partial concession, with one point that cannot be dropped

I concede the wording. Most of the code base evolves. What has to be rewritten is narrow: the **value domain** and the **status of the definition** (the executable step stops being the semantics and becomes one scheduler of it). The relational layer and the search infrastructure are additions. Precisely:

**Survives as-is**, apart from retyping its parameters:
- `Search.lean`: `Gen.Sys`, `search_sound`, `search_counterexample_real`. It is generic in `N`.
- `Integrity.lean` in full.
- `Resource.lean`, which is already over `Nat`.
- `Random.lean` and `Workload.lean`, with Nat time and rational rates.
- The tokenizer and parser of `Expr.lean`, which produce `Ast`.
- The monitor lemmas of `Temporal.lean` (`never_monitor`, `precedes_monitor`, `greplay_nodes`). These are generic in the step record type.
- Hash, Json, the `#guard_msgs` pins, and the `Impl/Refinement.lean` method.

**Survives through a proved correspondence:**
- `V2.step`, as the deterministic scheduler: `step_sound : step env c = committed r c' → Rel c (lbl r) c'`.
- `Explore.successors`, through `choices_complete` (every `Rel` step is some pick).
- `explore_sound` and `tcheck_sound`, re-derived over `Rel` by instantiating `Gen.Sys`.
- The model-checking team's canonical-state quotient, as `abs ∘ step = astep ∘ abs`.
- The `Expr.eval` integer path, through `eval` on the new typed domain. **This survives only if the executable also stops using `Float` for typed values.** See below.

**Discarded:**
- `Semantics.lean` (format 1) and the `Properties.lean` statements about it, unless `lift_agrees` is proved.
- `Lift.lean`, once format 1 is deleted.
- `Value.arr/obj` identity counters (`nid`, `Value.lean:27-28`) and the MIRRORED aliasing rule (`Semantics.lean:504-508`).
- Format-1 `Float` time.
- Guards and effects stored as source strings (`TransitionIn.guard : Option String`, `Format2.lean:87`), replaced by an elaborated `Ast`.

**Is "add a relational Step ⊇ step, delete format 1, migrate" enough?** Only if the new `Step` is stated over a domain other than `Value.num : Float`. Lean's `Float` operations are opaque: `Float.add` and `Float.lt` are `@[extern]` with no logical laws. That leaves two options, and neither works:
- **(i) `Step` over `Float`.** Then no inductive invariant involving arithmetic is provable.
- **(ii) `Step` over `Int`/`ℚ` while `step` still computes in `Float`.** Then the correspondence theorem `step_sound` is itself unprovable, because it needs `Float.add x 1 = ↑(x+1)` for `|x| < 2^53`, which Lean cannot state as a provable fact.

So the domain has to change in the *executable* too. That is a rewrite of `Value`, `Expr.eval` and every function that pattern-matches on `.num`. It is not an addition on top.

**A property provable in my plan and unprovable in the evolve plan.** Take behavior `ctr`:
- variables: `n : u32 = 0`, `L : u32 = 10`;
- transition `inc`: guard `n < L`, effect `set n = n + 1`, emits `inc`;
- scripted `inc` at 0.

The property is the unbounded invariant `∀ c, Reach c → ctr.n ≤ ctr.L`. Its inductive step is `n < L → n + 1 ≤ L`:
- Over `Int`, `omega` proves it.
- Over `Float`, no lemma exists, and `native_decide` can only enumerate a bounded explorer run. Today's explorer state also never closes a cycle, because of `taken` (modelchecking F1).

The model-checking team's k-induction (their change 3) therefore cannot be carried out on this example without the domain change. **Conclusion:** evolve everything except `Value`/`eval`/time-in-format-1/identities. Those are replaced, not wrapped.

### C2. Is F4 a defect or a deliberate semantics?

It is deliberate and documented:
- `docs/semantics.md:11`: "Phase 2 runs the winners' effects, behavior by behavior, on a copy of the configuration".
- `docs/simulation.md:146`: "a later behavior sees the variables **and the state** that an earlier winner already wrote".
- `docs/simulation.md:85`: scenario order "is the order of every per-behavior loop".
- `fireOne` doc comment: "so a later behavior sees it".

So F4 is not a bug against the docs. It is a defect against the objective, for three reasons:
1. **The order belongs to the scenario, not to the system.** Two scenarios of the same spec that list behaviors in different orders give different semantics to the same components. The meaning of `a ‖ b` is therefore not a function of `a` and `b`, so no assume-guarantee rule can be stated.
2. **The docs' own runtime claim contradicts a fixed order.** `docs/semantics.md:82` maps `behavior.transaction {isolation: "serializable"}` to the engine step. Serializability guarantees equivalence to *some* serial order, not a chosen one. A fixed scenario order is therefore an under-approximation of the runtime's behaviors. Safety verdicts computed over it are not sound for implementation conformance (class 7): in the F4 example the runtime may also produce `b.y = 0` when the model says `1`.
3. **Neither the explorer nor the validator varies it or reports it.** `canPick` permutes queue entries only, and `validate.js:402` covers the order of transitions only.

**Minimal change that is commutative and keeps every golden trace:** keep the executable `step` exactly as it is, with scenario order as its scheduler. Define the relation `Rel` to quantify over permutations π of the winners in phase 2. Then:
- The goldens are unchanged, because they are the run with π = scenario order.
- `step_sound` holds with π = id.
- The set of runs is invariant under reordering `behaviors`, which is commutativity of `‖` up to equality of run sets, modulo seq renaming (equal-time emitted entries are already permuted by `canPick`).
- The explorer gains a pick for π. A static independence check (no phase-2 expression of one winner reads `<b>.x` or `<b>.state` of another winner) gives partial-order reduction, so the n! blow-up appears only where cross reads exist.

**Cleaner but golden-breaking alternative:** snapshot semantics for cross-behavior reads in phase 2 (`resolve [b, name]` with `b ≠ self` reads `cur`). This changes exactly the goldens that contain a phase-2 cross read, which a lint can enumerate in advance. I recommend the permutation relation first, because it changes nothing observable. Snapshot semantics can come later, as a spec-level decision.

### C3. The first foundational milestone: (a) typed core and relation

I choose (a), and I take the part of (b) that binds claims to statements into it. The argument is about what can be stated, and what can be trusted, without what.

**What cannot be *stated* without (a):**

| Class | Statement | What it needs |
|---|---|---|
| Safety under assumptions | `∀ e ∈ EnvA, ∀ c, Reach (⟦M⟧ ‖ e) c → φ c` | `⟦·⟧`, `‖`, `Env`, `Reach` over `Rel` |
| Liveness | `∀ tr ∈ Runs ⟦M⟧, Fair tr → ◇P tr` | infinite runs of `Rel` |
| Refinement | `obs '' Traces ⟦I⟧ ⊆ Traces ⟦A⟧` | `Traces`, `obs` |
| Assume-guarantee | the AG rule | `‖` and contracts as trace pairs |

None of these has a term in today's Lean to write the statement with.

**Why (b)'s statement binding is blocked by (a), not the reverse.** The lean-theorem team's fix (L1: `isDefEq(thm.type, template(claim))`) needs a template that mentions *the spec*. Today no Lean term denotes a spec's behavior: the map spec → engine input is JS `sim-input.js` (F1). A template can only mention a JS-produced engine input, which is exactly the projection gap of L5. Statement binding of a safety claim is therefore literally inexpressible until `⟦·⟧ : Model → Core` exists in Lean, and that is part of (a). Templates written now against `runInput`/`Value` would be rewritten when the domain changes (C1).

**Why (c) comes after (a).** Canonicalisation is a quotient of the configuration type plus a bisimulation `abs ∘ step = astep ∘ abs`. (a) removes `nid` identities and changes `Value`, so roughly half of (c)'s work (renaming identities) disappears, and the bisimulation proof would be redone against the new `step`. Doing (c) first proves a theorem about a type that is about to be deleted. (c) is what makes (a)'s unbounded verdicts reachable: fixpoint `holds`, k-induction and lasso search for liveness. It is the second milestone, not the first.

**What depends on nothing and should ship immediately as hygiene, not as a foundational milestone:**
- (b)'s provenance hashes;
- the `stale` status;
- skip-aware evidence;
- refusing `opaque` constants in `about`.

These prevent false greens today and are not invalidated by (a). They do not give any guarantee class an object to stand on.

**Completion criterion for milestone (a):**
- `Core`, `Rel` (with the winner permutation of C2), and `⟦·⟧ : Model → Core` exist in Lean, with no `Float` in `Core`.
- `step_sound` and `choices_complete` are proved.
- `explore_sound` is re-derived through `Gen.Sys` over `Rel`.
- The `ctr` invariant of C1 is proved without a bound.
- The F4 example gives one verdict for both listings.
- `sim-input.js` is deleted.
