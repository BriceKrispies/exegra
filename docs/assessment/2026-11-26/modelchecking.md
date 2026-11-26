# Model checking and transition systems: assessment

Scope: formal/Exegra/{Explore,Search,Prove,Temporal,Semantics}.lean, Format2.lean (exploration status only), tools/prove.js, src/core/proof-export.js, cli/commands.js `prove`, src/core/claims.js (trace methods), docs/simulation.md, docs/verification.md, docs/claims-and-evidence.md. Lean could not be run. Every conclusion below comes from reading the source. "DEMONSTRATED" means I traced the counterexample through the code by hand, not by running it.

## 1. Verdict

The bounded explorer can be evolved. The search kernel itself (layered BFS, `explore_sound`, `explore_counterexample_real`, the generic `Gen.search` and the monitor-product `tcheck_sound`) is honest, carefully stated and fully proved. Three things are wrong around it:

- **The explored state type is unusable for unbounded reasoning.** It contains monotone counters and history (`taken`, `seq`, `nid`, `attempts` order, object identities). The state graph is therefore acyclic and layered by depth, so no fixpoint, cycle, lasso or inductive argument is possible on it.
- **The claim-status pipeline ignores the explorer.** A trace claim's green `verified` comes from one deterministic run plus "negatives" (mutation testing). The JS and Lean temporal semantics also differ.
- **There is no liveness foundation.** "eventually" is a property of the final configuration of finite, possibly truncated runs, with no fairness.

What is needed: keep the kernel, replace the state representation with a canonical quotient, rebuild the status vocabulary on top of the explorer, and add a separate infinite-trace and fairness layer. A full rewrite is not needed.

## 2. Fundamental limitations

**F1. The state includes history counters, so every state space is a DAG layered by depth. No fixpoint, no reduction, no unbounded proof.** Severity: BLOCKS-OBJECTIVE (unbounded safety, liveness). Status: ARGUED.
- `State := {mask, cfg : Config}` (Explore.lean ~L207) derives `DecidableEq` over all of `Config` (Semantics.lean L404-418): `seq`, `nid`, `attempts`, `delayedBy` and `taken`. Every committed step sets `taken := c.taken + 1` (Semantics.lean `stepHead`), so every state at BFS layer d has `taken = d`, and two states at different depths are never equal.
- The visited set therefore never closes a cycle. An empty frontier happens only when every run quiesces or fails.
- Worse, `attempts := (ev, n) :: c.attempts.filter (·.1 != ev)` records delivery order. Delivering a then b gives `[(b,1),(a,1)]`; b then a gives `[(a,1),(b,1)]`. Commuting interleavings never merge.
- Counterexample: n independent clients, each consuming one scripted event at t=0. The semantic state space has 2^n states. The explorer visits one state per ordered prefix (Σ_k n!/(n-k)!): for n=8 that is about 109,600 states against 256.
- Fresh object identities (`Value.arr i`, `Value.obj i`, compared in `Value.beq`) and `seq` numbers on pending entries split states the same way.
- Consequence: any k-induction or IC3 built on this `State` cannot work. A canonical (identity-renamed, counter-free) quotient with a bisimulation proof is a prerequisite.

**F2. Bounded `holds` for invariants is not separated from fixpoint `holds`, and the bound is the scenario's truncation.** Severity: LIMITS. Status: DEMONSTRATED.
- `Explore.bfs` returns `.holds` both for an empty frontier and for a non-empty frontier at depth 0 (`| 0, _ :: _, V => .holds V.size`).
- `Gen.search` (Search.lean L137) returns `.incomplete` in that case. Two conventions in one codebase.
- The default bound is `stepBound(maxSteps)` (default 1000). `prove` caps a larger `--bound` and says (tools/prove.js note) "the most a run of this scenario takes". That is true only because `maxSteps` truncates runs. It is not because the system stops.
- Counterexample: behavior `ctr` with variable `n = 0` and transition `tick` (`n := n + 1`, emits `tick`), scripted `tick` at t=0, default `maxSteps`. The claim `ctr.n <= 1000` gets "Verified by Lean for all 1001 configurations reachable within 1000 steps". Step 1001 violates it. The output has no flag saying that runs were cut off non-quiescent.

**F3. In claim status, `verified` for trace claims means "one run passed, and each declared negative failed".** Severity: BLOCKS-OBJECTIVE (it blurs "passing test" with "verified"). Status: DEMONSTRATED.
- `evaluateTraceClaim` (claims.js L1005-1124) runs `runScenarioOnce` per listed scenario. That is a single deterministic run with the engine's delivery order and one fault set.
- It returns `verified` when the trace holds and every negative violates the claim (L1104-1124).
- Negatives are a vacuity or mutation heuristic. They show the check is sensitive. They add nothing to the positive conclusion, and any fault that breaks the claim by any route counts.
- The explorer is never consulted: `lean-exhaustive` results go only to CLI output (`proveScenario` is called only from cli/commands.js L1109).
- Counterexample: tests/fixtures/race, claim `racy-store.value == racy-store.writes` on `lost-update-race`. The scripted run passes (docs/simulation.md L246), and `exegra prove` finds a 10-step counterexample. Add a negative whose fault corrupts `writes` (for example an `enable-transition` fault on a faultOnly transition `writes := writes + 5`) and the claim turns green `verified` while Lean holds a real counterexample to it.
- AGENTS.md: "Exegra shows a green verified status only for what it established by checking the model itself". One trace is not "the model".

**F4. Truncated runs count as complete runs. "eventually" judges the configuration at an arbitrary cut point.** Severity: BLOCKS-OBJECTIVE (liveness). Status: DEMONSTRATED.
- `Ended` (Temporal.lean) includes `lim ≤ fin.cfg.taken`. `Form.holdsEnd` accepts an `eventually` whose occurrence was seen and whose `expr` is true at the final node, even when that node ends at the step limit. `Form.unk` flags only the failing cases.
- JS does the same: `traceEventually` evaluates `trace.final`, and step-limit only adds a note (claims.js L1056).
- Counterexample: behavior `blinker` with states off/on and transitions `turn-on` (off→on) and `turn-off` (on→off), both on `tick`, both emitting `tick`. Scripted `tick` at 0. Claim: `eventually {occurs:{transition:"turn-on"}, expr:"blinker.state == 'on'"}`.
  - With `maxSteps: 11`, the run ends at the limit in `on`. Lean `tcheck` says holds ("Verified by Lean over every complete run…"). JS gives `verified` once any negative (drop the first `tick`) violates it.
  - With `maxSteps: 10`, both say incomplete or inconclusive.
  - The verdict depends on the parity of the step limit, for a system that never settles. This is neither finite-trace LTL F (which would be satisfied at step 1 by `turn-on` alone) nor infinite-trace FG. It is a bespoke "occurred, and true at the end" predicate.
- The same applies to `never` and `precedes`: a `never explode` whose `explode` fires at step 1001 "holds on every complete run".
- There is no fairness notion anywhere (grep: none in Explore, Search or Temporal). Infinite runs do not exist in the model.

**F5. JS and Lean disagree on what an occurrence is.** Severity: LIMITS (it violates "Lean is the sole authority"). Status: DEMONSTRATED.
- Lean `Matcher.hit (.event e)` = any `deliver` step of `e` (Temporal.lean L47-49), scripted inputs included.
- JS `traceEventually` drops deliveries whose `source.kind === 'scenario'`, and `precedes` likewise ignores scripted deliveries (claims.js L1077, `traceEventually`).
- Counterexample: `eventually {occurs:{event:"go-a"}}` on `lost-update-race`, where `go-a` is scripted. `exegra prove` reports holds ("Verified by Lean"). The claim evaluator reports inconclusive ("occurs only as the scenario's own scripted input").

**F6. "Every interleaving" means only exactly equal Float times, and "every fault subset" means only all-or-nothing activation.** Severity: LIMITS. Status: DEMONSTRATED.
- `canPick` compares `p.time == h.time` on `Float` (Explore.lean ~L222).
- Shift the race fixture's `go-b` to `at: 0.001`: every entry has a distinct time, there is one path, and the claim holds. An emit with `after: 0.2` at t=0.1 gives 0.30000000000000004, which never ties with a scripted 0.3.
- Faults: the mask picks on or off per fault. An `Occurrence.any` fault acts at every match (Input.lean L70-73).
- Counterexample: a retrying client with a drop fault on `ack` and no occurrence. The explorer covers "every ack dropped" (never completes) and "none dropped". It never covers "only the first ack dropped", where the retry produces the duplicate commit. `never duplicate-commit` holds on all masks.
- docs/simulation.md L341 admits "Nothing covers other inputs or timings". The CLI summary still says "every subset of its faults" without saying that a subset activates a fault at all of its matches.

**F7. Failed steps are silently pruned from the invariant search.** Severity: LIMITS. Status: ARGUED.
- `succOf` returns `none` on `.failed` (Explore.lean ~L229). An interleaving in which a guard or effect errors is a dead end, and `holds` gives no hint that some admitted runs crash. `tcheck` does treat them as complete runs.
- Related: there is no theorem constraining `.incomplete`. An explorer that always answered `incomplete` would satisfy every proved theorem, because the theorems prove partial correctness only.

**F8. The admitted-run relation is self-defined.** Severity: LIMITS. Status: ARGUED.
- `Reachable` is defined from `successors`, the same function the BFS runs. `explore_sound` is therefore internal completeness of the search, which is real and valuable. It says nothing about adequacy. Only `step_mem_successors` (the deterministic run is included) links it to `step`.
- No independent definition of "admissible schedule or fault behavior" exists to prove `successors` complete against.

**F9. `input_decodes` is about a `partial def`.** Severity: MINOR. Status: ARGUED.
- `Json.parse` is built from `partial def`s (Json.lean L32-182), which are logically opaque. `decodesTo inputText input = true` by `native_decide` therefore has content only through the trusted compiler. The explorer theorems are about the embedded term and are unaffected.

**F10. Masks are built eagerly.** Severity: MINOR. Status: ARGUED.
- `masks env = allMasks |faults|` builds all 2^n masks as a strict list before `addAll` checks the cap, so `--max-states` does not protect against 30+ faults.
- Exploration of format-2 inputs is not implemented (WG-4741). `lift_agrees` is `sorry` (Lift.lean L136).

## 3. Overclaims

- **Trace claims.** The `verified` status (claims.js L1124; claims-and-evidence.md L109 "An evaluator checked the model") rests on one trace. The scope text says "not of all possible executions", but the status colour is the same as structural, model-wide verification. It also outranks `exegra prove`, whose counterexamples never change a status.
- **README line 9.** "A trace claim counts as verified only when its declared negative scenarios each violate it" presents a mutation-sensitivity heuristic as if it strengthened the verdict.
- **Prove note.** "The most a run of this scenario takes" (tools/prove.js) hides the fact that `maxSteps` (default 1000) truncates non-terminating systems.
- **Temporal "holds".** "Verified by Lean over every complete run" for temporal claims counts runs cut off at the step limit as complete. The text does say "ending … at the step limit", but "eventually … holds" reads as liveness.
- **Interleavings.** "Every order of delivery of simultaneous events" / "every interleaving" (cli summary, docs) holds only for bit-equal Float times.
- **Fault subsets.** "Every subset of the scenario's faults" does not cover per-occurrence fault behavior.
- **Honest statements, for contrast.** docs/simulation.md L263 and spec L15698 correctly say that unbounded proof (WG-4686) does not exist. `invariants-proved-within-bounds` is correctly `supported` by evidence and not self-verified.

## 4. Preserve

- **`Explore.lean` BFS soundness.** The `Grow`/`BfsInv` layered invariant is exactly the "every state within d steps is visited after d layers" lemma. Global-visited-set BFS is easy to get wrong, and this one is proved. The counterexamples are replayable and proved real.
- **`Search.lean`.** A generic `Sys N` search whose `holds` requires an empty frontier, so it is a genuine fixpoint statement over the whole reachable set. This is the right primitive for unbounded checking once states are finite and canonical.
- **The monitor-product construction in `Temporal.lean`.** `never_monitor`, `precedes_monitor` and `greplay_nodes` tie the monitor to trace semantics. It extends naturally to safety automata and, with acceptance conditions, to Büchi products.
- **The output discipline.** Three-valued results (`holds` / `counterexample` / `incomplete`), axiom pinning with `#guard_msgs`, and `native_decide` trust listed per theorem.
- **The `undecided` / `pending` treatment in `checkTrace`.** An absence in an unfinished run is not a violation.

## 5. Architectural decisions that prevent the objective

1. **Raw `Config` as the model-checking state.** Replace it with a canonical abstract state: machines and pending entries, with `seq` renumbered by order, identities renamed canonically, `attempts` as a sorted map, and `taken` removed. Prove a bisimulation between the abstract and concrete step. Without this there is no fixpoint, no partial-order reduction and no induction.
2. **The step limit as the end of the universe.** Separate "system quiescent", "exploration bound" and "scenario truncation" in every result type. Treat truncation as `incomplete` for invariants too, unless the frontier is empty.
3. **Two independent trace-property evaluators** (JS `claims.js` and Lean `Temporal.lean`) with different matcher semantics. There should be one definition, in Lean, that both `checkTrace` and `prove` call.
4. **Claim status derived from one run plus negatives.** Status should be computed from the strongest available evaluator, with distinct statuses: run-checked, bounded-exhaustive (with its bound and scope), proved-unbounded. Negatives should become a vacuity or sensitivity attribute (as `claim-strength.js` already does), never a promotion to `verified`.
5. **"eventually" as a final-configuration predicate.** Replace it with a real temporal logic. Finite-trace LTLf on quiescent runs for bounded scenarios, and infinite-trace LTL with explicit weak or strong fairness on transitions for liveness, checked by lasso detection on the canonical finite state space.

## 6. Highest-leverage changes, in dependency order

1. **Canonical abstract state with a proved bisimulation.** Done when Lean proves `abs (step c) = astep (abs c)` and an `explore` on abstract states visits 2^n (not about n!) states on the n-independent-clients fixture, checked by a test.
2. **Fixpoint verdict for invariants.** `holds` only on an empty frontier (`Gen.search` semantics), plus a theorem `∀ n, Reachable env n s → inv s`, i.e. unbounded within the scenario's finite input. Done when the `ctr` counterexample (F2) reports `incomplete` and a terminating fixture reports an unbounded `holds` theorem.
3. **Inductive invariants and k-induction (WG-4686).** Accept a user-supplied or strengthened invariant `I` with Lean proof obligations `init → I`, `I ∧ step → I'` and `I → P`, where the explorer supplies counterexamples to induction. Done when one fixture invariant is proved without a bound and `#print axioms` shows standard axioms only.
4. **Unify trace semantics in Lean and rewire claim status.** `checkTrace` calls Lean `TraceHolds`. Status takes the strongest of single-run, bounded-exhaustive or proved, and negatives move to an attribute. Done when F5's `go-a` example agrees across both paths, and the race claim cannot be `verified` while `prove` has a counterexample (a regression test).
5. **Liveness with fairness.** Add infinite-run semantics, lasso search over the canonical state space, and fairness declarations as explicit assumptions in the spec. Done when the blinker (F4) reports "violated: lasso off→on→off" for `FG on`, and "holds under weak fairness of `turn-on`" for `GF on`.

## 7. Predictions about other teams

- **Lean or formal team.** They will likely conclude that "the explorer is proved sound, no sorry", and they will be right. Expect some to read `explore_sound` as covering "all behaviors", missing that `Reachable` is defined from the explorer's own `successors` (F8). Expect them to miss the history fields in `State` (F1), because they show up only as a performance and unboundedness issue, not a proof gap.
- **Claims and evidence team.** They may judge the negatives rule a sound strengthening ("a check that cannot fail is not verified"). It is a vacuity filter. It does not make the claim more true (F3).
- **Docs-oriented reviewers.** They will credit the many honest scope sentences, and rightly. But they may miss that the CLI and status colours still say "verified" and "every interleaving / every subset" without the Float-tie and all-or-nothing-fault caveats (F6).
- **Rust or differential team.** They may treat Lean/Rust agreement as evidence for the explorer. The Rust explorer (WG-4650) does not exist yet, and agreement would not address F1, F4 or F5 anyway.
- **Liveness and fairness.** Some team will likely say liveness is "partially supported via eventually". There is no infinite-trace semantics and no fairness. Class 4 is absent, not partial.

## Cross-challenge

### C1. Is a canonical quotient of the current `Config` well-defined?

**Yes, with stated restrictions, and with a precise list of what must not be erased.**

Here is what the semantics can observe, read from the source.

- **Identities.** Guards and claims never see them. `Value.eqv` ignores identities and field order (Value.lean L149-170; the header at L11-14 says "no identity is observable", WG-4902). Resolution (`resolve`, `claimResolve`) only returns values. The MIRRORED comment on `step` (Semantics.lean L506-508, "guards see `a == b` true") is stale: it predates WG-4902 and contradicts Value.lean. Identities and `nid` can be erased or renamed. Keep object *field order*: it is observable, because it decides which error an emit payload reports (Value.lean L8-10).
- **`seq`.** Unobservable except in two places. `insertPending` orders by time only (L97-104), so the order of the queue list already carries the tie order. `seq` is also the key of `delayedBy`. The canonical form renumbers pending entries 0..n-1 in list order, remaps the `delayedBy` keys, and drops `delayedBy` rows whose entry is no longer pending. Without that last step, stale keys collide after renumbering.
- **`attempts`.** Semantic, not history. `faultMatches` reads it through `attemptOf` (L436-445). Its keys are unique (`filter` before `cons`), so the canonical form is the list sorted by key.
- **`taken`.** Observable only by step-limit truncation (`advance`, Temporal `move`: `lim ≤ taken`) and by the `Step.index` records. Neither `Matcher.hit` nor `claimInv` reads it. Explore's `succOf` does not read it either. So `taken` can be dropped for the limit-free relation, which is the one `explore` uses. It cannot be dropped for `tcheck` as defined today, where truncation is part of the run semantics. That is another reason to remove truncation from run semantics (F4).
- **Float.** Merging states with bit-identical floats is trivially sound. The canonicaliser never merges different floats. `0` and `-0` stay distinct, which is correct: `1/x` tells them apart.
- **Guards parsed from strings.** They are part of `Env`, not `Config`. Parsing is a pure function of `Env`, so it does not affect the quotient.

**Proposition (ARGUED, proof sketch).** Let κ be the canonical form above. Then κ c₁ = κ c₂ implies that `step env c₁` and `step env c₂` have the same constructor. Their records agree up to `index`, `seq` and identities, and κ is equal on their results. `claimInv e` and `Matcher.hit` agree on both sides.

Proof sketch:
- Every read in `stepHead`, `choose`, `fireAll`, `resolve` and `eval` goes through one of: values (compared by `eqv`), the order of the pending list, `lookupNat attempts`, `lookupSeq delayedBy head.seq` under the consistent remapping, or `time`.
- Fresh identities come from `nid` and are only ever compared by `eqv`.

**Counterexamples showing what a naive canonicaliser would get wrong.**

1. **Erasing `attempts` as "history" (DEMONSTRATED by reading).**
   - Model: behavior `m` in `s0` has a transition only from `s1` on `e`. Fault `drop-event e` with `occurrence: 2`.
   - Config A: `e` was delivered once and ignored, so `attempts = [(e,1)]`. Config B: the same machines and queue, `attempts = []`.
   - Machines and queue are identical in A and B. After `go` moves `m` to `s1`, the next `e` is dropped in A and fires the transition in B.
   - `never {transition: t}` tells them apart.
2. **Erasing `delayedBy`.** A delay fault without an occurrence delays each entry at most once (`delayOf?`). An entry that was already delayed and an identical fresh one behave differently.
3. **Erasing `taken` under `tcheck`.** Two configurations at depths `lim-1` and `lim` are merged, but only one of them may take another step.

**Before or after a typed core?** I partly concede. The quotient is well-defined *now*, and it unblocks empty-frontier fixpoints, which are exact and decidable today. Float does not obstruct an equality-based quotient. Float does obstruct what comes next: inductive invariants over arithmetic, non-Zeno arguments and symbolic reasoning all need algebraic laws, and Float has none in the kernel.

Recommendation: build the typed core's `Conf` canonical by construction (no identities, no `seq` or `taken`, attempts as a finite map, positional queue). Build the format-1 κ only as a cheap stop-gap, used as a specification for that design, and do not invest in proving it if format 1 is to be deleted. Order: typed-core `Conf` (canonical by construction) → fixpoint search → induction.

### C2. Behavior order within a step versus `explore_sound`

The theorem is not unsound: it is a true statement about `Reachable env`, which `successors` defines. It is **unsound as a statement about the system** whenever the intended system lets concurrent components react to one event in any order. This is exactly F8, an adequacy gap. The admitted-run relation fixes one sequential composition: phase 1 reads the snapshot `cur`, while phase 2 effects read `s.next` sequentially in scenario order (`runEffects`, `fireAll`, Semantics.lean L324-381).

foundations' F4 example is a concrete instance:
- Behavior `a`: `set x = 1` on `e`. Behavior `b`: `set y = a.x` on `e`.
- Invariant `b.y == 0`: "Verified by Lean for all N configurations" with the listing `[b, a]`, a counterexample with `[a, b]`.
- Same components, same event. The CLI's "every order of delivery of simultaneous events" invites reading this as full interleaving.

Both listings are reachable in the system. Only one is in `Reachable`, so `explore_sound`'s guarantee does not transfer to the system.

The cheapest fix makes phase 2 commutative instead of exploring k! orders:
- A behavior reads its *own* machine from `s.next`, which keeps sequential effects within one transition, and reads other machines from `cur`, the snapshot.
- Effects write only the firing behavior's own variables and state (`runEffects` sets `s.next.machine? bid`), so there are no write-write conflicts.
- The only remaining order dependence is the insertion order of equal-time emits. The explorer already permutes those entries (`canPick`).
- Completion criterion: a Lean theorem `fireAll_perm : ws ~ ws' → fireAll ... ws s ≈ fireAll ... ws' s`, up to the queue order among equal-time entries, plus `explore` giving the same verdict for both listings of F4.

The alternative is to add the winner permutation as an explorer choice, with a `choices_complete` theorem against a relational specification.

### C3. Minimal Lean definitions for safety (unbounded) and liveness (under fairness)

**What can be stated over today's `step`:** all of the definitions below. `step` is total, so a `Prop` relation follows from it (`Succ` already exists).

**What can be proved today:**
- Closed-set (fixpoint) certificates, by enumeration plus `native_decide`. This needs `taken` out of the state (C1), otherwise only terminating scenarios close.
- Lasso refutations.

**What cannot be proved today:**
- Preservation steps of inductive invariants about arithmetic. Float is opaque, and guard strings are parsed inside `step`, so every lemma about a guard is `native_decide` on one instance.
- Non-Zeno arguments over Float time.

Liveness also needs **entry identity** for fairness: "an entry that stays pending at the head time is eventually delivered". An unfair explorer run can starve a time-0 entry forever by always picking the blinker's re-emitted `tick` (k=0) at t=0. So canonicalisation must keep labels positional (the pick index), so that entries can be tracked through the relation.

```lean
namespace Exegra.LTS

structure LTS (S L : Type) where
  init : S → Prop
  step : S → L → S → Prop

/-- Label of a scenario step: the pick and the record (event, fired transitions). -/
structure Label where
  pick : Nat
  rec  : Step

def scenarioLTS (env : Env) : LTS State Label        -- from succOf; no step limit
def stutter (M : LTS S L) (term : S → Prop) : LTS S (Option L)   -- quiescent/failed states loop

/-- Unbounded safety. -/
inductive Reach (M : LTS S L) : S → Prop
def Safe (M : LTS S L) (P : S → Prop) : Prop := ∀ s, Reach M s → P s
def Inductive (M : LTS S L) (I : S → Prop) : Prop :=
  (∀ s, M.init s → I s) ∧ ∀ s l t, I s → M.step s l t → I t
theorem safe_of_inductive {M : LTS S L} {I P : S → Prop} :
  Inductive M I → (∀ s, I s → P s) → Safe M P
def KInductive (M : LTS S L) (P : S → Prop) (k : Nat) : Prop
theorem safe_of_kInductive {M : LTS S L} {P : S → Prop} {k : Nat} :
  KInductive M P k → Safe M P
/-- Fixpoint certificate the explorer can produce and native_decide can check. -/
def Closed (M : LTS S L) (V : List S) : Prop :=
  (∀ s, M.init s → s ∈ V) ∧ ∀ s ∈ V, ∀ l t, M.step s l t → t ∈ V
theorem closed_inductive {M : LTS S L} {V : List S} : Closed M V → Inductive M (· ∈ V)
theorem successors_complete (env : Env) (s t : State) (l : Label) :
  (scenarioLTS env).step s l t → (l.pick, t) ∈ successors env s

/-- Canonical quotient (C1). -/
def canon : Config → Config
theorem step_canon (env : Env) (c : Config) :
  StepResult.map canon (step env (canon c)) ≈ StepResult.map canon (step env c)

/-- Infinite runs, LTL, fairness. -/
structure Run (M : LTS S L) where
  st : Nat → S
  lb : Nat → L
  start : M.init (st 0)
  succ : ∀ n, M.step (st n) (lb n) (st (n+1))
inductive LTL (AP : Type) | atom (p : AP) | not (φ : LTL AP) | and (φ ψ : LTL AP)
  | next (φ : LTL AP) | until (φ ψ : LTL AP)
def LTL.sat (val : S → AP → Prop) (σ : Nat → S) : LTL AP → Prop
def WeakFair (r : Run M) (en : S → E → Prop) (tk : L → E → Prop) : Prop :=
  ∀ e, (∃ N, ∀ n ≥ N, en (r.st n) e) → ∀ N, ∃ n ≥ N, tk (r.lb n) e
def NonZeno (r : Run M) (time : S → T) [LT T] : Prop   -- needs Nat/ℚ time to be provable
def LiveUnder (M : LTS S L) (fair : Run M → Prop) (val) (φ : LTL AP) : Prop :=
  ∀ r : Run M, fair r → LTL.sat val r.st φ
structure Lasso (M : LTS S L) where
  stem : List (L × S)
  loop : List (L × S)    -- well-formed: a cycle of M
theorem lasso_refutes {M : LTS S L} (x : Lasso M) (h : ¬ LTL.sat val x.toRun.st φ)
  (hf : fair x.toRun) : ¬ LiveUnder M fair val φ
end Exegra.LTS
```

The first three to add are `Reach`/`Safe`/`Inductive`/`safe_of_inductive`, `Closed` with `closed_inductive`, and `successors_complete`. Together they turn the existing BFS into an unbounded safety prover for finite canonical state spaces. `Run`, `WeakFair` and `Lasso` come next. Proving `NonZeno`, and preservation lemmas for arithmetic, waits for the typed, Float-free core.
