# Adversarial review of M1 (commits fd3f8d9, 42e7240)

Scope: docs/foundations.md sections 3-4; formal/Exegra/Core/{LTS,Calculus,Examples}.lean; their use by
M2 (Format2.lean step_sound), M4 (Search.lean Gen.search_sound), M5, M6, M7. Reasoned from source; Lean
was not run. All proofs look correct as written; the findings concern what they claim and how they are shaped.

## Summary

| # | Finding | Severity |
|---|---------|----------|
| 1 | k-induction soundness is an M1 deliverable and is absent | MUST-FIX (or remove from M1 text) |
| 2 | Calculus state: silent out-of-range reads (0) and writes (no-op) | MUST-FIX before M2 copies it |
| 3 | Snapshot claim rests on `exec_swap` (2 distinct updates); duplicates are order-dependent and unrejected | MUST-FIX |
| 4 | No bridge from `Gen.search` / `Enum` to `LTS.Invariant`; `Enum` lacks soundness, so no refutation | SHOULD-FIX (blocks M4) |
| 5 | "Relative completeness" names a trivial semantic fact | SHOULD-FIX (wording) |
| 6 | Vacuity and deadlock not flagged; no error-state convention (the "failed steps dropped" defect returns) | SHOULD-FIX |
| 7 | Labels: `Prog.lts` labels are non-unique Strings; no τ, no alphabet | SHOULD-FIX before M5/M6 |
| 8 | "typed" calculus claim; spec.jsonc integration, demo and limitations (M1's own completion rules) missing | SHOULD-FIX |
| 9 | `bounded_not_unbounded` correct but only an existential; missing monotonicity / diameter lemmas | NOTE |
| 10 | Int calculus vs Float interpreter: M2 `step_sound` cannot hold against Format2 as is | NOTE (M2 planning) |
| 11 | Axiom guards cover 5 of ~15 theorems; exact-set pins are brittle | NOTE |

## 1. k-induction is missing (MUST-FIX)

foundations.md M1: "LTS, reachability, invariants, inductive invariants, `safe_of_inductive`, k-induction
soundness, closed-set certificates". `grep -rn k-induction formal/` finds nothing. The commit message does not
claim it (honest), but the milestone text lists it and M4 ("k-induction in the explorer") depends on it. Either
add it or move it explicitly to M4. Statement:

```lean
/-- `l` is a path: consecutive states are related by some step. -/
def PathL (M : LTS σ α) : List σ → Prop
  | [] | [_] => True
  | s :: t :: r => (∃ a, M.step s a t) ∧ PathL M (t :: r)

theorem invariant_of_k_induction (M : LTS σ α) (P : σ → Prop) (k : Nat)
    (hbase : M.BoundedInvariant k P)
    (hstep : ∀ (l : List σ) (t : σ), l.length = k + 1 → M.PathL (l ++ [t]) →
      (∀ s ∈ l, P s) → P t) :
    M.Invariant P
```
(k = 0 recovers 1-induction relative to P. Proof by strong induction on the depth from `reachIn_of_reach`,
which needs a path-producing variant of `Reach`: `reach_path : M.Reach t → ∃ l s, M.init s ∧ M.PathL (s :: l) ∧ (s::l).getLast? = some t`.)
Also add the adversarial example: a property that is k-inductive for some k but not 1-inductive.

## 2. Out-of-range semantics in the calculus (MUST-FIX before M2 inherits it)

`getAt` returns 0 past the end and `setAt` ignores writes past the end. Concrete trap: change `counter` to
`init := []`. Then `inc` is a no-op, and `Invariant (fun s => getAt s 0 ≤ L)` and even
`Invariant (fun s => getAt s 0 = 0)` are provable: a "counter" that never counts is certified safe. This is the
totality hack the assessment condemns (errors become benign values). The Examples happen to be safe only because
the inductive invariants pin `s = [n]`. Note also `getAt s 0 ≤ L` is true of `[]`, so the property itself is
satisfied by ill-shaped states.

Fix (preferred): index everything by the number of variables, so ill-formed programs are unrepresentable.
```lean
inductive IExpr (n : Nat) | lit (v : Int) | var (i : Fin n) | add (a b : IExpr n) | sub (a b : IExpr n)
structure Cmd (n : Nat) where
  label  : String
  guard  : BExpr n
  update : Fin n → Option (IExpr n)      -- a partial function: no duplicates, no order
def Cmd.exec (c : Cmd n) (s : Vector Int n) : Vector Int n :=
  Vector.ofFn fun i => match c.update i with | some e => e.eval s | none => s[i]
```
Snapshot reads then hold by definition (`exec_get : (c.exec s)[i] = ((c.update i).map (·.eval s)).getD s[i]`,
proved by `simp`). `Vector Int n` has `DecidableEq`, so `checkClosed`/`decide` still works (kernel cost is higher
than `List`; measure on `mod3`).

Fallback (keep `List Int`): a decidable `Prog.WF` (every variable index in guards, right-hand sides and
left-hand sides `< p.init.length`; update targets `Nodup`), the theorem
`Prog.length_invariant : p.lts.Invariant (fun s => s.length = p.init.length)`, and every calculus theorem
taking `p.WF`. Weaker: nothing stops a later lemma forgetting the hypothesis.

## 3. Snapshot reads: `exec_swap` is not a basis for the claim (MUST-FIX)

Reads are snapshot by construction (`u.2.eval s` reads the pre-state); what `exec_swap` shows is that *writes*
commute, for exactly two updates to distinct variables. Gaps:
* Duplicates: `[(0,e),(0,f)]` executes to `f`'s value, `[(0,f),(0,e)]` to `e`'s. Order-dependent, accepted
  silently, last-write-wins. The docstring hedges ("when they assign distinct variables") but no predicate or
  type rejects it. M2's `[a, b]`/`[b, a]` criterion is exactly this situation.
* More than two updates: not covered; needs a permutation theorem.
* The guard and label arguments of `exec_swap` are irrelevant (fine, but signals the statement is about `foldl`).

If the `List` representation is kept, the statements that actually justify the claim are:
```lean
theorem Cmd.exec_perm (c : Cmd) (u : List (Nat × IExpr)) (hnd : (c.updates.map Prod.fst).Nodup)
    (hp : c.updates.Perm u) (s : List Int) : c.exec s = { c with updates := u }.exec s
theorem Cmd.exec_get_upd (c : Cmd) (s : List Int) (i : Nat) (e : IExpr)
    (hnd : (c.updates.map Prod.fst).Nodup) (hi : i < s.length) (he : (i, e) ∈ c.updates) :
    getAt (c.exec s) i = e.eval s
theorem Cmd.exec_get_other (c : Cmd) (s : List Int) (i : Nat) (hn : i ∉ c.updates.map Prod.fst) :
    getAt (c.exec s) i = getAt s i
```
With the `Fin n → Option` representation of finding 2 all three are definitional and duplicates impossible.

## 4. Bridge to `Gen.search` (SHOULD-FIX; M4 blocked without it)

`Enum.succ_complete` (every step's target is listed) is the right obligation for *holds*: it is what
`Gen.search_sound` needs. It is not enough for *counterexamples*: `Enum` may list junk successors or inits, so a
search violation over an `Enum` does not refute `Invariant`. Add soundness (separately, so certificates stay
cheap) and the bridge:

```lean
namespace Exegra.Core.LTS
/-- `S` over-approximates `M`. -/
structure Covers (S : Gen.Sys σ) (M : LTS σ α) : Prop where
  init : ∀ s, M.init s → s ∈ S.init
  step : ∀ s a t, M.step s a t → ∃ k, S.next s k = some t
/-- `S` under-approximates `M`. -/
structure Within (S : Gen.Sys σ) (M : LTS σ α) : Prop where
  init : ∀ s, s ∈ S.init → M.init s
  step : ∀ s k t, S.next s k = some t → ∃ a, M.step s a t

theorem invariant_of_search [DecidableEq σ] [Hashable σ] {M : LTS σ α} {S : Gen.Sys σ}
    (hc : Covers S M) {ok : σ → Bool} {bound cap n : Nat}
    (h : Gen.search S ok bound cap = .holds n) : M.Invariant (fun s => ok s = true)

theorem not_invariant_of_search [DecidableEq σ] [Hashable σ] {M : LTS σ α} {S : Gen.Sys σ}
    (hw : Within S M) {ok : σ → Bool} {bound cap : Nat} {p : Gen.Path σ}
    (h : Gen.search S ok bound cap = .counterexample p) :
    ∃ s, M.ReachIn bound s ∧ ok s = false        -- hence ¬ M.Invariant (ok · = true)

def Enum.toSys (E : Enum M) : Gen.Sys σ :=
  { init := E.inits, width := fun s => (E.succ s).length, next := fun s k => (E.succ s)[k]?,
    lt := by intro s k t h; exact (List.getElem?_eq_some_iff.mp h).1 }
theorem Enum.toSys_covers (E : Enum M) : Covers E.toSys M
end Exegra.Core.LTS
```
(Proof of `invariant_of_search`: `Reach M s → ∃ m, Gen.Reach S m s` by induction using `Covers`, then
`search_sound`.) Also needed: `reachIn_mono : m ≤ n → M.ReachIn m s → M.ReachIn n s` to match depths.

## 5. "Relative completeness" (SHOULD-FIX, wording)

`invariant_iff_inductive_strengthening` is the standard semantic fact with `I := Reach`; its proof is one line.
Relative completeness in the Cook sense is completeness *relative to an assertion language* whose
expressiveness is the substantive assumption. Here the assertion language is all of `σ → Prop`, so the
expressiveness premise is free and the theorem says nothing about whether a *checkable* strengthening exists.
The docstring's caveat ("finding one is the hard part") is honest; the label "complete relative to the logic" is
not — there is no logic. Rename to `invariant_iff_exists_inductive` / "semantic completeness of inductive
invariants", and state in the docs that inductive invariants expressible as `BExpr` (linear guards) are *not*
complete for `Prog`. Optionally prove that incompleteness with a small example, which would be the meaningful
counterpart.

## 6. Vacuity, deadlock and error states (SHOULD-FIX)

* An `LTS` with `init := fun _ => False` satisfies every `Invariant`; nothing flags it. `Prog.lts` always has
  exactly one initial state, so the Examples are not vacuous, but the generic results will be applied to M2/M6
  systems (e.g. a composition whose synchronisation blocks everything, or an `init` predicate built from
  contradictory assumptions). Exegra's trace claims already treat vacuity as inconclusive; the Lean side should
  give the claim layer something to check. Add
  ```lean
  def NonVacuous (M : LTS σ α) : Prop := ∃ s, M.init s
  def Deadlock (M : LTS σ α) (s : σ) : Prop := ∀ a t, ¬ M.step s a t
  ```
  and require the claim layer (M3 status lattice) to record `NonVacuous` (and, for safety claims, a reachable
  witness or a deadlock-freedom check) before showing an invariant as established. Do not put the side condition
  into `safe_of_inductive` itself; it is a property of the claim, not of soundness.
* Format2's `step` returns `.failed`/`.stopped`/`.idle`. If M2 models a failed step as "no transition", every
  invariant becomes true past the failure: the "failed steps dropped" defect in the capability matrix returns
  in the foundation. Fix the convention now: failures step to an explicit error state (`σ ⊕ Err` or a `bad`
  predicate), and an Exegra safety claim is `Invariant (fun s => ¬ bad s ∧ P s)`.

## 7. Labels and the LTS shape for M5-M7 (SHOULD-FIX before M5/M6)

The `LTS σ α` with `Prop` init/step is the right core object; nothing here must be redone. But:
* `Prog.lts` labels steps by `c.label : String`, and labels need not be distinct. Per-command weak/strong
  fairness (M5) needs command identity: label by `Fin p.cmds.length` (keep the String for display) or require
  distinct labels in `Prog.WF`.
* M7 stuttering simulation and M6 hiding need internal steps: decide now on `LTS σ (Option α)` (τ = `none`) or a
  separate `internal : α → Prop`, and define `Enabled M a s := ∃ t, M.step s a t`, runs (`Nat → σ × α` with
  steps), maximal finite runs vs deadlock, and traces/observations — section 3 item 1 lists these as part of the
  foundation, but none exists yet; the capability matrix should not imply otherwise.
* M6: alphabets are not part of `LTS`. Synchronised product needs them; carry them in a component structure
  (`structure Component (σ α) extends LTS σ α where inp out : α → Prop; disjoint : ∀ a, ¬(inp a ∧ out a)`)
  rather than changing `LTS`. Not blocking.

## 8. Claims vs deliverables (SHOULD-FIX)

* M1 promises a "minimal *typed* guarded-command calculus". It is single-sorted (only `Int` variables; the
  `IExpr`/`BExpr` split is the only typing, and variables are untyped indices). Either say "single-sorted" or
  type it (finding 2 makes contexts explicit).
* foundations.md section 4 says every milestone includes "an executable demonstration, integration with
  specs/exegra/spec.jsonc, documented limitations". `specs/exegra/spec.jsonc` has no entry for `Exegra.Core`
  (no lean-theorem claim about `safe_of_inductive`, `counter_le`, ...), and CLAUDE.md says every change starts
  there. No limitations are written down (the out-of-range and duplicate-update semantics in particular).
* Commit fd3f8d9 says "relative completeness" (see 5) and "snapshot reads" (see 3); otherwise it matches what is
  proved and does not claim k-induction.
* The three listed completion criteria are met: `counter_le` (no bound, every `L ≥ 0`),
  `ne_neg_one_not_inductive` + `ne_neg_one_invariant`, `mod3_in_range` by `decide` on `checkClosed`.
  Caveat on the second: the criterion says the non-inductive invariant "is not accepted without strengthening";
  what is proved is that it is not inductive. There is no checker that could "accept" anything; fine, but the
  wording overstates.

## 9. `bounded_not_unbounded` (NOTE)

Correctly characterised: `ReachIn 5` is "at most 5 steps" (the `init` constructor is available at every
index), `n ≤ 5` holds there and fails at `[6]`. The LTS header's "No single depth suffices in general" is an
existential over systems and is witnessed only for depth 5; the general form is a one-liner and should replace
it: `theorem no_depth_suffices (k : Nat) : unbounded.lts.BoundedInvariant k (fun s => getAt s 0 ≤ k) ∧ ¬ unbounded.lts.Invariant (fun s => getAt s 0 ≤ k)`.
The positive counterpart M4 needs is missing: for a system whose reachable set has at most `d` elements,
`BoundedInvariant d P → Invariant P` (diameter bound), plus `reachIn_mono`.

## 10. Int calculus vs the format-2 interpreter (NOTE, M2 planning)

`Exegra.Value.num` is `Float`, and Format2's step is a deterministic, seeded function with failure results.
`step_sound` relating it to an Int/Rat calculus is false as the interpreter stands; M2 must either move the
interpreter's numbers to `Int`/`Rat` first or state `step_sound` modulo an explicit numeric abstraction. Also,
the M1 expression language has no division/modulo, so its "total denotation" sidesteps the hard case; M2 must not
adopt Lean's `x / 0 = 0` silently (route it to the error state of finding 6).

## 11. Axiom guards (NOTE)

`#print axioms` guards cover `safe_of_inductive`, `checkClosed_sound`, `counter_le`, `bounded_not_unbounded`,
`mod3_in_range`; not `invariant_of_closed`, `invariant_iff_*`, `ne_neg_one_*`, `exec_swap`. Exact-set pins
(`[propext, Quot.sound]`) break on a toolchain bump that adds `Classical.choice`, which the policy allows;
prefer a check that the set is a subset of the allowed three.
