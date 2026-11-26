import Exegra.Core.Calculus

/-
Positive and adversarial examples of the safety theory (docs/foundations.md, M1 completion
criteria). Each is proved, not tested; `#print axioms` below pins what each proof rests on.

* `counter_le`: a counter with guard `n < L` and effect `n := n + 1` never exceeds `L`, for every
  `L ≥ 0`, with no bound on the length of runs. Proved by an inductive invariant; this is the
  property that separates an `Int` semantics from a `Float` one (assessment, foundations C1).
* `nonneg_not_inductive` and `ne_neg_one_invariant`: `n ≠ -1` is true of every reachable state of
  an unbounded counter but is not inductive (from `-2`, a state that satisfies it but is not
  reachable, one step violates it). The method does not accept it as it stands; it is proved
  through the strengthening `0 ≤ n`.
* `bounded_not_unbounded`: for the unbounded counter, `n ≤ 5` holds in every state reachable in at
  most 5 steps, yet is not an invariant. A search to a fixed depth that finds no counterexample
  proves nothing beyond that depth.
* `mod3_in_range`: a finite system proved safe with no bound by a closed-set certificate checked
  by kernel evaluation (`decide`), not `native_decide`.
-/

namespace Exegra.Core.Examples

open LTS

/-! ### A bounded counter -/

def incTo (L : Int) : Cmd :=
  { label := "inc", guard := .lt (.var 0) (.lit L), updates := [(0, .add (.var 0) (.lit 1))] }

def counter (L : Int) : Prog := { init := [0], cmds := [incTo L] }

theorem incTo_exec (L n : Int) : (incTo L).exec [n] = [n + 1] := rfl

theorem incTo_guard (L n : Int) : (incTo L).guard.eval [n] = decide (n < L) := rfl

/-- **The counter never exceeds its limit**, for every limit `L ≥ 0`, with no bound on runs. -/
theorem counter_le (L : Int) (hL : 0 ≤ L) :
    (counter L).lts.Invariant (fun s => getAt s 0 ≤ L) := by
  refine safe_of_inductive (M := (counter L).lts) (I := fun s => ∃ n, s = [n] ∧ 0 ≤ n ∧ n ≤ L)
    (P := fun s => getAt s 0 ≤ L) ?_ ?_
  · constructor
    · intro s hs
      exact ⟨0, hs, by omega, hL⟩
    · intro s a t hs hst
      obtain ⟨n, rfl, h0, hn⟩ := hs
      obtain ⟨c, hc, -, hg, rfl⟩ := hst
      simp only [counter, List.mem_singleton] at hc
      subst hc
      rw [incTo_guard] at hg
      have hlt : n < L := of_decide_eq_true hg
      rw [incTo_exec]
      exact ⟨n + 1, rfl, by omega, by omega⟩
  · intro s hs
    obtain ⟨n, rfl, -, hn⟩ := hs
    exact hn

/-! ### An unbounded counter -/

def inc : Cmd := { label := "inc", guard := .tt, updates := [(0, .add (.var 0) (.lit 1))] }

def unbounded : Prog := { init := [0], cmds := [inc] }

theorem inc_exec (n : Int) : inc.exec [n] = [n + 1] := rfl

theorem unbounded_step (n : Int) : unbounded.lts.step [n] "inc" [n + 1] :=
  ⟨inc, List.mem_singleton.mpr rfl, rfl, rfl, (inc_exec n).symm⟩

/-- Every state of the unbounded counter is `[n]` for some `n ≥ 0` (an inductive invariant). -/
theorem unbounded_inductive : unbounded.lts.Inductive (fun s => ∃ n, s = [n] ∧ 0 ≤ n) := by
  constructor
  · intro s hs
    exact ⟨0, hs, by omega⟩
  · intro s a t hs hst
    obtain ⟨n, rfl, h0⟩ := hs
    obtain ⟨c, hc, -, -, rfl⟩ := hst
    simp only [unbounded, List.mem_singleton] at hc
    subst hc
    rw [inc_exec]
    exact ⟨n + 1, rfl, by omega⟩

/-- `n ≠ -1` is not inductive: `[-2]` satisfies it and steps to `[-1]`. -/
theorem ne_neg_one_not_inductive : ¬ unbounded.lts.Inductive (fun s => getAt s 0 ≠ -1) := by
  intro h
  have := h.2 [-2] "inc" [-2 + 1] (by decide) (unbounded_step (-2))
  exact this (by decide)

/-- …yet it is an invariant, proved through the strengthening `0 ≤ n`. -/
theorem ne_neg_one_invariant : unbounded.lts.Invariant (fun s => getAt s 0 ≠ -1) := by
  refine safe_of_inductive (P := fun s => getAt s 0 ≠ -1) unbounded_inductive ?_
  intro s hs
  obtain ⟨n, rfl, h0⟩ := hs
  show n ≠ -1
  omega

/-- Every state reachable in at most `k` steps is `[n]` with `n ≤ k`. -/
theorem unbounded_reachIn (k : Nat) (s : List Int) (h : unbounded.lts.ReachIn k s) :
    ∃ n : Int, s = [n] ∧ n ≤ (k : Int) := by
  induction h with
  | init hi => exact ⟨0, hi, by omega⟩
  | @step m s t a _ hst ih =>
    obtain ⟨n, rfl, hn⟩ := ih
    obtain ⟨c, hc, -, -, rfl⟩ := hst
    simp only [unbounded, List.mem_singleton] at hc
    subst hc
    rw [inc_exec]
    exact ⟨n + 1, rfl, by omega⟩

/-- `[k]` is reachable for every `k`. -/
theorem unbounded_reach (k : Nat) : unbounded.lts.Reach [(k : Int)] := by
  induction k with
  | zero => exact .init rfl
  | succ k ih =>
    have e : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
    rw [e]
    exact .step ih (unbounded_step k)

/-- **Bounded exploration is not proof.** `n ≤ 5` holds to depth 5 and is not an invariant. -/
theorem bounded_not_unbounded :
    unbounded.lts.BoundedInvariant 5 (fun s => getAt s 0 ≤ 5) ∧
    ¬ unbounded.lts.Invariant (fun s => getAt s 0 ≤ 5) := by
  constructor
  · intro s hs
    obtain ⟨n, rfl, hn⟩ := unbounded_reachIn 5 s hs
    show n ≤ 5
    omega
  · intro h
    have := h _ (unbounded_reach 6)
    exact absurd this (by decide)

/-! ### A finite system proved by a closed-set certificate -/

def step01 : Cmd := { label := "inc", guard := .lt (.var 0) (.lit 2), updates := [(0, .add (.var 0) (.lit 1))] }
def wrap : Cmd := { label := "wrap", guard := .eq (.var 0) (.lit 2), updates := [(0, .lit 0)] }

/-- Counts 0, 1, 2 and wraps to 0. -/
def mod3 : Prog := { init := [0], cmds := [step01, wrap] }

/-- **`0 ≤ n ≤ 2` in every reachable state**, by the certificate `[[0], [1], [2]]`, checked by
kernel evaluation. -/
theorem mod3_in_range :
    mod3.lts.Invariant (fun s => (decide (0 ≤ getAt s 0) && decide (getAt s 0 ≤ 2)) = true) :=
  checkClosed_sound mod3.enum [[0], [1], [2]]
    (fun s => decide (0 ≤ getAt s 0) && decide (getAt s 0 ≤ 2)) (by decide)

end Exegra.Core.Examples

/-- info: 'Exegra.Core.LTS.safe_of_inductive' does not depend on any axioms -/
#guard_msgs in
#print axioms Exegra.Core.LTS.safe_of_inductive

/-- info: 'Exegra.Core.LTS.checkClosed_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.LTS.checkClosed_sound

/-- info: 'Exegra.Core.Examples.counter_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Examples.counter_le

/-- info: 'Exegra.Core.Examples.bounded_not_unbounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Examples.bounded_not_unbounded

/-- info: 'Exegra.Core.Examples.mod3_in_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Examples.mod3_in_range
