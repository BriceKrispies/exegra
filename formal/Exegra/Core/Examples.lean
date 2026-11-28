import Exegra.Core.Calculus
import Exegra.Core.Search

/-
Positive and adversarial examples of the safety theory (docs/foundations.md, M1 completion
criteria). Each is proved, not tested; `#print axioms` below pins what each proof rests on.

* `counter_le`: a counter with guard `n < L` and effect `n := n + 1` never exceeds `L`, for every
  `L ≥ 0`, with no bound on the length of runs. Proved by an inductive invariant; this is the
  property that separates an `Int` semantics from a floating-point one (assessment, foundations C1).
* `ne_neg_one_not_inductive` and `ne_neg_one_invariant`: `n ≠ -1` is true of every reachable state
  of an unbounded counter but is not inductive (from `-2`, a state that satisfies it but is not
  reachable, one step violates it). The method does not accept it as it stands; it is proved
  through the strengthening `0 ≤ n`.
* `bounded_not_unbounded`: for every depth `k`, `n ≤ k` holds in every state of the unbounded
  counter reachable in at most `k` steps, yet is not an invariant. No search to a fixed depth that
  finds no counterexample proves anything beyond that depth.
* `vacuous_false`: a system with no initial state has `False` as an invariant, which is why claims
  built on invariants must establish `NonVacuous` (every program does: `Prog.nonVacuous`).
* `kSys_not_inductive`, `kSys_kInductive`, `kSys_invariant`: a property that is not inductive (a
  state outside the reachable set violates it after one step) but is 2-inductive, proved an
  invariant by `kInduction_sound`.
* `mod3_in_range`: a finite system proved safe with no bound by a closed-set certificate checked by
  kernel evaluation (`decide`), not `native_decide`.
-/

namespace Exegra.Core.Examples

open LTS

/-- The one variable of a one-variable program. -/
def v0 : Fin 1 := ⟨0, by decide⟩

/-! ### A bounded counter -/

def incTo (L : Int) : Cmd 1 :=
  { guard := .lt (.var v0) (.lit L), update := fun _ => some (.add (.var v0) (.lit 1)) }

def counter (L : Int) : Prog 1 := { init := [0], init_length := rfl, cmds := [incTo L] }

theorem incTo_exec (L n : Int) : (incTo L).exec [n] = [n + 1] := rfl

theorem incTo_guard (L n : Int) : (incTo L).guard.eval [n] = decide (n < L) := rfl

/-- The only command of a one-command program. -/
theorem only_cmd {c : Cmd 1} {i : Fin [c].length} : [c][i] = c := by
  obtain ⟨j, hj⟩ := i
  have : j = 0 := by simp at hj; omega
  subst this
  rfl

/-- **The counter never exceeds its limit**, for every limit `L ≥ 0`, with no bound on runs. -/
theorem counter_le (L : Int) (hL : 0 ≤ L) :
    (counter L).lts.Invariant (fun s => getAt s 0 ≤ L) := by
  refine safe_of_inductive (M := (counter L).lts) (I := fun s => ∃ n, s = [n] ∧ 0 ≤ n ∧ n ≤ L)
    (P := fun s => getAt s 0 ≤ L) ⟨?_, ?_⟩ ?_
  · intro s hs
    exact ⟨0, hs, by omega, hL⟩
  · intro s i t hs hst
    obtain ⟨n, rfl, h0, hn⟩ := hs
    obtain ⟨hg, rfl⟩ := hst
    have hc : (counter L).cmds[i] = incTo L := only_cmd
    rw [hc, incTo_guard] at hg
    have hlt : n < L := of_decide_eq_true hg
    rw [hc, incTo_exec]
    exact ⟨n + 1, rfl, by omega, by omega⟩
  · intro s hs
    obtain ⟨n, rfl, -, hn⟩ := hs
    exact hn

/-! ### An unbounded counter -/

def inc : Cmd 1 := { guard := .tt, update := fun _ => some (.add (.var v0) (.lit 1)) }

def unbounded : Prog 1 := { init := [0], init_length := rfl, cmds := [inc] }

theorem inc_exec (n : Int) : inc.exec [n] = [n + 1] := rfl

theorem unbounded_step (n : Int) : unbounded.lts.step [n] ⟨0, by decide⟩ [n + 1] :=
  ⟨rfl, (inc_exec n).symm⟩

/-- Every reachable state of the unbounded counter is `[n]` for some `n ≥ 0`. -/
theorem unbounded_inductive : unbounded.lts.Inductive (fun s => ∃ n, s = [n] ∧ 0 ≤ n) := by
  constructor
  · intro s hs
    exact ⟨0, hs, by omega⟩
  · intro s i t hs hst
    obtain ⟨n, rfl, h0⟩ := hs
    obtain ⟨-, rfl⟩ := hst
    have hc : unbounded.cmds[i] = inc := only_cmd
    rw [hc, inc_exec]
    exact ⟨n + 1, rfl, by omega⟩

/-- `n ≠ -1` is not inductive: `[-2]` satisfies it and steps to `[-1]`. -/
theorem ne_neg_one_not_inductive : ¬ unbounded.lts.Inductive (fun s => getAt s 0 ≠ -1) := by
  intro h
  have := h.2 [-2] ⟨0, by decide⟩ [-2 + 1] (by decide) (unbounded_step (-2))
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
  | @step m s t i _ hst ih =>
    obtain ⟨n, rfl, hn⟩ := ih
    obtain ⟨-, rfl⟩ := hst
    have hc : unbounded.cmds[i] = inc := only_cmd
    rw [hc, inc_exec]
    exact ⟨n + 1, rfl, by omega⟩

/-- `[k]` is reachable for every `k`. -/
theorem unbounded_reach (k : Nat) : unbounded.lts.Reach [(k : Int)] := by
  induction k with
  | zero => exact .init rfl
  | succ k ih =>
    have e : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
    rw [e]
    exact .step ih (unbounded_step k)

/-- **Bounded exploration is not proof**, at every depth: `n ≤ k` holds to depth `k` and is not an
invariant. -/
theorem bounded_not_unbounded (k : Nat) :
    unbounded.lts.BoundedInvariant k (fun s => getAt s 0 ≤ k) ∧
    ¬ unbounded.lts.Invariant (fun s => getAt s 0 ≤ k) := by
  constructor
  · intro s hs
    obtain ⟨n, rfl, hn⟩ := unbounded_reachIn k s hs
    show n ≤ k
    exact hn
  · intro h
    have h1 : getAt [((k + 1 : Nat) : Int)] 0 ≤ (k : Int) := h _ (unbounded_reach (k + 1))
    have e : getAt [((k + 1 : Nat) : Int)] 0 = (k : Int) + 1 := by
      show ((k + 1 : Nat) : Int) = (k : Int) + 1
      omega
    rw [e] at h1
    omega

/-! ### Vacuity -/

/-- A system with no initial state. -/
def empty : LTS Unit Unit := { init := fun _ => False, step := fun _ _ _ => False }

/-- **Vacuity.** `False` is an invariant of a system with no initial state. -/
theorem vacuous_false : empty.Invariant (fun _ => False) :=
  invariant_of_no_init (fun ⟨_, h⟩ => h) _

/-! ### A finite system proved by a closed-set certificate -/

def step01 : Cmd 1 := { guard := .lt (.var v0) (.lit 2), update := fun _ => some (.add (.var v0) (.lit 1)) }
def wrap : Cmd 1 := { guard := .eq (.var v0) (.lit 2), update := fun _ => some (.lit 0) }

/-- Counts 0, 1, 2 and wraps to 0. -/
def mod3 : Prog 1 := { init := [0], init_length := rfl, cmds := [step01, wrap] }

/-- **`0 ≤ n ≤ 2` in every reachable state**, by the certificate `[[0], [1], [2]]`, checked by
kernel evaluation. -/
theorem mod3_in_range :
    mod3.lts.Invariant (fun s => (decide (0 ≤ getAt s 0) && decide (getAt s 0 ≤ 2)) = true) :=
  checkClosed_sound mod3.enum [[0], [1], [2]]
    (fun s => decide (0 ≤ getAt s 0) && decide (getAt s 0 ≤ 2)) (by decide)

/-! ### A 2-inductive invariant that is not inductive -/

/-- States `0 ⇄ 1` are reachable; `2 → 3 → 3` is not: nothing leads to `2`. -/
def kSys : LTS Nat Unit where
  init s := s = 0
  step s _ t := (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) ∨ (s = 2 ∧ t = 3) ∨ (s = 3 ∧ t = 3)

/-- The property: the state is never `3`. -/
def kP (s : Nat) : Prop := s ≠ 3

/-- **Not inductive**: `2` satisfies `kP` and steps to `3`. -/
theorem kSys_not_inductive : ¬ kSys.Inductive kP := by
  intro h
  exact h.2 2 () 3 (by simp [kP]) (by simp [kSys]) rfl

/-- **2-inductive**: a path of three states whose first two are not `3` cannot end in `3`, because
the only other way into `3` is from `2`, which has no predecessor. -/
theorem kSys_kInductive : kSys.KInductive 2 kP := by
  refine ⟨?_, ?_⟩
  · intro s hs
    cases hs with
    | init hi => simp [kSys] at hi; simp [kP, hi]
    | step h0 hst =>
      cases h0 with
      | init hi => simp only [kSys] at hi hst; subst hi; simp [kP]; omega
  · intro xs hl hp hpre
    match xs, hl, hp with
    | [x0, x1, x2], _, ⟨⟨_, h01⟩, ⟨_, h12⟩, _⟩ =>
      have p0 : x0 ≠ 3 := hpre 0 (by omega)
      have p1 : x1 ≠ 3 := hpre 1 (by omega)
      show x2 ≠ 3
      simp only [kSys] at h01 h12
      omega

/-- **The invariant, by k-induction** with `k = 2`. -/
theorem kSys_invariant : kSys.Invariant kP := kInduction_sound (by decide) kSys_kInductive

end Exegra.Core.Examples

/-- info: 'Exegra.Core.LTS.safe_of_inductive' does not depend on any axioms -/
#guard_msgs in
#print axioms Exegra.Core.LTS.safe_of_inductive

/-- info: 'Exegra.Core.LTS.checkClosed_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.LTS.checkClosed_sound

/-- info: 'Exegra.Core.LTS.invariant_of_search' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.LTS.invariant_of_search

/-- info: 'Exegra.Core.LTS.not_invariant_of_search' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.LTS.not_invariant_of_search

/-- info: 'Exegra.Core.Cmd.exec_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Cmd.exec_get

/-- info: 'Exegra.Core.Examples.counter_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Examples.counter_le

/-- info: 'Exegra.Core.Examples.bounded_not_unbounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Examples.bounded_not_unbounded

/-- info: 'Exegra.Core.Examples.mod3_in_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Examples.mod3_in_range

/-- info: 'Exegra.Core.LTS.kInduction_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.LTS.kInduction_sound

/-- info: 'Exegra.Core.Examples.kSys_not_inductive' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Core.Examples.kSys_not_inductive

/-- info: 'Exegra.Core.Examples.kSys_kInductive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Examples.kSys_kInductive

/-- info: 'Exegra.Core.Examples.kSys_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Examples.kSys_invariant
