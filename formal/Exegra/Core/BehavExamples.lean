import Exegra.Core.Behav

/-
Examples of the behaviour calculus (plan-M2, M2.1). Each is proved, not tested; `#print axioms`
below pins what each proof rests on.

* The `[a, b]` / `[b, a]` example of docs/foundations.md M2 (modelchecking F4). Two machines react
  to the same event `e` at time 0: `a` sets `x := 1`, `b` sets `y := a.x`. `f4AB` lists `a` first,
  `f4BA` lists `b` first; both start with `x = y = 0`.
  * `f4_ab_safe`, `f4_ba_safe`: under snapshot reads `y = 0` in every reachable state of both
    listings, with no bound on runs. `yAB` and `yBA` are `none` on the error state, so the
    invariants also say that no run fails. Proved by `safe_of_inductive` with the two reachable
    states, the delivery computed by `decide`.
  * `f4_next_reads_differ`: under today's next-configuration rule (`deliverNext`) the same delivery
    gives `y = 1` for one listing and `y = 0` for the other: two verdicts for one model.
  * `f4_nonVacuous`: both systems have an initial state, so the invariants are not vacuous.
* `divZero_counterexample`: a guard `1 / 0 > 0` makes the delivery fail; the run reaches the error
  state, so `ok` is not an invariant. A failing step is a counterexample, not a missing step.
-/

namespace Exegra.Core.Behav.Examples

open Exegra.Core.LTS
open Exegra.Core.Behav

/-! ### The `[a, b]` / `[b, a]` example -/

/-- Two machines, each with one integer variable and one control state `s`. -/
def f4Sig : Sig := { machines := 2, vars := fun _ => [Ty.num], states := fun _ => ["s"] }

/-- The only variable of a machine. -/
def var0 (m : Fin 2) : Fin (f4Sig.vars m).length := ⟨0, Nat.zero_lt_one⟩

/-- The only control state of a machine. -/
def st0 (m : Fin 2) : Fin (f4Sig.states m).length := ⟨0, Nat.zero_lt_one⟩

/-- `on e: x := 1` (event `e` is `0`). -/
def setOne (m : Fin 2) : Trans f4Sig m :=
  { src := st0 m, dst := st0 m, event := 0, guard := .val (.bool true),
    effects := [.set (var0 m) (.val (.int 1))] }

/-- `on e: y := a.x`, reading machine `a`. -/
def copyFrom (m a : Fin 2) : Trans f4Sig m :=
  { src := st0 m, dst := st0 m, event := 0, guard := .val (.bool true),
    effects := [.set (var0 m) (.ref (.other a (var0 a)))] }

/-- Both machines at `0`, one entry of event `e` pending at time `0`. -/
def f4Init : Cfg :=
  { time := 0, machines := [⟨0, [.int 0]⟩, ⟨0, [.int 0]⟩], pending := [⟨0, 0, []⟩] }

def ma : Fin 2 := ⟨0, by decide⟩
def mb : Fin 2 := ⟨1, by decide⟩

/-- `a` is machine 0, `b` is machine 1. -/
def f4AB : Sys :=
  { sig := f4Sig, trans := fun m => if m.val = 0 then [setOne m] else [copyFrom m ma],
    init := f4Init }

/-- `b` is machine 0, `a` is machine 1. -/
def f4BA : Sys :=
  { sig := f4Sig, trans := fun m => if m.val = 0 then [copyFrom m mb] else [setOne m],
    init := f4Init }

/-- Variable 0 of machine `m`; `none` on the error state or a state of the wrong shape. -/
def yOf (m : Nat) : State → Option Val
  | .run c => match c.machines[m]? with
    | some ms => ms.vars[0]?
    | none => none
  | .err _ => none

/-- `b.y` in `f4AB`. -/
def yAB : State → Option Val := yOf 1

/-- `b.y` in `f4BA`. -/
def yBA : State → Option Val := yOf 0

/-- The configuration after the delivery in `f4AB`: `x = 1`, `y = 0`, nothing pending. -/
def f4AB1 : Cfg := { time := 0, machines := [⟨0, [.int 1]⟩, ⟨0, [.int 0]⟩], pending := [] }

/-- The configuration after the delivery in `f4BA`: `y = 0`, `x = 1`, nothing pending. -/
def f4BA1 : Cfg := { time := 0, machines := [⟨0, [.int 0]⟩, ⟨0, [.int 1]⟩], pending := [] }

theorem f4AB_deliver : (deliver f4AB f4Init 0).map (outcome f4Init) = some (.run f4AB1) := by
  decide

theorem f4BA_deliver : (deliver f4BA f4Init 0).map (outcome f4Init) = some (.run f4BA1) := by
  decide

/-- The two reachable states of a system whose initial configuration has one pending entry, at
index 0, delivered to `c₁`, which has nothing pending. -/
theorem two_state_inductive {sys : Sys} {c₁ : Cfg} (hlen : sys.init.pending.length = 1)
    (hd : (deliver sys sys.init 0).map (outcome sys.init) = some (.run c₁))
    (h₁ : c₁.pending = []) :
    (Sys.lts sys).Inductive (fun s => s = .run sys.init ∨ s = .run c₁) := by
  constructor
  · intro s hs
    exact Or.inl hs
  · intro s k t hs hst
    rcases hs with rfl | rfl
    · have hst' : (deliver sys sys.init k).map (outcome sys.init) = some t := hst
      cases k with
      | zero =>
        rw [hd] at hst'
        exact Or.inr (Option.some.inj hst').symm
      | succ k =>
        rw [deliver_none_of_length_le sys sys.init (by rw [hlen]; omega)] at hst'
        cases hst'
    · exact absurd hst (deadlocked_of_pending_nil sys c₁ h₁ k t)

/-- **`[a, b]`: `b.y = 0` in every reachable state**, and no run fails. -/
theorem f4_ab_safe : (Sys.lts f4AB).Invariant (fun s => yAB s = some (.int 0)) :=
  safe_of_inductive (two_state_inductive (c₁ := f4AB1) rfl f4AB_deliver rfl) (by
    intro s hs
    rcases hs with rfl | rfl <;> decide)

/-- **`[b, a]`: `b.y = 0` in every reachable state**, and no run fails: the same verdict. -/
theorem f4_ba_safe : (Sys.lts f4BA).Invariant (fun s => yBA s = some (.int 0)) :=
  safe_of_inductive (two_state_inductive (c₁ := f4BA1) rfl f4BA_deliver rfl) (by
    intro s hs
    rcases hs with rfl | rfl <;> decide)

/-- Both systems have an initial state. -/
theorem f4_nonVacuous : (Sys.lts f4AB).NonVacuous ∧ (Sys.lts f4BA).NonVacuous :=
  ⟨lts_nonVacuous f4AB, lts_nonVacuous f4BA⟩

/-- The state after delivering the first pending entry from the initial configuration under the
next-configuration rule; the initial state if there is none. -/
def afterNext (sys : Sys) : State :=
  match deliverNext sys sys.init 0 with
  | some r => outcome sys.init r
  | none => .run sys.init

/-- **The next-configuration rule gives two verdicts**: the same delivery leaves `y = 1` when `a`
is listed first and `y = 0` when `b` is. -/
theorem f4_next_reads_differ :
    yAB (afterNext f4AB) = some (.int 1) ∧ yBA (afterNext f4BA) = some (.int 0) := by
  decide

/-! ### A failing step reaches the error state -/

def oneSig : Sig := { machines := 1, vars := fun _ => [], states := fun _ => ["s"] }

def oneSt (m : Fin 1) : Fin (oneSig.states m).length := ⟨0, Nat.zero_lt_one⟩

/-- `on e when 1 / 0 > 0`. -/
def divGuard (m : Fin 1) : Trans oneSig m :=
  { src := oneSt m, dst := oneSt m, event := 0,
    guard := .bin .lt (.val (.int 0)) (.bin .div (.val (.int 1)) (.val (.int 0))),
    effects := [] }

def divSys : Sys :=
  { sig := oneSig, trans := fun m => [divGuard m],
    init := { time := 0, machines := [⟨0, []⟩], pending := [⟨0, 0, []⟩] } }

theorem divSys_deliver :
    (deliver divSys divSys.init 0).map (outcome divSys.init) = some (.err divSys.init) := by
  decide

/-- **A failing step is a counterexample**: the error state is reachable, so `ok` is not an
invariant. -/
theorem divZero_counterexample :
    (Sys.lts divSys).Reach (.err divSys.init) ∧ ¬ (Sys.lts divSys).Invariant (fun s => s.ok = true) := by
  have hr : (Sys.lts divSys).Reach (.err divSys.init) := .step (.init rfl) divSys_deliver
  exact ⟨hr, fun h => absurd (h _ hr) (by decide)⟩

end Exegra.Core.Behav.Examples

/-- info: 'Exegra.Core.Behav.phase2_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.phase2_perm

/-- info: 'Exegra.Core.Behav.phase2_perm_emitted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.phase2_perm_emitted

/-- info: 'Exegra.Core.Behav.Examples.f4_ab_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.f4_ab_safe

/-- info: 'Exegra.Core.Behav.Examples.f4_ba_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.f4_ba_safe

/-- info: 'Exegra.Core.Behav.Examples.f4_next_reads_differ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.f4_next_reads_differ

/-- info: 'Exegra.Core.Behav.Examples.divZero_counterexample' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.divZero_counterexample
