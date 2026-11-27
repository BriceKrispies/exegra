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
  * `f4_next_reads_differ`: under the calculus's model of today's next-configuration rule
    (`deliverNext`, with `phase2Next`) the same delivery gives `y = 1` for one listing and `y = 0`
    for the other: two verdicts for one model.
  * `f4_nonVacuous`: both systems have an initial state, so the invariants are not vacuous.
  * `f4Init_shaped`, `f4_ab_no_shape`: the initial configuration is shaped, so no step of `f4AB`
    from a reachable configuration fails with `shape` (`shape_unreachable`).
* `divZero_counterexample`: a guard `1 / 0 > 0` makes the delivery fail; the run reaches the error
  state, so `ok` is not an invariant. A failing step is a counterexample, not a missing step.
* Arithmetic as format 2 computes it (docs/assessment/2026-11-26/review-M2.1.md, D2 and D3):
  `mod_truncates` (`-7 % 2 = -1`), `typed_div_truncates` (`7 / 2 = 3` and `-7 / 2 = -3` in `i32`),
  `untyped_div_inexact`, and `u8_overflow`: with `x : u8 = 200` the guard `x + 100 > 255` is the
  error `overflow`, as format 2 reports, not `true`.
* `emitted_inserted_by_time`: an entry emitted at time 5 goes before a pending entry at time 10, as
  format 2's `insertE` puts it (D6); `emission_order_irrelevant`: two machines that emit on the same
  event give the same successor whichever order they fire in (D1, by `deliver_perm`).
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

/-- **The next-configuration rule gives two verdicts**: under `deliverNext` (the calculus's model
of today's rule, `phase2Next`) the same delivery leaves `b.y = 1` when `a` is listed first (machine
1 of `f4AB`) and `b.y = 0` when `b` is (machine 0 of `f4BA`). -/
theorem f4_next_reads_differ :
    (deliverNext f4AB f4Init 0).map (outcome f4Init) =
        some (.run { time := 0, machines := [⟨0, [.int 1]⟩, ⟨0, [.int 1]⟩], pending := [] }) ∧
      (deliverNext f4BA f4Init 0).map (outcome f4Init) = some (.run f4BA1) := by
  decide

/-- The initial configuration of the example has the shape of its signature. -/
theorem f4Init_shaped : f4Init.Shaped f4AB := by
  refine ⟨rfl, fun m x hx => ?_⟩
  obtain ⟨m, hm⟩ := m
  have fit : VarsFit [Ty.num] [.int 0] :=
    ⟨rfl, fun i h _ => match i, h with
      | 0, _ => rfl
      | _ + 1, h => absurd h (by simp)⟩
  match m, hm with
  | 0, _ => cases hx; exact ⟨Nat.zero_lt_one, fit⟩
  | 1, _ => cases hx; exact ⟨Nat.zero_lt_one, fit⟩

/-- No step of `f4AB` from a reachable configuration fails with `shape`. -/
theorem f4_ab_no_shape {c : Cfg} (hr : (Sys.lts f4AB).Reach (.run c)) (k : Nat) :
    deliver f4AB c k ≠ some (.error .shape) :=
  shape_unreachable f4AB f4Init_shaped hr k

/-! ### A failing step reaches the error state -/

def oneSig : Sig := { machines := 1, vars := fun _ => [], states := fun _ => ["s"] }

def oneSt (m : Fin 1) : Fin (oneSig.states m).length := ⟨0, Nat.zero_lt_one⟩

/-- `on e when 1 / 0 > 0`. -/
def divGuard (m : Fin 1) : Trans oneSig m :=
  { src := oneSt m, dst := oneSt m, event := 0,
    guard := .bin .lt (.val (.int 0)) (.bin (.arith .div .untyped) (.val (.int 1)) (.val (.int 0))),
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

/-! ### Arithmetic as format 2 computes it -/

/-- The range of format 2's `i32` (Value.lean:184-195). -/
def i32 : ATy := .int (-2147483648) 2147483647

/-- `%` is the truncated remainder: `-7 % 2 = -1` (format 2's `Num.fmod`), not `1`. -/
theorem mod_truncates : BOp.apply (.arith .mod .untyped) (.int (-7)) (.int 2) = .ok (.int (-1)) := by
  rfl

/-- Typed `/` truncates toward zero, as format 2's `divIn`. -/
theorem typed_div_truncates :
    BOp.apply (.arith .div i32) (.int 7) (.int 2) = .ok (.int 3) ∧
      BOp.apply (.arith .div i32) (.int (-7)) (.int 2) = .ok (.int (-3)) := ⟨rfl, rfl⟩

/-- Untyped `/` with a remainder is an error (format 2 computes the fraction `3.5`, which the
calculus does not represent), never another value. -/
theorem untyped_div_inexact : BOp.apply (.arith .div .untyped) (.int 7) (.int 2) = .error .inexact := by
  rfl

def u8Sig : Sig := { machines := 1, vars := fun _ => [Ty.int 0 255], states := fun _ => ["s"] }

/-- `x + 100 > 255` on a `u8` variable `x`, the sum computed in `u8` (format 2's `staticTy` of
`x + 100` is `u8`). -/
def u8Guard : Expr u8Sig ⟨0, by decide⟩ :=
  .bin .lt (.val (.int 255)) (.bin (.arith .add (.int 0 255)) (.ref (.own ⟨0, by decide⟩)) (.val (.int 100)))

/-- **Overflow is checked at the arithmetic node**: with `x = 200` the guard is the error
`overflow` (format 2: "Integer overflow: "+" on u8 gives 300"), not `true`. -/
theorem u8_overflow :
    u8Guard.eval { snap := [⟨0, [.int 200]⟩], time := 0, own := ⟨0, [.int 200]⟩, payload := [] } =
      .error .overflow := by
  rfl

/-! ### The queue -/

def oSig : Sig := { machines := 1, vars := fun _ => [], states := fun _ => ["s"] }

/-- On event 0, emit event 1 after 5. -/
def emitLater (m : Fin 1) : Trans oSig m :=
  { src := ⟨0, Nat.zero_lt_one⟩, dst := ⟨0, Nat.zero_lt_one⟩, event := 0,
    guard := .val (.bool true), effects := [.emit 1 5 []] }

def oSys : Sys :=
  { sig := oSig, trans := fun m => [emitLater m],
    init := { time := 0, machines := [⟨0, []⟩], pending := [⟨0, 0, []⟩, ⟨10, 2, []⟩] } }

/-- The entry emitted at time 5 is inserted before the pending entry at time 10. -/
theorem emitted_inserted_by_time :
    (deliver oSys oSys.init 0).map (outcome oSys.init) =
      some (.run { time := 0, machines := [⟨0, []⟩], pending := [⟨5, 1, []⟩, ⟨10, 2, []⟩] }) := by
  decide

def emSig : Sig := { machines := 2, vars := fun _ => [], states := fun _ => ["s"] }

/-- On event 0, machine `m` emits event `m + 1` at once. -/
def emitOwn (m : Fin 2) : Trans emSig m :=
  { src := ⟨0, Nat.zero_lt_one⟩, dst := ⟨0, Nat.zero_lt_one⟩, event := 0,
    guard := .val (.bool true), effects := [.emit (m.val + 1) 0 []] }

def emSys : Sys :=
  { sig := emSig, trans := fun m => [emitOwn m],
    init := { time := 0, machines := [⟨0, []⟩, ⟨0, []⟩], pending := [⟨0, 0, []⟩] } }

/-- **Emission order is irrelevant**: firing the two winners in reverse order gives the same
successor, pending list included (review-M2.1, D1). -/
theorem emission_order_irrelevant :
    (deliverWith emSys (fun c e ws ms => phase2 emSys c e ws.reverse ms) emSys.init 0).map
        (outcome emSys.init) =
      some (.run { time := 0, machines := [⟨0, []⟩, ⟨0, []⟩], pending := [⟨0, 1, []⟩, ⟨0, 2, []⟩] }) := by
  rw [deliver_perm emSys (fun _ _ ws => ws.reverse) (fun _ _ ws => List.reverse_perm ws)]
  decide

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


/-- info: 'Exegra.Core.Behav.deliver_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.deliver_perm

/-- info: 'Exegra.Core.Behav.winners_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.winners_nodup

/-- info: 'Exegra.Core.Behav.shaped_invariant' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.shaped_invariant

/-- info: 'Exegra.Core.Behav.deliver_ne_shape' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.deliver_ne_shape

/-- info: 'Exegra.Core.Behav.shape_unreachable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.shape_unreachable

/-- info: 'Exegra.Core.Behav.Expr.eval_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Expr.eval_fits

/-- info: 'Exegra.Core.Behav.Examples.f4_ab_no_shape' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.f4_ab_no_shape

/-- info: 'Exegra.Core.Behav.Examples.mod_truncates' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.mod_truncates

/-- info: 'Exegra.Core.Behav.Examples.typed_div_truncates' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.typed_div_truncates

/-- info: 'Exegra.Core.Behav.Examples.untyped_div_inexact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.untyped_div_inexact

/-- info: 'Exegra.Core.Behav.Examples.u8_overflow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.u8_overflow

/-- info: 'Exegra.Core.Behav.Examples.emitted_inserted_by_time' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.emitted_inserted_by_time

/-- info: 'Exegra.Core.Behav.Examples.emission_order_irrelevant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.emission_order_irrelevant
