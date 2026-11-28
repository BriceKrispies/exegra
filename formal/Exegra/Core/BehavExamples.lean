import Exegra.Core.BehavExec

/-
Examples of the behaviour calculus (plan-M2, M2.1 to M2.3). Each is proved, not tested; the
`#guard_msgs` blocks at the end pin what each proof rests on.

* The `[a, b]` / `[b, a]` example of docs/foundations.md M2 (modelchecking F4). Two machines react
  to the same event `e` at time 0: `a` sets `x := 1`, `b` sets `y := a.x`. `f4AB` lists `a` first,
  `f4BA` lists `b` first; both start with `x = y = 0`.
  * `f4_ab_safe`, `f4_ba_safe`: under snapshot reads `y = 0` in every reachable state of both
    listings, with no bound on runs. `yAB` and `yBA` are `none` on the error state, so the
    invariants also say that no run fails. Proved by `safe_of_inductive` with the two reachable
    states, the delivery computed by `decide`.
  * `f4_ab_safe_closed`: the same invariant of `f4AB` from a closed-set certificate over the
    executable enumeration `Exec.enum`, checked by kernel evaluation.
  * `f4_exec_same_machines`: the executable scheduler commits the same machines (`x = 1`, `y = 0`,
    up to the listing) for both listings.
  * `f4_next_reads_differ`: under the calculus's model of today's next-configuration rule
    (`deliverNext`, with `phase2Next`) the same delivery gives `y = 1` for one listing and `y = 0`
    for the other: two verdicts for one model.
  * `f4_nonVacuous`; `f4Init_shaped`, `f4_ab_no_shape`; `f4_wf` (both systems are well-formed).
* `divZero_counterexample`: a guard `1 / 0 > 0` makes the delivery fail; the run reaches the error
  state, so `ok` is not an invariant. A failing step is a counterexample, not a missing step.
* Arithmetic as format 2 computes it: `mod_truncates`, `typed_div_truncates`,
  `untyped_div_inexact`, `u8_overflow`.
* The queue: `emitted_inserted_by_time`, `emission_order_irrelevant`.
* Timers (M2.2): `timer_then_cancel` (setting a timer and cancelling it in the same transition leaves
  no entry), `timer_reset` (setting a timer drops its pending entry and queues the new one).
* Faults (M2.2): `drop_second_delivery` (a `drop` fault with occurrence 2 drops exactly the second
  delivery of the event: after three deliveries the counter is 2 and three attempts are counted),
  `drop_fault_optional` (the same system without the fault, the other mask, counts 3).
* Counted instances and aggregates (M2.7): two instances of a worker and a monitor reading
  `worker.sum.x + worker.count.busy` in the same step. `agg_last_safe`, `agg_first_safe`: the
  monitor reads `0` in every reachable state whichever way the machines are listed;
  `agg_next_reads_differ`: the next-configuration rule reads `4` or `0` depending on the listing.
* Replies (M2.7): `reply_reaches_requester` (a request carries its sender and the reply is
  delivered to it), `reply_without_sender_fails`.
-/

namespace Exegra.Core.Behav.Examples

open Exegra.Core.LTS
open Exegra.Core.Behav

/-! ### The `[a, b]` / `[b, a]` example -/

/-- The label delivering the head of a configuration's queue, with no draws. -/
def headLabel (c : Cfg) : Label := ⟨c.pending.headD { time := 0, event := 0, payload := [] }, [], []⟩

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
  { time := 0, machines := [{ ctrl := 0, vars := [.int 0] }, { ctrl := 0, vars := [.int 0] }],
    pending := [{ time := 0, event := 0, payload := [] }] }

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
  | .run _ c => match c.machines[m]? with
    | some ms => ms.vars[0]?
    | none => none
  | .err _ _ => none

/-- `b.y` in `f4AB`. -/
def yAB : State → Option Val := yOf 1

/-- `b.y` in `f4BA`. -/
def yBA : State → Option Val := yOf 0

/-- The configuration after the delivery in `f4AB`: `x = 1`, `y = 0`, nothing pending, one attempt
of event `e`. -/
def f4AB1 : Cfg :=
  { time := 0, machines := [{ ctrl := 0, vars := [.int 1] }, { ctrl := 0, vars := [.int 0] }], pending := [], attempts := [1] }

/-- The configuration after the delivery in `f4BA`: `y = 0`, `x = 1`, nothing pending. -/
def f4BA1 : Cfg :=
  { time := 0, machines := [{ ctrl := 0, vars := [.int 0] }, { ctrl := 0, vars := [.int 1] }], pending := [], attempts := [1] }

theorem f4AB_deliver : (deliver f4AB [] f4Init (headLabel f4Init)).map (outcome [] f4Init) = some (.run [] f4AB1) := by
  decide

theorem f4BA_deliver : (deliver f4BA [] f4Init (headLabel f4Init)).map (outcome [] f4Init) = some (.run [] f4BA1) := by
  decide

/-- The two reachable states of a system with no faults and no sampled delays whose initial
configuration has one pending entry, delivered to `c₁`, which has nothing pending. -/
theorem two_state_inductive {sys : Sys} {c₁ : Cfg} (hf : sys.faults = []) (hsm : sys.samples = [])
    (hres : sys.resources = []) (hlk : sys.links = []) (hrt : sys.routes = []) (hlen : sys.init.pending.length = 1)
    (hd : (deliver sys [] sys.init (headLabel sys.init)).map (outcome [] sys.init) = some (.run [] c₁))
    (h₁ : c₁.pending = []) :
    (Sys.lts sys).Inductive (fun s => s = .run [] sys.init ∨ s = .run [] c₁) := by
  constructor
  · intro s hs
    exact Or.inl (init_of_no_faults hf hs)
  · intro s l t hs hst
    rcases hs with rfl | rfl
    · have hst' : Step sys [] sys.init l t := hst
      obtain ⟨hdr, hrdy⟩ := Step.ready hst'
      have hl : l = headLabel sys.init := by
        have hdl : l.draws = [] := by
          have := hdr.1
          simp [Sys.dists, hsm] at this
          exact this
        obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
        have hmem := hrdy.1
        rw [hx] at hmem
        have hxe : l.entry = x := List.mem_singleton.mp hmem
        have hwd : l.wdraws = [] := wdraws_nil_of_nores hres hlk hrt hst'
        cases l
        simp only [headLabel, hx] at hdl hxe hwd ⊢
        rw [hxe, hdl, hwd]; rfl
      have h2 := (deliver_eq_step (sys := sys) (mask := []) (c := sys.init) (l := l) (t := t)).mpr hst'
      rw [hl, hd] at h2
      exact Or.inr (Option.some.inj h2).symm
    · exact absurd hst (deadlocked_of_pending_nil sys [] c₁ h₁ l t)

/-- **`[a, b]`: `b.y = 0` in every reachable state**, and no run fails. -/
theorem f4_ab_safe : (Sys.lts f4AB).Invariant (fun s => yAB s = some (.int 0)) :=
  safe_of_inductive (two_state_inductive (c₁ := f4AB1) rfl rfl rfl rfl rfl rfl f4AB_deliver rfl) (by
    intro s hs
    rcases hs with rfl | rfl <;> decide)

/-- **`[b, a]`: `b.y = 0` in every reachable state**, and no run fails: the same verdict. -/
theorem f4_ba_safe : (Sys.lts f4BA).Invariant (fun s => yBA s = some (.int 0)) :=
  safe_of_inductive (two_state_inductive (c₁ := f4BA1) rfl rfl rfl rfl rfl rfl f4BA_deliver rfl) (by
    intro s hs
    rcases hs with rfl | rfl <;> decide)

/-- **`[a, b]` from a closed-set certificate** over the executable enumeration: the two states are
closed under `Exec.enum`'s successors and satisfy the property, checked by kernel evaluation. -/
theorem f4_ab_safe_closed :
    (Sys.lts f4AB).Invariant (fun s => (yAB s == some (.int 0)) = true) :=
  checkClosed_sound (Exec.enum f4AB) [.run [] f4Init, .run [] f4AB1] _ (by decide)

/-- Both systems have an initial state. -/
theorem f4_nonVacuous : (Sys.lts f4AB).NonVacuous ∧ (Sys.lts f4BA).NonVacuous :=
  ⟨lts_nonVacuous f4AB, lts_nonVacuous f4BA⟩

/-- Both systems are well-formed. -/
theorem f4_wf : f4AB.WF ∧ f4BA.WF := ⟨by decide, by decide⟩

/-- The machines a scheduler result commits, if it commits. -/
def committedMachines : XResult → Option (List MState)
  | .committed _ s _ => some s.cfg.machines
  | _ => none

/-- **The executable scheduler commits the same machines for both listings** (`a`'s `x = 1`,
`b`'s `y = 0`, in each listing's machine order). -/
theorem f4_exec_same_machines :
    committedMachines (Exec.step f4AB (.run [] f4Init) {}) = some [{ ctrl := 0, vars := [.int 1] }, { ctrl := 0, vars := [.int 0] }] ∧
      committedMachines (Exec.step f4BA (.run [] f4Init) {}) = some [{ ctrl := 0, vars := [.int 0] }, { ctrl := 0, vars := [.int 1] }] := by
  decide

/-- **The next-configuration rule gives two verdicts**: under `deliverNext` (the calculus's model
of today's rule, `phase2Next`) the same delivery leaves `b.y = 1` when `a` is listed first (machine
1 of `f4AB`) and `b.y = 0` when `b` is (machine 0 of `f4BA`). -/
theorem f4_next_reads_differ :
    (deliverNext f4AB [] f4Init 0 []).map (outcome [] f4Init) =
        some (.run [] { time := 0, machines := [{ ctrl := 0, vars := [.int 1] }, { ctrl := 0, vars := [.int 1] }], pending := [],
                        attempts := [1] }) ∧
      (deliverNext f4BA [] f4Init 0 []).map (outcome [] f4Init) = some (.run [] f4BA1) := by
  decide

/-- The initial configuration of the example has the shape of its signature. -/
theorem f4Init_shaped : f4Init.Shaped f4AB := WF.shaped f4_wf.1

/-- No step of `f4AB` from a reachable configuration fails with `shape`. -/
theorem f4_ab_no_shape {m : List Bool} {c : Cfg} (hr : (Sys.lts f4AB).Reach (.run m c)) (l : Label) :
    deliver f4AB m c l ≠ some (.error .shape) :=
  shape_unreachable f4AB f4Init_shaped hr l

/-! ### Counted instances and aggregates read from the snapshot (M2.7) -/

/-- Three machines, each with one integer variable and the control states `idle` and `busy`. Two
are the instances of a counted behaviour `worker`, one is a `monitor` reading their aggregates. -/
def aggSig : Sig := { machines := 3, vars := fun _ => [Ty.num], states := fun _ => ["idle", "busy"] }

def aVar (m : Fin 3) : Fin (aggSig.vars m).length := ⟨0, Nat.zero_lt_one⟩

/-- A worker: `on e: x := 1`, moving from `idle` to `busy`. -/
def work (m : Fin 3) : Trans aggSig m :=
  { src := ⟨0, Nat.zero_lt_two⟩, dst := ⟨1, Nat.one_lt_two⟩, event := 0, guard := .val (.bool true),
    effects := [.set (aVar m) (.val (.int 1))] }

/-- The monitor: `on e: t := worker.sum.x + worker.count.busy` over the worker instances `ws`. -/
def watch (m : Fin 3) (ws : List (Fin 3)) : Trans aggSig m :=
  { src := ⟨0, Nat.zero_lt_two⟩, dst := ⟨0, Nat.zero_lt_two⟩, event := 0, guard := .val (.bool true),
    effects := [.set (aVar m) (.bin (.arith .add .untyped)
      (.ref (.agg .sum (ws.map fun w => ⟨w, aVar w⟩))) (.ref (.count ws "busy")))] }

def aggInit : Cfg :=
  { time := 0, machines := [{ ctrl := 0, vars := [.int 0] }, { ctrl := 0, vars := [.int 0] }, { ctrl := 0, vars := [.int 0] }],
    pending := [{ time := 0, event := 0, payload := [] }] }

/-- The workers listed first (machines 0 and 1), the monitor last (machine 2). -/
def aggLast : Sys :=
  { sig := aggSig, init := aggInit,
    trans := fun m => if m.val = 2 then [watch m [⟨0, by decide⟩, ⟨1, by decide⟩]] else [work m] }

/-- The monitor listed first (machine 0), the workers after it (machines 1 and 2). -/
def aggFirst : Sys :=
  { sig := aggSig, init := aggInit,
    trans := fun m => if m.val = 0 then [watch m [⟨1, by decide⟩, ⟨2, by decide⟩]] else [work m] }

def aggLast1 : Cfg :=
  { time := 0, machines := [{ ctrl := 1, vars := [.int 1] }, { ctrl := 1, vars := [.int 1] }, { ctrl := 0, vars := [.int 0] }], pending := [], attempts := [1] }

def aggFirst1 : Cfg :=
  { time := 0, machines := [{ ctrl := 0, vars := [.int 0] }, { ctrl := 1, vars := [.int 1] }, { ctrl := 1, vars := [.int 1] }], pending := [], attempts := [1] }

theorem agg_wf : aggLast.WF ∧ aggFirst.WF := ⟨by decide, by decide⟩

theorem aggLast_deliver :
    (deliver aggLast [] aggInit (headLabel aggInit)).map (outcome [] aggInit) = some (.run [] aggLast1) := by
  decide

theorem aggFirst_deliver :
    (deliver aggFirst [] aggInit (headLabel aggInit)).map (outcome [] aggInit) = some (.run [] aggFirst1) := by
  decide

/-- **Aggregates are read from the start of the step, whatever the listing**: the monitor's
`worker.sum.x + worker.count.busy` is `0` in every reachable state of both listings, although
both workers fire in the same step. -/
theorem agg_last_safe : (Sys.lts aggLast).Invariant (fun s => yOf 2 s = some (.int 0)) :=
  safe_of_inductive (two_state_inductive (c₁ := aggLast1) rfl rfl rfl rfl rfl rfl aggLast_deliver rfl) (by
    intro s hs
    rcases hs with rfl | rfl <;> decide)

theorem agg_first_safe : (Sys.lts aggFirst).Invariant (fun s => yOf 0 s = some (.int 0)) :=
  safe_of_inductive (two_state_inductive (c₁ := aggFirst1) rfl rfl rfl rfl rfl rfl aggFirst_deliver rfl) (by
    intro s hs
    rcases hs with rfl | rfl <;> decide)

/-- Under the next-configuration rule (`deliverNext`) the monitor listed last reads both workers
as they fired, `2 + 2 = 4`, and the monitor listed first reads `0`: two verdicts. -/
theorem agg_next_reads_differ :
    (deliverNext aggLast [] aggInit 0 []).map (outcome [] aggInit) =
        some (.run [] { aggLast1 with machines := [{ ctrl := 1, vars := [.int 1] }, { ctrl := 1, vars := [.int 1] }, { ctrl := 0, vars := [.int 4] }] }) ∧
      (deliverNext aggFirst [] aggInit 0 []).map (outcome [] aggInit) = some (.run [] aggFirst1) := by
  decide

/-! ### Replies -/

def rSig : Sig := { machines := 2, vars := fun _ => [Ty.num], states := fun _ => ["s"] }

def rSt (m : Fin 2) : Fin (rSig.states m).length := ⟨0, Nat.zero_lt_one⟩

/-- The client (machine 0): on event 0 it emits the request (event 1); on the answer (event 2) it
sets `got := 1`. The server (machine 1): on the request it replies with event 2. -/
def rTrans (m : Fin 2) : List (Trans rSig m) :=
  if m.val = 0 then
    [{ src := rSt m, dst := rSt m, event := 0, guard := .val (.bool true), effects := [.emit 1 0 []] },
     { src := rSt m, dst := rSt m, event := 2, guard := .val (.bool true),
       effects := [.set ⟨0, Nat.zero_lt_one⟩ (.val (.int 1))] }]
  else [{ src := rSt m, dst := rSt m, event := 1, guard := .val (.bool true), effects := [.reply 2 0 []] }]

def rSys (ev : Nat) : Sys :=
  { sig := rSig, trans := rTrans,
    init := { time := 0, machines := [{ ctrl := 0, vars := [.int 0] }, { ctrl := 0, vars := [.int 0] }], pending := [{ time := 0, event := ev, payload := [] }] } }

/-- **A reply reaches the requester**: the request carries its sender, the server's reply is
targeted at it, and the client takes it. -/
theorem reply_reaches_requester :
    ((Exec.run (rSys 0) 3 (.run [] (rSys 0).init) {}).states.getLast?).map (·.cfg) =
      some { time := 0, machines := [{ ctrl := 0, vars := [.int 1] }, { ctrl := 0, vars := [.int 0] }], pending := [], attempts := [1, 1, 1] } := by
  decide

/-- **A reply to an entry without a sender fails**: the run ends in the error state. -/
theorem reply_without_sender_fails :
    (((Exec.run (rSys 1) 3 (.run [] (rSys 1).init) {}).states.getLast?).map State.ok) = some false ∧
      ((deliver (rSys 1) [] (rSys 1).init (headLabel (rSys 1).init)).map fun r => match r with
        | .error e => some e
        | .ok _ => none) = some (some .noRequester) := by
  decide

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
    init := { time := 0, machines := [{ ctrl := 0, vars := [] }], pending := [{ time := 0, event := 0, payload := [] }] } }

theorem divSys_deliver :
    (deliver divSys [] divSys.init (headLabel divSys.init)).map (outcome [] divSys.init) = some (.err [] divSys.init) := by
  decide

/-- **A failing step is a counterexample**: the error state is reachable, so `ok` is not an
invariant. -/
theorem divZero_counterexample :
    (Sys.lts divSys).Reach (.err [] divSys.init) ∧
      ¬ (Sys.lts divSys).Invariant (fun s => s.ok = true) := by
  have h0 : (Sys.lts divSys).Reach (.run [] divSys.init) := .init ⟨[], rfl, by rw [initCfg_nil]⟩
  have hr : (Sys.lts divSys).Reach (.err [] divSys.init) := .step (a := headLabel divSys.init) h0 (deliver_eq_step.mp divSys_deliver)
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

-- Untyped `/` with a remainder is the exact rational (WG-5683): `7 / 2` is `7/2`, not `3` and not
-- an error; `0.1 + 0.2 == 0.3`. Checked by evaluation: `Rat` arithmetic does not reduce in the kernel.
#guard match BOp.apply (.arith .div .untyped) (.int 7) (.int 2) with
  | .ok (.rat q) => q == 7 / 2
  | _ => false
#guard match BOp.apply (.arith .add .untyped) (.rat (1 / 10)) (.rat (2 / 10)) with
  | .ok v => v.equiv (.rat (3 / 10))
  | _ => false

def u8Sig : Sig := { machines := 1, vars := fun _ => [Ty.int 0 255], states := fun _ => ["s"] }

/-- `x + 100 > 255` on a `u8` variable `x`, the sum computed in `u8` (format 2's `staticTy` of
`x + 100` is `u8`). -/
def u8Guard : Expr u8Sig ⟨0, by decide⟩ :=
  .bin .lt (.val (.int 255)) (.bin (.arith .add (.int 0 255)) (.ref (.own ⟨0, by decide⟩)) (.val (.int 100)))

/-- **Overflow is checked at the arithmetic node**: with `x = 200` the guard is the error
`overflow` (format 2: "Integer overflow: "+" on u8 gives 300"), not `true`. -/
theorem u8_overflow :
    u8Guard.eval { snap := [{ ctrl := 0, vars := [.int 200] }], time := 0, own := { ctrl := 0, vars := [.int 200] }, payload := [] } =
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
    init := { time := 0, machines := [{ ctrl := 0, vars := [] }],
              pending := [{ time := 0, event := 0, payload := [] }, { time := 10, event := 2, payload := [] }] } }

/-- The entry emitted at time 5 is inserted before the pending entry at time 10. -/
theorem emitted_inserted_by_time :
    (deliverAt oSys [] oSys.init 0 []).map (outcome [] oSys.init) =
      some (.run [] { time := 0, machines := [{ ctrl := 0, vars := [] }],
                      pending := [{ time := 5, event := 1, payload := [], sender := some 0 },
                                 { time := 10, event := 2, payload := [] }],
                      attempts := [1] }) := by
  decide

def emSig : Sig := { machines := 2, vars := fun _ => [], states := fun _ => ["s"] }

/-- On event 0, machine `m` emits event `m + 1` at once. -/
def emitOwn (m : Fin 2) : Trans emSig m :=
  { src := ⟨0, Nat.zero_lt_one⟩, dst := ⟨0, Nat.zero_lt_one⟩, event := 0,
    guard := .val (.bool true), effects := [.emit (m.val + 1) 0 []] }

def emSys : Sys :=
  { sig := emSig, trans := fun m => [emitOwn m],
    init := { time := 0, machines := [{ ctrl := 0, vars := [] }, { ctrl := 0, vars := [] }], pending := [{ time := 0, event := 0, payload := [] }] } }

/-- **Emission order is irrelevant**: firing the two winners in reverse order gives the same
successor, pending list included (review-M2.1, D1). -/
theorem emission_order_irrelevant :
    (deliverWith emSys (fun c e ws ms => phase2 emSys c e ws.reverse ms) [] emSys.init 0 []).map
        (outcome [] emSys.init) =
      some (.run [] { time := 0, machines := [{ ctrl := 0, vars := [] }, { ctrl := 0, vars := [] }],
                      pending := [{ time := 0, event := 1, payload := [], sender := some 0 },
                                 { time := 0, event := 2, payload := [], sender := some 1 }],
                      attempts := [1] }) := by
  rw [deliver_perm emSys (fun _ _ ws => ws.reverse) (fun _ _ ws => List.reverse_perm ws)]
  decide

/-! ### Timers -/

/-- On event 0, run `effs`. -/
def onZero (effs : List (Effect oSig ⟨0, Nat.zero_lt_one⟩)) : Sys :=
  { sig := oSig,
    trans := fun m => match m with
      | ⟨0, _⟩ => [{ src := ⟨0, Nat.zero_lt_one⟩, dst := ⟨0, Nat.zero_lt_one⟩, event := 0,
                      guard := .val (.bool true), effects := effs }],
    init := { time := 0, machines := [{ ctrl := 0, vars := [] }],
              pending := [{ time := 0, event := 0, payload := [] },
                          { time := 10, event := 1, payload := [], target := some 0, timer := some 0 }] } }

/-- **Setting a timer and cancelling it in the same transition leaves no entry**, and the timer's
earlier entry is dropped too. -/
theorem timer_then_cancel :
    ((deliverAt (onZero [.timer 0 5 1 [], .cancel 0]) [] (onZero [.timer 0 5 1 [], .cancel 0]).init 0 []).bind
      (·.toOption)).map (·.pending) = some [] := by
  decide

/-- **Setting a timer replaces its pending entry**: the entry at 10 is dropped, the new one is at
3. -/
theorem timer_reset :
    ((deliverAt (onZero [.timer 0 3 1 []]) [] (onZero [.timer 0 3 1 []]).init 0 []).bind
      (·.toOption)).map (·.pending) =
      some [{ time := 3, event := 1, payload := [], target := some 0, timer := some 0 }] := by
  decide

/-! ### Faults -/

def ctrSig : Sig := { machines := 1, vars := fun _ => [Ty.num], states := fun _ => ["s"] }

/-- On event 0, `n := n + 1`; three deliveries of event 0 at times 0, 1, 2; a `drop` fault on the
second attempt of event 0. -/
def dropSys : Sys :=
  { sig := ctrSig,
    trans := fun m => match m with
      | ⟨0, _⟩ => [{ src := ⟨0, Nat.zero_lt_one⟩, dst := ⟨0, Nat.zero_lt_one⟩, event := 0,
                      guard := .val (.bool true),
                      effects := [.set ⟨0, Nat.zero_lt_one⟩
                        (.bin (.arith .add .untyped) (.ref (.own ⟨0, Nat.zero_lt_one⟩)) (.val (.int 1)))] }],
    init := { time := 0, machines := [{ ctrl := 0, vars := [.int 0] }],
              pending := [{ time := 0, event := 0, payload := [] }, { time := 1, event := 0, payload := [] },
                          { time := 2, event := 0, payload := [] }] },
    faults := [{ kind := .drop, event := 0, occ := .exactly 2 }] }

/-- The last state of a run of the scheduler. -/
def lastOf (l : List State) : Option State := l.getLast?

/-- **A `drop` fault with occurrence 2 drops exactly the second delivery**: under the mask that
activates it, three deliveries leave the counter at 2, with three attempts counted. -/
theorem drop_second_delivery :
    (lastOf (Exec.run dropSys 3 (.run [true] (dropSys.initCfg [true])) {}).states).map (·.cfg) =
      some { time := 2, machines := [{ ctrl := 0, vars := [.int 2] }], pending := [], attempts := [3] } := by
  decide

/-- Under the other mask, the fault is off and the counter reaches 3. -/
theorem drop_fault_optional :
    (lastOf (Exec.run dropSys 3 (.run [false] (dropSys.initCfg [false])) {}).states).map (·.cfg) =
      some { time := 2, machines := [{ ctrl := 0, vars := [.int 3] }], pending := [], attempts := [3] } := by
  decide


/-! ### A bounded counter, by an inductive invariant -/

abbrev ctrS : Sig := { machines := 1, vars := fun _ => [Ty.num], states := fun _ => ["s"] }

def ctrT (L : Int) (m : Fin 1) : Trans ctrS m :=
  { src := ⟨0, Nat.zero_lt_one⟩, dst := ⟨0, Nat.zero_lt_one⟩, event := 0,
    guard := .bin .lt (.ref (.own ⟨0, Nat.zero_lt_one⟩)) (.val (.int L)),
    effects := [.set ⟨0, Nat.zero_lt_one⟩
        (.bin (.arith .add .untyped) (.ref (.own ⟨0, Nat.zero_lt_one⟩)) (.val (.int 1))),
      .emit 0 1 []] }

def ctrSys (L : Int) : Sys :=
  { sig := ctrS, trans := fun m => match m with | ⟨0, _⟩ => [ctrT L ⟨0, Nat.zero_lt_one⟩],
    init := { time := 0, machines := [{ ctrl := 0, vars := [.int 0] }], pending := [{ time := 0, event := 0, payload := [] }] } }


theorem ctr_guard (L : Int) (n : Nat) (cx : Ctx) (hc : cx.own = { ctrl := 0, vars := [.int n] }) :
    Expr.eval cx (.bin .lt (.ref (.own ⟨0, Nat.zero_lt_one⟩)) (.val (.int L)) : Expr ctrS ⟨0, Nat.zero_lt_one⟩) = .ok (.bool (decide ((n : Int) < L))) := by
  obtain ⟨sn, tm, own, pl⟩ := cx
  simp only at hc
  subst hc
  rfl

theorem ctr_scan (L : Int) (c : Cfg) (e : Entry) (n : Nat) (hm : c.machines = [{ ctrl := 0, vars := [.int n] }]) (he : e.event = 0) :
    scan (ctrSys L) [] c e ⟨0, Nat.zero_lt_one⟩ { ctrl := 0, vars := [.int n] } (finList ((ctrSys L).trans ⟨0, Nat.zero_lt_one⟩).length) =
      .ok (if (n : Int) < L then some ⟨0, Nat.zero_lt_one⟩ else none) := by
  show scan (ctrSys L) [] c e ⟨0, Nat.zero_lt_one⟩ { ctrl := 0, vars := [.int n] } [⟨0, Nat.zero_lt_one⟩] = _
  have hg := ctr_guard L n (ctxOf c e { ctrl := 0, vars := [.int n] }) rfl
  simp only [scan]
  show (if _ then _ else _) = _
  have hsrc : ((ctrSys L).trans ⟨0, Nat.zero_lt_one⟩).get ⟨0, Nat.zero_lt_one⟩ = ctrT L ⟨0, Nat.zero_lt_one⟩ := rfl
  simp only [hsrc]
  simp only [ctrT, he, hg]
  erw [hg]
  by_cases h : (n : Int) < L <;> simp [h]

theorem ctr_winners (L : Int) (c : Cfg) (e : Entry) (n : Nat) (hm : c.machines = [{ ctrl := 0, vars := [.int n] }]) (he : e.event = 0)
    (ht : e.target = none) (hr : e.routes = none) :
    winners (ctrSys L) [] c e = .ok (if (n : Int) < L then [⟨⟨0, Nat.zero_lt_one⟩, ⟨0, Nat.zero_lt_one⟩⟩] else []) := by
  unfold winners addressed liveAt
  simp only [ht, hr]
  have hf : finList (ctrSys L).sig.machines = [⟨0, Nat.zero_lt_one⟩] := rfl
  rw [hf]
  simp only [List.filter, Option.all, Option.getD, List.all_nil, Bool.and_self, hm, List.getElem?_cons_zero,
    Option.map_some, winnersOf, choose, at?]
  rw [ctr_scan L c e n hm he]
  by_cases h : (n : Int) < L <;> simp [h]

theorem ctr_rhs (n : Nat) (cx : Ctx) (hc : cx.own = { ctrl := 0, vars := [.int n] }) (hn : (n : Int) + 1 ≤ 9007199254740991) :
    Expr.eval cx (.bin (.arith .add .untyped) (.ref (.own ⟨0, Nat.zero_lt_one⟩)) (.val (.int 1)) : Expr ctrS ⟨0, Nat.zero_lt_one⟩) = .ok (.int ((n : Int) + 1)) := by
  obtain ⟨sn, tm, own, pl⟩ := cx
  simp only at hc
  subst hc
  have hm0 : maxSafe = 9007199254740991 := rfl
  have h1 : -maxSafe ≤ (n : Int) := by rw [hm0]; omega
  have h2 : (n : Int) ≤ maxSafe := by rw [hm0]; omega
  have h3 : -maxSafe ≤ (1 : Int) := by rw [hm0]; omega
  have h4 : (1 : Int) ≤ maxSafe := by rw [hm0]; omega
  have h5 : -maxSafe ≤ (n : Int) + 1 := by rw [hm0]; omega
  have h6 : (n : Int) + 1 ≤ maxSafe := by rw [hm0]; omega
  simp [Expr.eval, Ref.eval, at?, BOp.apply, arithVals, AOp.apply, checked, ATy.holds, ATy.lo, ATy.hi, h1, h2, h3, h4, h5, h6]

theorem ctr_effects (L : Int) (c : Cfg) (e : Entry) (n : Nat) (hm : c.machines = [{ ctrl := 0, vars := [.int n] }])
    (hn : (n : Int) + 1 ≤ 9007199254740991) (hT : c.time + 1 < timeLimit) :
    runEffects c e (ctrT L ⟨0, Nat.zero_lt_one⟩).effects { ctrl := 0, vars := [.int n] } =
      .ok ({ ctrl := 0, vars := [.int ((n : Int) + 1)] }, ([{ time := c.time + 1, event := 0, payload := [], sender := some 0 }], [])) := by
  have hr := ctr_rhs n (ctxOf c e { ctrl := 0, vars := [.int n] }) rfl hn
  have hm0 : maxSafe = 9007199254740991 := rfl
  have hfit : Val.check ((ctrS.vars (⟨0, Nat.zero_lt_one⟩ : Fin ctrS.machines)).get ⟨0, by decide⟩) (.int ((n : Int) + 1)) = .ok (.int ((n : Int) + 1)) := by
    show Val.check Ty.num _ = _
    simp only [Val.check, Val.fits, hm0]
    have h5 : -9007199254740991 ≤ (n : Int) + 1 := by omega
    simp [h5, hn]
  have hl : ¬ timeLimit ≤ c.time + 1 := Nat.not_le.mpr hT
  simp only [ctrT, runEffects]
  generalize timeLimit = T at *
  erw [hr]
  split
  · rename_i err h; cases h
  · rename_i x h
    cases h
    split
    · rename_i err h; rw [hfit] at h; cases h
    · rename_i x' h
      rw [hfit] at h
      cases h
      rw [if_pos (by simp), if_neg hl]
      rfl


theorem ctr_fireOne (L : Int) (c : Cfg) (e : Entry) (n : Nat) (hm : c.machines = [{ ctrl := 0, vars := [.int n] }])
    (hn : (n : Int) + 1 ≤ 9007199254740991) (hT : c.time + 1 < timeLimit) :
    fireOne (ctrSys L) c e ⟨⟨0, Nat.zero_lt_one⟩, ⟨0, Nat.zero_lt_one⟩⟩ { ctrl := 0, vars := [.int n] } =
      .ok ({ ctrl := 0, vars := [.int ((n : Int) + 1)] }, ([{ time := c.time + 1, event := 0, payload := [], sender := some 0 }], [])) := by
  have h := ctr_effects L c e n hm hn hT
  simp only [fireOne]
  rw [show runEffects c e (((ctrSys L).trans ⟨0, Nat.zero_lt_one⟩).get ⟨0, Nat.zero_lt_one⟩).effects { ctrl := 0, vars := [.int n] } = _ from h]
  rfl

theorem ctr_phase2 (L : Int) (c : Cfg) (e : Entry) (n : Nat) (hm : c.machines = [{ ctrl := 0, vars := [.int n] }])
    (hn : (n : Int) + 1 ≤ 9007199254740991) (hT : c.time + 1 < timeLimit) :
    phase2 (ctrSys L) c e [⟨⟨0, Nat.zero_lt_one⟩, ⟨0, Nat.zero_lt_one⟩⟩] [{ ctrl := 0, vars := [.int n] }] =
      .ok ([{ ctrl := 0, vars := [.int ((n : Int) + 1)] }], [(0, ([{ time := c.time + 1, event := 0, payload := [], sender := some 0 }], []))]) := by
  simp only [phase2, List.getElem?_cons_zero]
  rw [ctr_fireOne L c e n hm hn hT]
  rfl

def ctrVal (s : State) : Option Val := s.cfg.machines[0]?.bind (fun ms => ms.vars[0]?)

def CtrI (L : Int) (s : State) : Prop :=
  ∃ (n t : Nat) (p : List Entry) (a : List Nat), (n : Int) ≤ L ∧ t ≤ n ∧
    (p = [] ∨ ∃ snd : Option Nat, p = [{ time := n, event := 0, payload := [], sender := snd }]) ∧
    s = .run [] { time := t, machines := [{ ctrl := 0, vars := [.int n] }], pending := p, attempts := a }

theorem ctr_active (L : Int) : (ctrSys L).active [] = [] := rfl

theorem ctr_step (L : Int) (hL : L < 9007199254740991) {s' : State} {l : Label} {n t : Nat}
    {p : List Entry} {a : List Nat} (hn : (n : Int) ≤ L) (ht : t ≤ n)
    (hp : p = [] ∨ ∃ snd : Option Nat, p = [{ time := n, event := 0, payload := [], sender := snd }])
    (h : Step (ctrSys L) [] { time := t, machines := [{ ctrl := 0, vars := [.int n] }], pending := p, attempts := a } l s') :
    CtrI L s' := by
  obtain ⟨hd, hr⟩ := Step.ready h
  obtain ⟨snd, hent⟩ : ∃ snd : Option Nat, p = [{ time := n, event := 0, payload := [], sender := snd }] := by
    rcases hp with rfl | h
    · exact absurd hr.1 (by simp)
    · exact h
  subst hent
  have hle : l.entry = { time := n, event := 0, payload := [], sender := snd } := List.mem_singleton.mp hr.1
  have hTL : timeLimit = 9007199254740992 := rfl
  have hmach : (ctrSys L).sig.machines = 1 := rfl
  cases h with
  | drop _ _ _ _ _ hdr => rw [ctr_active] at hdr; simp [dropHit] at hdr
  | delay _ _ _ _ _ _ hf => rw [ctr_active] at hf; simp [delayFault] at hf
  | delayTimeErr _ _ _ _ _ _ hf => rw [ctr_active] at hf; simp [delayFault] at hf
  | worldOk _ _ hk => exact absurd (by rw [hle]) hk
  | worldErr _ _ hk => exact absurd (by rw [hle]) hk
  | routeErr _ _ _ hro => rw [routeOf_nil rfl] at hro; cases hro
  | deliverOk hd hr _ hro hdr hnone hw hp2 hs hfit hfill hdup =>
    obtain ⟨rfl, rfl, -⟩ := routeOf_nil_eq (sys := ctrSys L) rfl hro
    obtain ⟨-, rfl⟩ := nores_settle (sys := ctrSys L) rfl rfl hs hfit hfill
    generalize hS : (ctrSys L).resolve l.draws = S at *
    have hS' := hS.symm.trans (resolve_nil (sys := ctrSys L) rfl l.draws)
    subst hS'
    rw [hle] at hw hp2 hdup
    rw [ctr_active] at hw hdup
    rw [ctr_winners L _ _ n rfl rfl rfl rfl] at hw
    have hn1 : (n : Int) + 1 ≤ 9007199254740991 := by omega
    have hT1 : n + 1 < timeLimit := by rw [hTL]; omega
    by_cases hlt : (n : Int) < L
    · rw [if_pos hlt] at hw
      cases hw
      change phase2 (ctrSys L) _ _ _ [{ ctrl := 0, vars := [.int n] }] = _ at hp2
      rw [ctr_phase2 L _ _ n rfl hn1 hT1] at hp2
      cases hp2
      cases hdup with
      | none h0 =>
        exact ⟨n + 1, n, [{ time := n + 1, event := 0, payload := [], sender := some 0 }], setAt a 0 (a.getD 0 0 + 1), by omega, by omega, Or.inr ⟨some 0, rfl⟩, by simp [Cfg.putAll, Entry.isEvent, Cfg.commit, Cfg.popE, Cfg.bumpAttempts, inMachineOrder, blockOf, isTimerOf, touchedOf, Cfg.attemptsOf, hmach, List.range_succ, insertByTime]⟩
      | some h0 hl => simp [dupFault] at h0
    · rw [if_neg hlt] at hw
      cases hw
      simp only [phase2] at hp2
      cases hp2
      cases hdup with
      | none h0 =>
        exact ⟨n, n, [], setAt a 0 (a.getD 0 0 + 1), by omega, by omega, Or.inl rfl, by simp [Cfg.putAll, Entry.isEvent, Cfg.commit, Cfg.popE, Cfg.bumpAttempts, inMachineOrder, blockOf, isTimerOf, touchedOf, Cfg.attemptsOf, hmach, List.range_succ, insertByTime]⟩
      | some h0 hl => simp [dupFault] at h0
  | deliverErr hd hr _ hro hdr hnone hfail =>
    obtain ⟨rfl, rfl, -⟩ := routeOf_nil_eq (sys := ctrSys L) rfl hro
    generalize hS : (ctrSys L).resolve l.draws = S at *
    have hS' := hS.symm.trans (resolve_nil (sys := ctrSys L) rfl l.draws)
    subst hS'
    rw [hle, ctr_active] at hfail
    have hn1 : (n : Int) + 1 ≤ 9007199254740991 := by omega
    have hT1 : n + 1 < timeLimit := by rw [hTL]; omega
    cases hfail with
    | winners _ hw => rw [ctr_winners L _ _ n rfl rfl rfl rfl] at hw; cases hw
    | settle _ _ hs _ hfill => exact (nores_settle_err (sys := ctrSys L) rfl rfl hs hfill).elim
    | phase2 _ hw hp2 =>
      rw [ctr_winners L _ _ n rfl rfl rfl rfl] at hw
      by_cases hlt : (n : Int) < L
      · rw [if_pos hlt] at hw
        cases hw
        change phase2 (ctrSys L) _ _ _ [{ ctrl := 0, vars := [.int n] }] = _ at hp2
        rw [ctr_phase2 L _ _ n rfl hn1 hT1] at hp2; cases hp2
      · rw [if_neg hlt] at hw
        cases hw
        simp only [phase2] at hp2; cases hp2
    | dup _ _ _ _ _ h0 _ => simp [dupFault] at h0

/-- **The counter never exceeds its bound**, for every bound below `2^53 - 1`, by an inductive
invariant (no unfolding of `deliver` on concrete times). -/
theorem ctr_le : ∀ L : Int, 0 ≤ L → L < 2 ^ 53 - 1 →
    (Sys.lts (ctrSys L)).Invariant (fun s => s.ok = true ∧ ∀ v, ctrVal s = some (.int v) → v ≤ L) := by
  intro L hL0 hL
  have h53 : (2 : Int) ^ 53 = 9007199254740992 := by decide
  rw [h53] at hL
  have hL' : L < 9007199254740991 := by omega
  refine safe_of_inductive (I := CtrI L) ⟨?_, ?_⟩ ?_
  · intro s hs
    have hs' := init_of_no_faults (sys := ctrSys L) rfl hs
    subst hs'
    exact ⟨0, 0, [{ time := 0, event := 0, payload := [] }], [], hL0, Nat.le_refl _, Or.inr ⟨none, rfl⟩, rfl⟩
  · intro s l t hs hst
    obtain ⟨n, tt, p, a, hn, ht, hp, rfl⟩ := hs
    exact ctr_step L hL' hn ht hp hst
  · intro s hs
    obtain ⟨n, tt, p, a, hn, ht, hp, rfl⟩ := hs
    refine ⟨rfl, fun v hv => ?_⟩
    simp only [ctrVal, State.cfg] at hv
    simp at hv
    omega

/-! ### A system whose only randomness is a two-outcome choice -/

abbrev chS : Sig := { machines := 1, vars := fun _ => [Ty.num], states := fun _ => ["s"] }

def chT (m : Fin 1) : List (Trans chS m) :=
  [{ src := ⟨0, Nat.zero_lt_one⟩, dst := ⟨0, Nat.zero_lt_one⟩, event := 0, guard := .val (.bool true),
     effects := [.emit 1 0 []] },
   { src := ⟨0, Nat.zero_lt_one⟩, dst := ⟨0, Nat.zero_lt_one⟩, event := 1, guard := .val (.bool true),
     effects := [.set ⟨0, Nat.zero_lt_one⟩ (.ref .time)] }]

/-- The only randomness is a two-outcome `choice`: the delay of the second event. -/
def chSys : Sys :=
  { sig := chS, trans := fun m => match m with | ⟨0, _⟩ => chT ⟨0, Nat.zero_lt_one⟩,
    init := { time := 0, machines := [{ ctrl := 0, vars := [.int 0] }], pending := [{ time := 0, event := 0, payload := [] }] },
    samples := [(0, 0, 0, .choice [3, 5])] }

def chX (s : State) : Option Val := s.cfg.machines[0]?.bind (fun ms => ms.vars[0]?)

def chGood (s : State) : Bool := s.ok && (match chX s with
  | some (.int v) => v == 0 || v == 3 || v == 5
  | _ => false)

def chBad (s : State) : Bool := s.ok && (match chX s with
  | some (.int v) => v != 5
  | _ => false)

example : chSys.WF := by decide

example : (Exec.successors chSys (.run [] chSys.init)).length = 2 := by decide
def chC1 (d : Nat) : Cfg :=
  { time := 0, machines := [{ ctrl := 0, vars := [.int 0] }], pending := [{ time := d, event := 1, payload := [], sender := some 0 }], attempts := [1] }
def chC2 (d : Nat) : Cfg :=
  { time := d, machines := [{ ctrl := 0, vars := [.int d] }], pending := [], attempts := [1, 1] }

def chL : List State :=
  [.run [] chSys.init, .run [] (chC1 3), .run [] (chC1 5), .run [] (chC2 3), .run [] (chC2 5)]

set_option maxRecDepth 100000 in
theorem choice_safe : (Sys.lts chSys).Invariant (fun s => chGood s = true) :=
  checkClosed_sound (Exec.enum chSys) chL chGood (by decide)

set_option maxRecDepth 100000 in
/-- A variant of the invariant that fails for the outcome 5 is refuted by `Exec.cex_refutes`, in
its kernel-evaluable form: the list-based search, equal in result to `Gen.search`, finds the
counterexample by `decide` (no `native_decide`, no `Lean.ofReduceBool`). -/
theorem choice_unsafe : ¬ (Sys.lts chSys).Invariant (fun s => chBad s = true) :=
  Exec.cex_refutesL (bound := 3) (cap := 100) (by decide)

set_option maxRecDepth 100000 in
/-- The invariant that holds for both outcomes, also proved through the list-based search. -/
theorem choice_safe_search : (Sys.lts chSys).Invariant (fun s => chGood s = true) :=
  Exec.holds_invariantL (bound := 3) (cap := 100) (by decide)

end Exegra.Core.Behav.Examples

/-- info: 'Exegra.Core.Behav.phase2_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.phase2_perm

/-- info: 'Exegra.Core.Behav.phase2_perm_emitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.phase2_perm_emitted

/-- info: 'Exegra.Core.Behav.winners_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.winners_nodup

/-- info: 'Exegra.Core.Behav.deliver_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.deliver_perm

/-- info: 'Exegra.Core.Behav.mask_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.mask_const

/-- info: 'Exegra.Core.Behav.shaped_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.shaped_invariant

/-- info: 'Exegra.Core.Behav.deliver_ne_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.deliver_ne_shape

/-- info: 'Exegra.Core.Behav.shape_unreachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.shape_unreachable

/-- info: 'Exegra.Core.Behav.Expr.eval_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Expr.eval_fits

/-- info: 'Exegra.Core.Behav.time_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.time_invariant

/-- info: 'Exegra.Core.Behav.sorted_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.sorted_invariant

/-- info: 'Exegra.Core.Behav.deliver_ne_sort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.deliver_ne_sort

/-- info: 'Exegra.Core.Behav.sort_unreachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.sort_unreachable

/-- info: 'Exegra.Core.Behav.wf_shaped_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.wf_shaped_invariant

/-- info: 'Exegra.Core.Behav.Expr.eval_ne_sort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Expr.eval_ne_sort

/-- info: 'Exegra.Core.Behav.Exec.step_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Exec.step_sound

/-- info: 'Exegra.Core.Behav.Exec.step_failed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Exec.step_failed

/-- info: 'Exegra.Core.Behav.Exec.idle_deadlocked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Exec.idle_deadlocked

/-- info: 'Exegra.Core.Behav.Exec.stopped_deadlocked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Exec.stopped_deadlocked

/-- info: 'Exegra.Core.Behav.Exec.step_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Exec.step_live

/-- info: 'Exegra.Core.Behav.run_reach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.run_reach

/-- info: 'Exegra.Core.Behav.successors_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.successors_complete

/-- info: 'Exegra.Core.Behav.successors_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.successors_sound

/-- info: 'Exegra.Core.Behav.Exec.covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Exec.covers

/-- info: 'Exegra.Core.Behav.Exec.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Exec.sound

/-- info: 'Exegra.Core.Behav.Exec.holds_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Exec.holds_invariant

/-- info: 'Exegra.Core.Behav.Exec.cex_refutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Exec.cex_refutes

/-- info: 'Exegra.Core.Behav.Examples.f4_ab_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.f4_ab_safe

/-- info: 'Exegra.Core.Behav.Examples.f4_ba_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.f4_ba_safe

/-- info: 'Exegra.Core.Behav.Examples.f4_ab_safe_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.f4_ab_safe_closed

/-- info: 'Exegra.Core.Behav.Examples.f4_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.f4_wf

/-- info: 'Exegra.Core.Behav.Examples.f4_exec_same_machines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.f4_exec_same_machines

/-- info: 'Exegra.Core.Behav.Examples.f4_next_reads_differ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.f4_next_reads_differ

/-- info: 'Exegra.Core.Behav.Examples.f4_ab_no_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.f4_ab_no_shape

/-- info: 'Exegra.Core.Behav.Examples.divZero_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.divZero_counterexample

/-- info: 'Exegra.Core.Behav.Examples.mod_truncates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.mod_truncates

/-- info: 'Exegra.Core.Behav.Examples.typed_div_truncates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.typed_div_truncates

/-- info: 'Exegra.Core.Behav.Examples.u8_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.u8_overflow

/-- info: 'Exegra.Core.Behav.Examples.emitted_inserted_by_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.emitted_inserted_by_time

/-- info: 'Exegra.Core.Behav.Examples.emission_order_irrelevant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.emission_order_irrelevant

/-- info: 'Exegra.Core.Behav.Examples.timer_then_cancel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.timer_then_cancel

/-- info: 'Exegra.Core.Behav.Examples.timer_reset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.timer_reset

/-- info: 'Exegra.Core.Behav.Examples.drop_second_delivery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.drop_second_delivery

/-- info: 'Exegra.Core.Behav.Examples.drop_fault_optional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.drop_fault_optional

/-- info: 'Exegra.Core.Behav.deliver_iff_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.deliver_iff_step

/-- info: 'Exegra.Core.Behav.pending_perm_bisim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.pending_perm_bisim

/-- info: 'Exegra.Core.Behav.target_only' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.target_only

/-- info: 'Exegra.Core.Behav.Examples.ctr_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.ctr_le

/-- info: 'Exegra.Core.Behav.sample_mem_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.sample_mem_support

/-- info: 'Exegra.Core.Behav.successorsUpTo_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.successorsUpTo_eq

/-- info: 'Exegra.Core.Behav.Exec.stopped_deadlocked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Exec.stopped_deadlocked

/-- info: 'Exegra.Core.Behav.Examples.choice_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.choice_safe

/-- info: 'Exegra.Core.Behav.Examples.choice_unsafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.choice_unsafe

/-- info: 'Exegra.Core.Behav.Examples.choice_safe_search' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.choice_safe_search

/-- info: 'Exegra.Core.Behav.phase2_eq_par' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.phase2_eq_par

/-- info: 'Exegra.Core.Behav.Examples.agg_last_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.agg_last_safe

/-- info: 'Exegra.Core.Behav.Examples.agg_first_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.agg_first_safe

/-- info: 'Exegra.Core.Behav.Examples.agg_next_reads_differ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.agg_next_reads_differ

/-- info: 'Exegra.Core.Behav.Examples.reply_reaches_requester' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.reply_reaches_requester

/-- info: 'Exegra.Core.Behav.Examples.reply_without_sender_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.Examples.reply_without_sender_fails
