import Exegra.Core.BehavExamples
import Exegra.Semantics
import Exegra.Format2

open Exegra.Core.LTS Exegra.Core.Behav Exegra.Core.Behav.Examples

namespace ReviewM21

def sm {α : Type} : Except Err α → Sum Err α | .ok a => .inr a | .error e => .inl e
def showV : Except String Exegra.Value → String | .ok v => "ok " ++ Exegra.Json.write v | .error e => "error: " ++ e

/-! ## D1. Emission order: same machines, different pending lists, different next step -/

/-- Two machines; on event 0, machine m emits event (m+1) after 0. -/
def emSig : Sig := { machines := 2, vars := fun _ => [], states := fun _ => ["s"] }
def emSt (m : Fin 2) : Fin (emSig.states m).length := ⟨0, Nat.zero_lt_one⟩
def emitT (m : Fin 2) : Trans emSig m :=
  { src := emSt m, dst := emSt m, event := 0, guard := .val (.bool true),
    effects := [.emit (m.val + 1) 0 []] }
def emSys : Sys :=
  { sig := emSig, trans := fun m => [emitT m],
    init := { time := 0, machines := [⟨0, []⟩, ⟨0, []⟩], pending := [⟨0, 0, []⟩] } }
def w0 : Winner emSys := ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
def w1 : Winner emSys := ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
def c0 : Cfg := { emSys.init with pending := [] }
def e0 : Entry := ⟨0, 0, []⟩

-- machines agree (phase2_perm) ...
example : (phase2 emSys c0 e0 [w0, w1] c0.machines).toOption.map Prod.fst =
          (phase2 emSys c0 e0 [w1, w0] c0.machines).toOption.map Prod.fst := by decide
-- ... but the emitted lists, hence the pending queue, hence the configuration, differ
#eval (phase2 emSys c0 e0 [w0, w1] c0.machines).toOption.map Prod.snd
#eval (phase2 emSys c0 e0 [w1, w0] c0.machines).toOption.map Prod.snd
example : (phase2 emSys c0 e0 [w0, w1] c0.machines).toOption.map Prod.snd ≠
          (phase2 emSys c0 e0 [w1, w0] c0.machines).toOption.map Prod.snd := by decide

/-- the step with reversed winner order (what a different listing / scheduler would do) -/
def deliverRev (sys : Sys) (c : Cfg) (k : Nat) : Option (Except Err Cfg) :=
  deliverWith sys (fun c e ws ms => phase2 sys c e ws.reverse ms) c k
-- the whole step is NOT order-independent as a function to Cfg/State:
example : (deliver emSys emSys.init 0).map (·.toOption) ≠ (deliverRev emSys emSys.init 0).map (·.toOption) := by decide
-- and a state predicate distinguishes them: "label 0 delivers event 1 next"
example : ((deliver emSys emSys.init 0).bind (·.toOption)).map (fun c => (c.pending[0]?).map (·.event)) = some (some 1) := by decide
example : ((deliverRev emSys emSys.init 0).bind (·.toOption)).map (fun c => (c.pending[0]?).map (·.event)) = some (some 2) := by decide

/-! ## D1b. Winners are Nodup -- provable, but not stated in Behav.lean -/

theorem finList_nodup : (n : Nat) → (finList n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
    simp only [finList]
    refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · simp only [List.mem_map, not_exists, not_and]
      intro x _ h; exact absurd h (Fin.succ_ne_zero x)
    · exact List.pairwise_map.mpr ((finList_nodup n).imp fun h e => h (Fin.succ_inj.mp e))

theorem winnersOf_sublist {sys : Sys} {c : Cfg} {e : Entry} :
    (ms : List (Fin sys.sig.machines)) → (ws : List (Winner sys)) →
    winnersOf sys c e ms = .ok ws → (ws.map (·.mach)).Sublist ms
  | [], ws, h => by simp [winnersOf] at h; subst h; simp
  | m :: ms, ws, h => by
    simp only [winnersOf] at h
    split at h
    · cases h
    · rename_i w hw
      split at h
      · cases h
      · rename_i ws' hws
        have ih := winnersOf_sublist ms ws' hws
        cases h
        cases w with
        | none => exact ih.cons m
        | some w =>
          have : w.mach = m := by
            unfold choose at hw
            revert hw
            cases at? c.machines m.val with
            | error _ => intro hw; cases hw
            | ok own =>
              simp only
              cases scan sys c e m own (finList (sys.trans m).length) with
              | error _ => intro hw; cases hw
              | ok r => cases r with
                | none => intro hw; cases hw
                | some i => intro hw; cases hw; rfl
          simp only [List.map_cons, this]
          exact ih.cons_cons m

theorem winners_nodup {sys : Sys} {c : Cfg} {e : Entry} {ws : List (Winner sys)}
    (h : winners sys c e = .ok ws) : (ws.map (·.mach)).Nodup :=
  (winnersOf_sublist _ ws h).nodup (finList_nodup _)

/-! ## D2. `%` and `/` differ from format 2 -/

-- calculus: Int.emod
#eval BOp.apply .mod (.int (-7)) (.int 2)
-- format 2 (untyped and i32): truncated remainder
#eval showV <| (Exegra.compile "(0 - 7) % 2") >>= Exegra.eval (fun _ => .undef) Exegra.TyEnv.untyped
def i32x : Exegra.TyEnv := fun p => if p == ["x"] then .int .i32 else .none
#eval showV <| (Exegra.compile "x % 2") >>= Exegra.eval (fun p => if p == ["x"] then .num (-7) else .undef) i32x
-- typed integer division: format 2 truncates, the calculus errors
#eval showV <| (Exegra.compile "x / 2") >>= Exegra.eval (fun p => if p == ["x"] then .num 7 else .undef) i32x
#eval BOp.apply .div (.int 7) (.int 2)
example : sm (BOp.apply .mod (.int (-7)) (.int 2)) = .inr (.int 1) := by decide

/-! ## D3. Overflow is not relative to declared types (except at `set`) -/
def u8x : Exegra.TyEnv := fun p => if p == ["x"] then .int .u8 else .none
-- format 2: x : u8 = 200, guard `x + 100 > 255` fails the step
#eval showV <| (Exegra.compile "x + 100 > 255") >>= Exegra.eval (fun p => if p == ["x"] then .num 200 else .undef) u8x
-- calculus: same guard on a u8 variable evaluates to true
def u8Sig : Sig := { machines := 1, vars := fun _ => [Ty.int 0 255], states := fun _ => ["s"] }
def gx : Expr u8Sig ⟨0, by decide⟩ :=
  .bin .lt (.val (.int 255)) (.bin .add (.ref (.own ⟨0, by decide⟩)) (.val (.int 100)))
#eval gx.eval { snap := [⟨0, [.int 200]⟩], time := 0, own := ⟨0, [.int 200]⟩, payload := [] }
example : sm (gx.eval { snap := [⟨0, [.int 200]⟩], time := 0, own := ⟨0, [.int 200]⟩, payload := [] })
    = .inr (.bool true) := by decide

/-! ## D4. `Expr.ty?` is not sound for `eval` (literals, time, fields) -/
def big : Expr u8Sig ⟨0, by decide⟩ := .val (.int (2 ^ 60))
example : big.ty? = some Ty.num ∧
    (big.eval { snap := [], time := 0, own := ⟨0, []⟩, payload := [] }).toOption.map (·.fits Ty.num) = some false := by
  decide
def fld : Expr u8Sig ⟨0, by decide⟩ := .ref (.field 7 (.int 0 255))
example : fld.ty? = some (.int 0 255) ∧
    (fld.eval { snap := [], time := 0, own := ⟨0, []⟩, payload := [(7, .int 1000)] }).toOption.map (·.fits (.int 0 255)) = some false := by
  decide

/-! ## D5. `Err.shape` reachable from an ill-shaped init (no Sys.WF) -/
def badF4 : Sys := { f4AB with init := { f4Init with machines := [⟨0, [.int 0]⟩] } }
example : (deliver badF4 badF4.init 0).map sm = some (.inl .shape) := by decide

/-! ## D6. Format-2 queue is time-sorted, the calculus appends -/
def oSig : Sig := { machines := 1, vars := fun _ => [], states := fun _ => ["s"] }
def oT (m : Fin 1) : Trans oSig m :=
  { src := ⟨0, Nat.zero_lt_one⟩, dst := ⟨0, Nat.zero_lt_one⟩, event := 0, guard := .val (.bool true),
    effects := [.emit 1 5 []] }
def oInit : Cfg := { time := 0, machines := [⟨0, []⟩], pending := [⟨0, 0, []⟩, ⟨10, 2, []⟩] }
def oSys : Sys := { sig := oSig, trans := fun m => [oT m], init := oInit }
-- after the step the calculus queue is [t=10, t=5]; format 2's insertE would give [t=5, t=10]
#eval ((deliver oSys oSys.init 0).bind (·.toOption)).map (fun c => c.pending.map (·.time))

end ReviewM21
#print axioms ReviewM21.winners_nodup
