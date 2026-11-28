import Exegra.ProveB
import Exegra.Core.BehavLive

/-
`exegra prove`, model checking part (WG-5682): closed-set certificates for invariants, and liveness
claims under weak fairness.

* **Certificates.** For an invariant the explorer proves (`holds`, an empty frontier), `certificate`
  gives the states it visited, written as Lean terms (`stateLean`). The proof file states
  `checkClosed (Exec.enum sys) L p = true` for that list `L` and derives the invariant by
  `checkClosed_sound`; removing a state from `L` makes the check false.
* **Liveness.** A claim `GF p` or `FG p` on the states of a scenario, under weak fairness of the
  entries that can fire the declared fair transitions (`fairLabels`), is decided by
  `liveVerdict`: `proved` by the ranking search (`rankProves`, `GF` only), `violated` by the lasso
  search (`lassoSearch`, whose result may be a Zeno lasso), `incomplete` when the reachable states
  were not all found within the bound and the cap, and `not supported` otherwise. A state that
  failed (`s.ok = false`) violates `p`. `liveVerdictOf_proved` and `liveVerdictOf_violated` give the
  meaning of the verdict a proof file states.
-/

namespace Exegra.V2.ProveLive

open Exegra
open Exegra.V2.B
open Exegra.V2.ProveB
open Exegra.Core.LTS

abbrev State := Core.Behav.State
abbrev Label := Core.Behav.Label

/-! ### Systems and predicates of an input text -/

/-- The system with no machine (what a refused input gives). -/
def emptySys : Core.Behav.Sys :=
  { sig := ⟨0, fun _ => [], fun _ => []⟩, trans := fun _ => [], init := { time := 0, machines := [], pending := [] } }

/-- The elaborated system of an input text (`emptySys` when it is refused). -/
def sysOfText (text : String) : Core.Behav.Sys :=
  match prepareText text with
  | some (sys, _) => sys
  | none => emptySys

/-- A claim's state invariant on the states of an input text: running, and the expression true. -/
def invP (text src : String) : State → Bool :=
  match prepareText text with
  | some (_, I) => fun s => s.ok && claimInvB I src s
  | none => fun _ => false

/-- **The invariant a closed-set certificate proves**, in the form `s.ok = true ∧ P s`. -/
theorem invariant_of_certificate {text src : String} {L : List State}
    (h : checkClosed (Core.Behav.Exec.enum (sysOfText text)) L (invP text src) = true) :
    (Core.Behav.Sys.lts (sysOfText text)).Invariant (fun s => s.ok = true ∧ invP text src s = true) := by
  intro s hs
  have := checkClosed_sound _ L _ h s hs
  refine ⟨?_, this⟩
  unfold invP at this
  cases hp : prepareText text with
  | none => rw [hp] at this; cases this
  | some v =>
    obtain ⟨_, I⟩ := v
    rw [hp] at this
    simp only [Bool.and_eq_true] at this
    exact this.1

/-! ### States as Lean terms -/

def valLean : Core.Behav.Val → String
  | .int n => s!"(.int ({n}))"
  | .bool b => s!"(.bool {b})"
  | .str x => s!"(.str {x.quote})"
  | .lit c j => s!"(.lit {c.quote} {j.quote})"
  | .rat q => s!"(.rat (mkRat ({q.num}) {q.den}))"

def listLean {β : Type} (f : β → String) (xs : List β) : String :=
  "[" ++ ", ".intercalate (xs.map f) ++ "]"

def optLean (o : Option Nat) : String :=
  match o with
  | none => "none"
  | some n => s!"(some {n})"

def fieldsLean (pl : List (Nat × Core.Behav.Val)) : String :=
  listLean (fun (p : Nat × Core.Behav.Val) => s!"({p.1}, {valLean p.2})") pl

def distLeanW : Core.Behav.Dist → String
  | .fixed v => s!"(.fixed {v})"
  | .choice vs => s!"(.choice {listLean toString vs})"
  | .uniform lo hi => s!"(.uniform {lo} {hi})"
  | .table pts => s!"(.table {listLean (fun (p : Nat × Nat) => s!"({p.1}, {p.2})") pts})"

def reqKindLeanW : Res.ReqKind → String
  | .use => ".use" | .acquire => ".acquire"

def infoLean (i : Core.Behav.RInfo) : String :=
  s!"\{ thenEv := {i.thenEv}, refused := {optLean i.refused}, payload := {fieldsLean i.payload}, " ++
  s!"demand := {distLeanW i.demand}, site := ({i.site.1}, {i.site.2}) }"

/-- A request of the world as a Lean term (WG-5683: certificates carry the world). -/
def reqLean (r : Core.Behav.RReq) : String :=
  s!"\{ id := {r.id}, owner := {r.owner}, cls := {r.cls}, units := {r.units}, since := {r.since}, " ++
  s!"kind := {reqKindLeanW r.kind}, info := {infoLean r.info} }"

def holdLean (h : Res.Hold Nat) : String :=
  s!"\{ owner := {h.owner}, cls := {h.cls}, units := {h.units}, req := {optLean h.req} }"

def rstLean (s : Core.Behav.RSt) : String :=
  s!"\{ capacity := {s.capacity}, holds := {listLean holdLean s.holds}, waiting := {listLean reqLean s.waiting} }"

def worldLean (w : Core.Behav.World) : String :=
  s!"\{ res := {listLean rstLean w.res}, nextReq := {w.nextReq}, active := {listLean toString w.active} }"

def wopLean : Core.Behav.WOp → String
  | .req res cls units kind info => s!"(.req {res} {cls} {units} {reqKindLeanW kind} {infoLean info})"
  | .release res cls units => s!"(.release {res} {cls} {units})"

def ekindLean : Core.Behav.EKind → String
  | .event => ".event"
  | .op o => s!"(.op {wopLean o})"
  | .serviceDone res r waited served => s!"(.serviceDone {res} {reqLean r} {waited} {served})"
  | .waitTimeout res q => s!"(.waitTimeout {res} {q})"
  | .faultEdge f on => s!"(.faultEdge {f} {on})"

def entryLean (e : Core.Behav.Entry) : String :=
  s!"\{ time := {e.time}, event := {e.event}, payload := {fieldsLean e.payload}, " ++
  s!"target := {optLean e.target}, timer := {optLean e.timer}, done := {listLean toString e.done}, sender := {optLean e.sender}, " ++
  s!"kind := {ekindLean e.kind} }"

/-- A configuration as a Lean term: every field, the world included (a certificate that dropped the
world or the entries' kinds would name states the calculus never reaches). -/
def cfgLean (c : Core.Behav.Cfg) : String :=
  s!"\{ time := {c.time}, machines := {listLean (fun (m : Core.Behav.MState) => s!"⟨{m.ctrl}, {listLean valLean m.vars}⟩") c.machines}, " ++
  s!"pending := {listLean entryLean c.pending}, attempts := {listLean toString c.attempts}, attCap := {optLean c.attCap}, " ++
  s!"world := {worldLean c.world} }"

/-- A calculus state as a Lean term of type `Core.Behav.State`. -/
def stateLean : State → String
  | .run m c => s!"Core.Behav.State.run {listLean toString m} {cfgLean c}"
  | .err m c => s!"Core.Behav.State.err {listLean toString m} {cfgLean c}"

/-- The visited states of a search that proved an invariant, as Lean terms (none when the search
does not reach an empty frontier). -/
def certificate (sys : Core.Behav.Sys) (bound cap : Nat) : Option (List String) :=
  (Core.Behav.reachable (Core.Behav.Exec.gen sys) bound cap).map (·.map stateLean)

/-! ### Liveness -/

/-- The fair labels of fair transitions: a label is fair when its entry is of the event a fair
transition is on and is addressed to every machine or to a machine of that transition's
behaviour. -/
def fairLabels (I : Info) (trs : List String) : Label → Bool := fun l =>
  (List.range I.behs.length).any fun j =>
    let b := I.behs.getD j default
    b.transitions.any fun t =>
      trs.contains t.id && Elab.evIdx I.input t.on == l.entry.event &&
        (match l.entry.target with
          | none => true
          | some m => (List.range (Elab.instCount b)).any fun k => Elab.machineOf I.behs j k == m)

/-- The liveness forms of a claim. -/
def formOf : String → Option Core.Behav.LForm
  | "FG" => some .FG
  | "GF" => some .GF
  | _ => none

/-- The verdict of a liveness claim. -/
inductive LVerdict where
  | proved
  | violated
  | incomplete (reason : Gen.Reason)
  | notSupported
  | refused
  deriving DecidableEq, Repr

def LVerdict.name : LVerdict → String
  | .proved => "proved"
  | .violated => "violated"
  | .incomplete _ => "incomplete"
  | .notSupported => "not supported"
  | .refused => "refused"

/-- The verdict of a liveness claim: `proved` by the ranking search (`GF` only), `violated` by the
lasso search, `incomplete` when the reachable states were not all found, `notSupported` when
neither search decides it. -/
def liveVerdict (sys : Core.Behav.Sys) (I : Info) (form : Core.Behav.LForm) (src : String)
    (fair : List String) (bound cap : Nat) : LVerdict :=
  let p := fun (s : State) => s.ok && claimInvB I src s
  let f := fairLabels I fair
  if capped sys then .incomplete .cap
  else if form = .GF ∧ Core.Behav.rankProves sys f p bound cap = true then .proved
  else match Core.Behav.lassoSearch sys f p form bound cap with
    | .lasso _ _ _ => .violated
    | .incomplete why => .incomplete why
    | .noLasso => .notSupported

/-- The verdict of a liveness claim on an input text, as a proof file states it. -/
def liveVerdictOf (text : String) (form : String) (src : String) (fair : List String) (bound cap : Nat) : LVerdict :=
  match prepareText text, formOf form with
  | some (sys, I), some fm => liveVerdict sys I fm src fair bound cap
  | _, _ => .refused

/-- The state predicate and fair labels of a liveness claim on an input text. -/
def liveP (text src : String) : State → Bool := invP text src

def liveFair (text : String) (fair : List String) : Label → Bool :=
  match prepareText text with
  | some (_, I) => fairLabels I fair
  | none => fun _ => false

theorem liveVerdictOf_eq {text form src : String} {fair : List String} {bound cap : Nat} {v : LVerdict}
    (h : liveVerdictOf text form src fair bound cap = v) (hv : v ≠ .refused) :
    ∃ sys I fm, prepareText text = some (sys, I) ∧ formOf form = some fm ∧
      liveVerdict sys I fm src fair bound cap = v := by
  unfold liveVerdictOf at h
  split at h
  · rename_i sys I fm hp hf
    exact ⟨sys, I, fm, hp, hf, h⟩
  · exact absurd h.symm hv

/-- **A `proved` verdict of `GF p`**: every weakly fair run of the calculus system of the text is in
`p` infinitely often. -/
theorem liveVerdictOf_proved {text src : String} {fair : List String} {bound cap : Nat}
    (h : liveVerdictOf text "GF" src fair bound cap = .proved) :
    ∀ r : Core.LTS.Run (Core.Behav.Sys.lts (sysOfText text)),
      r.WeakFair (Core.Behav.fairOf (liveFair text fair)) → (□◇ (fun s => liveP text src s = true)) r := by
  obtain ⟨sys, I, fm, hp, hf, hv⟩ := liveVerdictOf_eq h (by decide)
  simp only [formOf, Option.some.injEq] at hf
  subst hf
  have e1 : sysOfText text = sys := by simp [sysOfText, hp]
  have e2 : liveFair text fair = fairLabels I fair := by simp [liveFair, hp]
  have e3 : liveP text src = fun s => s.ok && claimInvB I src s := by funext s; simp [liveP, invP, hp]
  rw [e1, e2, e3]
  unfold liveVerdict at hv
  dsimp only at hv
  split at hv
  · cases hv
  · split at hv
    · rename_i hr
      exact Core.Behav.rankProves_sound hr.2
    · split at hv <;> cases hv

/-- **A `violated` verdict of `GF p`**: not every weakly fair run is in `p` infinitely often. -/
theorem liveVerdictOf_violated_GF {text src : String} {fair : List String} {bound cap : Nat}
    (h : liveVerdictOf text "GF" src fair bound cap = .violated) :
    ¬ ∀ r : Core.LTS.Run (Core.Behav.Sys.lts (sysOfText text)),
      r.WeakFair (Core.Behav.fairOf (liveFair text fair)) → (□◇ (fun s => liveP text src s = true)) r := by
  obtain ⟨sys, I, fm, hp, hf, hv⟩ := liveVerdictOf_eq h (by decide)
  simp only [formOf, Option.some.injEq] at hf
  subst hf
  have e1 : sysOfText text = sys := by simp [sysOfText, hp]
  have e2 : liveFair text fair = fairLabels I fair := by simp [liveFair, hp]
  have e3 : liveP text src = fun s => s.ok && claimInvB I src s := by funext s; simp [liveP, invP, hp]
  rw [e1, e2, e3]
  unfold liveVerdict at hv
  dsimp only at hv
  split at hv
  · cases hv
  · split at hv
    · cases hv
    · split at hv
      · rename_i hl
        apply Core.Behav.lassoSearch_refutes_GF (bound := bound) (cap := cap)
        rw [hl]; rfl
      · cases hv
      · cases hv

/-- **A `violated` verdict of `FG p`**: not every weakly fair run is eventually always in `p`. -/
theorem liveVerdictOf_violated_FG {text src : String} {fair : List String} {bound cap : Nat}
    (h : liveVerdictOf text "FG" src fair bound cap = .violated) :
    ¬ ∀ r : Core.LTS.Run (Core.Behav.Sys.lts (sysOfText text)),
      r.WeakFair (Core.Behav.fairOf (liveFair text fair)) → (◇□ (fun s => liveP text src s = true)) r := by
  obtain ⟨sys, I, fm, hp, hf, hv⟩ := liveVerdictOf_eq h (by decide)
  simp only [formOf, Option.some.injEq] at hf
  subst hf
  have e1 : sysOfText text = sys := by simp [sysOfText, hp]
  have e2 : liveFair text fair = fairLabels I fair := by simp [liveFair, hp]
  have e3 : liveP text src = fun s => s.ok && claimInvB I src s := by funext s; simp [liveP, invP, hp]
  rw [e1, e2, e3]
  unfold liveVerdict at hv
  dsimp only at hv
  split at hv
  · cases hv
  · split at hv
    · rename_i hc; exact absurd hc.1 (by decide)
    · split at hv
      · rename_i hl
        apply Core.Behav.lassoSearch_refutes_FG (bound := bound) (cap := cap)
        rw [hl]; rfl
      · cases hv
      · cases hv

/-! ### The protocols -/

/-- The text of a calculus state for a lasso: the control state of each machine, `b:s` when the
system has several. -/
def stateText (I : Info) (s : State) : String :=
  let ms := s.cfg.machines.zipIdx.map fun (m, i) =>
    let b := I.beh i
    let st := (Elab.statesOf b).getD m.ctrl ""
    if s.cfg.machines.length == 1 then st else s!"{b.id}:{st}"
  let base := ", ".intercalate ms
  if s.ok then base else base ++ " (failed)"

open Encode in
def liveJson (sys : Core.Behav.Sys) (I : Info) (id : String) (form : Core.Behav.LForm) (src : String)
    (fair : List String) (bound cap : Nat) : Value :=
  let p := fun (s : State) => s.ok && claimInvB I src s
  let f := fairLabels I fair
  let v := liveVerdict sys I form src fair bound cap
  let base := [("id", s id), ("verdict", s v.name)] ++
    (match v with | .incomplete why => [("reason", s why.name)] | _ => [])
  if v == .violated then
    match Core.Behav.lassoSearch sys f p form bound cap with
    | .lasso x0 pre cyc =>
      let st := Core.Behav.pathEnd x0 pre
      let stem := x0 :: pre.map (·.2)
      -- a cycle with a step of the relation keeps the time: a Zeno run
      let prevs := st :: cyc.map (·.2)
      let zeno := (prevs.take cyc.length).any fun q => !(Core.Behav.Exec.successors sys q).isEmpty
      o (base ++ [("stem", strings (stem.map (stateText I))), ("cycle", strings ((st :: cyc.map (·.2)).map (stateText I))),
        ("zeno", .bool zeno), ("time", nat st.cfg.time)])
    | _ => o base
  else o base

/-- `{input, claims: [{id, form, expr, fair}], bound, maxStates}`: the liveness verdict per claim. -/
def livenessValue (req : Value) : Except String String := do
  let root ← match req with
    | .obj _ fs => pure fs
    | _ => throw "liveness: the request must be an object"
  let (_, sys, I) ← prepare (fieldOr root "input")
  let bound ← natField root "bound" "liveness"
  let cap ← natField root "maxStates" "liveness"
  let claims ← match fieldOr root "claims" with
    | .arr _ xs => xs.mapM fun c => match c with
      | .obj _ fs => match fieldOr fs "id", fieldOr fs "form", fieldOr fs "expr" with
        | .str id, .str fm, .str e => do
          let some form := formOf fm | throw s!"liveness: unknown form {fm}"
          let fair := match fieldOr fs "fair" with
            | .arr _ ts => ts.filterMap Value.asString?
            | _ => []
          pure (id, form, e, fair)
        | _, _, _ => throw "liveness: a claim needs \"id\", \"form\" and \"expr\" strings"
      | _ => throw "liveness: a claim must be an object"
    | _ => throw "liveness: \"claims\" must be an array"
  let results := claims.map fun (id, form, e, fair) => liveJson sys I id form e fair bound cap
  pure (Json.write (Encode.o [("results", Encode.a results)]))

/-- `{input, bound, maxStates}`: the states a search visits when it reaches an empty frontier, as
Lean terms, or `null`. -/
def certificateValue (req : Value) : Except String String := do
  let root ← match req with
    | .obj _ fs => pure fs
    | _ => throw "certificate: the request must be an object"
  let (_, sys, _) ← prepare (fieldOr root "input")
  let bound ← natField root "bound" "certificate"
  let cap ← natField root "maxStates" "certificate"
  pure (Json.write (match certificate sys bound cap with
    | some ls => Encode.o [("states", Encode.strings ls)]
    | none => Encode.o [("states", .null)]))

def runLiveness (text : String) : Except String String := do livenessValue (← Json.parse text)
def runCertificate (text : String) : Except String String := do certificateValue (← Json.parse text)

end Exegra.V2.ProveLive

/-- info: 'Exegra.V2.ProveLive.invariant_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.V2.ProveLive.invariant_of_certificate

/-- info: 'Exegra.V2.ProveLive.liveVerdictOf_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.V2.ProveLive.liveVerdictOf_proved

/-- info: 'Exegra.V2.ProveLive.liveVerdictOf_violated_GF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.V2.ProveLive.liveVerdictOf_violated_GF

/-- info: 'Exegra.V2.ProveLive.liveVerdictOf_violated_FG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.V2.ProveLive.liveVerdictOf_violated_FG
