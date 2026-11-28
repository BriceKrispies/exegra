import Exegra.Json
import Exegra.Trace
import Exegra.Impl.Semantics

/-!
Boundary traces, hiding and the boundary refinement check (WG-5729; docs/composition.md).

A composite's behaviour is the composition of its members' machines (one calculus system: the
machines of a scenario are composed by being listed in one engine input, and `Exegra.Elab` turns that
input into one `Core.Behav.Sys`) with the events internal to the composite hidden. Hiding is a
projection of a trace: the steps that deliver a hidden event are removed and the rest are kept in
order. Nothing here runs behaviour: the refinement check runs both systems on the engine
(`Impl.runAnyValue`, proved equal to the definition, `Impl.runAnyValue_eq`) and compares the
projections of the two traces it returns.

* **The generic part** (proved): `hide` and `onto` (projection onto a boundary alphabet) are filters
  on any list of observations with an event name. `onto_hide_disjoint` is invariant I1 (hiding events
  internal to a composite never changes its trace over its boundary alphabet), `hide_hide` and
  `hide_comm` the hiding laws of P10, `hide_append` that hiding is a homomorphism of concatenation
  (so it commutes with taking prefixes). `zipCheck` compares two observation lists element by element
  and returns the first mismatching position; `zipCheck_none_iff` proves it exact (no mismatch
  exactly when the lists are related position by position). `Agrees` (the projections of two traces
  agree up to a relation on observations) is reflexive and transitive when the relation is
  (`Agrees.refl`, `Agrees.trans`: refinement checked this way is a preorder, part of I3) and is
  preserved by hiding more events (`Agrees.hide_more`, congruence under hiding, part of I3).
* **The executable part** (`engine.boundary`, `engine.refineBoundary` at the call boundary, registered in `Exegra/Api/Boundary.lean`): decodes
  the steps of a trace into observations (kind, event, time, payload), projects them, and compares
  an abstract run with a concrete run: equal events, kinds and payloads, the concrete time equal to
  the abstract time multiplied by the declared time scale, the same outcome, and the same final
  configuration of every machine both runs share outside the region (the environment). The result is
  a step correspondence (the certificate: which concrete step realises each abstract boundary step,
  and which concrete steps are stutters of hidden events) or the first boundary counterexample.

What is not here: a theorem that the composition of two separately elaborated systems is the system
of the composed input (WG-5685 develops `Sys.compose`); refinement over every interleaving (the check
compares the deterministic scheduler's runs; `exegra prove` explores interleavings of one system).
-/

namespace Exegra.Boundary

/-! ### Hiding and projection, on any list of observations -/

section Generic

variable {α : Type} (ev : α → String)

/-- Hide the events of `H`: keep the observations whose event is not in `H`, in order. -/
def hide (H : List String) (xs : List α) : List α := xs.filter (fun x => !H.contains (ev x))

/-- Project onto a boundary alphabet `B`: keep the observations whose event is in `B`, in order. -/
def onto (B : List String) (xs : List α) : List α := xs.filter (fun x => B.contains (ev x))

theorem hide_nil (xs : List α) : hide ev [] xs = xs := by
  simp [hide]

theorem hide_append (H : List String) (xs ys : List α) :
    hide ev H (xs ++ ys) = hide ev H xs ++ hide ev H ys := by
  simp [hide, List.filter_append]

/-- **Hiding composes** (P10): hiding `H₁` and then `H₂` hides `H₁ ++ H₂`. -/
theorem hide_hide (H₁ H₂ : List String) (xs : List α) :
    hide ev H₂ (hide ev H₁ xs) = hide ev (H₁ ++ H₂) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [hide] at ih ⊢
    by_cases h1 : H₁.contains (ev x) = true <;> by_cases h2 : H₂.contains (ev x) = true <;>
      simp_all

/-- The order in which two sets of events are hidden does not matter (P10). -/
theorem hide_comm (H₁ H₂ : List String) (xs : List α) :
    hide ev H₂ (hide ev H₁ xs) = hide ev H₁ (hide ev H₂ xs) := by
  rw [hide_hide, hide_hide]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [hide] at ih ⊢
    by_cases h1 : H₁.contains (ev x) = true <;> by_cases h2 : H₂.contains (ev x) = true <;>
      simp_all

/-- **I1.** Hiding events that are not on the boundary never changes the trace over the boundary
alphabet: when no event of `H` is in `B`, projecting onto `B` after hiding `H` is projecting onto `B`. -/
theorem onto_hide_disjoint (B H : List String) (hd : ∀ e, B.contains e = true → H.contains e = false)
    (xs : List α) : onto ev B (hide ev H xs) = onto ev B xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [onto, hide] at ih ⊢
    by_cases hb : B.contains (ev x) = true
    · have hh := hd _ hb
      simp_all
    · by_cases hh : H.contains (ev x) = true <;> simp_all

/-- Hiding everything outside the boundary is projecting onto it. -/
theorem hide_eq_onto (B H : List String) (hc : ∀ e, H.contains e = !B.contains e) (xs : List α) :
    hide ev H xs = onto ev B xs := by
  simp only [hide, onto, hc, Bool.not_not]

end Generic

/-! ### Comparing two observation lists -/

section Compare

variable {α β : Type} (r : α → β → Bool)

/-- Two lists related position by position by `r`, with the same length. -/
def Rel2 : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => r a b = true ∧ Rel2 as bs
  | _, _ => False

/-- The first position `≥ i` where the lists stop being related by `r` (a different element, or one
list ending before the other), or `none` when they are related position by position. -/
def zipCheck : List α → List β → Nat → Option Nat
  | [], [], _ => none
  | a :: as, b :: bs, i => if r a b then zipCheck as bs (i + 1) else some i
  | _, _, i => some i

/-- `zipCheck` is exact: it finds no mismatch exactly when the lists are related position by position.
So a certificate (no mismatch) means the projections agree, and a counterexample position is a real
disagreement. -/
theorem zipCheck_none_iff (xs : List α) (ys : List β) (i : Nat) :
    zipCheck r xs ys i = none ↔ Rel2 r xs ys := by
  induction xs generalizing ys i with
  | nil => cases ys <;> simp [zipCheck, Rel2]
  | cons x xs ih =>
    cases ys with
    | nil => simp [zipCheck, Rel2]
    | cons y ys =>
      simp only [zipCheck, Rel2]
      by_cases h : r x y = true
      · simp [h, ih]
      · simp [h]

/-- A reported mismatch position is never before the starting position (it indexes the lists). -/
theorem zipCheck_some_ge (xs : List α) (ys : List β) (i k : Nat) (h : zipCheck r xs ys i = some k) :
    i ≤ k := by
  induction xs generalizing ys i with
  | nil => cases ys <;> simp_all [zipCheck]
  | cons x xs ih =>
    cases ys with
    | nil => simp_all [zipCheck]
    | cons y ys =>
      simp only [zipCheck] at h
      split at h
      · have := ih ys (i + 1) h; omega
      · simp_all

end Compare

/-! ### Refinement on boundary traces is a preorder and a congruence under hiding -/

section Agrees

variable {α : Type} (ev : α → String) (r : α → α → Bool)

theorem Rel2.refl (hr : ∀ x, r x x = true) : (xs : List α) → Rel2 r xs xs
  | [] => trivial
  | x :: xs => ⟨hr x, Rel2.refl hr xs⟩

theorem Rel2.trans (ht : ∀ x y z, r x y = true → r y z = true → r x z = true) :
    (xs ys zs : List α) → Rel2 r xs ys → Rel2 r ys zs → Rel2 r xs zs
  | [], [], [], _, _ => trivial
  | x :: xs, y :: ys, z :: zs, ⟨h1, t1⟩, ⟨h2, t2⟩ => ⟨ht x y z h1 h2, Rel2.trans ht xs ys zs t1 t2⟩
  | [], [], _ :: _, _, h => h.elim
  | [], _ :: _, _, h, _ => h.elim
  | _ :: _, [], _, h, _ => h.elim
  | _ :: _, _ :: _, [], _, h => h.elim

/-- Related lists stay related after hiding, when related observations have the same event. -/
theorem Rel2.hide (he : ∀ x y, r x y = true → ev x = ev y) (H : List String) :
    (xs ys : List α) → Rel2 r xs ys → Rel2 r (hide ev H xs) (hide ev H ys)
  | [], [], _ => trivial
  | x :: xs, y :: ys, ⟨h1, t1⟩ => by
    have ih := Rel2.hide he H xs ys t1
    have hev := he x y h1
    simp only [Boundary.hide, List.filter_cons, hev] at ih ⊢
    split
    · exact ⟨h1, ih⟩
    · exact ih
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- The concrete trace `c` agrees with the abstract trace `a` over everything but `H`: their
projections are related position by position by `r` (which compares event, kind, payload and the
scaled time). -/
def Agrees (H : List String) (a c : List α) : Prop :=
  Rel2 r (hide ev H a) (hide ev H c)

/-- Agreement is reflexive (part of I3: refinement is a preorder). -/
theorem Agrees.refl (hr : ∀ x, r x x = true) (H : List String) (a : List α) : Agrees ev r H a a :=
  Rel2.refl r hr _

/-- Agreement is transitive (part of I3: refinement is a preorder). -/
theorem Agrees.trans (ht : ∀ x y z, r x y = true → r y z = true → r x z = true) (H : List String)
    {a b c : List α} (h₁ : Agrees ev r H a b) (h₂ : Agrees ev r H b c) : Agrees ev r H a c :=
  Rel2.trans r ht _ _ _ h₁ h₂

/-- Agreement survives hiding more events (part of I3: refinement is preserved by hiding). -/
theorem Agrees.hide_more (he : ∀ x y, r x y = true → ev x = ev y) (H H' : List String)
    {a c : List α} (h : Agrees ev r H a c) : Agrees ev r (H ++ H') a c := by
  unfold Agrees at *
  rw [← hide_hide, ← hide_hide]
  exact Rel2.hide ev r he H' _ _ h

end Agrees

/-! ### Observations of a trace (executable) -/

/-- What a boundary step shows: its index in the trace, kind, delivered event, time and payload. -/
structure Obs where
  index : Nat
  kind : String
  event : String
  time : Rat
  payload : Value

def field? (v : Value) (k : String) : Option Value :=
  match v with
  | .obj _ fs => objGet? fs k
  | _ => none

def str? (v : Option Value) : String :=
  match v with
  | some (.str s) => s
  | _ => ""

def num? (v : Option Value) : Rat :=
  match v with
  | some (.num x) => x
  | _ => 0

def items (v : Option Value) : List Value :=
  match v with
  | some (.arr _ xs) => xs
  | _ => []

/-- The observation of one trace step. -/
def obsOf (i : Nat) (step : Value) : Obs :=
  let e := (field? step "event").getD .null
  { index := i, kind := str? (field? step "kind"), event := str? (field? e "id"),
    time := num? (field? step "time"), payload := (field? e "payload").getD (.obj 0 []) }

def observations (trace : Value) : List Obs :=
  (items (field? trace "steps")).zipIdx.map (fun (s, i) => obsOf i s)

/-- Structural equality of JSON values: numbers by value, objects by their keys whatever their
order, arrays element by element; identities are ignored. -/
partial def veq : Value → Value → Bool
  | .undef, .undef => true
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .num a, .num b => a == b
  | .str a, .str b => a == b
  | .arr _ xs, .arr _ ys => xs.length == ys.length && (xs.zip ys).all (fun p => veq p.1 p.2)
  | .obj _ fs, .obj _ gs =>
    fs.length == gs.length && fs.all (fun (k, v) => match objGet? gs k with
      | some w => veq v w
      | none => false)
  | _, _ => false

/-- An abstract boundary step and a concrete one match: same kind, event and payload, and the concrete
time is the abstract time multiplied by the time scale (concrete units per abstract tick). -/
def stepMatch (scale : Rat) (a c : Obs) : Bool :=
  a.kind == c.kind && a.event == c.event && c.time == a.time * scale && veq a.payload c.payload

/-! ### The call boundary -/

open Encode in
def obsJson (o : Obs) : Value :=
  .obj 0 [("index", nat o.index), ("kind", s o.kind), ("event", s o.event), ("time", .num o.time),
    ("payload", o.payload)]

def strList (v : Option Value) : List String :=
  (items v).filterMap (fun x => match x with | .str s => some s | _ => none)

/-- `{trace, hidden: [event]}` to the boundary trace: the steps whose event is not hidden. -/
def boundaryValue (args : Value) : Except String String := do
  let trace ← match field? args "trace" with
    | some t@(.obj ..) => pure t
    | _ => throw "engine.boundary: \"trace\" must be a trace object"
  let H := strList (field? args "hidden")
  let kept := hide Obs.event H (observations trace)
  pure (Json.write (.obj 0 [("steps", .arr 0 (kept.map obsJson)),
    ("hidden", .num ((((observations trace).length - kept.length : Nat) : Rat)))]))

/-- Run an engine input on the engine the claims are evaluated on, and parse its trace. -/
def runTrace (input : Value) : Except String Value := do
  let text ← Impl.runAnyValue input
  Json.parse text

/-- The first machine of `ids` whose final configuration differs between the two traces. -/
def machineMismatch (ids : List String) (a c : Value) : Option String :=
  let ma := (field? a "final").bind (field? · "machines")
  let mc := (field? c "final").bind (field? · "machines")
  ids.find? (fun id => !veq ((ma.bind (field? · id)).getD .undef) ((mc.bind (field? · id)).getD .undef))

open Encode in
/-- `{abstract, concrete, hidden, timeScale, environment}`: run both engine inputs, project both traces
by hiding `hidden`, and compare. `environment` lists the machines both runs share (outside the region
being compared), whose final configurations must be equal. The reply is
`{verdict: "certificate", correspondence, stutters, ...}` or `{verdict: "counterexample", at, reason,
abstract, concrete, ...}`. -/
def refineValue (args : Value) : Except String String := do
  let ai ← match field? args "abstract" with
    | some v => pure v
    | none => throw "engine.refineBoundary: \"abstract\" (an engine input) is missing"
  let ci ← match field? args "concrete" with
    | some v => pure v
    | none => throw "engine.refineBoundary: \"concrete\" (an engine input) is missing"
  let H := strList (field? args "hidden")
  let scale := match field? args "timeScale" with
    | some (.num x) => x
    | _ => 1
  let env := strList (field? args "environment")
  let at_ ← (runTrace ai).mapError (fun e => s!"the abstract run failed: {e}")
  let ct ← (runTrace ci).mapError (fun e => s!"the concrete run failed: {e}")
  let ao := observations at_
  let co := observations ct
  let ab := hide Obs.event H ao
  let cb := hide Obs.event H co
  let stutters := (co.filter (fun x => H.contains x.event)).map (fun x => nat x.index)
  let common : List (String × Value) := [
    ("abstract", o [("steps", nat ao.length), ("boundarySteps", nat ab.length),
      ("outcome", (field? at_ "outcome").getD .null)]),
    ("concrete", o [("steps", nat co.length), ("boundarySteps", nat cb.length),
      ("outcome", (field? ct "outcome").getD .null)]),
    ("hidden", a (H.map s)), ("timeScale", .num scale)]
  let cex (k : Nat) (reason : String) (extra : List (String × Value)) : String :=
    Json.write (o ([("verdict", s "counterexample"), ("at", nat k), ("reason", s reason),
      ("abstractStep", match ab[k]? with | some x => obsJson x | none => .null),
      ("concreteStep", match cb[k]? with | some x => obsJson x | none => .null),
      ("agreedPrefix", a ((ab.take k).map obsJson))] ++ extra ++ common))
  match zipCheck (stepMatch scale) ab cb 0 with
  | some k =>
    let reason := match ab[k]?, cb[k]? with
      | none, _ => "concrete-longer"
      | _, none => "abstract-longer"
      | some x, some y =>
        if x.event != y.event then "event" else if x.kind != y.kind then "kind"
        else if !veq x.payload y.payload then "payload" else "time"
    pure (cex k reason [])
  | none =>
    let oa := str? (field? at_ "outcome")
    let oc := str? (field? ct "outcome")
    if oa != oc then pure (cex ab.length "outcome" [])
    else match machineMismatch env at_ ct with
      | some m => pure (cex ab.length "environment" [("machine", s m)])
      | none =>
        pure (Json.write (o ([("verdict", s "certificate"),
          ("correspondence", a ((ab.zip cb).map (fun (x, y) =>
            o [("abstractIndex", nat x.index), ("concreteIndex", nat y.index), ("event", s x.event),
               ("time", .num x.time)]))),
          ("stutters", a stutters),
          ("abstractHidden", a ((ao.filter (fun x => H.contains x.event)).map (fun x => nat x.index)))]
          ++ common)))

/-! ### Axioms: only the standard ones -/

/-- info: 'Exegra.Boundary.hide_hide' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Boundary.hide_hide

/-- info: 'Exegra.Boundary.hide_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Boundary.hide_comm

/-- info: 'Exegra.Boundary.hide_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Boundary.hide_append

/-- info: 'Exegra.Boundary.onto_hide_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Boundary.onto_hide_disjoint

/-- info: 'Exegra.Boundary.hide_eq_onto' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Boundary.hide_eq_onto

/-- info: 'Exegra.Boundary.zipCheck_none_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Boundary.zipCheck_none_iff

/-- info: 'Exegra.Boundary.zipCheck_some_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Boundary.zipCheck_some_ge

/-- info: 'Exegra.Boundary.Agrees.refl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Boundary.Agrees.refl

/-- info: 'Exegra.Boundary.Agrees.trans' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Boundary.Agrees.trans

/-- info: 'Exegra.Boundary.Agrees.hide_more' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Boundary.Agrees.hide_more

end Exegra.Boundary
