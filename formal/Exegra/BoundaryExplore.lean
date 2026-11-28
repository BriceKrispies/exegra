import Exegra.Boundary
import Exegra.ProveB

/-!
Refinement of a declared abstraction over every interleaving and fault mask (WG-5734; docs/composition.md).

`engine.refineBoundary` (`Boundary.lean`) compares the deterministic scheduler's run of a scenario at
the abstraction with its run at the members. This module explores both systems instead: the calculus's
transition system of each engine input (`Core.Behav.Exec.successors`, complete and sound for
`Sys.lts`), every delivery order among simultaneous entries, every subset of the scenario's faults and
every draw, and checks **trace inclusion on the boundary**: every boundary trace a run of the members
can show (the deliveries of events that are not hidden, with time and payload) is a boundary trace of a
run of the abstraction with the same active faults.

* **The generic part** (proved). An observable transition system `OLts` has initial states and, per
  state, successors labelled with an observation or `none` (a silent step). `Runs L s tr t`: `t` is
  reached from `s` showing the observations `tr`. The checker searches the product of the concrete
  system with *sets* of abstract states (a subset construction: the abstract states that can have shown
  the same boundary trace, closed under silent steps) for a node whose set is empty, with the generic
  breadth-first search `Gen.search`. `explore_holds` is the soundness theorem of its certificate: when
  the search ends with `holds`, every run of the concrete system from an initial state shows a trace
  that a run of the abstract system, from an initial state compatible with it (the same faults), shows
  as well, up to the relation on observations. The silent closure is computed with fuel and may stop
  early; that only removes abstract candidates (a counterexample can then be spurious and is reported
  as found, never hidden), so a certificate stays sound.
* **The executable part** (`exploreValue`, `engine.refineExplore` at the call boundary): elaborates
  both engine inputs, instantiates the generic checker with the calculus (a step shows its event when
  it delivers an event entry that is not hidden: neither dropped nor delayed by a fault) and reports a
  certificate with the number of product nodes, a counterexample with the members' run (its fault
  mask, the picks, the replayed steps and its boundary trace), or `incomplete` (a bound or the state
  budget was reached, or a support is above the draw cap).

What it does not compare: the final configuration of the machines outside the region and the outcome
of the runs (the scripted check compares those), and liveness (inclusion of finite traces is a safety
statement).
-/

namespace Exegra.Boundary

set_option linter.unusedSectionVars false

/-! ### Observable transition systems and their runs -/

section Generic

variable {S O : Type}

/-- An observable transition system: initial states and labelled successors (`none`: silent). -/
structure OLts (S O : Type) where
  init : List S
  succ : S → List (Option O × S)

/-- `Runs L s tr t`: from `s`, `t` is reached showing the observations `tr` (silent steps show nothing). -/
inductive Runs (L : OLts S O) (s : S) : List O → S → Prop
  | refl : Runs L s [] s
  | tau {tr : List O} {u t : S} : Runs L s tr u → (none, t) ∈ L.succ u → Runs L s tr t
  | vis {tr : List O} {u t : S} {o : O} : Runs L s tr u → (some o, t) ∈ L.succ u → Runs L s (tr ++ [o]) t

theorem Rel2.snoc {α β : Type} {r : α → β → Bool} :
    ∀ {xs : List α} {ys : List β} {x : α} {y : β}, Rel2 r xs ys → r x y = true → Rel2 r (xs ++ [x]) (ys ++ [y])
  | [], [], _, _, _, h => ⟨h, trivial⟩
  | _ :: xs, _ :: ys, _, _, ⟨h1, h2⟩, h => ⟨h1, Rel2.snoc (xs := xs) (ys := ys) h2 h⟩
  | [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim

variable [DecidableEq S]

/-- The list without repeated elements (first occurrences kept). -/
def dedup (xs : List S) : List S := xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

theorem mem_dedup_aux : ∀ (xs acc : List S) (x : S), x ∈ xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc → x ∈ acc ∨ x ∈ xs
  | [], acc, x, h => .inl h
  | y :: ys, acc, x, h => by
    simp only [List.foldl_cons] at h
    rcases mem_dedup_aux ys _ x h with h' | h'
    · split at h'
      · exact .inl h'
      · rcases List.mem_append.mp h' with h'' | h''
        · exact .inl h''
        · simp only [List.mem_singleton] at h''
          exact .inr (h'' ▸ List.mem_cons_self)
    · exact .inr (List.mem_cons_of_mem _ h')

theorem mem_dedup {xs : List S} {x : S} (h : x ∈ dedup xs) : x ∈ xs := by
  rcases mem_dedup_aux xs [] x h with h' | h'
  · simp at h'
  · exact h'

/-- One round of silent successors added to a set of states. -/
def tauStep (L : OLts S O) (A : List S) : List S :=
  dedup (A ++ A.flatMap fun a => (L.succ a).filterMap fun p => if p.1.isNone then some p.2 else none)

/-- The silent closure of a set of states, with fuel: rounds of `tauStep` until nothing is added. -/
def tauClose (L : OLts S O) : Nat → List S → List S
  | 0, A => A
  | n + 1, A =>
    let B := tauStep L A
    if B.length == A.length then A else tauClose L n B

/-- A property of states preserved by silent steps holds on the silent closure of a set it holds on. -/
theorem tauClose_mem (L : OLts S O) (P : S → Prop) (hP : ∀ a t, P a → (none, t) ∈ L.succ a → P t) :
    ∀ (n : Nat) (A : List S), (∀ a ∈ A, P a) → ∀ a ∈ tauClose L n A, P a
  | 0, A, hA, a, ha => hA a ha
  | n + 1, A, hA, a, ha => by
    simp only [tauClose] at ha
    split at ha
    · exact hA a ha
    · refine tauClose_mem L P hP n _ ?_ a ha
      intro b hb
      have hb := mem_dedup hb
      rcases List.mem_append.mp hb with hb | hb
      · exact hA b hb
      · simp only [List.mem_flatMap, List.mem_filterMap] at hb
        obtain ⟨a', ha', p, hp, hq⟩ := hb
        split at hq
        · rename_i hn
          simp only [Option.some.injEq] at hq
          subst hq
          obtain ⟨x, t⟩ := p
          simp only [Option.isNone_iff_eq_none] at hn
          subst hn
          exact hP a' t (hA a' ha') hp
        · cases hq

/-- The abstract states that can follow a set by showing an observation related to `o`, closed under
silent steps. -/
def after {Oc : Type} (L : OLts S O) (m : O → Oc → Bool) (fuel : Nat) (o : Oc) (A : List S) : List S :=
  tauClose L fuel (dedup (A.flatMap fun a => (L.succ a).filterMap fun p =>
    match p.1 with
    | some x => if m x o then some p.2 else none
    | none => none))

variable {Sc Oc : Type} [DecidableEq Sc] [Hashable Sc] [Hashable S]

/-- The successor of a product node: the concrete step `k`, with the abstract set advanced when the step
shows an observation. -/
def pnext (Lc : OLts Sc Oc) (La : OLts S O) (m : O → Oc → Bool) (fuel : Nat) (n : Sc × List S) (k : Nat) :
    Option (Sc × List S) :=
  ((Lc.succ n.1)[k]?).map fun p => match p.1 with
    | none => (p.2, n.2)
    | some o => (p.2, after La m fuel o n.2)

/-- The product of the concrete system with sets of abstract states. An initial node pairs each concrete
initial state with the silent closure of the abstract initial states `compat` admits for it. -/
def psys (Lc : OLts Sc Oc) (La : OLts S O) (m : O → Oc → Bool) (compat : Sc → S → Bool) (fuel : Nat) :
    Gen.Sys (Sc × List S) where
  init := Lc.init.map fun c0 => (c0, tauClose La fuel (La.init.filter (compat c0)))
  width n := (Lc.succ n.1).length
  next := pnext Lc La m fuel
  lt := by
    intro n k t h
    simp only [pnext, Option.map_eq_some_iff] at h
    obtain ⟨p, hp, -⟩ := h
    exact (List.getElem?_eq_some_iff.mp hp).1

/-- The checker: search the product for a node whose abstract set is empty. -/
def explore (Lc : OLts Sc Oc) (La : OLts S O) (m : O → Oc → Bool) (compat : Sc → S → Bool)
    (fuel bound cap : Nat) : Gen.Result (Sc × List S) :=
  Gen.search (psys Lc La m compat fuel) (fun n => !n.2.isEmpty) bound cap

/-- What every abstract state of a product node reached along a concrete run from `c0` showing `tc`
satisfies: it is reached from an abstract initial state compatible with `c0`, showing a trace related to
`tc` position by position. -/
def Matched (La : OLts S O) (m : O → Oc → Bool) (compat : Sc → S → Bool) (c0 : Sc) (tc : List Oc) (a : S) : Prop :=
  ∃ a0 ∈ La.init, compat c0 a0 = true ∧ ∃ ta, Runs La a0 ta a ∧ Rel2 m ta tc

theorem matched_tau (La : OLts S O) (m : O → Oc → Bool) (compat : Sc → S → Bool) (c0 : Sc) (tc : List Oc) :
    ∀ a t, Matched La m compat c0 tc a → (none, t) ∈ La.succ a → Matched La m compat c0 tc t := by
  rintro a t ⟨a0, h0, hc, ta, hr, hrel⟩ hs
  exact ⟨a0, h0, hc, ta, .tau hr hs, hrel⟩

/-- Along every concrete run there is a reachable product node whose abstract states are all matched. -/
theorem reach_of_runs (Lc : OLts Sc Oc) (La : OLts S O) (m : O → Oc → Bool) (compat : Sc → S → Bool)
    (fuel : Nat) (c0 : Sc) (h0 : c0 ∈ Lc.init) :
    ∀ {tc : List Oc} {c : Sc}, Runs Lc c0 tc c →
      ∃ d A, Gen.Reach (psys Lc La m compat fuel) d (c, A) ∧ ∀ a ∈ A, Matched La m compat c0 tc a := by
  intro tc c hr
  induction hr with
  | refl =>
    refine ⟨0, _, .init (List.mem_map.mpr ⟨c0, h0, rfl⟩), ?_⟩
    refine tauClose_mem La _ (matched_tau La m compat c0 []) fuel _ ?_
    intro a ha
    simp only [List.mem_filter] at ha
    exact ⟨a, ha.1, ha.2, [], .refl, trivial⟩
  | @tau tr u t _ hs ih =>
    obtain ⟨d, A, hreach, hA⟩ := ih
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hs
    refine ⟨d + 1, A, .step hreach ⟨k, Gen.mem_succs.mpr ?_⟩, hA⟩
    simp only [psys, pnext, hk, Option.map_some]
  | @vis tr u t o _ hs ih =>
    obtain ⟨d, A, hreach, hA⟩ := ih
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hs
    refine ⟨d + 1, after La m fuel o A, .step hreach ⟨k, Gen.mem_succs.mpr ?_⟩, ?_⟩
    · simp only [psys, pnext, hk, Option.map_some]
    · refine tauClose_mem La _ (matched_tau La m compat c0 (tr ++ [o])) fuel _ ?_
      intro b hb
      have hb := mem_dedup hb
      simp only [List.mem_flatMap, List.mem_filterMap] at hb
      obtain ⟨a, ha, p, hp, hq⟩ := hb
      obtain ⟨x, t'⟩ := p
      cases x with
      | none => cases hq
      | some x =>
        simp only at hq
        split at hq
        · rename_i hm
          simp only [Option.some.injEq] at hq
          subst hq
          obtain ⟨a0, ha0, hc, ta, hra, hrel⟩ := hA a ha
          exact ⟨a0, ha0, hc, ta ++ [x], .vis hra hp, Rel2.snoc hrel hm⟩
        · cases hq

/-- **The explorer's certificate is sound: trace inclusion on the boundary.** When the search ends with
`holds`, every run of the concrete system from an initial state `c0` showing the observations `tc` has a
run of the abstract system, from an initial state compatible with `c0`, showing observations related to
`tc` position by position. -/
theorem explore_holds {Lc : OLts Sc Oc} {La : OLts S O} {m : O → Oc → Bool} {compat : Sc → S → Bool}
    {fuel bound cap k : Nat} (h : explore Lc La m compat fuel bound cap = .holds k) :
    ∀ c0 ∈ Lc.init, ∀ tc c, Runs Lc c0 tc c →
      ∃ a0 ∈ La.init, compat c0 a0 = true ∧ ∃ ta a, Runs La a0 ta a ∧ Rel2 m ta tc := by
  intro c0 h0 tc c hr
  obtain ⟨d, A, hreach, hA⟩ := reach_of_runs Lc La m compat fuel c0 h0 hr
  have hok := Gen.search_sound h d _ hreach
  cases A with
  | nil => simp at hok
  | cons a _ =>
    obtain ⟨a0, ha0, hc, ta, hra, hrel⟩ := hA a List.mem_cons_self
    exact ⟨a0, ha0, hc, ta, a, hra, hrel⟩

/-- **A counterexample of the explorer is a real run of the concrete system** that replays, through the
product, to a node where no abstract candidate is left. -/
theorem explore_cex {Lc : OLts Sc Oc} {La : OLts S O} {m : O → Oc → Bool} {compat : Sc → S → Bool}
    {fuel bound cap : Nat} {p : Gen.Path (Sc × List S)} (h : explore Lc La m compat fuel bound cap = .counterexample p) :
    p.root ∈ (psys Lc La m compat fuel).init ∧
      ∃ t, Gen.greplay (psys Lc La m compat fuel) p.root p.picks = some t ∧ t.2 = [] := by
  obtain ⟨hr, -, t, ht, hb⟩ := Gen.search_counterexample_real h
  refine ⟨hr, t, ht, ?_⟩
  cases ht2 : t.2 with
  | nil => rfl
  | cons _ _ => simp [ht2] at hb

end Generic

/-! ### The calculus as an observable transition system -/

open Exegra.V2.B
open Exegra.V2.ProveB

/-- A boundary observation of a calculus step: the delivered event, the time and the payload (fields
sorted by their number). -/
structure CObs where
  event : String
  time : Nat
  payload : List (Nat × Core.Behav.Val)
  deriving DecidableEq

def insertField (x : Nat × Core.Behav.Val) : List (Nat × Core.Behav.Val) → List (Nat × Core.Behav.Val)
  | [] => [x]
  | y :: ys => if x.1 ≤ y.1 then x :: y :: ys else y :: insertField x ys

def sortFields (xs : List (Nat × Core.Behav.Val)) : List (Nat × Core.Behav.Val) := xs.foldr insertField []

/-- What a step shows on the boundary: the delivery of an event entry whose event is not hidden and
that no fault drops, loses or delays (the deliveries `exegra prove`'s temporal matchers see). -/
def stepObs (I : Info) (sys : Core.Behav.Sys) (H : List String) (s : Core.Behav.State) (l : Core.Behav.Label) :
    Option CObs :=
  match s with
  | .err _ _ => none
  | .run mask c =>
    let e := l.entry
    match e.kind, e.timer with
    | .event, none =>
      let act := sys.active mask
      let att := c.attemptsOf e.event + 1
      if act.any (fun p => p.2.hits [.drop, .lose] e.event att e.time) then none
      else match Core.Behav.delayFault act e att with
        | some _ => none
        | none =>
          let name := I.event e.event
          if H.contains name then none else some { event := name, time := e.time, payload := sortFields e.payload }
    | _, _ => none

/-- The calculus system of an elaborated input as an observable transition system. -/
def calcLts (I : Info) (sys : Core.Behav.Sys) (H : List String) : OLts Core.Behav.State CObs where
  init := Core.Behav.Exec.inits sys
  succ s := (Core.Behav.Exec.successors sys s).map fun (l, t) => (stepObs I sys H s l, t)

/-- An abstract observation and a concrete one match: same event and payload, the concrete time the
abstract time multiplied by the (whole) time scale. -/
def cobsMatch (scale : Nat) (a c : CObs) : Bool :=
  a.event == c.event && c.time == a.time * scale && a.payload == c.payload

/-- An abstract initial state is compatible with a concrete one when the same faults are active. -/
def maskCompat (Ic Ia : Info) (c a : Core.Behav.State) : Bool :=
  activeIds Ic c.mask == activeIds Ia a.mask

/-- The explorer on two elaborated inputs. -/
def exploreB (Ic Ia : Info) (sc sa : Core.Behav.Sys) (H : List String) (scale fuel bound cap : Nat) :
    Gen.Result (Core.Behav.State × List Core.Behav.State) :=
  if capped sc || capped sa then .incomplete .cap 0
  else explore (calcLts Ic sc H) (calcLts Ia sa H) (cobsMatch scale) (maskCompat Ic Ia) fuel bound cap

/-- **The certificate of the explorer on the calculus**: every run of the members' system, from any fault
mask, shows a boundary trace that a run of the abstraction's system, with the same active faults, shows
too (events, payloads and times under the time scale). -/
theorem exploreB_holds {Ic Ia : Info} {sc sa : Core.Behav.Sys} {H : List String} {scale fuel bound cap k : Nat}
    (h : exploreB Ic Ia sc sa H scale fuel bound cap = .holds k) :
    ∀ c0 ∈ Core.Behav.Exec.inits sc, ∀ tc c, Runs (calcLts Ic sc H) c0 tc c →
      ∃ a0 ∈ Core.Behav.Exec.inits sa, maskCompat Ic Ia c0 a0 = true ∧
        ∃ ta a, Runs (calcLts Ia sa H) a0 ta a ∧ Rel2 (cobsMatch scale) ta tc := by
  unfold exploreB at h
  split at h
  · cases h
  · exact explore_holds h

/-! ### The call boundary -/

open Encode in
def cobsJson (I : Info) (ob : CObs) : Value :=
  o [("event", s ob.event), ("time", nat ob.time), ("payload", payloadValue I ob.payload)]

/-- The boundary trace of a concrete path: the observations along the picks. -/
def pathObs (L : OLts Core.Behav.State CObs) : Core.Behav.State → List Nat → List CObs
  | _, [] => []
  | st, k :: ks => match (L.succ st)[k]? with
    | some (x, t) => (match x with | some o => [o] | none => []) ++ pathObs L t ks
    | none => []

open Encode in
/-- `{abstract, concrete, hidden, timeScale, bound, maxStates}`: explore both engine inputs and check
trace inclusion on the boundary. `{verdict: "certificate", states}`, `{verdict: "counterexample", faults,
picks, steps, boundary}` (the members' run and the boundary trace no run of the abstraction shows), or
`{verdict: "incomplete", reason, states}`. -/
def exploreValue (args : Value) : Except String String := do
  let ai ← match field? args "abstract" with
    | some v => pure v
    | none => throw "engine.refineExplore: \"abstract\" (an engine input) is missing"
  let ci ← match field? args "concrete" with
    | some v => pure v
    | none => throw "engine.refineExplore: \"concrete\" (an engine input) is missing"
  let H := strList (field? args "hidden")
  let scale : Nat ← match field? args "timeScale" with
    | some (.num x) =>
      if x.den == 1 && 0 < x.num then pure x.num.toNat
      else throw "engine.refineExplore: the time scale must be a positive whole number"
    | _ => pure 1
  let nat? (k : String) (d : Nat) : Nat := match field? args k with
    | some (.num x) => x.floor.toNat
    | _ => d
  let bound := nat? "bound" 64
  let cap := nat? "maxStates" 20000
  let (_, sa, Ia) ← (prepare ai).mapError (fun e => s!"the abstract input is not explored: {e}")
  let (_, sc, Ic) ← (prepare ci).mapError (fun e => s!"the concrete input is not explored: {e}")
  let common : List (String × Value) := [("hidden", a (H.map s)), ("timeScale", nat scale),
    ("bound", nat bound), ("maxStates", nat cap), ("faults", strings (Ic.env.faults.map (·.id)))]
  match exploreB Ic Ia sc sa H scale bound bound cap with
  | .holds k => pure (Json.write (o ([("verdict", s "certificate"), ("states", nat k)] ++ common)))
  | .incomplete why k =>
    pure (Json.write (o ([("verdict", s "incomplete"), ("reason", s why.name), ("states", nat k)] ++ common)))
  | .counterexample p =>
    let L := calcLts Ic sc H
    let run := cexJson Ic sc "members" p.root.1 p.picks
    let boundary := pathObs L p.root.1 p.picks
    pure (Json.write (o ([("verdict", s "counterexample"), ("run", run),
      ("activeFaults", strings (activeIds Ic p.root.1.mask)),
      ("boundary", a (boundary.map (cobsJson Ic)))] ++ common)))

end Exegra.Boundary

/-- info: 'Exegra.Boundary.explore_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Boundary.explore_holds

/-- info: 'Exegra.Boundary.exploreB_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Boundary.exploreB_holds

/-- info: 'Exegra.Boundary.explore_cex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Boundary.explore_cex
