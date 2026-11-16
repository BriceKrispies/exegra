import Exegra.Format2

/-
The lift of a version-1 input to version 2 and the statement of `lift_agrees`
(`docs/simulation.md`, "Backward compatibility").

**`lift_agrees` is stated here and NOT proved: its proof is `sorry`.** The pin at the end records
that it depends on `sorryAx`, so the build fails if that ever changes silently, in either
direction. Until it is proved, the agreement is checked differentially:
`node tools/differential.js --lift` runs every liftable golden input through both versions of
`exegra-lean` and compares the stripped version-2 trace with the version-1 trace.

The hypotheses are the three side conditions of the specification, plus two it does not list
but the version-2 input needs (ids distinct across behaviors, events, faults, resources and the
scenario, and no event named by the empty string, which the version-2 trace uses for internal
entries).
-/

namespace Exegra.Lift

def isNat (x : Float) : Bool := x.floor == x && x ≥ 0 && x < 9007199254740992

def toNat (x : Float) : Nat := x.toUInt64.toNat

def liftEffect : Exegra.Effect → V2.Effect
  | .set v to => .set v to
  | .emit e after p => .emit e (.fixed (toNat after)) p false
  | .malformed => .malformed

def liftBehavior (b : BehaviorIn) : V2.BehaviorIn :=
  { id := b.id, subject := b.subject, initial := b.initial, variables := b.variables,
    instances := .single,
    transitions := b.transitions.map fun t =>
      { id := t.id, source := t.source, target := t.target, on := t.on, guard := t.guard,
        effects := t.effects.map liftEffect, faultOnly := t.faultOnly } }

/-- `lift(I)`: unit `tick`, no seed, no new list, every time and duration as an integer. -/
def lift (i : SimInput) : V2.Input :=
  { unit := "tick", perSecond := none, events := i.events, routes := [], resources := [],
    behaviors := i.behaviors.map liftBehavior,
    faults := i.faults.map fun f =>
      { id := f.id, kind := f.kind, event := f.event, transition := f.transition,
        occurrence := f.occurrence, delayBy := toNat f.delayBy, injectAt := toNat f.injectAt,
        payload := f.payload },
    scenario :=
      { id := i.scenario.id, faults := i.scenario.faults, stepLimit := toNat i.scenario.stepLimit,
        seed := none, horizon := none, warmup := none, stopAt := none, output := "trace",
        steps := i.scenario.steps.map fun st =>
          { time := toNat st.time, event := st.event, payload := st.payload, target := none } } }

/-- Every expression source of an input (guards, string `to` values and payload entries). -/
def exprSources (i : SimInput) : List String :=
  i.behaviors.flatMap fun b => b.transitions.flatMap fun t =>
    t.guard.toList ++ t.effects.flatMap fun
      | .set _ (some (.str s)) => [s]
      | .emit _ _ p => p.filterMap fun (_, v) => v.asString?
      | _ => []

/-- A reference format 2 would resolve differently from format 1. -/
def newRef : List String → Bool
  | ["instance"] => true
  | _ :: second :: _ :: _ => ["count", "sum", "min", "max", "instances"].contains second
  | _ => false

/-- The side conditions of `lift_agrees`. -/
structure Liftable (i : SimInput) : Prop where
  /-- 1. Integer times, durations and step limit in range. -/
  times : (i.scenario.steps.all fun st => isNat st.time) ∧
    (i.faults.all fun f => isNat f.delayBy && isNat f.injectAt) ∧
    (i.behaviors.all fun b => b.transitions.all fun t => t.effects.all fun
      | .emit _ after _ => isNat after
      | _ => true) ∧
    isNat i.scenario.stepLimit ∧ 1 ≤ i.scenario.stepLimit
  /-- 2. No variable named `instance` and no reference format 2 resolves anew. -/
  names : (i.behaviors.all fun b => b.variables.all (·.name != "instance")) ∧
    (exprSources i).all fun src => match parseExpr src with
      | .ok ast => !(V2.refsOf ast).any newRef
      | .error _ => true
  /-- 3. The version-1 run creates no queue entry at a time of 2^53 or more. -/
  bounded : ∀ st ∈ (traceOf i).steps, ∀ p ∈ st.config.pending, p.time < 9007199254740992
  /-- Not in the specification: ids are distinct and no event is named "". -/
  distinct : ((i.behaviors.map (·.id)) ++ i.events ++ i.faults.map (·.id) ++ [i.scenario.id]).Nodup
  nonempty : ∀ e ∈ i.events, e ≠ ""

/-! ## Stripping the version-2 fields -/

def drop (keys : List String) : Value → Value
  | .obj k fs => .obj k (fs.filter fun (key, _) => !keys.contains key)
  | v => v

def isEmptyObj : Value → Bool
  | .obj _ [] => true
  | _ => false

def overArr (f : Value → Value) : Value → Value
  | .arr k xs => .arr k (xs.map f)
  | v => v

def overKey (key : String) (f : Value → Value) : Value → Value
  | .obj k fs => .obj k (fs.map fun (k', v) => if k' == key then (k', f v) else (k', v))
  | v => v

def configKeys : List String :=
  ["resources", "links", "timers", "workloads", "meters", "routeCounters", "streams", "down",
   "incarnations"]

def stripConfig (c : Value) : Value :=
  overKey "pending" (overArr (drop ["scheduledAt", "routes", "from", "target"])) (drop configKeys c)

def stripStep (s : Value) : Value :=
  let s := drop ["resources", "draws"] s
  let s := overKey "event" (drop ["scheduledAt", "routes", "from", "target"]) s
  let s := overKey "fired" (overArr (drop ["instance"])) s
  let s := overKey "ignored" (overArr (drop ["instance"])) s
  overKey "config" stripConfig s

/-- The version-2 trace without `version`, `timeUnit`, `seed`, `instance`, `resources`, `links`,
`timers`, `workloads`, `meters`, `routeCounters`, `streams`, `down`, `draws`, `truncated` and
empty `routes` (the specification's list), and without `scheduledAt`, `from`, `target`, `incarnations`,
`initialDraws` and `stepsTaken`, which the specification's list leaves out although the
version-2 trace carries them. -/
def strip (t : Value) : Value :=
  let t := drop ["version", "timeUnit", "seed", "truncated", "initialDraws", "stepsTaken"] t
  let t := overKey "initial" stripConfig t
  let t := overKey "final" stripConfig t
  overKey "steps" (overArr stripStep) t

/-- **`lift_agrees`** (stated, not proved: `sorry`). For a liftable version-1 input, version 2 of
the lifted input refuses exactly when version 1 refuses, with the same message, and otherwise its
stripped trace is the version-1 trace. -/
theorem lift_agrees (i : SimInput) (h : Liftable i) :
    (match runInput i, V2.validate (lift i) with
     | .ok tr, .ok () => strip (V2.Encode.trace (V2.traceOf (lift i))) = Encode.trace tr
     | .error e, .error e' => e = e'
     | _, _ => False) := by
  sorry

/-- info: 'Exegra.Lift.lift_agrees' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lift_agrees

end Exegra.Lift
