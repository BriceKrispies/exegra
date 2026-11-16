import Exegra.Json

/-
The trace, format version 1 (`docs/simulation.md`, "Trace"; `engine/exegra-engine/src/trace.rs`):
configurations, steps, the run's outcome, and their JSON encoding.

Traces are compared as JSON values (`tools/conformance.js`): key order is ignored and numbers
are compared by value, so the encoding only has to produce the right members and values.
Array order is part of the format and is kept everywhere.
-/

namespace Exegra

/-- Where a queue entry came from. -/
inductive Source where
  /-- Input step `step` of `scenario.steps`. -/
  | scenario (step : Nat)
  /-- An `inject-event` fault. -/
  | fault (fault : String)
  /-- An `emit` effect. -/
  | transition (transition behavior : String)
  deriving Inhabited

/-- One queue entry. -/
structure Pending where
  seq : Nat
  time : Float
  event : String
  payload : Value
  source : Source
  deriving Inhabited

/-- One machine: a behavior's state and variables. -/
structure Machine where
  state : String
  vars : List (String × Value)
  deriving Inhabited

/-- A configuration: logical time, one machine per behavior (in creation order), and the
pending queue ordered by `(time, seq)`. -/
structure Configuration where
  time : Float
  machines : List (String × Machine)
  pending : List Pending
  deriving Inhabited

def Configuration.machine? (c : Configuration) (id : String) : Option Machine :=
  (c.machines.find? (·.1 == id)).map (·.2)

/-- `machines[id] = m`: an existing machine keeps its position. -/
def Configuration.setMachine (c : Configuration) (id : String) (m : Machine) : Configuration :=
  if c.machines.any (·.1 == id) then
    { c with machines := c.machines.map fun (k, x) => if k == id then (k, m) else (k, x) }
  else { c with machines := c.machines ++ [(id, m)] }

inductive StepKind where
  | deliver | drop | delay
  deriving DecidableEq, Inhabited

def StepKind.name : StepKind → String
  | .deliver => "deliver" | .drop => "drop" | .delay => "delay"

/-- The head of the queue as a step records it. -/
structure EventRecord where
  id : String
  payload : Value
  seq : Nat
  source : Source
  deriving Inhabited

structure SetRecord where
  varName : String
  /-- `undef` (left out of the JSON) when the variable had no value. -/
  before : Value
  after : Value
  deriving Inhabited

structure EmitRecord where
  event : String
  time : Float
  seq : Nat
  payload : Value
  deriving Inhabited

structure Fired where
  behavior : String
  transition : String
  source : String
  target : String
  guard : Option String
  sets : List SetRecord
  emitted : List EmitRecord
  deriving Inhabited

inductive IgnoredReason where
  | noTransition | guardFalse | disabled
  deriving DecidableEq, Inhabited

def IgnoredReason.name : IgnoredReason → String
  | .noTransition => "no-transition" | .guardFalse => "guard-false" | .disabled => "disabled"

structure Ignored where
  behavior : String
  reason : IgnoredReason
  considered : List String
  deriving Inhabited

inductive FaultEffect where
  | dropped | delayed | enabled | disabled | injected
  deriving DecidableEq, Inhabited

def FaultEffect.name : FaultEffect → String
  | .dropped => "dropped" | .delayed => "delayed" | .enabled => "enabled"
  | .disabled => "disabled" | .injected => "injected"

structure FaultRecord where
  fault : String
  effect : FaultEffect
  deriving Inhabited

/-- One step of a run. -/
structure Step where
  index : Nat
  time : Float
  kind : StepKind
  event : EventRecord
  fired : List Fired
  ignored : List Ignored
  faults : List FaultRecord
  responsible : List String
  config : Configuration
  /-- The message of a failed step. -/
  error : Option String
  deriving Inhabited

inductive Outcome where
  | running | quiescent | stepLimit | error
  deriving DecidableEq, Inhabited

def Outcome.name : Outcome → String
  | .running => "running" | .quiescent => "quiescent" | .stepLimit => "step-limit"
  | .error => "error"

/-- A run. -/
structure Trace where
  scenarioId : String
  faults : List String
  initial : Configuration
  steps : List Step
  outcome : Outcome
  final : Configuration
  deriving Inhabited

/-! ## JSON encoding -/

namespace Encode

def o (fs : List (String × Value)) : Value := .obj 0 fs
def s (x : String) : Value := .str x
def n (x : Float) : Value := .num x
def nat (k : Nat) : Value := .num k.toFloat
def a (xs : List Value) : Value := .arr 0 xs
def strings (xs : List String) : Value := a (xs.map s)

def source : Source → Value
  | .scenario step => o [("kind", s "scenario"), ("step", nat step)]
  | .fault f => o [("kind", s "fault"), ("fault", s f)]
  | .transition t b => o [("kind", s "transition"), ("transition", s t), ("behavior", s b)]

def pending (p : Pending) : Value :=
  o [("seq", nat p.seq), ("time", n p.time), ("event", s p.event), ("payload", p.payload),
     ("source", source p.source)]

def configuration (c : Configuration) : Value :=
  o [("time", n c.time),
     ("machines", o (c.machines.map fun (id, m) =>
        (id, o [("state", s m.state), ("vars", .obj 0 m.vars)]))),
     ("pending", a (c.pending.map pending))]

def fired (f : Fired) : Value :=
  o [("behavior", s f.behavior), ("transition", s f.transition), ("from", s f.source),
     ("to", s f.target), ("guard", match f.guard with | some g => s g | none => .null),
     ("sets", a (f.sets.map fun r =>
        o [("variable", s r.varName), ("before", r.before), ("after", r.after)])),
     ("emitted", a (f.emitted.map fun e =>
        o [("event", s e.event), ("time", n e.time), ("seq", nat e.seq), ("payload", e.payload)]))]

def step (st : Step) : Value :=
  o ([("index", nat st.index), ("time", n st.time), ("kind", s st.kind.name),
      ("event", o [("id", s st.event.id), ("payload", st.event.payload),
                   ("seq", nat st.event.seq), ("source", source st.event.source)]),
      ("fired", a (st.fired.map fired)),
      ("ignored", a (st.ignored.map fun i =>
         o [("behavior", s i.behavior), ("reason", s i.reason.name),
            ("considered", strings i.considered)])),
      ("faults", a (st.faults.map fun f => o [("fault", s f.fault), ("effect", s f.effect.name)])),
      ("responsible", strings st.responsible),
      ("config", configuration st.config)] ++
     match st.error with
     | some m => [("error", o [("message", s m)])]
     | none => [])

def trace (t : Trace) : Value :=
  o [("scenarioId", s t.scenarioId), ("faults", strings t.faults),
     ("initial", configuration t.initial), ("steps", a (t.steps.map step)),
     ("outcome", s t.outcome.name), ("final", configuration t.final)]

end Encode

/-- The trace as compact JSON text. -/
def Trace.toJson (t : Trace) : String := Json.write (Encode.trace t)

end Exegra
