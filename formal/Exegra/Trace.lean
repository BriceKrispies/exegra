import Exegra.Json

/-
The records a format-2 trace shares with the formats before it (`docs/simulation.md`, "Trace";
`Exegra/Format2.lean` encodes the trace): a machine, the records of a fired transition, an ignored
behaviour and a fault, and the JSON helpers. Format 1 is gone (WG-5681).

Traces are compared as JSON values (`tools/conformance.js`): key order is ignored and numbers
are compared by value, so the encoding only has to produce the right members and values.
Array order is part of the format and is kept everywhere.
-/

namespace Exegra

structure Machine where
  state : String
  vars : List (String × Value)
  types : List (String × STy) := []
  deriving Inhabited

/-- The declared types a machine's expressions are evaluated with. -/
def machineTys : Option Machine → TyEnv
  | some m => tyLookup m.types
  | none => TyEnv.untyped

/-- A configuration: logical time, one machine per behavior (in creation order), and the
pending queue ordered by `(time, seq)`. -/
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
  /-- A format-2 effect (`capacity`, `limit`, `collapsed`, `scaled`, `replaced`, ...). -/
  | other (name : String)
  deriving DecidableEq, Inhabited

def FaultEffect.name : FaultEffect → String
  | .dropped => "dropped" | .delayed => "delayed" | .enabled => "enabled"
  | .disabled => "disabled" | .injected => "injected" | .other n => n

structure FaultRecord where
  fault : String
  effect : FaultEffect
  deriving Inhabited

namespace Encode

def o (fs : List (String × Value)) : Value := .obj 0 fs
def s (x : String) : Value := .str x
def n (x : Float) : Value := .num x
def nat (k : Nat) : Value := .num k.toFloat
def a (xs : List Value) : Value := .arr 0 xs
def strings (xs : List String) : Value := a (xs.map s)

def fired (f : Fired) : Value :=
  o [("behavior", s f.behavior), ("transition", s f.transition), ("from", s f.source),
     ("to", s f.target), ("guard", match f.guard with | some g => s g | none => .null),
     ("sets", a (f.sets.map fun r =>
        o [("variable", s r.varName), ("before", r.before), ("after", r.after)])),
     ("emitted", a (f.emitted.map fun e =>
        o [("event", s e.event), ("time", n e.time), ("seq", nat e.seq), ("payload", e.payload)]))]

end Encode

end Exegra
