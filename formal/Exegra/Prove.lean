import Exegra.Explore
import Exegra.Json

/-
What `exegra prove` needs on the Lean side.

* `claimInv src`: a state invariant of a specification (an expression over the configuration,
  `evaluate.expr` of a `state-invariant` claim) as a predicate on configurations. References
  resolve as `checkTrace` resolves them (`src/core/claims.js`, `configResolver`): `time`,
  `<behavior>.state` and `<behavior>.<variable>`. The invariant holds in a configuration when the
  expression evaluates to `true` there; `false`, a value that is not a boolean, an evaluation
  error or an expression that does not parse all count as a violation.
* `decodesTo text i`: the engine input text decodes (with the semantics' own reader, the one
  `exegra-lean` and the conformance suite use) to exactly the input term `i`. The generated proof
  file checks it, so the theorem it states is about the scenario's own engine input.
* `SimInput.toLean`: the Lean term of a decoded input, which the generated file embeds.
* `runExplore`: the `exegra-lean explore` protocol (one JSON request on stdin, one JSON answer on
  stdout); see `formal/Main.lean`.
-/

namespace Exegra

/-! ## State invariants of claims -/

/-- Reference resolution of a claim expression in a configuration (`configResolver`). -/
def claimResolve (c : Configuration) : List String → Value
  | ["time"] => .num c.time
  | [b, name] => match c.machine? b with
    | none => .undef
    | some m => if name == "state" then .str m.state else (objGet? m.vars name).getD .undef
  | _ => .undef

/-- Does a parsed claim expression evaluate to `true` in the configuration? -/
def claimHolds (ast : Ast) (c : Config) : Bool :=
  match eval (claimResolve c.conf) TyEnv.untyped ast with
  | .ok (.bool true) => true
  | _ => false

/-- A claim's state invariant as a predicate on configurations. -/
def claimInv (src : String) : Config → Bool :=
  match parseExpr src with
  | .ok ast => claimHolds ast
  | .error _ => fun _ => false

/-! ## The embedded input -/

deriving instance DecidableEq for StepIn
deriving instance DecidableEq for VariableIn
deriving instance DecidableEq for Effect
deriving instance DecidableEq for TransitionIn
deriving instance DecidableEq for BehaviorIn
deriving instance DecidableEq for Occurrence
deriving instance DecidableEq for FaultIn
deriving instance DecidableEq for ScenarioIn
deriving instance DecidableEq for SimInput

/-- Decode an engine input text. -/
def decodeText (text : String) : Except String SimInput := do
  let v ← Json.parse text
  Decode.input v

/-- The input text decodes to exactly `i`. -/
def decodesTo (text : String) (i : SimInput) : Bool :=
  match decodeText text with
  | .ok j => decide (j = i)
  | .error _ => false

namespace Lit

def str (s : String) : String := s.quote

def float (x : Float) : String := s!"(Float.ofBits {x.toBits.toNat})"

def list (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"

def optStr : Option String → String
  | some s => s!"(some {str s})"
  | none => "none"

mutual
def value : Value → String
  | .undef => "Value.undef"
  | .null => "Value.null"
  | .bool b => s!"(Value.bool {b})"
  | .num x => s!"(Value.num {float x})"
  | .str s => s!"(Value.str {str s})"
  | .arr i xs => s!"(Value.arr {i} {list (values xs)})"
  | .obj i fs => s!"(Value.obj {i} {list (fields fs)})"

def values : List Value → List String
  | [] => []
  | x :: xs => value x :: values xs

def fields : List (String × Value) → List String
  | [] => []
  | (k, x) :: xs => s!"({str k}, {value x})" :: fields xs
end

def effect : Effect → String
  | .set n to => s!"(Effect.set {str n} {match to with | some v => s!"(some {value v})" | none => "none"})"
  | .emit e after ps => s!"(Effect.emit {str e} {float after} {list (fields ps)})"
  | .malformed => "Effect.malformed"

def transition (t : TransitionIn) : String :=
  s!"\{ id := {str t.id}, source := {str t.source}, target := {str t.target}, on := {str t.on}, " ++
  s!"guard := {optStr t.guard}, effects := {list (t.effects.map effect)}, faultOnly := {t.faultOnly} }"

def behavior (b : BehaviorIn) : String :=
  s!"\{ id := {str b.id}, subject := {optStr b.subject}, initial := {str b.initial}, " ++
  s!"variables := {list (b.variables.map fun v => s!"\{ name := {str v.name}, initial := {value v.initial} }")}, " ++
  s!"transitions := {list (b.transitions.map transition)} }"

def occurrence : Occurrence → String
  | .any => "Occurrence.any"
  | .exactly n => s!"(Occurrence.exactly {float n})"
  | .never => "Occurrence.never"

def fault (f : FaultIn) : String :=
  s!"\{ id := {str f.id}, kind := {optStr f.kind}, event := {optStr f.event}, " ++
  s!"transition := {optStr f.transition}, occurrence := {occurrence f.occurrence}, " ++
  s!"delayBy := {float f.delayBy}, injectAt := {float f.injectAt}, payload := {value f.payload} }"

def step (s : StepIn) : String :=
  s!"\{ time := {float s.time}, event := {str s.event}, payload := {value s.payload} }"

end Lit

/-- The Lean term of an input (a `SimInput` structure instance). -/
def SimInput.toLean (i : SimInput) : String :=
  "{ scenario := { id := " ++ Lit.str i.scenario.id ++ ", " ++
  "steps := " ++ Lit.list (i.scenario.steps.map Lit.step) ++ ", " ++
  "faults := " ++ Lit.list (i.scenario.faults.map Lit.str) ++ ", " ++
  "stepLimit := " ++ Lit.float i.scenario.stepLimit ++ " }, " ++
  "behaviors := " ++ Lit.list (i.behaviors.map Lit.behavior) ++ ", " ++
  "events := " ++ Lit.list (i.events.map Lit.str) ++ ", " ++
  "faults := " ++ Lit.list (i.faults.map Lit.fault) ++ " }"

/-! ## The `explore` protocol -/

/-- The steps of a counterexample, replayed (the records `step` makes, as a trace holds them). -/
def replaySteps (env : Env) (s : State) : List Nat → List Step
  | [] => []
  | k :: ks =>
    if canPick s.cfg k then
      match step (withFaults env s.mask) (moveToFront s.cfg k) with
      | .committed r c' => r :: replaySteps env { s with cfg := c' } ks
      | _ => []
    else []

def faultIdsOf (env : Env) (mask : List Bool) : List String :=
  (pickBy mask env.faults).map (·.id)

open Encode in
def resultJson (env : Env) (id : String) (r : Result) : Value :=
  match r with
  | .holds n => o [("id", s id), ("verdict", s "holds"), ("states", nat n)]
  | .incomplete n => o [("id", s id), ("verdict", s "incomplete"), ("states", nat n)]
  | .counterexample p =>
    let s0 := initState env p.mask
    o [("id", s id), ("verdict", s "counterexample"),
       ("mask", a (p.mask.map Value.bool)), ("picks", a (p.picks.map nat)),
       ("faults", strings (faultIdsOf env p.mask)),
       ("initial", configuration s0.cfg.conf),
       ("steps", a ((replaySteps env s0 p.picks).map Encode.step))]

def fieldOr (o : List (String × Value)) (k : String) : Value := (objGet? o k).getD .undef

/-- One request: `{input, claims: [{id, expr}], bound, maxStates, emitLean?}`. The answer holds
the active fault ids, the result of each claim and, when `emitLean` is true, the Lean term of
the input. -/
def exploreValue (req : Value) : Except String String := do
  let root ← match req with
    | .obj _ fs => pure fs
    | _ => throw "explore: the request must be an object"
  let i ← Decode.input (fieldOr root "input")
  validate i
  let env := envOf i
  let bound ← match fieldOr root "bound" with
    | .num x => pure x.toUInt64.toNat
    | _ => throw "explore: \"bound\" must be a number"
  let cap ← match fieldOr root "maxStates" with
    | .num x => pure x.toUInt64.toNat
    | _ => throw "explore: \"maxStates\" must be a number"
  let claims ← match fieldOr root "claims" with
    | .arr _ xs => xs.mapM fun c => match c with
      | .obj _ fs => match fieldOr fs "id", fieldOr fs "expr" with
        | .str id, .str e => pure (id, e)
        | _, _ => throw "explore: a claim needs \"id\" and \"expr\" strings"
      | _ => throw "explore: a claim must be an object"
    | _ => throw "explore: \"claims\" must be an array"
  let results := claims.map fun (id, e) => resultJson env id (explore env (claimInv e) bound cap)
  let emitLean := match fieldOr root "emitLean" with
    | .bool true => true
    | _ => false
  let out : Value := Encode.o ([("faults", Encode.strings (env.faults.map (·.id))),
      ("results", Encode.a results)] ++
      (if emitLean then [("leanInput", .str i.toLean)] else []))
  pure (Json.write out)

/-- `exploreValue` on JSON text: what `exegra-lean explore` runs. -/
def runExplore (text : String) : Except String String := do
  let req ← Json.parse text
  exploreValue req

end Exegra
