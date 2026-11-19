import Exegra.Json

/-
The engine input, format `exegra-sim-input` version 1 (`docs/simulation.md`, "Engine input";
`engine/exegra-engine/src/input.rs`).

Decoding checks the format and version first, then the shape of every field the engine reads,
in the engine's order and with its refusal messages (ORDER marks where the order of the checks
decides which refusal is reported). Literal values (variable initials, payloads, literal `to`
and payload entries) are kept as values, untouched.
-/

namespace Exegra

structure StepIn where
  time : Float
  event : String
  /-- `payload ?? {}`. -/
  payload : Value
  deriving Inhabited

structure VariableIn where
  name : String
  /-- `undef` when the input has no `initial`. -/
  initial : Value
  deriving Inhabited

inductive Effect where
  /-- `{set, to}`; `to` is `none` when absent (an error when the effect runs). -/
  | set (varName : String) (to : Option Value)
  /-- `{emit, after, payload}` with `after ?? 0` and `payload ?? {}` applied. -/
  | emit (event : String) (after : Float) (payload : List (String × Value))
  /-- Neither `set` nor `emit` (an error when the effect runs). -/
  | malformed
  deriving Inhabited

structure TransitionIn where
  id : String
  source : String
  target : String
  on : String
  /-- The guard when it is a string; anything else means no guard. -/
  guard : Option String
  effects : List Effect
  /-- `faultOnly === true`. -/
  faultOnly : Bool
  deriving Inhabited

structure BehaviorIn where
  id : String
  /-- Used only for `responsible`, and only when it is a string. -/
  subject : Option String
  initial : String
  variables : List VariableIn
  transitions : List TransitionIn
  /-- The declared types of the references its expressions read (`types`, WG-4902). -/
  types : List (String × STy) := []
  deriving Inhabited

/-- How a fault's `occurrence` matches an attempt number. -/
inductive Occurrence where
  /-- No `occurrence`: every attempt. -/
  | any
  /-- A number: that attempt only. -/
  | exactly (n : Float)
  /-- Present but not a number: `occurrence === attempt` never holds. -/
  | never
  deriving Inhabited

def Occurrence.matches : Occurrence → Nat → Bool
  | .any, _ => true
  | .exactly n, k => n == k.toFloat
  | .never, _ => false

structure FaultIn where
  id : String
  kind : Option String
  event : Option String
  transition : Option String
  occurrence : Occurrence
  /-- `by` of a `delay-event` fault (required for that kind), else 0. -/
  delayBy : Float
  /-- `at` of an `inject-event` fault (required for that kind), else 0. -/
  injectAt : Float
  /-- `payload ?? {}`. -/
  payload : Value
  deriving Inhabited

def FaultIn.isKind (f : FaultIn) (k : String) : Bool := f.kind == some k

structure ScenarioIn where
  id : String
  steps : List StepIn
  /-- The active fault ids as listed; the semantics removes repeats. -/
  faults : List String
  /-- `stepLimit ?? 1000`. -/
  stepLimit : Float
  deriving Inhabited

structure SimInput where
  scenario : ScenarioIn
  behaviors : List BehaviorIn
  events : List String
  faults : List FaultIn
  deriving Inhabited

/-! ## Decoding -/

namespace Decode

abbrev R := Except String

def field (o : List (String × Value)) (key : String) : Value := (objGet? o key).getD .undef

def object (v : Value) (what : String) : R (List (String × Value)) :=
  match v with
  | .obj _ fs => .ok fs
  | _ => .error s!"{what} must be an object."

def string (o : List (String × Value)) (key what : String) : R String :=
  match field o key with
  | .str s => .ok s
  | _ => .error s!"{what}: \"{key}\" must be a string."

def number (o : List (String × Value)) (key what : String) : R Float :=
  match field o key with
  | .num x => .ok x
  | _ => .error s!"{what}: \"{key}\" must be a number."

def array (o : List (String × Value)) (key what : String) : R (List Value) :=
  match field o key with
  | .arr _ xs => .ok xs
  | _ => .error s!"{what}: \"{key}\" must be an array."

/-- `Array.isArray(x) ? x : []`. -/
def arrayOrEmpty (o : List (String × Value)) (key : String) : List Value :=
  match field o key with
  | .arr _ xs => xs
  | _ => []

/-- `x ?? {}`. -/
def payloadOrEmpty (v : Value) : Value := if v.isNullish then .obj 0 [] else v

/-- Map with the element index, stopping at the first error. -/
def mapIdx {α β} (f : Nat → α → R β) (xs : List α) : R (List β) :=
  let rec go (i : Nat) : List α → R (List β)
    | [] => .ok []
    | x :: xs => do let y ← f i x; let ys ← go (i + 1) xs; pure (y :: ys)
  go 0 xs

def effect (v : Value) (what : String) : R Effect :=
  match v with
  | .obj _ fx =>
    if objHas fx "set" then
      let to := match field fx "to" with
        | .undef => none
        | other => some other
      do
        let varName ← string fx "set" what
        pure (.set varName to)
    else if objHas fx "emit" then do
      -- ORDER: `after`, then `payload`, then the event id.
      let after ← match field fx "after" with
        | .num x => pure x
        | x => if x.isNullish then pure 0 else throw s!"{what}: \"after\" must be a number."
      let payload ← match field fx "payload" with
        | .obj _ fs => pure fs
        | x => if x.isNullish then pure [] else throw s!"{what}: \"payload\" must be an object."
      let event ← string fx "emit" what
      pure (.emit event after payload)
    else .ok .malformed
  | _ => .ok .malformed

def transition (v : Value) (what : String) : R TransitionIn := do
  let t ← object v what
  -- ORDER: the effects are decoded before the transition's own fields.
  let effects ← mapIdx (fun k fx => effect fx s!"{what}.effects[{k}]") (arrayOrEmpty t "effects")
  let id ← string t "id" what
  let source ← string t "from" what
  let target ← string t "to" what
  let on ← string t "on" what
  let guard := match field t "guard" with
    | .str s => some s
    | _ => none
  let faultOnly := match field t "faultOnly" with
    | .bool true => true
    | _ => false
  pure { id, source, target, on, guard, effects, faultOnly }

def behavior (v : Value) (i : Nat) : R BehaviorIn := do
  let what := s!"behaviors[{i}]"
  let b ← object v what
  -- ORDER: id, variables, transitions, then initial.
  let id ← string b "id" what
  let variables ← mapIdx (fun j var => do
      let vw := s!"{what}.variables[{j}]"
      let o ← object var vw
      let name ← string o "name" vw
      pure { name, initial := field o "initial" : VariableIn })
    (arrayOrEmpty b "variables")
  let transitions ← mapIdx (fun j t => transition t s!"{what}.transitions[{j}]")
    (arrayOrEmpty b "transitions")
  let subject := (field b "subject").asString?
  let initial ← string b "initial" what
  pure { id, subject, initial, variables, transitions, types := tysOfValue (field b "types") }

def fault (v : Value) (i : Nat) : R FaultIn := do
  let what := s!"faults[{i}]"
  let f ← object v what
  let optString (key : String) : R (Option String) :=
    match field f key with
    | .undef => .ok none
    | .str s => .ok (some s)
    | _ => .error s!"{what}: \"{key}\" must be a string."
  -- ORDER: kind, occurrence, by, at, id, event, transition, payload.
  let kind ← optString "kind"
  let occurrence := match field f "occurrence" with
    | .undef => Occurrence.any
    | .num n => .exactly n
    | _ => .never
  let delayBy ← if kind == some "delay-event" then number f "by" what else pure 0
  let injectAt ← if kind == some "inject-event" then number f "at" what else pure 0
  let id ← string f "id" what
  let event ← optString "event"
  let transition ← optString "transition"
  pure { id, kind, event, transition, occurrence, delayBy, injectAt,
         payload := payloadOrEmpty (field f "payload") }

def formatError : String := "Not an engine input: \"format\" must be \"exegra-sim-input\"."

/-- Decode a parsed engine input. Errors are refusals, not traces. -/
def input (v : Value) : R SimInput := do
  let root ← match v with
    | .obj _ fs => pure fs
    | _ => throw formatError
  if (field root "format").asString? != some "exegra-sim-input" then throw formatError
  let version := field root "version"
  match version with
  | .num x => if x == 1 then pure () else
      throw s!"Unsupported engine input version {version.display}; this engine reads version 1."
  | _ => throw s!"Unsupported engine input version {version.display}; this engine reads version 1."
  -- ORDER: events, behaviors, faults, then the scenario.
  let events ← mapIdx (fun i e => do
      let o ← object e s!"events[{i}]"
      string o "id" s!"events[{i}]")
    (← array root "events" "input")
  let behaviors ← mapIdx (fun i b => behavior b i) (← array root "behaviors" "input")
  let faults ← mapIdx (fun i f => fault f i) (← array root "faults" "input")
  let sc ← object (field root "scenario") "scenario"
  let id ← string sc "id" "scenario"
  let steps ← mapIdx (fun i st => do
      let what := s!"scenario.steps[{i}]"
      let o ← object st what
      let time ← number o "at" what
      let event ← string o "event" what
      pure { time, event, payload := payloadOrEmpty (field o "payload") : StepIn })
    (← array sc "steps" "scenario")
  let faultIds ← match field sc "faults" with
    | .arr _ xs => xs.mapM fun
        | .str s => pure s
        | _ => throw "scenario.faults must hold strings."
    | x => if x.isNullish then pure [] else throw "scenario: \"faults\" must be an array."
  let stepLimit ← match field sc "stepLimit" with
    | .num x => pure x
    | x => if x.isNullish then pure 1000 else throw "scenario: \"stepLimit\" must be a number."
  pure { scenario := { id, steps, faults := faultIds, stepLimit }, behaviors, events, faults }

end Decode

end Exegra
