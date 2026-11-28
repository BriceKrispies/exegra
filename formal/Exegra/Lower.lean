import Exegra.Lower.Input
import Exegra.Elab

/-!
# Lowering a model to the behaviour calculus

`Exegra.Lower.lower m sc`: scenario `sc` of the model `m` as a system of the behaviour calculus,
through its engine input (`Exegra.Lower.engineInput`, which replaces the JavaScript lowering
`src/core/sim-input.js`, `src/core/pools.js` and `src/core/distributions.js`), the format-2
decoder and the elaborator (`Exegra.V2.Elab.elab`). A scenario whose input the elaborator does not
take (outside the calculus's fragment, or ill-typed) is a `LowerError.refused` with the
elaborator's reason.

At the call boundary the shell sends the model as `{entities: [{id, kind, owner?, data}]}`
(`modelOfValue`); only the entities are read.
-/

namespace Exegra.Lower

open Exegra
open Exegra.Model (Model Entity)

/-- Why a scenario has no system. -/
inductive LowerError where
  /-- The model does not say enough to derive the scenario's engine input (an unknown scenario,
  behavior, event, fault or workload, a malformed duration, rate or distribution). -/
  | input (message : String)
  /-- The engine input is malformed (the format-2 decoder refuses it). -/
  | decode (message : String)
  /-- The elaborator refuses the input. -/
  | refused (r : V2.Elab.Refusal)
  deriving Inhabited

def LowerError.message : LowerError → String
  | .input m => m
  | .decode m => m
  | .refused r => r.message

/-- The decoded engine input of a scenario, with the scenario's own faults or `faults`. -/
def input (m : Model) (sc : String) (faults : Option (List Value) := none) : Except LowerError V2.Input := do
  let v ← (engineInput m sc faults).mapError .input
  match v with
  | .obj _ root => (V2.Decode.input root).mapError .decode
  | _ => throw (.decode "an engine input must be a JSON object")

/-- **The lowering**: scenario `sc` of model `m` as a system of the behaviour calculus. -/
def lower (m : Model) (sc : String) : Except LowerError Core.Behav.Sys := do
  let i ← input m sc
  (V2.Elab.«elab» i).mapError .refused

/-- The step limit of a scenario's runs (`maxSteps`, by default 1000; 1 when it has no input). -/
def stepLimit (m : Model) (sc : String) : Nat :=
  match input m sc with
  | .ok i => i.scenario.stepLimit
  | .error _ => 1

/-! ## At the call boundary -/

/-- A model from `{entities: [{id, kind, owner?, data}]}`: the entities, nothing else. -/
def modelOfValue (v : Value) : Model :=
  let es := (Dist.itemsOf (Dist.mem v "entities")).map fun e =>
    ({ id := (strOf? (Dist.mem e "id")).getD "", kind := (strOf? (Dist.mem e "kind")).getD "",
       data := Dist.mem e "data", owner := strOf? (Dist.mem e "owner"), path := [], raw := [] } : Entity)
  { schemaVersion := .undef, mmeta := .undef, vocabulary := .undef, kinds := [], entities := es,
    refs := [], exprs := [] }

/-- The arguments of a lowering request: `{model, scenario, faults?}`. -/
def requestOf (args : Value) : Model × String × Option (List Value) :=
  let faults := match Dist.mem args "faults" with
    | .arr _ xs => some xs
    | _ => none
  (modelOfValue (Dist.mem args "model"), (strOf? (Dist.mem args "scenario")).getD "", faults)

/-- `engine.input`: `{model, scenario, faults?}` to the scenario's engine input. -/
def engineInputValue (args : Value) : Except String String :=
  let (m, sc, faults) := requestOf args
  (engineInput m sc faults).map Json.write

/-- `lower.tables`: the pinned tables' canonical text and the lowering of each distribution
family of `{families: [{path, family}]}` (a refusal as `{error}`), for the comparison with the
tables the JavaScript lowering built. -/
def tablesValue (args : Value) : Except String String :=
  let fams := (Dist.itemsOf (Dist.mem args "families")).map fun f =>
    let path := (strOf? (Dist.mem f "path")).getD "distribution"
    match Dist.lowerDistribution (Dist.mem f "family") path with
    | .ok v => v
    | .error e => .obj 0 [("error", .str e)]
  .ok (Json.write (.obj 0 [("canonical", .str (Dist.canonicalText Dist.pinnedRows.get)),
    ("unitExponential", Dist.unitExponentialTable), ("families", .arr 0 fams)]))

end Exegra.Lower
