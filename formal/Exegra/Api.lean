import Exegra.Api.Basic
import Exegra.Api.Engine
import Exegra.Api.Model
import Exegra.Api.Verdict
import Exegra.Api.Boundary

/-!
The one entry point of the Lean core for the JavaScript shell (`src/core/lean.js`): a JSON
request `{"fn": <name>, "args": <JSON>}` to a JSON reply, `{"ok": <result>}` or
`{"error": <message>}`. The reply is always one of the two: an unknown function, a malformed
request and a refusal by the function are all `error` replies, never a trap.

**Adding functions.** A module port defines its functions in its own file under `Exegra/Api/`,
as a list of `Entry` (see `Exegra/Api/Engine.lean`), imports it here and appends the list to
`modules`. Nothing else changes: the C glue (`formal/wasm/glue.c`), the exported symbol and the
JS binding take any registered name. `registry_names_nodup` fails the build if two entries share
a name.
-/

namespace Exegra.Api

/-- The functions of the module ports, in lookup order. -/
def modules : List Entry := Engine.entries ++ ModelPort.entries ++ VerdictPort.entries ++ BoundaryPort.entries

def functionsDoc : String := "The registered functions, [{name, doc}], in lookup order."

/-- `[{name, doc}]` as JSON text. -/
def describe (es : List (String × String)) : String :=
  Json.write (.arr 0 (es.map fun (n, d) => .obj 0 [("name", .str n), ("doc", .str d)]))

/-- Every function the shell can call: the module ports' and `api.functions`. -/
def registry : List Entry :=
  modules ++ [{ name := "api.functions", doc := functionsDoc,
                fn := fun _ => pure (describe (modules.map (fun e => (e.name, e.doc)) ++
                  [("api.functions", functionsDoc)])) }]

/-- The function registered under a name. -/
def lookup (name : String) : Option Fn := (registry.find? (·.name == name)).map (·.fn)

/-- Call a registered function. -/
def call (name : String) (args : Value) : Except String String :=
  match lookup name with
  | some f => f args
  | none => .error s!"unknown function \"{name}\""

/-- Read a request `{"fn": <name>, "args": <JSON>}`; `args` may be left out. -/
def request (text : String) : Except String (String × Value) := do
  let v ← Json.parse text
  match v with
  | .obj _ fs =>
    match objGet? fs "fn" with
    | some (.str name) => pure (name, (objGet? fs "args").getD .null)
    | _ => throw "the request has no \"fn\" string"
  | _ => throw "the request must be an object {\"fn\", \"args\"}"

/-- The reply to one request: `{"ok": <result JSON>}` or `{"error": <message>}`. -/
def handle (text : String) : String :=
  match request text >>= fun (name, args) => call name args with
  | .ok out => "{\"ok\":" ++ out ++ "}"
  | .error msg => "{\"error\":" ++ Json.quote msg ++ "}"

/-- The exported symbol the C glue calls (`formal/wasm/glue.c`). -/
@[export exegra_call]
def callExport (text : String) : String := handle text

/-! ## What the boundary guarantees -/

/-- No two registered functions share a name, so a name selects exactly one function. -/
theorem registry_names_nodup : (registry.map (·.name)).Nodup := by decide

/-- The engine at the boundary is the implementation `exegra-lean` runs, on the parsed input. -/
theorem call_engine_run (v : Value) : call "engine.run" v = Impl.runAnyValue v := rfl

/-- The engine at the boundary computes the definition's dispatch (`Exegra.runAnyValue`,
`Exegra/Format2B.lean`), by the refinement theorem `Impl.runAnyValue_eq`. That is all this states:
for an input the elaborator accepts the definition runs `traceOfB`, the fold of the calculus
scheduler (`V2.runB_terminates`, `V2.runB_reach`); an input outside the fragment runs the legacy
interpreter, about which no theorem of the calculus says anything; a version-1 input is refused. -/
theorem call_engine_run_spec (v : Value) : call "engine.run" v = runAnyValue v :=
  Impl.runAnyValue_eq v

/-- The boundary refinement check at the call boundary is `Boundary.refineValue` (docs/composition.md). -/
theorem call_engine_refineBoundary (v : Value) : call "engine.refineBoundary" v = Boundary.refineValue v := rfl

theorem call_engine_boundary (v : Value) : call "engine.boundary" v = Boundary.boundaryValue v := rfl

theorem call_engine_explore (v : Value) : call "engine.explore" v = V2.ProveB.exploreValue v := rfl

theorem call_engine_temporal (v : Value) : call "engine.temporal" v = V2.ProveB.temporalValue v := rfl

/-- `exegra-lean`'s engine is the boundary's `engine.run` after parsing its input text. -/
theorem implRunAny_eq_parse_call (text : String) :
    Impl.runAny text = (Json.parse text >>= call "engine.run") := rfl

/-- The definition on input text is the boundary's `engine.run` after parsing its input text. -/
theorem runAny_eq_parse_call (text : String) :
    runAny text = (Json.parse text >>= call "engine.run") := by
  rw [← Impl.runAny_eq]
  rfl

/-- `model.derive` at the boundary is the model derivation, written as JSON. -/
theorem call_model_derive (v : Value) : call "model.derive" v = Model.deriveValue v := rfl

/-- **Model derivation is total at the boundary**: `model.derive` answers every argument value
with a result, never with an error (and, being a Lean definition, always returns). -/
theorem call_model_derive_total (v : Value) : ∃ out, call "model.derive" v = .ok out := ⟨_, rfl⟩

/-- `claims.status` at the boundary is the verdict of `Exegra.Verdict.status`, written as JSON. -/
theorem call_claims_status (v : Value) : call "claims.status" v = Verdict.statusValue v := rfl

/-- `verdict.isRegression` at the boundary is `Exegra.Verdict.isRegression` over each pair. -/
theorem call_verdict_isRegression (v : Value) :
    call "verdict.isRegression" v = Verdict.regressionValue v := rfl

/-- `hash.semantic` at the boundary computes the definition of the semantic hash
(`Exegra.Hash.semanticHash`) of the declarations it is given, by `Hash.semanticHash'_eq`. -/
theorem call_hash_semantic (v : Value) :
    call "hash.semantic" v = .ok (Json.quote (Hash.semanticHash (Model.get v "schemaVersion")
      (Model.get v "vocabulary") (ModelPort.decls v))) := by
  show ModelPort.semanticValue v = _
  simp [ModelPort.semanticValue, Hash.semanticHash'_eq]

end Exegra.Api
