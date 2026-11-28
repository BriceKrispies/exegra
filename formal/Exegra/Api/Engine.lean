import Exegra.Api.Basic
import Exegra.Format2
import Exegra.Impl.Refinement
import Exegra.Elab
import Exegra.ProveB
import Exegra.Lower
import Exegra.ProveLive

/-!
The simulation engine's functions at the call boundary: the dispatch `exegra-lean` runs, on
parsed JSON. Each is the function the native executable runs on text, after its `Json.parse`
(`runAny = Json.parse >=> runAnyValue`, and so on), so the browser, Node and the native
executable run the same code.

`engine.run` is the implementation `Exegra.Impl.runAnyValue` (expressions parsed once per run),
which `Exegra.Impl.runAnyValue_eq` proves equal to the definition `Exegra.runAnyValue` on every
input.
-/

namespace Exegra.Api.Engine

/-- One expression evaluated as a behavior's expressions are (`Exegra.eval`, WG-4902):
`{expr, env: {path: value}, types: {path: typeName}}`, where a path is dotted. The result is
`{"value": v}`, or `{"error": message}` when parsing or evaluation fails; the shared case table
(`tests/fixtures/expr-cases.json`) is run through it. -/
def exprEvalValue (args : Value) : Except String String :=
  let src := match args with
    | .obj _ fs => ((objGet? fs "expr").bind Value.asString?).getD ""
    | _ => ""
  let env := match args with
    | .obj _ fs => match objGet? fs "env" with
      | some (.obj _ e) => e
      | _ => []
    | _ => []
  let tys := match args with
    | .obj _ fs => tysOfValue ((objGet? fs "types").getD .null)
    | _ => []
  let out : Except String Value := match parseExpr src with
    | .error e => .error e
    | .ok ast => eval (fun p => (objGet? env (".".intercalate p)).getD .undef) (tyLookup tys) ast
  match out with
  | .ok v => .ok ("{\"value\":" ++ Json.write v ++ "}")
  | .error e => .ok ("{\"error\":" ++ Json.quote e ++ "}")

/-- `engine.runScenario`: `{model, scenario, faults?}` to the trace of the scenario's run, the
engine input lowered in Lean (`Exegra.Lower.engineInput`) and run as `engine.run` runs it. -/
def runScenarioValue (args : Value) : Except String String :=
  let (m, sc, faults) := Lower.requestOf args
  match Lower.engineInput m sc faults with
  | .ok v => Impl.runAnyValue v
  | .error e => .error e

def entries : List Entry := [
  { name := "engine.run",
    doc := "A version-2 engine input to its trace (version 1 is refused).",
    fn := Impl.runAnyValue },
  { name := "expr.eval",
    doc := "{expr, env: {path: value}, types: {path: typeName}} to {value} or {error}: one expression evaluated as a behavior's expressions are.",
    fn := exprEvalValue },
  { name := "engine.explore",
    doc := "An exploration request {input, claims, bound, maxStates} (a version-2 input) to the calculus explorer's result per claim.",
    fn := V2.ProveB.exploreValue },
  { name := "engine.elab",
    doc := "A version-2 engine input to its elaboration into the behaviour calculus: {accepted, machines, faults, samples} or {accepted: false, kind, detail, message}.",
    fn := V2.Elab.elabJson },
  { name := "engine.temporal",
    doc := "A temporal request {input, claims, bound, maxStates} (a version-2 input) to the calculus checker's result per claim.",
    fn := V2.ProveB.temporalValue },
  { name := "engine.input",
    doc := "{model: {entities: [{id, kind, owner?, data}]}, scenario, faults?} to the scenario's version-2 engine input, lowered in Lean.",
    fn := Lower.engineInputValue },
  { name := "engine.runScenario",
    doc := "{model, scenario, faults?} to the trace of the scenario's run: its engine input lowered in Lean, run as engine.run runs it.",
    fn := runScenarioValue },
  { name := "lower.tables",
    doc := "{families: [{path, family}]} to the pinned tables' canonical text, the unitExponential table and each family's lowered distribution.",
    fn := Lower.tablesValue },
  { name := "engine.liveness",
    doc := "A liveness request {input, claims: [{id, form: GF|FG, expr, fair: [transition]}], bound, maxStates} to the verdict per claim: proved, violated (with the lasso), incomplete or not supported.",
    fn := V2.ProveLive.livenessValue },
  { name := "claims.exprOnConfigs",
    doc := "{expr, configs: [config]} to [{value} | {error}]: a claim expression evaluated on trace configurations by the evaluator exegra prove uses (claimTruth).",
    fn := V2.ProveB.exprOnConfigsValue },
  { name := "claims.matcherHits",
    doc := "{matcher, steps} to [bool]: whether each trace step has the occurrence (Matcher.hit), as exegra prove decides it.",
    fn := V2.ProveB.matcherHitsValue },
  { name := "claims.formViolation",
    doc := "{form, steps} to {violatedAt, seen}: the monitor of a never, precedes or eventually form (Form.step) over trace steps.",
    fn := V2.ProveB.formViolationValue },
  { name := "engine.certificate",
    doc := "{input, bound, maxStates} to the states of a closed exploration as Lean terms (null when the frontier does not empty).",
    fn := V2.ProveLive.certificateValue }
]

end Exegra.Api.Engine
