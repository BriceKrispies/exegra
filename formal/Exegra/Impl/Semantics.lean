import Exegra.Format2B
import Exegra.Impl.Json

/-!
# The engine as the application runs it

`Exegra/Format2B.lean` is the **definition** of what a version-2 engine input runs: `V2.runInput`
dispatches an input the elaborator accepts to the calculus scheduler (`traceOfB`) and an input
outside the fragment to the legacy interpreter, and `Exegra.runAnyValue` refuses any other input.

This file is the **implementation** the application runs (`Exegra.Impl.runAnyValue`, registered
as `engine.run`). It differs from the definition in exactly one way: the trace is written as JSON
by the fast writer `JsonOut.write'` (`Exegra/Impl/Json.lean`) instead of `Json.write`.
`Exegra/Impl/Refinement.lean` proves that the two agree on every input (`Impl.runAnyValue_eq`,
`Impl.runAny_eq`). Format 1, and with it the compiled format-1 engine this file used to hold, is
gone (WG-5681).
-/

namespace Exegra.Impl

/-- `V2.runInput`, writing the trace with the fast writer: the definition's dispatch
(`V2.runInputWith`: the calculus scheduler for elaborated inputs, the legacy `V2.traceOf` for
inputs outside the fragment). -/
def runInputV2 (i : V2.Input) : Except String String := V2.runInputWith JsonOut.write' i

/-- `Exegra.runAnyValue` with the fast writer: a version-2 input runs `runInputV2`; any other
input is refused as the definition refuses it. -/
def runAnyValue (v : Value) : Except String String :=
  match v with
  | .obj _ root =>
    match objGet? root "version", objGet? root "format" with
    | some (.num x), some (.str "exegra-sim-input") =>
      if x == 2 then do runInputV2 (← V2.Decode.input root) else .error formatOneGone
    | _, _ => .error notAnInput
  | _ => .error notAnInput

/-- `runAnyValue` on JSON text: what `exegra-lean` runs. -/
def runAny (text : String) : Except String String := do
  let v ← Json.parse text
  runAnyValue v

end Exegra.Impl
