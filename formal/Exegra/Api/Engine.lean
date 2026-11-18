import Exegra.Api.Basic
import Exegra.Format2
import Exegra.Prove
import Exegra.Temporal
import Exegra.Impl.Refinement

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

def entries : List Entry := [
  { name := "engine.run",
    doc := "An engine input (format 1 or 2) to its trace.",
    fn := Impl.runAnyValue },
  { name := "engine.explore",
    doc := "An exploration request {input, claims, bound, maxStates, emitLean?} to the explorer's result per claim.",
    fn := exploreValue },
  { name := "engine.temporal",
    doc := "A temporal request {input, claims, bound, maxStates, emitLean?} to the checker's result per claim.",
    fn := temporalValue }
]

end Exegra.Api.Engine
