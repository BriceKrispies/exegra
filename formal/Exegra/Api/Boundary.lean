import Exegra.Api.Basic
import Exegra.Boundary

/-!
The boundary functions at the call boundary (docs/composition.md): the projection of a trace onto a
boundary (`engine.boundary`) and the comparison of an abstract run with a concrete run
(`engine.refineBoundary`), both defined in `Exegra/Boundary.lean`.
-/

namespace Exegra.Api.BoundaryPort

def entries : List Entry := [
  { name := "engine.boundary",
    doc := "{trace, hidden: [event]} to {steps, hidden}: the boundary trace, the steps whose event is not hidden (docs/composition.md).",
    fn := Boundary.boundaryValue },
  { name := "engine.refineBoundary",
    doc := "{abstract, concrete, hidden, timeScale, environment}: run both engine inputs and compare their boundary traces: a step correspondence (certificate) or the first boundary counterexample (docs/composition.md).",
    fn := Boundary.refineValue }
]

end Exegra.Api.BoundaryPort
