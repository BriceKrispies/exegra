import Exegra.Api.Basic
import Exegra.Boundary
import Exegra.BoundaryExplore

/-!
The boundary functions at the call boundary (docs/composition.md): the projection of a trace onto a
boundary (`engine.boundary`) and the comparison of an abstract run with a concrete run
(`engine.refineBoundary`), both defined in `Exegra/Boundary.lean`, and the exploration of both systems over
every interleaving (`engine.refineExplore`, `Exegra/BoundaryExplore.lean`).
-/

namespace Exegra.Api.BoundaryPort

def entries : List Entry := [
  { name := "engine.boundary",
    doc := "{trace, hidden: [event]} to {steps, hidden}: the boundary trace, the steps whose event is not hidden (docs/composition.md).",
    fn := Boundary.boundaryValue },
  { name := "engine.refineBoundary",
    doc := "{abstract, concrete, hidden, timeScale, environment}: run both engine inputs and compare their boundary traces: a step correspondence (certificate) or the first boundary counterexample (docs/composition.md).",
    fn := Boundary.refineValue },
  { name := "engine.refineExplore",
    doc := "{abstract, concrete, hidden, timeScale, bound, maxStates}: explore both engine inputs over every interleaving, fault mask and draw and check trace inclusion on the boundary: a certificate (explore_holds), a counterexample run of the members, or incomplete (docs/composition.md).",
    fn := Boundary.exploreValue }
]

end Exegra.Api.BoundaryPort
