import Exegra.Api.Basic
import Exegra.Multiscale

/-!
The structural abstraction semantics at the call boundary (WG-5699): the witnessed lift of a fact base
to a cut of a laminar hierarchy, with fibres and boundaries, computed by the definitions
`Exegra/Multiscale.lean` proves P1-P7 and P13 about. The JavaScript derivation (`src/core/abstraction.js`)
is compared with it on every golden cut of the self-specification (`tests/proofs/abstraction-lean.test.js`).
-/

namespace Exegra.Api.StructurePort

def entries : List Entry := [
  { name := "structure.derive",
    doc := "{elements: [{id, parent}], blocks, facts: [{id, from, to, kind}], coarsen?}: the lifted interactions with their witness sets, the fibres, the boundaries and the unplaced facts at the cut (formal/Exegra/Multiscale.lean).",
    fn := Multiscale.deriveValue }
]

end Exegra.Api.StructurePort
