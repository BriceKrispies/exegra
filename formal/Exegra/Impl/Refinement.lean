import Exegra.Impl.Semantics

/-!
# The implementation refines the definition

For every input, the engine the application runs (`Exegra.Impl`, see `Exegra/Impl/Semantics.lean`)
returns exactly what the definition (`Exegra.runAnyValue`, `Exegra/Format2B.lean`) returns: the two
dispatch alike, and the fast writer `JsonOut.write'` writes what `Json.write` writes
(`JsonOut.write'_eq`). Each statement depends only on Lean's standard axioms (checked at the end of
this file), and the implementation uses no `implemented_by`, `extern` or `csimp` of its own, so the
code the compiler emits is the code these theorems are about.
-/

namespace Exegra.Impl

theorem runInputV2_eq (i : V2.Input) : runInputV2 i = V2.runInput i := by
  unfold runInputV2 V2.runInput
  rw [show JsonOut.write' = Json.write from funext JsonOut.write'_eq]

/-- **The engine the application runs equals the definition** on every parsed input. -/
theorem runAnyValue_eq (v : Value) : Impl.runAnyValue v = Exegra.runAnyValue v := by
  unfold Impl.runAnyValue Exegra.runAnyValue
  simp only [runInputV2_eq]
  rfl

/-- **The engine the application runs equals the definition** on every input text. -/
theorem runAny_eq (text : String) : Impl.runAny text = Exegra.runAny text := by
  unfold Impl.runAny Exegra.runAny
  simp only [runAnyValue_eq]

/-! ## Axiom check -/

/-- info: 'Exegra.Impl.runAnyValue_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runAnyValue_eq

/-- info: 'Exegra.Impl.runAny_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runAny_eq

end Exegra.Impl
