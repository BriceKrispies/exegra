/-
Theorems the lean-theorem method must refuse (tests/core/lean-theorem.test.js). tools/lean-theorems.js
elaborates this file after `import Exegra`, so it is never part of the Lean core and `lake build`
never sees it.
-/

namespace ExegraFixture

/-- Proved with `sorry`: depends on sorryAx. -/
theorem uses_sorry (i : Exegra.V2.Input) : ∃ t, Exegra.V2.runInput i = .ok t := sorry

/-- Proved with `native_decide`: depends on Lean.ofReduceBool, trusting compiled code. -/
theorem uses_native_decide (i : Exegra.V2.Input) :
    Exegra.V2.runInput i = Exegra.V2.runInput i ∧ (2 : Nat) ^ 20 = 1048576 :=
  ⟨rfl, by native_decide⟩

/-- An axiom of our own. -/
axiom always_ok : ∀ i : Exegra.V2.Input, ∃ t, Exegra.V2.runInput i = .ok t

theorem uses_custom_axiom (i : Exegra.V2.Input) : ∃ t, Exegra.V2.runInput i = .ok t := always_ok i

/-- A true theorem whose statement mentions no implementation constant. -/
theorem off_topic : (2 : Nat) + 2 = 4 := rfl

end ExegraFixture
