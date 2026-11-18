import Exegra.Model
import Exegra.HashProps

/-!
# Properties of model derivation

- `derive_refs_resolve`: in a derived model whose diagnostics contain no reference diagnostic
  (`ref.unresolved`, `ref.kind`), every reference names an entity of the model whose kind the
  reference allows.
- `Model.semanticHash_presentation`: the semantic hash of a model is a function of its schema
  version, its vocabulary and its top-level declarations (id, kind, data) up to order; source
  positions, JSON paths, nested declarations' records, references, expressions, the effective
  meta-model and the order of declarations do not enter it.
- Totality: `derive` is a total function (every definition here is; none is `partial`), and at
  the call boundary `model.derive` answers every argument value with a result, never an error
  (`Exegra.Api.call_model_derive_total` in Exegra/Api.lean).
-/

namespace Exegra.Model

open Exegra

theorem mem_resolveRefs {es : List Entity} {refs : List Ref} {r : Ref} {d : Diag}
    (hr : r ∈ refs) (hd : resolveRef es r = some d) : d ∈ resolveRefs es refs :=
  List.mem_filterMap.mpr ⟨r, hr, hd⟩

/-- **References resolve**: when derivation reports no reference diagnostic, every reference of
the model names an entity of the model of a kind the reference allows. -/
theorem derive_refs_resolve (mm methods doc : Value) (m : Model)
    (hm : (derive mm methods doc).model = some m)
    (hd : ∀ d ∈ (derive mm methods doc).diagnostics,
      d.code ≠ "ref.unresolved" ∧ d.code ≠ "ref.kind") :
    ∀ r ∈ m.refs, ∃ e ∈ m.entities, e.id = r.target ∧ allowedKind r.allowed e.kind = true := by
  rcases hb : (build mm methods doc).run {} with ⟨_ | m', st⟩
  · simp [derive, hb] at hm
  · simp only [derive, hb, Option.some.injEq] at hm hd
    subst hm
    intro r hr
    have hdiag : ∀ d, resolveRef m'.entities r = some d → False := by
      intro d hres
      have hmem : d ∈ st.diags.toList ++ resolveRefs m'.entities m'.refs :=
        List.mem_append_right _ (mem_resolveRefs hr hres)
      have := hd d hmem
      unfold resolveRef at hres
      split at hres
      · simp only [Option.some.injEq] at hres; subst hres; exact this.1 rfl
      · split at hres
        · simp at hres
        · simp only [Option.some.injEq] at hres; subst hres; exact this.2 rfl
    cases ht : target? m'.entities r.target with
    | none =>
      exact (hdiag _ (by unfold resolveRef; rw [ht])).elim
    | some e =>
      refine ⟨e, List.mem_of_find?_eq_some ht, ?_, ?_⟩
      · have := List.find?_some ht
        simpa using this
      · cases hk : allowedKind r.allowed e.kind
        · exact (hdiag _ (by unfold resolveRef; rw [ht]; simp only [hk]; rfl)).elim
        · rfl

/-- **The hash sees only semantic content**: two models with the same schema version and
vocabulary and the same top-level declarations, up to order, have the same semantic hash. -/
theorem Model.semanticHash_presentation (m₁ m₂ : Model) (hs : m₁.schemaVersion = m₂.schemaVersion)
    (hv : m₁.vocabulary = m₂.vocabulary) (ht : m₁.top.Perm m₂.top)
    (hn : (m₁.top.map (·.1)).Nodup) :
    m₁.semanticHash = m₂.semanticHash := by
  unfold Model.semanticHash
  rw [hs, hv]
  exact Hash.semanticHash_perm _ _ ht hn

/-- info: 'Exegra.Model.derive_refs_resolve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms derive_refs_resolve

end Exegra.Model
