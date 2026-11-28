import Exegra.Core.Compose

/-
Assume-guarantee contracts over traces and the discharge of assumptions (WG-5685, criteria 4 and 5).

* A contract `(A, G)` is a pair of trace languages: an assumption and a guarantee.
* `Comp.Open M`, the traces of the open component `M` in an arbitrary environment: the sequences
  whose restriction to `M`'s alphabet is a trace of `M` (labels outside the alphabet are the
  environment's, and `M` does not constrain them). Over a component whose alphabet contains every
  label they are exactly `M`'s traces (`open_iff_traces`).
* `Sat M (A, G) := ∀ t ∈ Open M, t ∈ A → t ∈ G`; refinement `(A', G') ≼ (A, G) := A ⊆ A' ∧
  G' ⊆ G` (`sat_of_refines`: a component satisfying the finer contract satisfies the coarser one);
  `Compatible`: each guarantee implies the other side's assumption under the assumption of the
  composition.
* `ag_compose`: circular assume-guarantee reasoning is sound for prefix-closed languages under the
  one-step-ahead non-circularity side condition `NonCircular`, and `ag_circular_unsound`: without
  it, a concrete pair of components derives a false `Sat`.
* `DischargeGraph`: each claim's assumptions and, per assumption, the claim that discharges it.
  `discharge_sound`: if the graph is acyclic and every guarantee holds under its assumptions, every
  guarantee holds.
-/

namespace Exegra.Core

namespace Comp

variable {σ τ α : Type} [DecidableEq α]

/-- An assume-guarantee contract: an assumption and a guarantee, both trace languages. -/
abbrev Contract (α : Type) := Lang α × Lang α

/-- The traces of the open component `M`: every sequence whose restriction to `M`'s alphabet is a
trace of `M`. The labels outside the alphabet belong to the environment. -/
def Open (M : Comp σ α) : Lang α := fun t => t ↾ M.alpha ∈ Traces M

/-- Over a component whose alphabet contains every label, its open traces are its traces. -/
theorem open_iff_traces (M : Comp σ α) (hall : ∀ a, a ∈ M.alpha) (t : List α) :
    t ∈ Open M ↔ t ∈ Traces M := by
  have : t ↾ M.alpha = t := by
    simp only [restrict]
    exact List.filter_eq_self.2 (fun a _ => by simp [hall a])
  show t ↾ M.alpha ∈ Traces M ↔ _
  rw [this]

/-- **Satisfaction** (criterion 4): `Sat M (A, G) := ∀ t ∈ Traces M, t ∈ A → t ∈ G`, where the
traces of the component `M` are its traces in an arbitrary environment (`Open M`). -/
def Sat (M : Comp σ α) (c : Contract α) : Prop := ∀ t, t ∈ Open M → t ∈ c.1 → t ∈ c.2

/-- **Refinement** of contracts: `(A', G') ≼ (A, G) := A ⊆ A' ∧ G' ⊆ G` (the finer contract
assumes less and guarantees more). -/
def Refines (c' c : Contract α) : Prop := c.1 ⊆ c'.1 ∧ c'.2 ⊆ c.2

@[inherit_doc] infix:50 " ≼ " => Refines

theorem sat_of_refines {M : Comp σ α} {c' c : Contract α} (h : Sat M c') (hr : c' ≼ c) :
    Sat M c := fun t ht hA => hr.2 t (h t ht (hr.1 t hA))

/-- **Compatibility** of two contracts under the assumption `A` of their composition: each
guarantee implies the other side's assumption. -/
def Compatible (A : Lang α) (c₁ c₂ : Contract α) : Prop :=
  (∀ t, t ∈ A → t ∈ c₂.2 → t ∈ c₁.1) ∧ (∀ t, t ∈ A → t ∈ c₁.2 → t ∈ c₂.1)

/-- `p` is a strict prefix of `t`. -/
def StrictPrefix (p t : List α) : Prop := ∃ u, u ≠ [] ∧ p ++ u = t

/-- **Non-circularity, one step ahead**: under `A`, each side's assumption holds of a trace as soon
as the other side's guarantee holds of every strict prefix of it. -/
def NonCircular (A A₁ A₂ G₁ G₂ : Lang α) : Prop :=
  (∀ t, t ∈ A → (∀ p, StrictPrefix p t → p ∈ G₂) → t ∈ A₁) ∧
  (∀ t, t ∈ A → (∀ p, StrictPrefix p t → p ∈ G₁) → t ∈ A₂)

theorem restrict_append (t u L : List α) : (t ++ u) ↾ L = t ↾ L ++ u ↾ L := by
  simp [restrict, List.filter_append]

theorem restrict_restrict {L K : List α} (h : ∀ a, a ∈ K → a ∈ L) (t : List α) :
    (t ↾ L) ↾ K = t ↾ K := by
  simp only [restrict, List.filter_filter]
  congr 1; funext a
  by_cases hk : a ∈ K
  · simp [hk, h a hk]
  · simp [hk]

/-- A prefix of an open trace of a side of a composition, restricted to that side's alphabet, is a
trace of that side. -/
theorem open_left {M₁ : Comp σ α} {M₂ : Comp τ α} {t p u : List α}
    (ht : t ∈ Open (compose M₁ M₂)) (hp : p ++ u = t) : p ↾ M₁.alpha ∈ Traces M₁ := by
  have h := ((traces_compose M₁ M₂ _).1 ht).2.1
  rw [restrict_restrict (fun a ha => mem_alpha_compose.2 (Or.inl ha)), ← hp,
    restrict_append] at h
  exact LTS.traces_prefixClosed _ _ _ h

theorem open_right {M₁ : Comp σ α} {M₂ : Comp τ α} {t p u : List α}
    (ht : t ∈ Open (compose M₁ M₂)) (hp : p ++ u = t) : p ↾ M₂.alpha ∈ Traces M₂ := by
  have h := ((traces_compose M₁ M₂ _).1 ht).2.2
  rw [restrict_restrict (fun a ha => mem_alpha_compose.2 (Or.inr ha)), ← hp,
    restrict_append] at h
  exact LTS.traces_prefixClosed _ _ _ h

/-- **Circular assume-guarantee composition** (criterion 4): for prefix-closed `A, A₁, A₂, G₁, G₂`,
`Sat M₁ (A₁, G₁) → Sat M₂ (A₂, G₂) → (∀ t, t ∈ A → t ∈ G₂ → t ∈ A₁) →
(∀ t, t ∈ A → t ∈ G₁ → t ∈ A₂) → Sat (compose M₁ M₂) (A, G₁ ∩ G₂)`, with the non-circularity side
condition (each assumption is implied by the other guarantee on every strict prefix) stated as the
hypothesis `NonCircular A A₁ A₂ G₁ G₂`. -/
theorem ag_compose {M₁ : Comp σ α} {M₂ : Comp τ α} {A A₁ A₂ G₁ G₂ : Lang α}
    (hA : A.PrefixClosed) (_hA₁ : A₁.PrefixClosed) (_hA₂ : A₂.PrefixClosed)
    (_hG₁ : G₁.PrefixClosed) (_hG₂ : G₂.PrefixClosed)
    (h₁ : Sat M₁ (A₁, G₁)) (h₂ : Sat M₂ (A₂, G₂))
    (_h₁₂ : ∀ t, t ∈ A → t ∈ G₂ → t ∈ A₁) (_h₂₁ : ∀ t, t ∈ A → t ∈ G₁ → t ∈ A₂)
    (hnc : NonCircular A A₁ A₂ G₁ G₂) :
    Sat (compose M₁ M₂) (A, G₁ ∩ G₂) := by
  intro t ht hAt
  -- Every prefix of `t` is in both guarantees, by strong induction on its length.
  have key : ∀ n p, p.length = n → (∃ u, p ++ u = t) → p ∈ G₁ ∧ p ∈ G₂ := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro p hlen ⟨u, hu⟩
      have hpA : p ∈ A := hA p u (hu ▸ hAt)
      have hpre : ∀ q, StrictPrefix q p → q ∈ G₁ ∧ q ∈ G₂ := by
        rintro q ⟨v, hv, rfl⟩
        refine ih q.length ?_ q rfl ⟨v ++ u, by rw [← hu, List.append_assoc]⟩
        rw [← hlen, List.length_append]
        have : v.length ≠ 0 := by simpa using hv
        omega
      have hp1 : p ∈ A₁ := hnc.1 p hpA (fun q hq => (hpre q hq).2)
      have hp2 : p ∈ A₂ := hnc.2 p hpA (fun q hq => (hpre q hq).1)
      exact ⟨h₁ p (open_left ht hu) hp1, h₂ p (open_right ht hu) hp2⟩
  exact key t.length t rfl ⟨[], List.append_nil t⟩

/-- A one-label component: one state, a self-loop on `()`. -/
def loopComp (inputs outputs : List Unit) (h : ∀ a, a ∈ inputs → a ∉ outputs) : Comp Unit Unit where
  init _ := True
  step _ _ _ := True
  iface := ⟨inputs, outputs, h⟩

/-- The language of the empty trace alone. -/
def onlyNil : Lang Unit := fun t => t = []

theorem onlyNil_prefixClosed : onlyNil.PrefixClosed := by
  intro t u h
  show t = []
  have : t ++ u = [] := h
  exact (List.append_eq_nil_iff.1 this).1

/-- **Circular reasoning without the side condition is unsound** (criterion 4). Two components
that loop on the label they share: each guarantees, assuming the other has done nothing, that it
has done nothing. Every hypothesis of `ag_compose` but `NonCircular` holds, and the conclusion that
the composition never steps is false (it steps on `()`); `NonCircular` fails. -/
theorem ag_circular_unsound :
    ∃ (M₁ M₂ : Comp Unit Unit) (A A₁ A₂ G₁ G₂ : Lang Unit),
      A.PrefixClosed ∧ A₁.PrefixClosed ∧ A₂.PrefixClosed ∧ G₁.PrefixClosed ∧ G₂.PrefixClosed ∧
      Sat M₁ (A₁, G₁) ∧ Sat M₂ (A₂, G₂) ∧
      (∀ t, t ∈ A → t ∈ G₂ → t ∈ A₁) ∧ (∀ t, t ∈ A → t ∈ G₁ → t ∈ A₂) ∧
      ¬ NonCircular A A₁ A₂ G₁ G₂ ∧ ¬ Sat (compose M₁ M₂) (A, G₁ ∩ G₂) := by
  let M₁ := loopComp [] [()] (by simp)
  let M₂ := loopComp [()] [] (by simp)
  have hpc := onlyNil_prefixClosed
  have hcomp : [()] ∈ Open (compose M₁ M₂) := by
    show [()] ↾ (compose M₁ M₂).alpha ∈ Traces (compose M₁ M₂)
    have h1 : () ∈ M₁.alpha := by simp [M₁, loopComp, alpha, Iface.alpha]
    have h2 : () ∈ M₂.alpha := by simp [M₂, loopComp, alpha, Iface.alpha]
    have hr : [()] ↾ (compose M₁ M₂).alpha = [()] := by
      simp [restrict, mem_alpha_compose, h1]
    rw [hr]
    exact ⟨((), ()), ((), ()), ⟨trivial, trivial⟩,
      .cons (Or.inl ⟨h1, h2, trivial, trivial⟩) (.nil _)⟩
  refine ⟨M₁, M₂, Lang.univ, onlyNil, onlyNil, onlyNil, onlyNil,
    fun _ _ _ => trivial, hpc, hpc, hpc, hpc,
    fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, ?_, ?_⟩
  · intro hnc
    have : [()] ∈ onlyNil := hnc.1 [()] trivial (by
      rintro p ⟨u, hu, hpu⟩
      cases p with
      | nil => rfl
      | cons x xs =>
        exfalso
        have hl := congrArg List.length hpu
        simp only [List.length_append, List.length_cons, List.length_nil] at hl
        have : u.length ≠ 0 := by simpa using hu
        omega)
    exact absurd this (by simp [onlyNil, Lang.mem_def])
  · intro h
    have := (h [()] hcomp trivial).1
    exact absurd this (by simp [onlyNil, Lang.mem_def])

end Comp

/-! ### Discharge of assumptions -/

/-- The claims `ι` of a specification, each with its assumptions `κ`, and per assumption the claim
that discharges it. -/
structure DischargeGraph (ι κ : Type) where
  assumes : ι → List κ
  dischargedBy : κ → ι

/-- The discharge graph has no cycle: a ranking of the claims under which every claim ranks above
the claims that discharge its assumptions. A finite graph has such a ranking exactly when it has no
cycle (a topological order); `exegra validate` refuses a cycle (`assumption.discharge-cycle`). -/
def DischargeGraph.Acyclic {ι κ : Type} (D : DischargeGraph ι κ) : Prop :=
  ∃ rank : ι → Nat, ∀ c, ∀ k ∈ D.assumes c, rank (D.dischargedBy k) < rank c

/-- **Discharge is sound** (criterion 5): "if the graph is acyclic and every guarantee holds under
its assumptions, every guarantee holds". `holds c` is the guarantee of claim `c`, `assm k` the
assumption `k`, implied by the guarantee of the claim that discharges it. -/
theorem discharge_sound {ι κ : Type} (D : DischargeGraph ι κ) (holds : ι → Prop) (assm : κ → Prop)
    (hacyc : D.Acyclic) (hdis : ∀ k, holds (D.dischargedBy k) → assm k)
    (hguar : ∀ c, (∀ k ∈ D.assumes c, assm k) → holds c) : ∀ c, holds c := by
  obtain ⟨rank, hrank⟩ := hacyc
  have key : ∀ n c, rank c = n → holds c := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro c hc
      exact hguar c (fun k hk => hdis k (ih _ (hc ▸ hrank c k hk) _ rfl))
  exact fun c => key _ c rfl

end Exegra.Core

/-- info: 'Exegra.Core.Comp.ag_compose' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Comp.ag_compose

/-- info: 'Exegra.Core.Comp.ag_circular_unsound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Comp.ag_circular_unsound

/-- info: 'Exegra.Core.discharge_sound' does not depend on any axioms -/
#guard_msgs in
#print axioms Exegra.Core.discharge_sound
