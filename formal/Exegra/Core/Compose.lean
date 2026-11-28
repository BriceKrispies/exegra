import Exegra.Core.Live

/-
Components and their parallel composition (WG-5685, criteria 1 to 3).

* `Lang α`, a set of finite label sequences, with membership, inclusion and intersection, and
  `Lang.PrefixClosed`.
* `LTS.Path M s l u` (from `s` the labels `l` lead to `u`) and `LTS.Traces M`, the label sequences
  of the finite runs from an initial state; traces are prefix-closed (`LTS.traces_prefixClosed`).
* `Iface α`: the inputs and outputs of a component, disjoint. A component (`Comp σ α`) is an `LTS`
  with an interface; its alphabet is its inputs followed by its outputs.
* `Comp.compose A B` steps jointly on a label in both alphabets, lets either side step alone on a
  label only in its own alphabet (the other keeps its state) and has no step on any other label.
  Its outputs are both sides' outputs and its inputs the remaining inputs.
* `Iso M N`: a bijection on states mapping initial states to initial states and steps to steps with
  the same label, both ways. `compose_comm` and `compose_assoc`.
* `t ↾ L`, the restriction of a trace to the labels of `L`, and the projection lemma
  `traces_compose`.
-/

namespace Exegra.Core

/-- A language: a set of finite label sequences. -/
def Lang (α : Type) := List α → Prop

namespace Lang

variable {α : Type}

instance : Membership (List α) (Lang α) := ⟨fun L t => L t⟩
instance : HasSubset (Lang α) := ⟨fun L K => ∀ t, t ∈ L → t ∈ K⟩
instance : Inter (Lang α) := ⟨fun L K t => t ∈ L ∧ t ∈ K⟩

theorem mem_def {L : Lang α} {t : List α} : t ∈ L ↔ L t := Iff.rfl
theorem mem_inter {L K : Lang α} {t : List α} : t ∈ L ∩ K ↔ t ∈ L ∧ t ∈ K := Iff.rfl

/-- Every sequence. -/
def univ : Lang α := fun _ => True

/-- Every prefix of a member is a member. -/
def PrefixClosed (L : Lang α) : Prop := ∀ t u, t ++ u ∈ L → t ∈ L

end Lang

namespace LTS

variable {σ α : Type}

/-- From `s`, the labels `l` lead to `u` by steps of `M`. -/
inductive Path (M : LTS σ α) : σ → List α → σ → Prop
  | nil (s : σ) : Path M s [] s
  | cons {s t u : σ} {a : α} {l : List α} : M.step s a t → Path M t l u → Path M s (a :: l) u

theorem path_nil_iff {M : LTS σ α} {s u : σ} : M.Path s [] u ↔ u = s := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil _

theorem path_cons_iff {M : LTS σ α} {s u : σ} {a : α} {l : List α} :
    M.Path s (a :: l) u ↔ ∃ t, M.step s a t ∧ M.Path t l u := by
  constructor
  · intro h; cases h with | cons h1 h2 => exact ⟨_, h1, h2⟩
  · rintro ⟨t, h1, h2⟩; exact .cons h1 h2

theorem path_append {M : LTS σ α} : ∀ {s u : σ} {l₁ l₂ : List α},
    M.Path s (l₁ ++ l₂) u ↔ ∃ v, M.Path s l₁ v ∧ M.Path v l₂ u
  | s, u, [], l₂ => by simp [path_nil_iff]
  | s, u, a :: l₁, l₂ => by
    simp only [List.cons_append, path_cons_iff]
    constructor
    · rintro ⟨t, h1, h2⟩
      obtain ⟨v, h3, h4⟩ := path_append.1 h2
      exact ⟨v, ⟨t, h1, h3⟩, h4⟩
    · rintro ⟨v, ⟨t, h1, h3⟩, h4⟩
      exact ⟨t, h1, path_append.2 ⟨v, h3, h4⟩⟩

/-- The label sequences of the finite runs of `M` from an initial state. -/
def Traces (M : LTS σ α) : Lang α := fun l => ∃ s u, M.init s ∧ M.Path s l u

theorem traces_prefixClosed (M : LTS σ α) : M.Traces.PrefixClosed := by
  rintro t v ⟨s, u, hs, hp⟩
  obtain ⟨w, hw, _⟩ := path_append.1 hp
  exact ⟨s, w, hs, hw⟩

theorem reach_of_path {M : LTS σ α} {s u : σ} {l : List α} (hs : M.Reach s) (h : M.Path s l u) :
    M.Reach u := by
  induction h with
  | nil => exact hs
  | cons hst _ ih => exact ih (.step hs hst)

end LTS

/-- The interface of a component: its input and output labels, disjoint. -/
structure Iface (α : Type) where
  inputs : List α
  outputs : List α
  disjoint : ∀ a, a ∈ inputs → a ∉ outputs

/-- The alphabet of an interface: its inputs and its outputs. -/
def Iface.alpha {α : Type} (I : Iface α) : List α := I.inputs ++ I.outputs

/-- A component: a labelled transition system with an interface. -/
structure Comp (σ α : Type) extends LTS σ α where
  iface : Iface α

/-- Two transition systems over the same labels are isomorphic: a bijection on states maps
initial states to initial states and steps to steps with the same label, both ways. -/
def Iso {σ τ α : Type} (M : LTS σ α) (N : LTS τ α) : Prop :=
  ∃ (f : σ → τ) (g : τ → σ), (∀ s, g (f s) = s) ∧ (∀ t, f (g t) = t) ∧
    (∀ s, M.init s ↔ N.init (f s)) ∧ (∀ s a t, M.step s a t ↔ N.step (f s) a (f t))

/-- The restriction of a trace to the labels of `L`. -/
def restrict {α : Type} [DecidableEq α] (t : List α) (L : List α) : List α :=
  t.filter (fun a => decide (a ∈ L))

@[inherit_doc] infixl:70 " ↾ " => restrict

namespace Comp

variable {σ τ υ α : Type}

instance : Coe (Comp σ α) (LTS σ α) := ⟨Comp.toLTS⟩

/-- The alphabet of a component. -/
def alpha (A : Comp σ α) : List α := A.iface.alpha

/-- The traces of a component (of its transition system). -/
def Traces (A : Comp σ α) : Lang α := A.toLTS.Traces

variable [DecidableEq α]

/-- The interface of a composition: both sides' outputs, and the inputs neither side outputs. -/
def Iface.compose (I J : Iface α) : Iface α where
  inputs := (I.inputs ++ J.inputs).filter (fun a => decide (a ∉ I.outputs ++ J.outputs))
  outputs := I.outputs ++ J.outputs
  disjoint := by
    intro a ha
    simp only [List.mem_filter, decide_eq_true_eq] at ha
    exact ha.2

/-- **Parallel composition** (criterion 1). A label in both alphabets is a joint step; a label in
one alphabet only is a step of that side alone, the other keeping its state; a label in neither has
no step. -/
def compose (A : Comp σ α) (B : Comp τ α) : Comp (σ × τ) α where
  init p := A.init p.1 ∧ B.init p.2
  step p a q :=
    (a ∈ A.alpha ∧ a ∈ B.alpha ∧ A.step p.1 a q.1 ∧ B.step p.2 a q.2) ∨
    (a ∈ A.alpha ∧ a ∉ B.alpha ∧ A.step p.1 a q.1 ∧ q.2 = p.2) ∨
    (a ∉ A.alpha ∧ a ∈ B.alpha ∧ q.1 = p.1 ∧ B.step p.2 a q.2)
  iface := Iface.compose A.iface B.iface

theorem mem_alpha_compose {A : Comp σ α} {B : Comp τ α} {a : α} :
    a ∈ (compose A B).alpha ↔ a ∈ A.alpha ∨ a ∈ B.alpha := by
  simp only [alpha, compose, Iface.alpha, Iface.compose, List.mem_append, List.mem_filter,
    decide_eq_true_eq]
  by_cases h1 : a ∈ A.iface.outputs <;> by_cases h2 : a ∈ B.iface.outputs <;> simp [h1, h2]

theorem step_compose {A : Comp σ α} {B : Comp τ α} {p q : σ × τ} {a : α} :
    (compose A B).step p a q ↔
      (a ∈ A.alpha ∧ a ∈ B.alpha ∧ A.step p.1 a q.1 ∧ B.step p.2 a q.2) ∨
      (a ∈ A.alpha ∧ a ∉ B.alpha ∧ A.step p.1 a q.1 ∧ q.2 = p.2) ∨
      (a ∉ A.alpha ∧ a ∈ B.alpha ∧ q.1 = p.1 ∧ B.step p.2 a q.2) := Iff.rfl

theorem init_compose {A : Comp σ α} {B : Comp τ α} {p : σ × τ} :
    (compose A B).init p ↔ A.init p.1 ∧ B.init p.2 := Iff.rfl

/-- Isomorphism of components: of their transition systems. -/
def Iso (A : Comp σ α) (B : Comp τ α) : Prop := Exegra.Core.Iso A.toLTS B.toLTS

/-- `compose A B` is isomorphic to `compose B A`, by swapping the components of the state. -/
theorem compose_comm (A : Comp σ α) (B : Comp τ α) : Iso (compose A B) (compose B A) := by
  unfold Iso
  refine ⟨Prod.swap, Prod.swap, fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · intro s; simp only [compose, Prod.fst_swap, Prod.snd_swap]; exact And.comm
  · intro s a t
    simp only [compose, Prod.fst_swap, Prod.snd_swap]
    by_cases ha : a ∈ A.alpha <;> by_cases hb : a ∈ B.alpha <;> simp [ha, hb, and_comm]

/-- Composition is associative up to isomorphism, by reassociating the state. -/
theorem compose_assoc (A : Comp σ α) (B : Comp τ α) (C : Comp υ α) :
    Iso (compose (compose A B) C) (compose A (compose B C)) := by
  unfold Iso
  refine ⟨fun p => (p.1.1, (p.1.2, p.2)), fun p => ((p.1, p.2.1), p.2.2),
    fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · intro s; simp only [init_compose]; exact and_assoc
  · rintro ⟨⟨s1, s2⟩, s3⟩ a ⟨⟨t1, t2⟩, t3⟩
    simp only [step_compose, mem_alpha_compose]
    by_cases ha : a ∈ A.alpha <;> by_cases hb : a ∈ B.alpha <;> by_cases hc : a ∈ C.alpha <;>
      simp [ha, hb, hc, Prod.ext_iff, and_assoc] <;> grind

/-- The paths of a composition are the pairs of paths of its sides along the restrictions of a
trace over the two alphabets. -/
theorem path_compose {A : Comp σ α} {B : Comp τ α} :
    ∀ (t : List α) (s1 : σ) (s2 : τ) (u1 : σ) (u2 : τ),
      (compose A B).Path (s1, s2) t (u1, u2) ↔
        (∀ a ∈ t, a ∈ A.alpha ∨ a ∈ B.alpha) ∧ A.Path s1 (t ↾ A.alpha) u1 ∧
          B.Path s2 (t ↾ B.alpha) u2
  | [], s1, s2, u1, u2 => by
    simp only [LTS.path_nil_iff, restrict, List.filter_nil, Prod.mk.injEq, List.not_mem_nil,
      false_implies, implies_true, true_and]
  | a :: l, s1, s2, u1, u2 => by
    have ih := path_compose (A := A) (B := B) l
    rw [LTS.path_cons_iff]
    have hfA : (a :: l) ↾ A.alpha = if a ∈ A.alpha then a :: (l ↾ A.alpha) else l ↾ A.alpha := by
      by_cases h : a ∈ A.alpha <;> simp [restrict, h]
    have hfB : (a :: l) ↾ B.alpha = if a ∈ B.alpha then a :: (l ↾ B.alpha) else l ↾ B.alpha := by
      by_cases h : a ∈ B.alpha <;> simp [restrict, h]
    rw [hfA, hfB, List.forall_mem_cons]
    by_cases ha : a ∈ A.alpha <;> by_cases hb : a ∈ B.alpha
    · simp only [ha, hb, ↓reduceIte]
      constructor
      · rintro ⟨⟨v1, v2⟩, hst, hp⟩
        obtain ⟨hall, hA, hB⟩ := (ih v1 v2 u1 u2).1 hp
        rcases hst with ⟨-, -, h1, h2⟩ | ⟨-, hb', -⟩ | ⟨ha', -⟩
        · exact ⟨⟨by simp, hall⟩, .cons h1 hA, .cons h2 hB⟩
        · exact absurd hb hb'
        · exact absurd ha ha'
      · rintro ⟨⟨-, hall⟩, hA, hB⟩
        rw [LTS.path_cons_iff] at hA hB
        obtain ⟨v1, h1, hA⟩ := hA
        obtain ⟨v2, h2, hB⟩ := hB
        exact ⟨(v1, v2), Or.inl ⟨ha, hb, h1, h2⟩, (ih v1 v2 u1 u2).2 ⟨hall, hA, hB⟩⟩
    · simp only [ha, hb, ↓reduceIte]
      constructor
      · rintro ⟨⟨v1, v2⟩, hst, hp⟩
        rcases hst with ⟨-, hb', -⟩ | ⟨-, -, h1, h2⟩ | ⟨ha', -⟩
        · exact absurd hb' hb
        · obtain rfl : v2 = s2 := h2
          obtain ⟨hall, hA, hB⟩ := (ih v1 v2 u1 u2).1 hp
          exact ⟨⟨by simp, hall⟩, .cons h1 hA, hB⟩
        · exact absurd ha ha'
      · rintro ⟨⟨-, hall⟩, hA, hB⟩
        rw [LTS.path_cons_iff] at hA
        obtain ⟨v1, h1, hA⟩ := hA
        exact ⟨(v1, s2), Or.inr (Or.inl ⟨ha, hb, h1, rfl⟩), (ih v1 s2 u1 u2).2 ⟨hall, hA, hB⟩⟩
    · simp only [ha, hb, ↓reduceIte]
      constructor
      · rintro ⟨⟨v1, v2⟩, hst, hp⟩
        rcases hst with ⟨ha', -⟩ | ⟨ha', -⟩ | ⟨-, -, h1, h2⟩
        · exact absurd ha' ha
        · exact absurd ha' ha
        · obtain rfl : v1 = s1 := h1
          obtain ⟨hall, hA, hB⟩ := (ih v1 v2 u1 u2).1 hp
          exact ⟨⟨by simp, hall⟩, hA, .cons h2 hB⟩
      · rintro ⟨⟨-, hall⟩, hA, hB⟩
        rw [LTS.path_cons_iff] at hB
        obtain ⟨v2, h2, hB⟩ := hB
        exact ⟨(s1, v2), Or.inr (Or.inr ⟨ha, hb, rfl, h2⟩), (ih s1 v2 u1 u2).2 ⟨hall, hA, hB⟩⟩
    · constructor
      · rintro ⟨⟨v1, v2⟩, hst, -⟩
        rcases hst with ⟨ha', -⟩ | ⟨ha', -⟩ | ⟨-, hb', -⟩
        · exact absurd ha' ha
        · exact absurd ha' ha
        · exact absurd hb' hb
      · rintro ⟨⟨h | h, -⟩, -⟩
        · exact absurd h ha
        · exact absurd h hb

/-- **Projection lemma** (criterion 3): `t ∈ Traces (compose A B) ↔ t ⊆ (αA ∪ αB)* ∧
t ↾ αA ∈ Traces A ∧ t ↾ αB ∈ Traces B`; the union of the alphabets is their concatenation as lists. -/
theorem traces_compose (A : Comp σ α) (B : Comp τ α) (t : List α) :
    t ∈ Traces (compose A B) ↔
      t ⊆ A.alpha ++ B.alpha ∧ t ↾ A.alpha ∈ Traces A ∧ t ↾ B.alpha ∈ Traces B := by
  have hsub : t ⊆ A.alpha ++ B.alpha ↔ ∀ a ∈ t, a ∈ A.alpha ∨ a ∈ B.alpha := by
    simp only [List.subset_def, List.mem_append]
  rw [hsub]
  constructor
  · rintro ⟨⟨s1, s2⟩, ⟨u1, u2⟩, ⟨h1, h2⟩, hp⟩
    obtain ⟨hall, hA, hB⟩ := (path_compose t s1 s2 u1 u2).1 hp
    exact ⟨hall, ⟨s1, u1, h1, hA⟩, ⟨s2, u2, h2, hB⟩⟩
  · rintro ⟨hall, ⟨s1, u1, h1, hA⟩, ⟨s2, u2, h2, hB⟩⟩
    exact ⟨(s1, s2), (u1, u2), ⟨h1, h2⟩, (path_compose t s1 s2 u1 u2).2 ⟨hall, hA, hB⟩⟩

end Comp

end Exegra.Core

/-- info: 'Exegra.Core.Comp.compose_comm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Core.Comp.compose_comm

/-- info: 'Exegra.Core.Comp.compose_assoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Comp.compose_assoc

/-- info: 'Exegra.Core.Comp.traces_compose' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Comp.traces_compose
