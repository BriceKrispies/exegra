import Exegra.Core.Compose

/-
Refinement by stuttering simulation (WG-5685, criterion 8).

* `Obs α β`: the observation of a label, `none` for an internal one. `ObsTraces M`: the
  observations of the finite traces of `M`, internal labels dropped.
* `Simulates impl spec abs`: initial states map to initial states, and each step of `impl` from a
  reachable state maps through `abs : σI → σS` to a step of `spec` with the same observation, or is
  a stutter that leaves `abs` and the observation unchanged (its label is internal).
* `refines_traces`: the observable finite traces of `impl` are traces of `spec`. `refines_safety`:
  every invariant of `spec` read through `abs` is an invariant of `impl`.
* `refines_liveness`: a property `φ` of the state sequences of the weakly fair runs of `spec` holds
  of the abstraction of every weakly fair run of `impl` (`Run.map`: the sequence of abstract states
  with the stutters removed), given `NoInfiniteStutter` (a fair run of `impl` changes its abstract
  state infinitely often) and `MapsFair` (each fair action of `spec` has a fair action of `impl`
  enabled wherever it is enabled, whose steps are steps of that action and nothing else).
-/

namespace Exegra.Core.LTS

/-- The observation of a label: `none` for an internal label. -/
class Obs (α : Type) (β : outParam Type) where
  obs : α → Option β

open Obs

variable {σI αI σS αS β : Type} [Obs αI β] [Obs αS β]

/-- The observations of the finite traces of `M`, internal labels dropped. -/
def ObsTraces {σ α : Type} [Obs α β] (M : LTS σ α) : Lang β :=
  fun o => ∃ l, l ∈ M.Traces ∧ l.filterMap obs = o

/-- **Stuttering simulation** through `abs`: initial states map to initial states, and each step of
`impl` from a reachable state maps to a step of `spec` with the same observation or to a stutter
that leaves `abs` and the observation unchanged. -/
def Simulates (impl : LTS σI αI) (spec : LTS σS αS) (abs : σI → σS) : Prop :=
  (∀ s, impl.init s → spec.init (abs s)) ∧
  ∀ s a t, impl.Reach s → impl.step s a t →
    (∃ b, spec.step (abs s) b (abs t) ∧ obs b = obs a) ∨ (abs t = abs s ∧ obs a = none)

theorem sim_path {impl : LTS σI αI} {spec : LTS σS αS} {abs : σI → σS}
    (h : Simulates impl spec abs) {s u : σI} {l : List αI} (hs : impl.Reach s)
    (hp : impl.Path s l u) :
    ∃ l', spec.Path (abs s) l' (abs u) ∧ l'.filterMap obs = l.filterMap obs := by
  induction hp with
  | nil => exact ⟨[], .nil _, rfl⟩
  | @cons s' t u a l hst _ ih =>
    obtain ⟨l', hp', ho⟩ := ih (.step hs hst)
    rcases h.2 s' a t hs hst with ⟨b, hb, hob⟩ | ⟨heq, hoa⟩
    · refine ⟨b :: l', .cons hb hp', ?_⟩
      simp only [List.filterMap_cons, hob, ho]
    · refine ⟨l', heq ▸ hp', ?_⟩
      simp only [List.filterMap_cons, hoa, ho]

/-- **Refinement preserves finite traces**: `Simulates impl spec abs → ObsTraces impl ⊆
ObsTraces spec`. -/
theorem refines_traces {impl : LTS σI αI} {spec : LTS σS αS} {abs : σI → σS} :
    Simulates impl spec abs → ObsTraces impl ⊆ ObsTraces spec := by
  rintro h o ⟨l, ⟨s, u, hs, hp⟩, rfl⟩
  obtain ⟨l', hp', ho⟩ := sim_path h (.init hs) hp
  exact ⟨l', ⟨abs s, abs u, h.1 s hs, hp'⟩, ho⟩

theorem reach_abs {impl : LTS σI αI} {spec : LTS σS αS} {abs : σI → σS}
    (h : Simulates impl spec abs) {s : σI} (hs : impl.Reach s) : spec.Reach (abs s) := by
  induction hs with
  | init hi => exact .init (h.1 _ hi)
  | @step s t a hs hst ih =>
    rcases h.2 s a t hs hst with ⟨b, hb, _⟩ | ⟨heq, _⟩
    · exact .step ih hb
    · rw [heq]; exact ih

/-- **Refinement preserves safety**: `Simulates impl spec abs → spec.Invariant P →
impl.Invariant (P ∘ abs)`. -/
theorem refines_safety {impl : LTS σI αI} {spec : LTS σS αS} {abs : σI → σS} {P : σS → Prop} :
    Simulates impl spec abs → spec.Invariant P → impl.Invariant (P ∘ abs) :=
  fun h hP _ hs => hP _ (reach_abs h hs)

/-! ### Liveness -/

/-- A run of `spec` read as its sequence of states. -/
instance {σ α : Type} {M : LTS σ α} : CoeOut (Run M) (Nat → σ) := ⟨Run.st⟩

/-- The first index from `N` on satisfying `p`, if some index from `N` on does (an arbitrary index
otherwise). -/
noncomputable def firstFrom (p : Nat → Prop) (N : Nat) : Nat :=
  Classical.epsilon (fun i => N ≤ i ∧ p i ∧ ∀ j, N ≤ j → j < i → ¬ p j)

theorem exists_first {p : Nat → Prop} {N : Nat} (h : ∃ i, N ≤ i ∧ p i) :
    ∃ i, N ≤ i ∧ p i ∧ ∀ j, N ≤ j → j < i → ¬ p j := by
  obtain ⟨i, hNi, hpi⟩ := h
  induction i using Nat.strongRecOn with
  | ind i ih =>
    by_cases hm : ∃ j, N ≤ j ∧ j < i ∧ p j
    · obtain ⟨j, hNj, hji, hpj⟩ := hm
      exact ih j hji hNj hpj
    · exact ⟨i, hNi, hpi, fun j hNj hji hpj => hm ⟨j, hNj, hji, hpj⟩⟩

theorem firstFrom_spec {p : Nat → Prop} {N : Nat} (h : ∃ i, N ≤ i ∧ p i) :
    N ≤ firstFrom p N ∧ p (firstFrom p N) ∧ ∀ j, N ≤ j → j < firstFrom p N → ¬ p j :=
  Classical.epsilon_spec (exists_first h)

/-- The `n`-th index satisfying `p`, in increasing order. -/
noncomputable def nth (p : Nat → Prop) : Nat → Nat
  | 0 => firstFrom p 0
  | n + 1 => firstFrom p (nth p n + 1)

/-- The abstraction of a run: the abstract states at the start and after each index where the
abstract state changes, so that the stutters are removed. -/
noncomputable def Run.map {σ α : Type} {M : LTS σ α} (r : Run M) (abs : σ → σS) : Nat → σS
  | 0 => abs (r.st 0)
  | n + 1 => abs (r.st (nth (fun i => abs (r.st (i + 1)) ≠ abs (r.st i)) n + 1))

/-- A weakly fair run of `impl` changes its abstract state infinitely often. -/
def NoInfiniteStutter (impl : LTS σI αI) (abs : σI → σS) (F : ActSet αI) : Prop :=
  ∀ r : Run impl, r.WeakFair F → ∀ N, ∃ i, N ≤ i ∧ abs (r.st (i + 1)) ≠ abs (r.st i)

/-- Each fair action `b` of `spec` has a fair action `a` of `impl` that is enabled at every
reachable state whose abstraction enables `b`, and every `a`-step from a reachable state changes the
abstract state by a step of `spec` that only `b` makes. -/
def MapsFair (impl : LTS σI αI) (spec : LTS σS αS) (abs : σI → σS) (F : ActSet αI)
    (F' : ActSet αS) : Prop :=
  ∀ b ∈ F', ∃ a ∈ F,
    (∀ s, impl.Reach s → spec.Enabled (abs s) b → impl.Enabled s a) ∧
    (∀ s t, impl.Reach s → impl.step s a t →
      abs t ≠ abs s ∧ ∀ b', spec.step (abs s) b' (abs t) → b' = b)

section Liveness

variable {impl : LTS σI αI} {spec : LTS σS αS} {abs : σI → σS}

/-- Between `N` and the first index from `N` where the abstract state changes, it does not. -/
theorem const_until (r : Run impl) (p : Nat → Prop)
    (hp : ∀ i, ¬ p i → abs (r.st (i + 1)) = abs (r.st i)) {N : Nat} (h : ∃ i, N ≤ i ∧ p i) :
    ∀ j, N ≤ j → j ≤ firstFrom p N → abs (r.st j) = abs (r.st N) := by
  have hs := firstFrom_spec h
  intro j hNj hj
  induction j with
  | zero => obtain rfl : N = 0 := by omega
            rfl
  | succ j ih =>
    by_cases hNj' : N ≤ j
    · rw [hp j (hs.2.2 j hNj' (by omega)), ih hNj' (by omega)]
    · obtain rfl : N = j + 1 := by omega
      rfl

/-- **Refinement preserves liveness under fairness**: `Simulates impl spec abs →
NoInfiniteStutter impl abs F → MapsFair impl spec abs F F' → (∀ r : Run spec, r.WeakFair F' → φ r) →
∀ r : Run impl, r.WeakFair F → φ (r.map abs)`. A run of `spec` is read as its state sequence, and
`r.map abs` is the abstraction of `r` with the stutters removed; it is the state sequence of a weakly
fair run of `spec`. -/
theorem refines_liveness {F : ActSet αI} {F' : ActSet αS} {φ : (Nat → σS) → Prop} :
    Simulates impl spec abs → NoInfiniteStutter impl abs F → MapsFair impl spec abs F F' →
    (∀ r : Run spec, r.WeakFair F' → φ r) → ∀ r : Run impl, r.WeakFair F → φ (r.map abs) := by
  intro hsim hnis hmf hspec r hfair
  classical
  -- The indices where the abstract state changes, infinitely many.
  let p : Nat → Prop := fun i => abs (r.st (i + 1)) ≠ abs (r.st i)
  have hinf : ∀ N, ∃ i, N ≤ i ∧ p i := hnis r hfair
  have hp : ∀ i, ¬ p i → abs (r.st (i + 1)) = abs (r.st i) := fun i h => Classical.byContradiction h
  let k : Nat → Nat := nth p
  have hk0 : k 0 = firstFrom p 0 := rfl
  have hkS : ∀ n, k (n + 1) = firstFrom p (k n + 1) := fun _ => rfl
  have hkp : ∀ n, p (k n) := by
    intro n; cases n with
    | zero => exact (firstFrom_spec (hinf 0)).2.1
    | succ n => rw [hkS]; exact (firstFrom_spec (hinf _)).2.1
  have hklt : ∀ n, k n < k (n + 1) := fun n => by
    rw [hkS]; have := (firstFrom_spec (hinf (k n + 1))).1; omega
  let m : Nat → σS := r.map abs
  have hm0 : m 0 = abs (r.st 0) := rfl
  have hmS : ∀ n, m (n + 1) = abs (r.st (k n + 1)) := fun _ => rfl
  -- The abstract state at `k n` is `m n`.
  have hmk : ∀ n, abs (r.st (k n)) = m n := by
    intro n; cases n with
    | zero => rw [hk0, hm0]; exact const_until r p hp (hinf 0) _ (Nat.zero_le _) (Nat.le_refl _)
    | succ n =>
      rw [hkS, hmS]
      exact const_until r p hp (hinf _) _ (firstFrom_spec (hinf (k n + 1))).1 (Nat.le_refl _)
  -- Each index of `k` is a step of `impl` that maps to a step of `spec`.
  have hstepk : ∀ n, ∃ b, spec.step (m n) b (m (n + 1)) := by
    intro n
    have hpk := hkp n
    rcases r.step (k n) with hst | ⟨_, heq⟩
    · rcases hsim.2 _ _ _ (r.reach _) hst with ⟨b, hb, _⟩ | ⟨heq, _⟩
      · exact ⟨b, by rw [← hmk n, hmS]; exact hb⟩
      · exact absurd heq hpk
    · exact absurd (by rw [heq]) hpk
  obtain ⟨b0, _⟩ := hstepk 0
  haveI : Nonempty αS := ⟨b0⟩
  let lab : Nat → αS := fun n => Classical.epsilon (fun b => spec.step (m n) b (m (n + 1)))
  have hlab : ∀ n, spec.step (m n) (lab n) (m (n + 1)) := fun n =>
    Classical.epsilon_spec (hstepk n)
  let rs : Run spec := ⟨m, lab, hm0 ▸ hsim.1 _ r.init, fun n => Or.inl (hlab n)⟩
  -- Every index after `k N` lies after `k n` and at most at `k (n + 1)` for some `n ≥ N`.
  have hcover : ∀ N j, k N < j → ∃ n, N ≤ n ∧ k n < j ∧ j ≤ k (n + 1) := by
    intro N j
    induction j with
    | zero => intro h; omega
    | succ j ih =>
      intro h
      by_cases hj : k N < j
      · obtain ⟨n, hNn, h1, h2⟩ := ih hj
        by_cases hlt : j < k (n + 1)
        · exact ⟨n, hNn, by omega, hlt⟩
        · exact ⟨n + 1, by omega, by omega, by have := hklt (n + 1); omega⟩
      · exact ⟨N, Nat.le_refl _, by omega, by have := hklt N; omega⟩
  -- On that interval the abstract state is `m (n + 1)`.
  have hinterval : ∀ n j, k n < j → j ≤ k (n + 1) → abs (r.st j) = m (n + 1) := by
    intro n j h1 h2
    rw [hmS]
    exact const_until r p hp (hinf _) j (by omega) (by rw [← hkS]; exact h2)
  -- A real index in that interval is `k (n + 1)`.
  have hreal : ∀ n j, k n < j → j ≤ k (n + 1) → p j → j = k (n + 1) := by
    intro n j h1 h2 hpj
    refine Classical.byContradiction fun hne => ?_
    have hlt : j < k (n + 1) := by omega
    rw [hkS] at hlt
    exact (firstFrom_spec (hinf (k n + 1))).2.2 j (by omega) hlt hpj
  have hrs : rs.WeakFair F' := by
    intro b hb ⟨N, hN⟩ M
    obtain ⟨a, ha, hen, hstep⟩ := hmf b hb
    have himpl : ∃ N, ∀ i, N ≤ i → impl.Enabled (r.st i) a := by
      refine ⟨k N + 1, fun i hi => hen _ (r.reach i) ?_⟩
      obtain ⟨n, hNn, h1, h2⟩ := hcover N i (by omega)
      rw [hinterval n i h1 h2]
      exact hN (n + 1) (by omega)
    obtain ⟨i, hi, hlabi, hsti⟩ := hfair a ha himpl (k M + 1)
    obtain ⟨hne, huniq⟩ := hstep _ _ (r.reach i) hsti
    obtain ⟨n, hMn, h1, h2⟩ := hcover M i (by omega)
    have hik : i = k (n + 1) := hreal n i h1 h2 hne
    have hlb : lab (n + 1) = b := by
      apply huniq
      have := hlab (n + 1)
      rwa [← hmk (n + 1), hmS (n + 1), ← hik] at this
    exact ⟨n + 1, by omega, hlb, hlb ▸ hlab (n + 1)⟩
  exact hspec rs hrs

end Liveness

end Exegra.Core.LTS

/-- info: 'Exegra.Core.LTS.refines_traces' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.LTS.refines_traces

/-- info: 'Exegra.Core.LTS.refines_safety' does not depend on any axioms -/
#guard_msgs in
#print axioms Exegra.Core.LTS.refines_safety

/-- info: 'Exegra.Core.LTS.refines_liveness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.LTS.refines_liveness
