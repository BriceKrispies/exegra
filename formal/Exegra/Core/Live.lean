import Exegra.Core.LTS

/-
Infinite runs, fairness and a fragment of linear temporal logic over the transition systems of
`Exegra.Core.LTS` (WG-5682; docs/assessment/2026-11-26/modelchecking.md, C3).

* `Run M`: an infinite sequence of states and labels starting in an initial state, each step a step
  of `M`, except that a deadlocked state is extended by stuttering (`RStep`), so that a run that
  terminates is still infinite. A stutter is not a step of `M` and takes no action.
* `Enabled M s a`: some step from `s` has label `a`. `Taken r i a`: the run takes `a` at index `i`
  (the label is `a` and it is a step of `M`, not a stutter).
* Fairness over a declared set `F : ActSet α` of fair actions: `WeakFair` (an action enabled at
  every index from some point on is taken infinitely often) and `StrongFair` (an action enabled
  infinitely often is taken infinitely often); `strongFair_weakFair`.
* `□ P`, `◇ P`, `□◇ P`, `◇□ P` over runs, for a state predicate `P`.
* `lasso_refutes`: a reachable state with a weakly fair cycle back to itself through a state that
  violates `P` refutes `◇□ P` for every weakly fair run. `lasso_refutes_GF` refutes `□◇ P` when
  every state of the cycle violates `P`.
* `response_of_ranking`: a ranking `V` and a helpful fair action `h s` at every reachable state
  violating `P` prove `□◇ P` for every weakly fair run. The rule needs the helpful action to stay the
  same along steps that keep the rank (see its docstring); without that condition it is unsound
  (`ranking_without_helpful_unsound`).
* The blinker of the assessment (modelchecking F4): `blinker_not_FG_on` by `lasso_refutes`,
  `blinker_GF_on` by `response_of_ranking`.
-/

namespace Exegra.Core.LTS

variable {σ α : Type}

/-! ### Runs -/

/-- A step of `M`, or a stutter at a deadlocked state (the state is kept, the label is arbitrary). -/
def RStep (M : LTS σ α) (s : σ) (a : α) (t : σ) : Prop :=
  M.step s a t ∨ (M.Deadlocked s ∧ t = s)

/-- An infinite run of `M`: `st 0` is initial and every index is a step of `M`, or a stutter at a
deadlocked state, so that a terminating run is extended to an infinite one.

WG-5682 criterion 6: "`Run M` (`st : Nat → σ`, `lab : Nat → α`, `M.init (st 0)`,
`∀ i, M.step (st i) (lab i) (st (i+1))`), with a deadlocked state extended by stuttering so that
terminating runs are infinite": the step condition is `M.RStep`, a step of `M` or that stutter. -/
structure Run (M : LTS σ α) where
  st : Nat → σ
  lab : Nat → α
  init : M.init (st 0)
  step : ∀ i, M.RStep (st i) (lab i) (st (i + 1))

/-- Some step from `s` has label `a`. -/
def Enabled (M : LTS σ α) (s : σ) (a : α) : Prop := ∃ t, M.step s a t

/-- A set of actions (the fair actions a claim declares). -/
def ActSet (α : Type) := α → Prop

instance : Membership α (ActSet α) := ⟨fun F a => F a⟩
instance : Singleton α (ActSet α) := ⟨fun a b => b = a⟩

theorem ActSet.mem_singleton {a b : α} : b ∈ ({a} : ActSet α) ↔ b = a := Iff.rfl

namespace Run

variable {M : LTS σ α}

/-- The run takes action `a` at index `i`: a step of `M` (not a stutter) labelled `a`. -/
def Taken (r : Run M) (i : Nat) (a : α) : Prop := r.lab i = a ∧ M.step (r.st i) a (r.st (i + 1))

/-- **Weak fairness**: every fair action that is enabled at every index from some point on is
taken infinitely often. -/
def WeakFair (r : Run M) (F : ActSet α) : Prop :=
  ∀ a ∈ F, (∃ N, ∀ i, N ≤ i → M.Enabled (r.st i) a) → ∀ N, ∃ i, N ≤ i ∧ r.Taken i a

/-- **Strong fairness**: every fair action that is enabled infinitely often is taken infinitely
often. -/
def StrongFair (r : Run M) (F : ActSet α) : Prop :=
  ∀ a ∈ F, (∀ N, ∃ i, N ≤ i ∧ M.Enabled (r.st i) a) → ∀ N, ∃ i, N ≤ i ∧ r.Taken i a

theorem strongFair_weakFair {r : Run M} {F : ActSet α} : r.StrongFair F → r.WeakFair F := by
  intro h a ha ⟨N, hN⟩ N'
  exact h a ha (fun K => ⟨max N K, Nat.le_max_right _ _, hN _ (Nat.le_max_left _ _)⟩) N'

/-- Every state of a run is reachable. -/
theorem reach (r : Run M) : ∀ i, M.Reach (r.st i)
  | 0 => .init r.init
  | i + 1 => by
    rcases r.step i with h | ⟨_, h⟩
    · exact .step (reach r i) h
    · rw [h]; exact reach r i

end Run

/-! ### Temporal operators over runs -/

/-- `□ P`: every state of the run satisfies `P`. -/
def Always {M : LTS σ α} (P : σ → Prop) (r : Run M) : Prop := ∀ i, P (r.st i)
/-- `◇ P`: some state of the run satisfies `P`. -/
def Eventually {M : LTS σ α} (P : σ → Prop) (r : Run M) : Prop := ∃ i, P (r.st i)
/-- `□◇ P`: `P` holds infinitely often. -/
def InfOften {M : LTS σ α} (P : σ → Prop) (r : Run M) : Prop := ∀ N, ∃ i, N ≤ i ∧ P (r.st i)
/-- `◇□ P`: from some point on, `P` holds forever. -/
def EvAlways {M : LTS σ α} (P : σ → Prop) (r : Run M) : Prop := ∃ N, ∀ i, N ≤ i → P (r.st i)

scoped notation:max "□◇" P:max => InfOften P
scoped notation:max "◇□" P:max => EvAlways P
scoped notation:max "□" P:max => Always P
scoped notation:max "◇" P:max => Eventually P

/-! ### Paths with stuttering -/

/-- A sequence of steps (with stuttering) from `s`: each pair is a label and the state it leads to. -/
def RPathFrom (M : LTS σ α) : σ → List (α × σ) → Prop
  | _, [] => True
  | s, (a, t) :: rest => M.RStep s a t ∧ RPathFrom M t rest

/-- The states of a path from `s`: `s`, then the state of each step. -/
def pathStates (s : σ) (cyc : List (α × σ)) : List σ := s :: cyc.map Prod.snd

theorem rpath_get {M : LTS σ α} : ∀ (s : σ) (cyc : List (α × σ)), M.RPathFrom s cyc →
    ∀ k (hk : k < cyc.length),
      M.RStep ((pathStates s cyc)[k]'(by simp [pathStates]; omega)) (cyc[k]).1
        ((pathStates s cyc)[k + 1]'(by simp [pathStates]; omega))
  | _, [], _, k, hk => absurd hk (by simp)
  | s, (a, t) :: rest, ⟨h1, h2⟩, 0, _ => by simpa [pathStates] using h1
  | s, (a, t) :: rest, ⟨_, h2⟩, k + 1, hk => by
    have := rpath_get t rest h2 k (by simpa using hk)
    simpa [pathStates] using this

/-- A reachable state is the end of a path with stuttering from an initial state. -/
theorem reach_path {M : LTS σ α} {s : σ} (h : M.Reach s) :
    ∃ (x0 : σ) (pre : List (α × σ)), M.init x0 ∧ M.RPathFrom x0 pre ∧
      (pathStates x0 pre).getLast (by simp [pathStates]) = s := by
  induction h with
  | init hi => exact ⟨_, [], hi, trivial, rfl⟩
  | step _ hst ih =>
    rename_i u t a _
    obtain ⟨x0, pre, hi, hp, hl⟩ := ih
    refine ⟨x0, pre ++ [(a, t)], hi, ?_, by simp only [pathStates, List.map_append, List.map_cons, List.map_nil]; rw [List.getLast_cons (by simp)]; simp⟩
    have key : ∀ (y : σ) (q : List (α × σ)), M.RPathFrom y q →
        (pathStates y q).getLast (by simp [pathStates]) = u → M.RPathFrom y (q ++ [(a, t)]) := by
      intro y q
      induction q generalizing y with
      | nil => intro _ hl; simp [pathStates] at hl; subst hl; exact ⟨.inl hst, trivial⟩
      | cons p q ih =>
        intro hp hl
        obtain ⟨b, v⟩ := p
        refine ⟨hp.1, ih v hp.2 ?_⟩
        simpa [pathStates, List.getLast_cons] using hl
    exact key x0 pre hp hl

/-- A run that follows an infinite sequence of steps from a reachable state. -/
theorem run_through {M : LTS σ α} {s : σ} (hs : M.Reach s) (f : Nat → σ) (g : Nat → α)
    (h0 : f 0 = s) (hf : ∀ i, M.RStep (f i) (g i) (f (i + 1))) :
    ∃ (r : Run M) (m : Nat), ∀ i, r.st (m + i) = f i ∧ r.lab (m + i) = g i := by
  induction hs generalizing f g with
  | init hi =>
    exact ⟨⟨f, g, h0 ▸ hi, hf⟩, 0, fun i => by simp⟩
  | step _ hst ih =>
    rename_i u t a _
    let f' : Nat → σ := fun i => match i with | 0 => u | i + 1 => f i
    let g' : Nat → α := fun i => match i with | 0 => a | i + 1 => g i
    obtain ⟨r, m, hr⟩ := ih f' g' rfl (by
      intro i
      cases i with
      | zero => exact .inl (by simp only [f', g']; rw [h0]; exact hst)
      | succ i => exact hf i)
    exact ⟨r, m + 1, fun i => by
      have := hr (i + 1)
      simpa [f', g', Nat.add_assoc, Nat.add_comm 1] using this⟩

/-! ### Lassos -/

section Lasso

variable {M : LTS σ α} {s : σ} {cyc : List (α × σ)}

/-- The `j`-th state of the cycle repeated forever from `s` (`s` first). -/
private def cst (s : σ) (cyc : List (α × σ)) (hn : 0 < cyc.length) (j : Nat) : σ :=
  (pathStates s cyc)[j % cyc.length]'(by simp [pathStates]; have := Nat.mod_lt j hn; omega)

private def clab (cyc : List (α × σ)) (hn : 0 < cyc.length) (j : Nat) : α :=
  (cyc[j % cyc.length]'(Nat.mod_lt j hn)).1

private theorem cyc_inf (hn : 0 < cyc.length) (hpath : M.RPathFrom s cyc)
    (hback : (cyc.getLast (List.ne_nil_of_length_pos hn)).2 = s) :
    ∀ j, M.RStep (cst s cyc hn j) (clab cyc hn j) (cst s cyc hn (j + 1)) := by
  intro j
  have hk : j % cyc.length < cyc.length := Nat.mod_lt _ hn
  have hg := rpath_get s cyc hpath (j % cyc.length) hk
  have e3 : cst s cyc hn (j + 1) = (pathStates s cyc)[j % cyc.length + 1]'(by simp [pathStates]; omega) := by
    simp only [cst]
    by_cases hlt : j % cyc.length + 1 < cyc.length
    · have : (j + 1) % cyc.length = j % cyc.length + 1 := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt (a := 1) (by omega)]
        exact Nat.mod_eq_of_lt hlt
      simp only [this]
    · have heq : j % cyc.length + 1 = cyc.length := by omega
      have : (j + 1) % cyc.length = 0 := by
        have := Nat.div_add_mod j cyc.length
        rw [show j + 1 = cyc.length * (j / cyc.length + 1) by rw [Nat.mul_add]; omega]
        exact Nat.mul_mod_right _ _
      simp only [this, heq, pathStates, List.getElem_cons_zero]
      rw [← hback]
      simp [List.getLast_eq_getElem, List.getElem_cons]
  rw [e3]
  exact hg

/-- Every state of `pathStates s cyc` below the length of `cyc` is a state of `cyc` (`s` is the
last one). -/
private theorem mem_cycle_states (hne : cyc ≠ []) (hback : (cyc.getLast hne).2 = s) :
    ∀ k (hk : k < cyc.length), ∃ p ∈ cyc, p.2 = (pathStates s cyc)[k]'(by simp [pathStates]; omega) := by
  intro k hk
  cases k with
  | zero => exact ⟨cyc.getLast hne, List.getLast_mem hne, by simp [pathStates, hback]⟩
  | succ k => exact ⟨cyc[k], List.getElem_mem _, by simp [pathStates]⟩

private theorem period (n q k : Nat) (hk : k < n) : (n * q + k) % n = k := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]

/-- The run of a lasso: it reaches `s`, then repeats `cyc` forever. Position `k` of the cycle recurs
at every index `m + n*q + k`, and the run is weakly fair. -/
private theorem lasso_run {F : ActSet α} (hs : M.Reach s) (hne : cyc ≠ [])
    (hpath : M.RPathFrom s cyc) (hback : (cyc.getLast hne).2 = s)
    (hfair : ∀ a ∈ F, (∀ p ∈ cyc, M.Enabled p.2 a) → ∃ p ∈ cyc, p.1 = a) :
    ∃ (r : Run M) (m : Nat), r.WeakFair F ∧
      ∀ q k (hk : k < cyc.length),
        r.st (m + (cyc.length * q + k)) = (pathStates s cyc)[k]'(by simp [pathStates]; omega) := by
  have hn : 0 < cyc.length := List.length_pos_iff.mpr hne
  obtain ⟨r, m, hr⟩ := run_through hs (cst s cyc hn) (clab cyc hn)
    (by simp [cst, pathStates]) (cyc_inf hn hpath hback)
  have hpos : ∀ q k (hk : k < cyc.length),
      r.st (m + (cyc.length * q + k)) = (pathStates s cyc)[k]'(by simp [pathStates]; omega) ∧
      r.lab (m + (cyc.length * q + k)) = (cyc[k]).1 := by
    intro q k hk
    obtain ⟨h1, h2⟩ := hr (cyc.length * q + k)
    refine ⟨?_, ?_⟩
    · rw [h1]; simp only [cst, period _ _ _ hk]
    · rw [h2]; simp only [clab, period _ _ _ hk]
  have hin : ∀ i, m ≤ i → ∃ p ∈ cyc, p.2 = r.st i := by
    intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = m + j := ⟨i - m, by omega⟩
    have hk : j % cyc.length < cyc.length := Nat.mod_lt _ hn
    obtain ⟨p, hp, he⟩ := mem_cycle_states hne hback _ hk
    exact ⟨p, hp, by rw [he, (hr j).1]; rfl⟩
  refine ⟨r, m, ?_, fun q k hk => (hpos q k hk).1⟩
  intro a ha ⟨N, hN⟩ N'
  -- every state of the cycle occurs after `N`, so `a` is enabled at each
  have hen : ∀ p ∈ cyc, M.Enabled p.2 a := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
    have h := (hpos (N + 1) ((k + 1) % cyc.length) (Nat.mod_lt _ hn)).1
    have hge : N ≤ m + (cyc.length * (N + 1) + (k + 1) % cyc.length) := by
      have : N + 1 ≤ cyc.length * (N + 1) := Nat.le_mul_of_pos_left _ hn
      omega
    have := hN _ hge
    rw [h] at this
    by_cases hlt : k + 1 < cyc.length
    · simp only [Nat.mod_eq_of_lt hlt] at this; simpa [pathStates] using this
    · have heq : k + 1 = cyc.length := by omega
      simp only [heq, Nat.mod_self, pathStates, List.getElem_cons_zero] at this
      rw [← hback] at this
      have hk' : k = cyc.length - 1 := by omega
      subst hk'
      simpa [List.getLast_eq_getElem] using this
  obtain ⟨p, hp, hpa⟩ := hfair a ha hen
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
  refine ⟨m + (cyc.length * N' + k), ?_, ?_⟩
  · have : N' ≤ cyc.length * N' := Nat.le_mul_of_pos_left _ hn
    omega
  · have hl := (hpos N' k hk).2
    refine ⟨hl.trans hpa, ?_⟩
    have hstep := r.step (m + (cyc.length * N' + k))
    rw [hl, hpa] at hstep
    rcases hstep with h | ⟨hd, _⟩
    · exact h
    · obtain ⟨q, hq, he⟩ := hin (m + (cyc.length * N' + k)) (by omega)
      obtain ⟨t, ht⟩ := hen q hq
      rw [he] at ht
      exact absurd ht (hd a t)

/-- A state of `cyc` occurs at some position of `pathStates s cyc` below the length of `cyc`. -/
private theorem cycle_pos (hne : cyc ≠ []) (hback : (cyc.getLast hne).2 = s) {p : α × σ}
    (hp : p ∈ cyc) : ∃ k, ∃ hk : k < cyc.length,
      (pathStates s cyc)[k]'(by simp [pathStates]; omega) = p.2 := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
  by_cases hlt : k + 1 < cyc.length
  · exact ⟨k + 1, hlt, by simp [pathStates]⟩
  · refine ⟨0, List.length_pos_iff.mpr hne, ?_⟩
    have hk' : k = cyc.length - 1 := by omega
    subst hk'
    simp [pathStates, ← hback, List.getLast_eq_getElem]

/-- **A weakly fair lasso refutes `◇□ P`.** `s` is reachable; `cyc` is a path (with stuttering) of
length at least one from `s` back to `s`; some state of `cyc` violates `P`; and every fair action
enabled at every state of `cyc` is the label of some step of `cyc` (the cycle is weakly fair). Then
not every weakly fair run satisfies `◇□ P`: the run that reaches `s` and then repeats `cyc` forever
is weakly fair and violates `P` infinitely often.

WG-5682 criterion 7: "for a reachable `s`, a cycle `cyc` from `s` back to `s` (a path of length ≥ 1),
with some state of `cyc` violating `P`, and the cycle weakly fair (every fair action enabled at every
state of `cyc` is taken in `cyc`): `¬ ∀ r : Run M, r.WeakFair F → (◇□ P) r`". A step of the cycle may
stutter at a deadlocked state, as a run does. -/
theorem lasso_refutes {F : ActSet α} {P : σ → Prop} (hs : M.Reach s) (hne : cyc ≠ [])
    (hpath : M.RPathFrom s cyc) (hback : (cyc.getLast hne).2 = s) (hviol : ∃ p ∈ cyc, ¬ P p.2)
    (hfair : ∀ a ∈ F, (∀ p ∈ cyc, M.Enabled p.2 a) → ∃ p ∈ cyc, p.1 = a) :
    ¬ ∀ r : Run M, r.WeakFair F → (◇□ P) r := by
  intro hall
  obtain ⟨r, m, hwf, hpos⟩ := lasso_run hs hne hpath hback hfair
  obtain ⟨N, hN⟩ := hall r hwf
  obtain ⟨p, hp, hnp⟩ := hviol
  obtain ⟨k, hk, he⟩ := cycle_pos hne hback hp
  have hn : 0 < cyc.length := List.length_pos_iff.mpr hne
  have hge : N ≤ m + (cyc.length * N + k) := by
    have : N ≤ cyc.length * N := Nat.le_mul_of_pos_left _ hn
    omega
  have := hN _ hge
  rw [hpos N k hk, he] at this
  exact hnp this

/-- **A weakly fair lasso whose every state violates `P` refutes `□◇ P`.** -/
theorem lasso_refutes_GF {F : ActSet α} {P : σ → Prop} (hs : M.Reach s) (hne : cyc ≠ [])
    (hpath : M.RPathFrom s cyc) (hback : (cyc.getLast hne).2 = s) (hviol : ∀ p ∈ cyc, ¬ P p.2)
    (hfair : ∀ a ∈ F, (∀ p ∈ cyc, M.Enabled p.2 a) → ∃ p ∈ cyc, p.1 = a) :
    ¬ ∀ r : Run M, r.WeakFair F → (□◇ P) r := by
  intro hall
  obtain ⟨r, m, hwf, hpos⟩ := lasso_run hs hne hpath hback hfair
  have hn : 0 < cyc.length := List.length_pos_iff.mpr hne
  obtain ⟨i, hi, hP⟩ := hall r hwf m
  obtain ⟨j, rfl⟩ : ∃ j, i = m + j := ⟨i - m, by omega⟩
  have hk : j % cyc.length < cyc.length := Nat.mod_lt _ hn
  have hj : j = cyc.length * (j / cyc.length) + j % cyc.length := (Nat.div_add_mod j cyc.length).symm
  rw [hj, hpos _ _ hk] at hP
  obtain ⟨p, hp, he⟩ := mem_cycle_states hne hback _ hk
  exact hviol p hp (he ▸ hP)

end Lasso

/-! ### Ranking -/

/-- A sequence of naturals that does not increase from `N` on is constant from some `N' ≥ N` on. -/
theorem eventually_const (f : Nat → Nat) (N : Nat) (hmono : ∀ i, N ≤ i → f (i + 1) ≤ f i) :
    ∃ N', N ≤ N' ∧ ∀ i, N' ≤ i → f i = f N' := by
  induction h : f N using Nat.strongRecOn generalizing N with
  | ind v ih =>
    have hle : ∀ i, N ≤ i → f i ≤ f N := by
      intro i hi
      obtain ⟨d, rfl⟩ : ∃ d, i = N + d := ⟨i - N, by omega⟩
      induction d with
      | zero => exact Nat.le_refl _
      | succ d ihd => exact Nat.le_trans (hmono (N + d) (by omega)) (ihd (by omega))
    by_cases hc : ∃ i, N ≤ i ∧ f i < f N
    · obtain ⟨i, hi, hlt⟩ := hc
      obtain ⟨N', hN', hc'⟩ := ih (f i) (by omega) i (fun j hj => hmono j (by omega)) rfl
      exact ⟨N', by omega, hc'⟩
    · refine ⟨N, Nat.le_refl _, fun i hi => ?_⟩
      have := hle i hi
      have : ¬ f i < f N := fun h => hc ⟨i, hi, h⟩
      omega

/-- **Response from a ranking.** Let `V` rank the states and `h s` name a helpful action at each
reachable state `s` that violates `P`, such that

* `h s` is a fair action and is enabled at `s`;
* every step from `s` labelled `h s` reaches `P` or decreases `V`;
* every step from `s` reaches `P`, decreases `V`, or keeps `V` and the helpful action.

Then every weakly fair run satisfies `□◇ P`.

This is WG-5682's criterion 8 ("if for every reachable `s` with `¬ P s` there is a fair action
enabled at `s` all of whose steps decrease `V`, and no step from a reachable `¬ P` state increases
`V` unless it reaches `P`, then `∀ r : Run M, r.WeakFair F → (□◇ P) r`") with its last condition
strengthened from "does not increase `V`" to "decreases `V`, or keeps `V` and the helpful action".
The criterion's rule is unsound under weak fairness (`ranking_without_helpful_unsound`): a run can
keep `V` while moving between states whose helpful actions differ, so that no one of them stays
enabled long enough for weak fairness to force it. -/
theorem response_of_ranking {M : LTS σ α} {F : ActSet α} {P : σ → Prop} (V : σ → Nat) (h : σ → α)
    (hfair : ∀ s, M.Reach s → ¬ P s → h s ∈ F ∧ M.Enabled s (h s))
    (hdec : ∀ s t, M.Reach s → ¬ P s → M.step s (h s) t → P t ∨ V t < V s)
    (hstay : ∀ s a t, M.Reach s → ¬ P s → M.step s a t → P t ∨ V t < V s ∨ (V t = V s ∧ h t = h s)) :
    ∀ r : Run M, r.WeakFair F → (□◇ P) r := by
  intro r hwf N
  apply Classical.byContradiction
  intro hne
  have hnp : ∀ i, N ≤ i → ¬ P (r.st i) := fun i hi hp => hne ⟨i, hi, hp⟩
  -- from `N` on every index is a step of `M`: a state violating `P` has an enabled action
  have hreal : ∀ i, N ≤ i → M.step (r.st i) (r.lab i) (r.st (i + 1)) := by
    intro i hi
    rcases r.step i with hs | ⟨hd, _⟩
    · exact hs
    · obtain ⟨t, ht⟩ := (hfair _ (r.reach i) (hnp i hi)).2
      exact absurd ht (hd _ t)
  have hstep : ∀ i, N ≤ i → V (r.st (i + 1)) < V (r.st i) ∨
      (V (r.st (i + 1)) = V (r.st i) ∧ h (r.st (i + 1)) = h (r.st i)) := by
    intro i hi
    rcases hstay _ _ _ (r.reach i) (hnp i hi) (hreal i hi) with hp | hlt | heq
    · exact absurd hp (hnp (i + 1) (by omega))
    · exact .inl hlt
    · exact .inr heq
  obtain ⟨N', hN', hc⟩ := eventually_const (fun i => V (r.st i)) N (fun i hi => by
    rcases hstep i hi with h1 | h1 <;> omega)
  have hh : ∀ i, N' ≤ i → h (r.st i) = h (r.st N') := by
    intro i hi
    obtain ⟨d, rfl⟩ : ∃ d, i = N' + d := ⟨i - N', by omega⟩
    induction d with
    | zero => rfl
    | succ d ih =>
      rcases hstep (N' + d) (by omega) with h1 | h1
      · have e1 : V (r.st (N' + d)) = V (r.st N') := hc _ (by omega)
        have e2 : V (r.st (N' + d + 1)) = V (r.st N') := hc _ (by omega)
        omega
      · rw [show N' + (d + 1) = N' + d + 1 by omega, h1.2, ih (by omega)]
  have hF := (hfair _ (r.reach N') (hnp N' hN')).1
  obtain ⟨i, hi, _, ht⟩ := hwf _ hF ⟨N', fun i hi => by
    have := (hfair _ (r.reach i) (hnp i (by omega))).2
    rwa [hh i hi] at this⟩ N'
  have hti : M.step (r.st i) (h (r.st i)) (r.st (i + 1)) := by rw [hh i hi]; exact ht
  rcases hdec _ _ (r.reach i) (hnp i (by omega)) hti with hp | hlt
  · exact hnp (i + 1) (by omega) hp
  · have e1 : V (r.st i) = V (r.st N') := hc i hi
    have e2 : V (r.st (i + 1)) = V (r.st N') := hc (i + 1) (by omega)
    omega

/-- **The rule of WG-5682's criterion 8, read literally, is unsound** under weak fairness. In the
system `0 → 1 → 0` (actions `2`, `3`) with fair exits `0 → 2` (action `0`) and `1 → 2` (action `1`),
`V = 1` off the goal `2` and `0` on it: from each non-goal state a fair action is enabled whose every
step decreases `V`, and no step increases `V`; yet the run `0, 1, 0, 1, …` is weakly fair (neither
exit stays enabled) and never reaches `2`. -/
theorem ranking_without_helpful_unsound :
    ¬ ∀ (M : LTS Nat Nat) (F : ActSet Nat) (P : Nat → Prop) (V : Nat → Nat),
      (∀ s, M.Reach s → ¬ P s → ∃ a ∈ F, M.Enabled s a ∧ ∀ t, M.step s a t → V t < V s) →
      (∀ s a t, M.Reach s → ¬ P s → M.step s a t → P t ∨ V t ≤ V s) →
      ∀ r : Run M, r.WeakFair F → (□◇ P) r := by
  intro h
  let M : LTS Nat Nat :=
    { init := fun s => s = 0
      step := fun s a t => (s = 0 ∧ a = 0 ∧ t = 2) ∨ (s = 1 ∧ a = 1 ∧ t = 2) ∨
        (s = 0 ∧ a = 2 ∧ t = 1) ∨ (s = 1 ∧ a = 3 ∧ t = 0) }
  let F : ActSet Nat := fun a => a = 0 ∨ a = 1
  have hreach : ∀ s, M.Reach s → s ≤ 2 := by
    intro s hs
    induction hs with
    | init hi => simp only [M] at hi; omega
    | step _ hst _ => simp only [M] at hst; omega
  let r : Run M :=
    { st := fun i => i % 2
      lab := fun i => if i % 2 = 0 then 2 else 3
      init := by simp [M]
      step := fun i => by
        left
        show (i % 2 = 0 ∧ _ = 0 ∧ (i + 1) % 2 = 2) ∨ (i % 2 = 1 ∧ _ = 1 ∧ (i + 1) % 2 = 2) ∨
          (i % 2 = 0 ∧ _ = 2 ∧ (i + 1) % 2 = 1) ∨ (i % 2 = 1 ∧ _ = 3 ∧ (i + 1) % 2 = 0)
        split <;> omega }
  have hwf : r.WeakFair F := by
    intro a ha ⟨N, hN⟩ _
    rcases ha with rfl | rfl
    · obtain ⟨t, ht⟩ := hN (2 * N + 1) (by omega)
      simp only [M, r] at ht; omega
    · obtain ⟨t, ht⟩ := hN (2 * N) (by omega)
      simp only [M, r] at ht; omega
  have hinf := h M F (fun s => s = 2) (fun s => if s = 2 then 0 else 1)
    (by
      intro s hs hp
      have := hreach s hs
      by_cases h0 : s = 0
      · subst h0
        refine ⟨0, Or.inl rfl, ⟨2, by simp [M]⟩, fun t ht => ?_⟩
        have e : t = 2 := by first | (simp only [M] at ht; omega) | omega
        subst e; decide
      · have h1 : s = 1 := by omega
        subst h1
        refine ⟨1, Or.inr rfl, ⟨2, by simp [M]⟩, fun t ht => ?_⟩
        have e : t = 2 := by first | (simp only [M] at ht; omega) | omega
        subst e; decide)
    (by
      intro s a t _ _ hst
      simp only [M] at hst
      by_cases ht : t = 2
      · exact .inl ht
      · right; split <;> (try split) <;> omega)
    r hwf 0
  obtain ⟨i, _, hi⟩ := hinf
  simp only [r] at hi
  omega

/-! ### The blinker (modelchecking F4) -/

inductive BAct where
  | turnOn
  | turnOff
  deriving DecidableEq

/-- The blinker: `off → on` by `turn-on`, `on → off` by `turn-off`; `true` is on. -/
def blinker : LTS Bool BAct where
  init s := s = false
  step s a t := (s = false ∧ a = .turnOn ∧ t = true) ∨ (s = true ∧ a = .turnOff ∧ t = false)

/-- The blinker is on. -/
def on (s : Bool) : Prop := s = true

/-- **The blinker is not eventually always on**, under weak fairness of any set of actions: the lasso
`off → on → off` is weakly fair (no action is enabled in both states) and passes through `off`. -/
theorem blinker_not_FG_on (F : ActSet BAct) : ¬ ∀ r : Run blinker, r.WeakFair F → (◇□ on) r :=
  lasso_refutes (s := false) (cyc := [(.turnOn, true), (.turnOff, false)])
    (.init rfl) (by simp)
    ⟨.inl (.inl ⟨rfl, rfl, rfl⟩), .inl (.inr ⟨rfl, rfl, rfl⟩), trivial⟩ rfl
    ⟨(.turnOff, false), by simp, by simp [on]⟩
    (by
      intro a _ hen
      obtain ⟨t1, h1⟩ := hen (.turnOn, true) (by simp)
      obtain ⟨t2, h2⟩ := hen (.turnOff, false) (by simp)
      simp only [blinker] at h1 h2
      cases a <;> simp_all)

/-- **The blinker is on infinitely often under weak fairness of `turn-on`**, by a ranking: `off`
has rank 1 and its helpful action `turn-on` leads to `on`. -/
theorem blinker_GF_on : ∀ r : Run blinker, r.WeakFair {BAct.turnOn} → (□◇ on) r :=
  response_of_ranking (fun s => if s then 0 else 1) (fun _ => .turnOn)
    (by
      intro s _ hs
      simp only [on] at hs
      refine ⟨rfl, true, ?_⟩
      simp [blinker, hs])
    (by intro s t _ _ h; left; simp only [blinker] at h; simp only [on]; cases s <;> simp_all)
    (by intro s a t _ hs h; left; simp only [blinker, on] at h hs ⊢; cases s <;> simp_all)

end Exegra.Core.LTS


/-- info: 'Exegra.Core.LTS.Run.strongFair_weakFair' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Exegra.Core.LTS.Run.strongFair_weakFair

/-- info: 'Exegra.Core.LTS.lasso_refutes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.LTS.lasso_refutes

/-- info: 'Exegra.Core.LTS.lasso_refutes_GF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.LTS.lasso_refutes_GF

/-- info: 'Exegra.Core.LTS.response_of_ranking' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.LTS.response_of_ranking

/-- info: 'Exegra.Core.LTS.ranking_without_helpful_unsound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.LTS.ranking_without_helpful_unsound

/-- info: 'Exegra.Core.LTS.blinker_not_FG_on' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.LTS.blinker_not_FG_on

/-- info: 'Exegra.Core.LTS.blinker_GF_on' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.LTS.blinker_GF_on
