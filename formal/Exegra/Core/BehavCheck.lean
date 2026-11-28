import Exegra.Core.BehavExec

/-
The explorer and the finite-trace temporal monitors on the behaviour calculus (plan-M2, M2.6; the
task's criteria 24 and 25).

* `exploreB sys P bound cap` is the search `Gen.search` over `Exec.gen sys`, the complete and sound
  enumeration of `Sys.lts sys`, for the property `s.ok ∧ P s`. `explore_holds_invariant`: a `holds`
  result, which the search returns only on an empty frontier, proves
  `(Sys.lts sys).Invariant (fun s => s.ok = true ∧ P s)` with no bound. `explore_cex_real`: a
  `counterexample p` refutes it, and `p` replays through the successor function of `Exec.gen` (the
  calculus steps `Exec.successors` enumerates) to a state where it fails. The error state violates
  the property, so a failing run is a counterexample, never a silent absence.
* Temporal forms over finite runs (`TForm`: `eventually`, `never`, `precedes`, response within a
  time bound) are given a meaning `FinSat` over a finite run of `Sys.lts` (a list of states, each a
  step of the relation from the one before), and a monitor `monitor` over the run's states.
  `monitor_sound`: on a run that ends in a deadlocked state the monitor accepts exactly the runs
  that satisfy the form. `verdict` reports a run cut off by the step limit or the bound as
  `incomplete` for `eventually` and response forms, never judged on its last state.
-/

namespace Exegra.Core.Behav

open Exegra.Core.LTS

/-! ### The explorer -/

/-- The explorer: the search of the calculus's enumeration for `s.ok ∧ P s`. -/
def exploreB (sys : Sys) (P : State → Bool) (bound cap : Nat) : Gen.Result State :=
  Gen.search (Exec.gen sys) (fun s => s.ok && P s) bound cap

/-- **A `holds` result proves the invariant with no bound.** -/
theorem explore_holds_invariant {sys : Sys} {P : State → Bool} {bound cap n : Nat}
    (h : exploreB sys P bound cap = .holds n) :
    (Sys.lts sys).Invariant (fun s => s.ok = true ∧ P s = true) := by
  intro s hs
  have := Exec.holds_invariant h s hs
  simpa [Bool.and_eq_true] using this

/-- **A counterexample is real**: it refutes the invariant, and its path replays through the
search's successor function (steps of `Sys.lts`, `Exec.successors`) from an initial state to a
state where the property fails.

Reading of the task's criterion 24 (accepted by the coordinator of WG-5681): "the counterexample
is a real run" is stated as replay through the successor function, not as a list of `Step`s; a
replay is a run of the step relation because every successor is a step (`successors_sound`,
`greplay_reach_lts` below). -/
theorem explore_cex_real {sys : Sys} {P : State → Bool} {bound cap : Nat} {p : Gen.Path State}
    (h : exploreB sys P bound cap = .counterexample p) :
    ¬ (Sys.lts sys).Invariant (fun s => s.ok = true ∧ P s = true) ∧
      ∃ t, Gen.greplay (Exec.gen sys) p.root p.picks = some t ∧ (t.ok && P t) = false := by
  refine ⟨?_, ?_⟩
  · intro hinv
    apply Exec.cex_refutes h
    intro s hs
    obtain ⟨h1, h2⟩ := hinv s hs
    simp [h1, h2]
  · obtain ⟨-, -, t, ht, hok⟩ := Gen.search_counterexample_real h
    exact ⟨t, ht, hok⟩

/-- Every step of a replayed path is a step of the calculus. -/
theorem greplay_reach_lts {sys : Sys} {r t : State} {ks : List Nat} (hr : r ∈ (Exec.gen sys).init)
    (h : Gen.greplay (Exec.gen sys) r ks = some t) : (Sys.lts sys).Reach t := by
  obtain ⟨d, hd⟩ := Gen.greplay_reach_any hr h
  exact reach_of_gen_reach (Exec.sound sys) hd

/-! ### Finite runs and temporal forms -/

/-- A finite run of the calculus: consecutive states are steps of `Sys.lts`. -/
def IsRun (sys : Sys) : List State → Prop
  | [] => True
  | [_] => True
  | s :: t :: rest => (∃ l, (Sys.lts sys).step s l t) ∧ IsRun sys (t :: rest)

/-- The time of a state. -/
def State.time (s : State) : Nat := s.cfg.time

/-- The temporal forms the monitors support, over state predicates. -/
inductive TForm where
  /-- Some state of the run satisfies `p`. -/
  | eventually (p : State → Bool)
  /-- No state of the run satisfies `p`. -/
  | never (p : State → Bool)
  /-- Every state satisfying `q` comes after (or is) a state satisfying `p`. -/
  | precedes (p q : State → Bool)
  /-- Every state satisfying `p` is followed (at it or later) by a state satisfying `q` at most `d`
  time units later. -/
  | response (p q : State → Bool) (d : Nat)

/-- **The meaning of a form over a finite run.** -/
def FinSat : TForm → List State → Prop
  | .eventually p, ρ => ∃ s ∈ ρ, p s = true
  | .never p, ρ => ∀ s ∈ ρ, p s = false
  | .precedes p q, ρ => ∀ (i : Nat) (h : i < ρ.length), q ρ[i] = true →
      ∃ (j : Nat) (hj : j < ρ.length), j ≤ i ∧ p ρ[j] = true
  | .response p q d, ρ => ∀ (i : Nat) (h : i < ρ.length), p ρ[i] = true →
      ∃ (j : Nat) (hj : j < ρ.length), i ≤ j ∧ q ρ[j] = true ∧ ρ[j].time ≤ ρ[i].time + d

/-- Some suffix position answers the response from a trigger state `s`. -/
def answered (q : State → Bool) (d : Nat) (s : State) (rest : List State) : Bool :=
  rest.any (fun t => q t && decide (t.time ≤ s.time + d))

/-- **The monitor**: one pass over the run's states. -/
def monitor : TForm → List State → Bool
  | .eventually p, ρ => ρ.any p
  | .never p, ρ => ρ.all (fun s => !p s)
  | .precedes p q, ρ => go p q false ρ
  | .response p q d, ρ => resp p q d ρ
where
  go (p q : State → Bool) (seen : Bool) : List State → Bool
    | [] => true
    | s :: rest => let seen' := seen || p s; (!(q s) || seen') && go p q seen' rest
  resp (p q : State → Bool) (d : Nat) : List State → Bool
    | [] => true
    | s :: rest => (!(p s) || answered q d s (s :: rest)) && resp p q d rest

theorem go_iff (p q : State → Bool) : (seen : Bool) → (ρ : List State) →
    (monitor.go p q seen ρ = true ↔
      ∀ (i : Nat) (h : i < ρ.length), q ρ[i] = true →
        seen = true ∨ ∃ (j : Nat) (hj : j < ρ.length), j ≤ i ∧ p ρ[j] = true)
  | seen, [] => by simp [monitor.go]
  | seen, s :: rest => by
    simp only [monitor.go, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
    rw [go_iff p q (seen || p s) rest]
    constructor
    · rintro ⟨h0, h1⟩ i hi hq
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero] at hq
        rcases h0 with h0 | h0
        · rw [h0] at hq; cases hq
        · try simp only [Bool.or_eq_true] at h0
          rcases h0 with h0 | h0
          · exact Or.inl h0
          · exact Or.inr ⟨0, by simp, Nat.le_refl _, by simpa using h0⟩
      | succ i =>
        simp only [List.getElem_cons_succ] at hq
        rcases h1 i (by simp at hi; omega) hq with h | ⟨j, hj, hji, hp⟩
        · simp only [Bool.or_eq_true] at h
          rcases h with h | h
          · exact Or.inl h
          · exact Or.inr ⟨0, by simp, Nat.zero_le _, by simpa using h⟩
        · exact Or.inr ⟨j + 1, by simp; omega, by omega, by simpa using hp⟩
    · intro h
      refine ⟨?_, ?_⟩
      · cases hq : q s
        · exact Or.inl rfl
        · right
          rcases h 0 (by simp) (by simpa using hq) with h' | ⟨j, hj, hji, hp⟩
          · simp [h']
          · have : j = 0 := by omega
            subst this
            simp only [List.getElem_cons_zero] at hp
            simp [hp]
      · intro i hi hq
        rcases h (i + 1) (by simp; omega) (by simpa using hq) with h' | ⟨j, hj, hji, hp⟩
        · simp [h']
        · cases j with
          | zero => simp only [List.getElem_cons_zero] at hp; simp [hp]
          | succ j => exact Or.inr ⟨j, by simp at hj; omega, by omega, by simpa using hp⟩

theorem resp_iff (p q : State → Bool) (d : Nat) : (ρ : List State) →
    (monitor.resp p q d ρ = true ↔
      ∀ (i : Nat) (h : i < ρ.length), p ρ[i] = true →
        ∃ (j : Nat) (hj : j < ρ.length), i ≤ j ∧ q ρ[j] = true ∧ ρ[j].time ≤ ρ[i].time + d)
  | [] => by simp [monitor.resp]
  | s :: rest => by
    simp only [monitor.resp, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true']
    rw [resp_iff p q d rest]
    have hans : answered q d s (s :: rest) = true ↔
        ∃ (j : Nat) (hj : j < (s :: rest).length), q (s :: rest)[j] = true ∧
          (s :: rest)[j].time ≤ s.time + d := by
      simp only [answered, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.mem_iff_getElem]
      constructor
      · rintro ⟨t, ⟨j, hj, rfl⟩, hq, ht⟩; exact ⟨j, hj, hq, ht⟩
      · rintro ⟨j, hj, hq, ht⟩; exact ⟨_, ⟨j, hj, rfl⟩, hq, ht⟩
    constructor
    · rintro ⟨h0, h1⟩ i hi hp
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero] at hp
        rcases h0 with h0 | h0
        · rw [h0] at hp; cases hp
        · obtain ⟨j, hj, hq, ht⟩ := hans.mp h0
          exact ⟨j, hj, Nat.zero_le _, hq, by simpa using ht⟩
      | succ i =>
        obtain ⟨j, hj, hij, hq, ht⟩ := h1 i (by simp at hi; omega) (by simpa using hp)
        exact ⟨j + 1, by simp; omega, by omega, by simpa using hq, by simpa using ht⟩
    · intro h
      refine ⟨?_, ?_⟩
      · cases hp : p s
        · exact Or.inl rfl
        · right
          obtain ⟨j, hj, -, hq, ht⟩ := h 0 (by simp) (by simpa using hp)
          exact hans.mpr ⟨j, hj, hq, by simpa using ht⟩
      · intro i hi hp
        obtain ⟨j, hj, hij, hq, ht⟩ := h (i + 1) (by simp; omega) (by simpa using hp)
        cases j with
        | zero => omega
        | succ j => exact ⟨j, by simp at hj; omega, by omega, by simpa using hq, by simpa using ht⟩

/-- **The monitors are sound and complete** on every finite run of the calculus that ends in a
deadlocked state: the monitor accepts the run exactly when the run satisfies the form. -/
theorem monitor_sound {sys : Sys} (φ : TForm) {ρ : List State} (_hr : IsRun sys ρ)
    (_hd : ∀ s ∈ ρ.getLast?, (Sys.lts sys).Deadlocked s) :
    monitor φ ρ = true ↔ FinSat φ ρ := by
  cases φ with
  | eventually p => simp [monitor, FinSat, List.any_eq_true]
  | never p => simp [monitor, FinSat, List.all_eq_true]
  | precedes p q =>
    simp only [monitor, FinSat]
    rw [go_iff]
    simp
  | response p q d => simp only [monitor, FinSat]; exact resp_iff p q d ρ

/-- What a monitor reports on a run. -/
inductive Verdict where
  | holds | fails | incomplete
  deriving DecidableEq, Repr

/-- **The verdict on a run**: a run cut off by the step limit or the bound (`cut`) is
`incomplete` for `eventually` and response forms unless the run already satisfies them; it is
never judged on its last state. A run that ends in a deadlocked state is judged by `monitor`. -/
def verdict (φ : TForm) (ρ : List State) (cut : Bool) : Verdict :=
  match φ with
  | .eventually _ | .response .. =>
    if monitor φ ρ then .holds else if cut then .incomplete else .fails
  | _ => if monitor φ ρ then .holds else .fails

theorem verdict_cut_not_fails (φ : TForm) (ρ : List State)
    (hφ : (∃ p, φ = .eventually p) ∨ ∃ p q d, φ = .response p q d) : verdict φ ρ true ≠ .fails := by
  rcases hφ with ⟨p, rfl⟩ | ⟨p, q, d, rfl⟩ <;> simp only [verdict] <;> split <;> simp

end Exegra.Core.Behav

/-- info: 'Exegra.Core.Behav.explore_holds_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.explore_holds_invariant

/-- info: 'Exegra.Core.Behav.explore_cex_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.explore_cex_real

/-- info: 'Exegra.Core.Behav.monitor_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.monitor_sound
