/-
Labelled transition systems: the object every guarantee Exegra establishes is a proposition about
(docs/foundations.md, section 3).

An `LTS σ α` has a predicate of initial states and a step relation labelled by actions. Unlike the
legacy format-2 interpreter (`Exegra.V2.traceOf`), it is a relation: nondeterminism is part of the object, not
supplied from outside by an explorer, and a system with no successor from some state simply has
none.

This file proves the safety theory the rest builds on:

* `Reach`, the reachable states, and `Invariant P`: every reachable state satisfies `P`, with no
  bound on the length of runs;
* `safe_of_inductive`: an inductive invariant that implies `P` proves `Invariant P`;
* `invariant_iff_exists_inductive`: semantic completeness of the method. Every invariant has an
  inductive strengthening, namely the reachable set itself; this is the standard and easy direction,
  over arbitrary predicates `σ → Prop`. It says nothing about strengthenings expressible in a given
  assertion language (for the expressions of `Exegra.Core.Calculus` they need not exist), and finding
  one is not automatic;
* `NonVacuous` and `Deadlocked`: an `Invariant` of a system with no initial state is true of every
  predicate (`invariant_of_no_init`), so a claim built on an invariant must also establish
  `NonVacuous`. A state with no successor is `Deadlocked`. Partial operations are modelled by an
  explicit error state, never by the absence of a step: a missing step is a deadlock, and a theorem
  about the reachable states would otherwise silently exclude every run that fails;
* `ReachIn n` and `BoundedInvariant n P`, what a search to depth `n` can establish, and
  `invariant_iff_all_bounds`: an invariant is exactly a bounded invariant at every depth. No single
  depth suffices in general (`Exegra.Core.Examples.bounded_not_unbounded`);
* `IsPath`, `KInductive k P` and `kInduction_sound`: for `k ≥ 1`, a predicate that holds within
  `k - 1` steps and on the last state of every path of `k + 1` states (from any state) whose first
  `k` states satisfy it is an invariant (`Exegra.Core.Examples.kSys_*`: 2-inductive, not inductive);
* `Enum`, a complete enumeration of initial states and successors, and `invariant_of_closed`: a
  finite list of states that contains the initial states and is closed under successors proves an
  invariant of every state in it, with no bound. `checkClosed` is a Boolean check of that
  certificate, proved sound (`checkClosed_sound`), so a certificate can be checked by kernel
  evaluation (`decide`) without `native_decide`.
-/

namespace Exegra.Core

/-- A labelled transition system over states `σ` and actions `α`. -/
structure LTS (σ α : Type) where
  init : σ → Prop
  step : σ → α → σ → Prop

namespace LTS

variable {σ α : Type}

/-- The states reachable from an initial state by finitely many steps. -/
inductive Reach (M : LTS σ α) : σ → Prop
  | init {s : σ} : M.init s → Reach M s
  | step {s t : σ} {a : α} : Reach M s → M.step s a t → Reach M t

/-- `P` holds in every reachable state. -/
def Invariant (M : LTS σ α) (P : σ → Prop) : Prop :=
  ∀ s, M.Reach s → P s

/-- `I` holds initially and is preserved by every step, from any state satisfying it (reachable or
not). -/
def Inductive (M : LTS σ α) (I : σ → Prop) : Prop :=
  (∀ s, M.init s → I s) ∧ (∀ s a t, I s → M.step s a t → I t)

theorem reach_of_inductive {M : LTS σ α} {I : σ → Prop} (h : M.Inductive I) :
    ∀ s, M.Reach s → I s := by
  intro s hs
  induction hs with
  | init hi => exact h.1 _ hi
  | step _ hst ih => exact h.2 _ _ _ ih hst

/-- **Unbounded safety from an inductive invariant.** -/
theorem safe_of_inductive {M : LTS σ α} {I P : σ → Prop} (h : M.Inductive I)
    (himp : ∀ s, I s → P s) : M.Invariant P :=
  fun s hs => himp s (reach_of_inductive h s hs)

/-- The reachable set is itself inductive. -/
theorem reach_inductive (M : LTS σ α) : M.Inductive M.Reach :=
  ⟨fun _ h => .init h, fun _ _ _ h hst => .step h hst⟩

/-- **Semantic completeness.** `P` is an invariant exactly when some inductive invariant (over
arbitrary predicates) implies it; the reachable set is one. -/
theorem invariant_iff_exists_inductive (M : LTS σ α) (P : σ → Prop) :
    M.Invariant P ↔ ∃ I, M.Inductive I ∧ ∀ s, I s → P s :=
  ⟨fun h => ⟨M.Reach, reach_inductive M, h⟩, fun ⟨_, hI, himp⟩ => safe_of_inductive hI himp⟩

/-! ### Vacuity and deadlock -/

/-- The system has an initial state. -/
def NonVacuous (M : LTS σ α) : Prop := ∃ s, M.init s

/-- No step leaves `s`. -/
def Deadlocked (M : LTS σ α) (s : σ) : Prop := ∀ a t, ¬ M.step s a t

/-- A reachable state exists only if an initial state does. -/
theorem nonVacuous_of_reach {M : LTS σ α} {s : σ} (h : M.Reach s) : M.NonVacuous := by
  induction h with
  | init hi => exact ⟨_, hi⟩
  | step _ _ ih => exact ih

/-- **Vacuity.** With no initial state, every predicate is an invariant, `False` included. -/
theorem invariant_of_no_init {M : LTS σ α} (h : ¬ M.NonVacuous) (P : σ → Prop) : M.Invariant P :=
  fun _ hs => absurd (nonVacuous_of_reach hs) h

/-! ### Bounded reachability: what a search to a given depth establishes -/

/-- The states reachable in at most `n` steps. -/
inductive ReachIn (M : LTS σ α) : Nat → σ → Prop
  | init {n : Nat} {s : σ} : M.init s → ReachIn M n s
  | step {n : Nat} {s t : σ} {a : α} : ReachIn M n s → M.step s a t → ReachIn M (n + 1) t

/-- `P` holds in every state reachable in at most `n` steps. -/
def BoundedInvariant (M : LTS σ α) (n : Nat) (P : σ → Prop) : Prop :=
  ∀ s, M.ReachIn n s → P s

theorem reach_of_reachIn {M : LTS σ α} {n : Nat} {s : σ} (h : M.ReachIn n s) : M.Reach s := by
  induction h with
  | init hi => exact .init hi
  | step _ hst ih => exact .step ih hst

theorem reachIn_of_reach {M : LTS σ α} {s : σ} (h : M.Reach s) : ∃ n, M.ReachIn n s := by
  induction h with
  | init hi => exact ⟨0, .init hi⟩
  | step _ hst ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .step hn hst⟩

/-- An invariant is exactly a bounded invariant at every depth. -/
theorem invariant_iff_all_bounds (M : LTS σ α) (P : σ → Prop) :
    M.Invariant P ↔ ∀ n, M.BoundedInvariant n P := by
  constructor
  · intro h n s hs
    exact h s (reach_of_reachIn hs)
  · intro h s hs
    obtain ⟨n, hn⟩ := reachIn_of_reach hs
    exact h n s hn

/-! ### k-induction -/

/-- Consecutive states of the list are related by some step. The first state need not be
initial: a path may start anywhere, reachable or not. -/
def IsPath (M : LTS σ α) : List σ → Prop
  | [] => True
  | [_] => True
  | s :: t :: rest => (∃ a, M.step s a t) ∧ IsPath M (t :: rest)

/-- `P` is `k`-inductive: it holds in every state reachable in at most `k - 1` steps, and on every
path of `k + 1` states (from any state) whose first `k` states satisfy `P`, the last one does too.
For `k = 1` this is `Inductive P` restated over paths. -/
def KInductive (M : LTS σ α) (k : Nat) (P : σ → Prop) : Prop :=
  M.BoundedInvariant (k - 1) P ∧
    ∀ (xs : List σ) (hl : xs.length = k + 1), IsPath M xs →
      (∀ i (hi : i < k), P (xs[i]'(by omega))) → P (xs[k]'(by omega))

/-- The states reachable from an initial state in exactly `n` steps. -/
inductive ReachExact (M : LTS σ α) : Nat → σ → Prop
  | init {s : σ} : M.init s → ReachExact M 0 s
  | step {n : Nat} {s t : σ} {a : α} : ReachExact M n s → M.step s a t → ReachExact M (n + 1) t

theorem reachExact_of_reach {M : LTS σ α} {s : σ} (h : M.Reach s) : ∃ n, M.ReachExact n s := by
  induction h with
  | init hi => exact ⟨0, .init hi⟩
  | step _ hst ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .step hn hst⟩

theorem reachIn_mono {M : LTS σ α} {n m : Nat} {s : σ} (h : M.ReachIn n s) (hnm : n ≤ m) :
    M.ReachIn m s := by
  induction h generalizing m with
  | init hi => exact .init hi
  | step _ hst ih =>
    rename_i n' _ _ _
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact .step (ih (by omega)) hst

theorem reachIn_of_exact {M : LTS σ α} {n : Nat} {s : σ} (h : M.ReachExact n s) : M.ReachIn n s := by
  induction h with
  | init hi => exact .init hi
  | step _ hst ih => exact .step ih hst

theorem isPath_append {M : LTS σ α} : ∀ (xs : List σ) (u t : σ) (a : α),
    IsPath M (xs ++ [u]) → M.step u a t → IsPath M (xs ++ [u, t])
  | [], _, _, a, _, hst => ⟨⟨a, hst⟩, trivial⟩
  | [_], _, _, a, h, hst => ⟨h.1, ⟨a, hst⟩, trivial⟩
  | _ :: y :: rest, u, t, a, h, hst => ⟨h.1, isPath_append (y :: rest) u t a h.2 hst⟩

/-- The last `j + 1` states of a run of exactly `n + j` steps: a path ending at `s` whose `i`-th
state is reachable in exactly `n + i` steps. -/
theorem back_path {M : LTS σ α} : ∀ (j n : Nat) (s : σ), M.ReachExact (n + j) s →
    ∃ (xs : List σ) (hl : xs.length = j + 1), IsPath M xs ∧ xs[j]'(by omega) = s ∧
      ∀ i (hi : i < j + 1), M.ReachExact (n + i) (xs[i]'(by omega))
  | 0, n, s, h => ⟨[s], rfl, trivial, rfl, fun i hi => by
      obtain rfl : i = 0 := by omega
      simpa using h⟩
  | j + 1, n, s, h => by
    cases h with
    | step hu hst =>
      rename_i u a
      obtain ⟨xs, hl, hp, hlast, hr⟩ := back_path j n u hu
      have hxs : xs = xs.take j ++ [u] := by
        conv => lhs; rw [← List.take_append_drop j xs]
        congr 1
        rw [List.drop_eq_getElem_cons (by omega), hlast]
        simp [List.drop_eq_nil_of_le (by omega : xs.length ≤ j + 1)]
      refine ⟨xs ++ [s], by simp [hl], ?_, ?_, ?_⟩
      · have := isPath_append (M := M) (xs.take j) u s a (hxs ▸ hp) hst
        rw [hxs]; simpa using this
      · simp [List.getElem_append_right, hl]
      · intro i hi
        by_cases hij : i < j + 1
        · rw [List.getElem_append_left (by omega)]
          exact hr i hij
        · obtain rfl : i = j + 1 := by omega
          rw [List.getElem_append_right (by omega)]
          simpa [hl, Nat.add_assoc] using (ReachExact.step hu hst : M.ReachExact (n + j + 1) s)

/-- **k-induction is sound**: for `k ≥ 1`, a `k`-inductive predicate is an invariant, with no
bound on the length of runs. -/
theorem kInduction_sound {M : LTS σ α} {k : Nat} {P : σ → Prop} (hk : 0 < k)
    (h : M.KInductive k P) : M.Invariant P := by
  obtain ⟨hb, hstep⟩ := h
  have key : ∀ n s, M.ReachExact n s → P s := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro s hs
      by_cases hn : n < k
      · exact hb s (reachIn_mono (reachIn_of_exact hs) (by omega))
      · obtain ⟨d, rfl⟩ : ∃ d, n = d + k := ⟨n - k, by omega⟩
        obtain ⟨xs, hl, hp, hlast, hr⟩ := back_path k d s hs
        have := hstep xs hl hp (fun i hi => ih (d + i) (by omega) _ (hr i (by omega)))
        rwa [hlast] at this
  intro s hs
  obtain ⟨n, hn⟩ := reachExact_of_reach hs
  exact key n s hn

/-! ### Closed-set certificates -/

/-- A complete enumeration of the initial states and of the successors of each state. Completeness
is the obligation: every initial state is listed, and every step leads to a listed successor. -/
structure Enum (M : LTS σ α) where
  inits : List σ
  succ : σ → List σ
  init_complete : ∀ s, M.init s → s ∈ inits
  succ_complete : ∀ s a t, M.step s a t → t ∈ succ s

/-- `L` contains every initial state and is closed under successors. -/
def Closed {M : LTS σ α} (E : Enum M) (L : List σ) : Prop :=
  (∀ s, s ∈ E.inits → s ∈ L) ∧ ∀ s, s ∈ L → ∀ t, t ∈ E.succ s → t ∈ L

theorem closed_inductive {M : LTS σ α} (E : Enum M) {L : List σ} (h : Closed E L) :
    M.Inductive (· ∈ L) :=
  ⟨fun s hs => h.1 s (E.init_complete s hs),
   fun s a t hs hst => h.2 s hs t (E.succ_complete s a t hst)⟩

/-- **Unbounded safety from a closed-set certificate.** -/
theorem invariant_of_closed {M : LTS σ α} (E : Enum M) {L : List σ} {P : σ → Prop}
    (h : Closed E L) (hP : ∀ s, s ∈ L → P s) : M.Invariant P :=
  safe_of_inductive (closed_inductive E h) hP

/-- The certificate check: `L` contains the initial states, is closed under successors, and
satisfies `p` everywhere. -/
def checkClosed [DecidableEq σ] {M : LTS σ α} (E : Enum M) (L : List σ) (p : σ → Bool) : Bool :=
  E.inits.all (fun s => decide (s ∈ L)) &&
  L.all (fun s => (E.succ s).all (fun t => decide (t ∈ L))) &&
  L.all p

theorem checkClosed_sound [DecidableEq σ] {M : LTS σ α} (E : Enum M) (L : List σ)
    (p : σ → Bool) (h : checkClosed E L p = true) : M.Invariant (fun s => p s = true) := by
  simp only [checkClosed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hinit, hsucc⟩, hp⟩ := h
  exact invariant_of_closed E ⟨hinit, hsucc⟩ hp

end LTS

end Exegra.Core
