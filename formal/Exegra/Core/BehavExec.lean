import Exegra.Core.Behav
import Exegra.Core.Search

/-
The executable scheduler of the behaviour calculus and its successor function
(docs/assessment/2026-11-26/plan-M2.md, increment M2.3).

* `Exec.step` is the scheduler a run performs: it delivers the head of the queue (label 0), under
  the state's fault mask, and reports `idle` (nothing pending), `stopped` (the head is after
  `stopAt`), `committed` or `failed`. It computes with the relation's own delivery function
  `deliver`, so there is no second copy of the semantics beside the relation.
* `step_sound`, `step_failed`: every committed step is a step of `Sys.lts` labelled 0, and a failed
  step is a step to the explicit error state carrying the configuration before it.
* `idle_deadlocked`, `stopped_deadlocked`: when the scheduler stops on a sorted queue (which every
  reachable state of a well-formed system has, `sorted_invariant`), the relation has no step either:
  the scheduler never stops early. `step_live` is the same fact as progress.
* `Exec.run` folds `Exec.step` up to a step limit; `run_reach`: every state of a run is reachable.
* `Exec.successors`, with `successors_complete` and `successors_sound`: exactly the steps of the
  relation, every label included. `Exec.inits` lists the initial state of every fault mask.
* `Exec.enum` is the complete enumeration of `Sys.lts`, `Exec.gen` the search system of it, with
  `Exec.covers` and `Exec.sound`: `Gen.search` results on `Exec.gen` are theorems about the
  calculus's LTS (`Exec.holds_invariant`, `Exec.cex_refutes`), through `invariant_of_search` and
  `not_invariant_of_search` of `Exegra.Core.Search`.
-/

namespace Exegra.Core.Behav

open Exegra.Core.LTS

inductive XResult where
  | idle
  | stopped
  | committed (s : State)
  | failed (s : State)

/-- The executable step: delivers the head of the queue. -/
def Exec.step (sys : Sys) : State → XResult
  | .err _ _ => .idle
  | .run mask c =>
    match c.pending with
    | [] => .idle
    | e :: _ =>
      if sys.stopAt.all (fun s => decide (e.time ≤ s)) then
        match deliver sys mask c 0 with
        | some (.ok c') => .committed (.run mask c')
        | some (.error _) => .failed (.err mask c)
        | none => .idle
      else .stopped

theorem Exec.step_sound {sys : Sys} {s s' : State} (h : Exec.step sys s = .committed s') :
    (Sys.lts sys).step s 0 s' := by
  cases s with
  | err m c => simp [Exec.step] at h
  | run m c =>
    show (deliver sys m c 0).map (outcome m c) = some s'
    simp only [Exec.step] at h
    split at h
    · cases h
    · split at h
      · split at h
        · rename_i c' hd; cases h; rw [hd]; rfl
        · cases h
        · cases h
      · cases h

theorem Exec.step_failed {sys : Sys} {s s' : State} (h : Exec.step sys s = .failed s') :
    (Sys.lts sys).step s 0 s' ∧ s' = .err s.mask s.cfg := by
  cases s with
  | err m c => simp [Exec.step] at h
  | run m c =>
    simp only [Exec.step] at h
    split at h
    · cases h
    · split at h
      · split at h
        · cases h
        · rename_i err hd; cases h
          exact ⟨show (deliver sys m c 0).map (outcome m c) = some _ by rw [hd]; rfl, rfl⟩
        · cases h
      · cases h

/-- On a sorted queue whose head is not after `stopAt`, the head can be delivered. -/
theorem deliver_head_some {sys : Sys} {mask : List Bool} {c : Cfg} {e : Entry} {rest : List Entry}
    (hp : c.pending = e :: rest) (hs : c.Sorted) (hstop : sys.stopAt.all (fun s => decide (e.time ≤ s)) = true) :
    deliver sys mask c 0 ≠ none := by
  have hmin : c.pending.all (fun x => decide (e.time ≤ x.time)) = true := by
    simp only [List.all_eq_true, decide_eq_true_eq]
    intro x hx
    have hs' : c.pending.Pairwise (fun a b => a.time ≤ b.time) := hs
    rw [hp] at hx hs'
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_refl _
    · exact (List.pairwise_cons.mp hs').1 x hx
  unfold deliver deliverWith
  rw [hp]
  simp only [List.getElem?_cons_zero]
  rw [← hp, hmin, hstop]
  simp

theorem Exec.idle_deadlocked {sys : Sys} {s : State} (hs : s.cfg.Sorted)
    (h : Exec.step sys s = .idle) : (Sys.lts sys).Deadlocked s := by
  cases s with
  | err m c => exact err_deadlocked sys m c
  | run m c =>
    simp only [Exec.step] at h
    split at h
    · rename_i hp; exact deadlocked_of_pending_nil sys m c hp
    · rename_i e rest hp
      split at h
      · split at h
        · cases h
        · cases h
        · exact absurd ‹deliver sys _ c 0 = none› (deliver_head_some hp hs ‹_›)
      · cases h

theorem Exec.stopped_deadlocked {sys : Sys} {s : State} (hs : s.cfg.Sorted)
    (h : Exec.step sys s = .stopped) : (Sys.lts sys).Deadlocked s := by
  cases s with
  | err m c => exact err_deadlocked sys m c
  | run m c =>
    simp only [Exec.step] at h
    split at h
    · cases h
    · rename_i e rest hp
      split at h
      · split at h <;> cases h
      · rename_i hstop
        intro k t hst
        have hst' : (deliver sys m c k).map (outcome m c) = some t := hst
        unfold deliver deliverWith at hst'
        split at hst'
        · cases hst'
        · rename_i x hx
          split at hst'
          · rename_i hc
            apply hstop
            simp only [Bool.and_eq_true, Option.all_eq_true, decide_eq_true_eq] at hc ⊢
            intro s hsome
            have hx' : x ∈ c.pending := List.mem_of_getElem? hx
            have hex : e.time ≤ x.time := by
              have hs' : c.pending.Pairwise (fun a b => a.time ≤ b.time) := hs
              rw [hp] at hs' hx'
              rcases List.mem_cons.mp hx' with rfl | hx'
              · exact Nat.le_refl _
              · exact (List.pairwise_cons.mp hs').1 x hx'
            exact Nat.le_trans hex (hc.2 s hsome)
          · cases hst'

/-- **The scheduler makes progress**: on a sorted queue it is idle only when nothing is pending,
and otherwise it commits, fails, or stops at `stopAt`. -/
theorem Exec.step_live {sys : Sys} {m : List Bool} {c : Cfg} (hs : c.Sorted)
    (h : Exec.step sys (.run m c) = .idle) : c.pending = [] := by
  simp only [Exec.step] at h
  split at h
  · assumption
  · rename_i e rest hp
    split at h
    · split at h
      · cases h
      · cases h
      · exact absurd ‹deliver sys _ c 0 = none› (deliver_head_some hp hs ‹_›)
    · cases h

/-! ### Runs -/

/-- The states of a run from `s`, at most `fuel` steps: `s` first, then each state the scheduler
reaches, the error state included. -/
def Exec.run (sys : Sys) : Nat → State → List State
  | 0, s => [s]
  | fuel + 1, s =>
    match Exec.step sys s with
    | .committed s' => s :: Exec.run sys fuel s'
    | .failed s' => [s, s']
    | _ => [s]

/-- **Every state of a run is reachable** from a reachable start. -/
theorem run_reach {sys : Sys} : (fuel : Nat) → {s : State} → (Sys.lts sys).Reach s →
    ∀ t ∈ Exec.run sys fuel s, (Sys.lts sys).Reach t
  | 0, s, hr, t, ht => by simp [Exec.run] at ht; subst ht; exact hr
  | fuel + 1, s, hr, t, ht => by
    simp only [Exec.run] at ht
    split at ht
    · rename_i s' h
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hr
      · exact run_reach fuel (.step hr (Exec.step_sound h)) t ht
    · rename_i s' h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact hr
      · exact .step hr (Exec.step_failed h).1
    · simp at ht; subst ht; exact hr

/-! ### Successors and the enumeration -/

def Exec.successors (sys : Sys) : State → List (Nat × State)
  | .run mask c => (List.range c.pending.length).filterMap
      (fun k => (deliver sys mask c k).map (fun r => (k, outcome mask c r)))
  | .err _ _ => []

theorem successors_complete {sys : Sys} {s t : State} {k : Nat} (h : (Sys.lts sys).step s k t) :
    (k, t) ∈ Exec.successors sys s := by
  cases s with
  | err m c => exact absurd h id
  | run m c =>
    have h' : (deliver sys m c k).map (outcome m c) = some t := h
    simp only [Exec.successors, List.mem_filterMap, List.mem_range]
    refine ⟨k, ?_, ?_⟩
    · apply Nat.lt_of_not_le
      intro hk
      rw [deliver_none_of_length_le sys m c hk] at h'
      cases h'
    · cases hd : deliver sys m c k with
      | none => rw [hd] at h'; cases h'
      | some r => rw [hd] at h'; simp only [Option.map_some, Option.some.injEq] at h' ⊢; rw [h']

theorem successors_sound {sys : Sys} {s t : State} {k : Nat} (h : (k, t) ∈ Exec.successors sys s) :
    (Sys.lts sys).step s k t := by
  cases s with
  | err m c => simp [Exec.successors] at h
  | run m c =>
    show (deliver sys m c k).map (outcome m c) = some t
    simp only [Exec.successors, List.mem_filterMap, List.mem_range] at h
    obtain ⟨k', _, hk⟩ := h
    cases hd : deliver sys m c k' with
    | none => rw [hd] at hk; cases hk
    | some r =>
      rw [hd] at hk
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      rw [hd]; rfl

/-- Every list of `n` Booleans. -/
def masks : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (masks n).flatMap (fun m => [false :: m, true :: m])

theorem mem_masks : (m : List Bool) → m ∈ masks m.length
  | [] => by simp [masks]
  | b :: m => by
    simp only [masks, List.length_cons, List.mem_flatMap]
    exact ⟨m, mem_masks m, by cases b <;> simp⟩

theorem length_of_mem_masks : (n : Nat) → {m : List Bool} → m ∈ masks n → m.length = n
  | 0, m, h => by simp [masks] at h; subst h; rfl
  | n + 1, m, h => by
    simp only [masks, List.mem_flatMap] at h
    obtain ⟨m', hm', hm⟩ := h
    have := length_of_mem_masks n hm'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp [this]

/-- The initial state of every fault mask. -/
def Exec.inits (sys : Sys) : List State :=
  (masks sys.faults.length).map (fun m => .run m (sys.initCfg m))

/-- The complete enumeration of the calculus's transition system. -/
def Exec.enum (sys : Sys) : Enum (Sys.lts sys) where
  inits := Exec.inits sys
  succ s := (Exec.successors sys s).map Prod.snd
  init_complete := by
    intro s hs
    obtain ⟨m, hm, rfl⟩ := hs
    simp only [Exec.inits, List.mem_map]
    exact ⟨m, hm ▸ mem_masks m, rfl⟩
  succ_complete := by
    intro s k t h
    simp only [List.mem_map]
    exact ⟨(k, t), successors_complete h, rfl⟩

/-- The search system of the calculus: what `Gen.search` explores. -/
def Exec.gen (sys : Sys) : Gen.Sys State := (Exec.enum sys).toSys

theorem Exec.covers (sys : Sys) : Covers (Exec.gen sys) (Sys.lts sys) :=
  Enum.toSys_covers (Exec.enum sys)

theorem Exec.sound (sys : Sys) : Sound (Exec.gen sys) (Sys.lts sys) where
  init := by
    intro s hs
    simp only [Exec.gen, Enum.toSys, Exec.enum, Exec.inits, List.mem_map] at hs
    obtain ⟨m, hm, rfl⟩ := hs
    exact ⟨m, length_of_mem_masks _ hm, rfl⟩
  step := by
    intro s k t h
    simp only [Exec.gen, Enum.toSys, Exec.enum] at h
    have hm : t ∈ (Exec.successors sys s).map Prod.snd := List.mem_of_getElem? h
    simp only [List.mem_map] at hm
    obtain ⟨⟨a, t'⟩, hmem, rfl⟩ := hm
    exact ⟨a, successors_sound hmem⟩

/-- **A `holds` result of the search on the calculus proves an unbounded invariant** of its LTS. -/
theorem Exec.holds_invariant {sys : Sys} {ok : State → Bool} {bound cap n : Nat}
    (h : Gen.search (Exec.gen sys) ok bound cap = .holds n) :
    (Sys.lts sys).Invariant (fun s => ok s = true) :=
  invariant_of_search (Exec.covers sys) h

/-- **A counterexample of the search on the calculus refutes the invariant** of its LTS. -/
theorem Exec.cex_refutes {sys : Sys} {ok : State → Bool} {bound cap : Nat} {p : Gen.Path State}
    (h : Gen.search (Exec.gen sys) ok bound cap = .counterexample p) :
    ¬ (Sys.lts sys).Invariant (fun s => ok s = true) :=
  not_invariant_of_search (Exec.sound sys) h

end Exegra.Core.Behav
