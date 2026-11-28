import Exegra.Core.Behav
import Exegra.Core.Search
import Exegra.Random

/-
The executable scheduler of the behaviour calculus and its successor function
(docs/assessment/2026-11-26/plan-M2.md, increments M2.3 and M2.8).

* `Exec.step` is the scheduler a run performs: it delivers the head of the queue under the state's
  fault mask, with the draws its book gives (SplitMix streams through `Random.lean`, one stream
  per sampled delay of the system), and reports `idle` (nothing pending), `stopped` (the head is
  after `stopAt`), `committed` or `failed`. The calculus's own relation is `Step`
  (`Core/Behav.lean`); `Exec.step` computes with `deliver`, which is proved equal to `Step`
  (`deliver_iff_step`), so the relation is not the scheduler.
* `step_sound`, `step_failed`: every committed step is a step of `Sys.lts` with the label the
  record names, and a failed step is a step to the explicit error state.
* `idle_deadlocked`, `stopped_deadlocked`: when the scheduler stops on a sorted queue the relation
  has no step either.
* `sample_mem_support`: every draw lies in the support of its distribution.
* `Exec.run` folds `Exec.step` up to a step limit; `run_reach`: every state of a run is reachable.
* `Exec.successors`, with `successors_complete` and `successors_sound`: exactly the steps of the
  relation, every label (entry and draws) included. `Exec.successorsUpTo` truncates each support
  at a cap; `successorsUpTo_eq` says it is `Exec.successors` when nothing is truncated.
* `Exec.enum` is the complete enumeration of `Sys.lts`, `Exec.gen` the search system of it, with
  `Exec.covers` and `Exec.sound`.
-/

namespace Exegra.Core.Behav

open Exegra.Core.LTS

/-! ### Draws -/

/-- A draw of distribution `d` from the stream `name` of seed `seed`, at stream position `i`. -/
def Dist.sample (d : Dist) (seed : UInt64) (name : String) (i : Nat) : Nat :=
  let r := Exegra.Random.draw seed name i
  match d with
  | .fixed v => v
  | .choice vs => vs.getD (Exegra.Random.index r vs.length) 0
  | .uniform lo hi => Exegra.Random.uniformInt r lo hi
  | .table pts => Exegra.Random.sampleTable r pts

theorem sampleTable_go_bounds (u : Nat) : ∀ (L : List (Nat × Nat)) (a b : Nat),
    (∀ p ∈ L, a ≤ p.2 ∧ p.2 ≤ b) → L ≠ [] →
      a ≤ Exegra.Random.sampleTable.go u L ∧ Exegra.Random.sampleTable.go u L ≤ b
  | [], _, _, _, h => absurd rfl h
  | [(u0, x0)], a, b, hb, _ => by
    simp only [Exegra.Random.sampleTable.go]
    exact hb _ List.mem_cons_self
  | (u0, x0) :: (u1, x1) :: rest, a, b, hb, _ => by
    simp only [Exegra.Random.sampleTable.go]
    split
    · have h0 := hb (u0, x0) List.mem_cons_self
      have h1 := hb (u1, x1) (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only at h0 h1
      have hq : (u - u0) * (x1 - x0) / (u1 - u0) ≤ x1 - x0 := by
        by_cases hz : u1 - u0 = 0
        · rw [hz, Nat.div_zero]; exact Nat.zero_le _
        · rename_i hu
          have : u - u0 ≤ u1 - u0 := by omega
          calc (u - u0) * (x1 - x0) / (u1 - u0) ≤ (u1 - u0) * (x1 - x0) / (u1 - u0) :=
                Nat.div_le_div_right (Nat.mul_le_mul_right _ this)
            _ = x1 - x0 := Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hz)
      generalize (u - u0) * (x1 - x0) / (u1 - u0) = q at *
      exact ⟨by omega, by omega⟩
    · exact sampleTable_go_bounds u ((u1, x1) :: rest) a b
        (fun p hp => hb p (List.mem_cons_of_mem _ hp)) (by simp)

theorem foldl_min_le (xs : List Nat) : ∀ a : Nat, xs.foldl min a ≤ a ∧ ∀ y ∈ xs, xs.foldl min a ≤ y := by
  induction xs with
  | nil => intro a; simp
  | cons y ys ih =>
    intro a
    obtain ⟨h1, h2⟩ := ih (min a y)
    refine ⟨?_, ?_⟩
    · simp only [List.foldl_cons]; omega
    · intro z hz
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hz with rfl | hz
      · omega
      · exact h2 z hz

theorem le_foldl_max (xs : List Nat) : ∀ a : Nat, a ≤ xs.foldl max a ∧ ∀ y ∈ xs, y ≤ xs.foldl max a := by
  induction xs with
  | nil => intro a; simp
  | cons y ys ih =>
    intro a
    obtain ⟨h1, h2⟩ := ih (max a y)
    refine ⟨?_, ?_⟩
    · simp only [List.foldl_cons]; omega
    · intro z hz
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hz with rfl | hz
      · omega
      · exact h2 z hz

/-- **Every draw of a well-formed distribution lies in its support.** -/
theorem sample_mem_support {d : Dist} (hd : d.wf = true) (seed : UInt64) (name : String) (i : Nat) :
    d.sample seed name i ∈ d.support := by
  unfold Dist.sample
  cases d with
  | fixed v => simp [Dist.support]
  | choice vs =>
    simp only [Dist.support]
    have hv : vs ≠ [] := by
      intro h; subst h; simp [Dist.wf] at hd
    have hlen : 0 < vs.length := List.length_pos_iff.mpr hv
    have hle : Exegra.Random.index (Exegra.Random.draw seed name i) vs.length < vs.length := by
      unfold Exegra.Random.index
      have := Exegra.Random.uniformInt_le (Exegra.Random.draw seed name i) 0 (vs.length - 1) (Nat.zero_le _)
      omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hle]
    exact List.getElem_mem hle
  | uniform lo hi =>
    simp only [Dist.support]
    have hlh : lo ≤ hi := by simpa [Dist.wf] using hd
    have h1 := Exegra.Random.uniformInt_ge (Exegra.Random.draw seed name i) lo hi
    have h2 := Exegra.Random.uniformInt_le (Exegra.Random.draw seed name i) lo hi hlh
    rw [List.mem_range'_1]; omega
  | table pts =>
    simp only [Dist.support, Exegra.Random.sampleTable]
    cases hm : pts.map Prod.snd with
    | nil =>
      have : pts = [] := List.map_eq_nil_iff.mp hm
      subst this
      simp [Dist.wf] at hd
    | cons x xs =>
      have hne : pts ≠ [] := by intro h; subst h; simp at hm
      have hb := sampleTable_go_bounds ((Exegra.Random.draw seed name i).toNat / 2 ^ 32) pts
        (xs.foldl min x) (xs.foldl max x) (fun p hp => by
          have hmem : p.2 ∈ x :: xs := by rw [← hm]; exact List.mem_map_of_mem hp
          have h1 := (foldl_min_le xs x).2
          have h2 := (le_foldl_max xs x).2
          rcases List.mem_cons.mp hmem with h | h
          · rw [h]; exact ⟨(foldl_min_le xs x).1, (le_foldl_max xs x).1⟩
          · exact ⟨h1 _ h, h2 _ h⟩) hne
      rw [List.mem_range'_1]
      omega

/-! ### The book: streams, as format 2 draws them -/

/-- What a run keeps beside the state, not part of a calculus state: the scenario's seed, the
stream name of each draw slot (format 2's `after:{behavior}:{transition}:{effect}`, shared by the
instances of a behaviour), and how many draws each stream has made, streams in the order they were
first drawn (format 2's `streams`, Format2.lean:1012-1015). -/
structure Book where
  seed : Option UInt64 := none
  names : List String := []
  counts : List (String × Nat) := []

/-- The draws stream `n` has made. -/
def Book.count (b : Book) (n : String) : Nat := ((b.counts.find? (·.1 == n)).map (·.2)).getD 0

/-- The book after one draw from stream `n` (format 2's `bump`). -/
def Book.bump (b : Book) (n : String) : Book :=
  { b with counts := if b.counts.any (·.1 == n) then b.counts.map fun (k, c) => if k == n then (k, c + 1) else (k, c)
                     else b.counts ++ [(n, 1)] }

/-- The machine and transition of each winner of the delivery of `e`, when `e` is delivered (not
dropped or delayed) and phase 1 succeeds; otherwise none. The draws a step makes are those of the
sampled delays of these transitions, as format 2 draws only for the effects that run. -/
def Exec.fired (sys : Sys) (mask : List Bool) (c : Cfg) (e : Entry) : List (Nat × Nat) :=
  let act := sys.active mask
  let att := c.attemptsOf e.event + 1
  if act.any (fun p => p.2.hits [.drop, .lose] e.event att e.time) then []
  else match delayFault act e att with
    | some _ => []
    | none => match winners sys act (c.popE e) e with
      | .ok ws => ws.map (fun w => (w.mach.val, w.idx.val))
      | .error _ => []

/-- One draw slot: the next draw of its stream when its transition fires and a seed is given;
otherwise the first value of its support (format 2 takes a choice's first value without a seed),
with no draw made. -/
def Exec.drawSlot (fired : List (Nat × Nat)) (seed : Option UInt64) (name : String)
    (s : Nat × Nat × Nat × Dist) (b : Book) : Nat × Book :=
  match seed with
  | some sd =>
    if (s.1, s.2.1) ∈ fired then (s.2.2.2.sample sd name (b.count name), b.bump name)
    else (s.2.2.2.support.headD 0, b)
  | none => (s.2.2.2.support.headD 0, b)

/-- The draws of the slots `ss`, from slot number `k`, and the book after them. -/
def Exec.drawSlots (fired : List (Nat × Nat)) (b0 : Book) : Nat → List (Nat × Nat × Nat × Dist) → Book →
    List Nat × Book
  | _, [], b => ([], b)
  | k, s :: ss, b =>
    let (v, b1) := Exec.drawSlot fired b0.seed (b0.names.getD k "") s b
    let (vs, b2) := Exec.drawSlots fired b0 (k + 1) ss b1
    (v :: vs, b2)

/-- The draws of the step delivering `e` from `c`, and the book after it. -/
def Exec.drawsOf (sys : Sys) (mask : List Bool) (c : Cfg) (e : Entry) (b : Book) : List Nat × Book :=
  Exec.drawSlots (Exec.fired sys mask c e) b 0 sys.samples b

theorem Dist.support_ne_nil {d : Dist} (hd : d.wf = true) : d.support ≠ [] := by
  cases d with
  | fixed v => simp [Dist.support]
  | choice vs => simpa [Dist.support, Dist.wf] using hd
  | uniform lo hi =>
    simp only [Dist.wf, decide_eq_true_eq] at hd
    simp only [Dist.support, ne_eq, List.range'_eq_nil_iff]; omega
  | table pts =>
    simp only [Dist.support]
    cases hm : pts.map Prod.snd with
    | nil =>
      have : pts = [] := List.map_eq_nil_iff.mp hm
      subst this; simp [Dist.wf] at hd
    | cons x xs =>
      simp only [ne_eq, List.range'_eq_nil_iff]
      have h1 := (foldl_min_le xs x).1
      have h2 := (le_foldl_max xs x).1
      omega

theorem Dist.headD_mem {d : Dist} (hd : d.wf = true) : d.support.headD 0 ∈ d.support := by
  have := Dist.support_ne_nil hd
  cases h : d.support with
  | nil => exact absurd h this
  | cons x xs => simp

theorem drawSlots_ok (fired : List (Nat × Nat)) (b0 : Book) : (k : Nat) → (ss : List (Nat × Nat × Nat × Dist)) →
    (b : Book) → (∀ s ∈ ss, s.2.2.2.wf = true) →
    (Exec.drawSlots fired b0 k ss b).1.length = ss.length ∧
      ∀ p ∈ (Exec.drawSlots fired b0 k ss b).1.zip (ss.map fun s => s.2.2.2), p.1 ∈ p.2.support
  | _, [], _, _ => by simp [Exec.drawSlots]
  | k, s :: ss, b, hw => by
    have hs := hw s List.mem_cons_self
    have ih := drawSlots_ok fired b0 (k + 1) ss (Exec.drawSlot fired b0.seed (b0.names.getD k "") s b).2
      (fun t ht => hw t (List.mem_cons_of_mem _ ht))
    simp only [Exec.drawSlots, List.length_cons, List.map_cons, List.zip_cons_cons, List.mem_cons]
    refine ⟨by rw [ih.1], ?_⟩
    rintro p (rfl | hp)
    · simp only [Exec.drawSlot]
      split
      · split
        · exact sample_mem_support hs _ _ _
        · exact Dist.headD_mem hs
      · exact Dist.headD_mem hs
    · exact ih.2 p hp

theorem Exec.drawsOf_ok {sys : Sys} (hwf : sys.WF) (mask : List Bool) (c : Cfg) (e : Entry) (b : Book) :
    DrawsOk sys (Exec.drawsOf sys mask c e b).1 := by
  have hw : ∀ s ∈ sys.samples, s.2.2.2.wf = true := fun s hs =>
    WF.dists hwf _ (List.mem_map_of_mem hs)
  have h := drawSlots_ok (Exec.fired sys mask c e) b 0 sys.samples b hw
  unfold Exec.drawsOf
  refine ⟨by rw [h.1]; simp [Sys.dists], ?_⟩
  simpa [Sys.dists] using h.2

/-- What a step records: its label. -/
structure Rec where
  label : Label

def Exec.label (r : Rec) : Label := r.label

inductive XResult where
  | idle
  | stopped
  | committed (r : Rec) (s : State) (b : Book)
  | failed (r : Rec)

/-- The executable step: delivers the head of the queue, drawing for the sampled delays of the
transitions that fire, from their streams, as format 2 does. -/
def Exec.step (sys : Sys) : State → Book → XResult
  | .err _ _, _ => .idle
  | .run mask c, b =>
    match c.pending with
    | [] => .idle
    | e :: _ =>
      if sys.stopAt.all (fun s => decide (e.time ≤ s)) then
        match deliver sys mask c ⟨e, (Exec.drawsOf sys mask c e b).1⟩ with
        | some (.ok c') => .committed ⟨⟨e, (Exec.drawsOf sys mask c e b).1⟩⟩ (.run mask c') (Exec.drawsOf sys mask c e b).2
        | some (.error _) => .failed ⟨⟨e, (Exec.drawsOf sys mask c e b).1⟩⟩
        | none => .idle
      else .stopped

theorem Exec.step_sound {sys : Sys} {s s' : State} {b b' : Book} {r : Rec} (_hwf : sys.WF)
    (_hs : s.cfg.Sorted) (h : Exec.step sys s b = .committed r s' b') :
    (Sys.lts sys).step s (Exec.label r) s' := by
  cases s with
  | err m c => simp [Exec.step] at h
  | run m c =>
    simp only [Exec.step] at h
    split at h
    · cases h
    · split at h
      · split at h
        · rename_i c' hd
          cases h
          exact deliver_eq_step.mp (by simp only [Exec.label]; rw [hd]; rfl)
        · cases h
        · cases h
      · cases h

theorem Exec.step_failed {sys : Sys} {s : State} {b : Book} {r : Rec} (_hwf : sys.WF)
    (_hs : s.cfg.Sorted) (h : Exec.step sys s b = .failed r) :
    (Sys.lts sys).step s (Exec.label r) (.err s.mask s.cfg) := by
  cases s with
  | err m c => simp [Exec.step] at h
  | run m c =>
    simp only [Exec.step] at h
    split at h
    · cases h
    · split at h
      · split at h
        · cases h
        · rename_i err hd
          cases h
          exact deliver_eq_step.mp (by simp only [Exec.label]; rw [hd]; rfl)
        · cases h
      · cases h

/-- On a sorted queue whose head is not after `stopAt`, the head can be delivered. -/
theorem deliverAt_head_some {sys : Sys} {mask : List Bool} {c : Cfg} {e : Entry} {rest : List Entry}
    (hp : c.pending = e :: rest) (hs : c.Sorted) (hstop : sys.stopAt.all (fun s => decide (e.time ≤ s)) = true) :
    deliverAt sys mask c 0 ≠ none := by
  have hmin : c.pending.all (fun x => decide (e.time ≤ x.time)) = true := by
    simp only [List.all_eq_true, decide_eq_true_eq]
    intro x hx
    have hs' : c.pending.Pairwise (fun a b => a.time ≤ b.time) := hs
    rw [hp] at hx hs'
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_refl _
    · exact (List.pairwise_cons.mp hs').1 x hx
  unfold deliverAt deliverWith
  rw [hp]
  simp only [List.getElem?_cons_zero]
  rw [← hp, hmin, hstop]
  simp

/-- The head of a sorted queue is delivered with any draws in the supports, unless `stopAt`
forbids it. -/
theorem deliver_head_some {sys : Sys} {mask : List Bool} {c : Cfg} {e : Entry} {rest : List Entry}
    (ds : List Nat) (hd : DrawsOk sys ds)
    (hp : c.pending = e :: rest) (hs : c.Sorted) (hstop : sys.stopAt.all (fun s => decide (e.time ≤ s)) = true) :
    deliver sys mask c ⟨e, ds⟩ ≠ none := by
  unfold deliver
  simp only [hd, if_true]
  rw [hp]
  simp only [List.idxOf?_cons, BEq.rfl, if_true]
  exact deliverAt_head_some (sys := sys.resolve ds) hp hs hstop

theorem Exec.idle_deadlocked {sys : Sys} {s : State} {b : Book} (hwf : sys.WF) (hs : s.cfg.Sorted)
    (h : Exec.step sys s b = .idle) : (Sys.lts sys).Deadlocked s := by
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
        · exact absurd ‹deliver sys _ c _ = none›
            (deliver_head_some _ (Exec.drawsOf_ok hwf m c e b) hp hs ‹_›)
      · cases h

theorem Exec.stopped_deadlocked {sys : Sys} {s : State} {b : Book} (hs : s.cfg.Sorted)
    (h : Exec.step sys s b = .stopped) : (Sys.lts sys).Deadlocked s := by
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
        intro l t hst
        obtain ⟨_, hc1, hc2, hc3⟩ := Step.ready (show Step sys m c l t from hst)
        apply hstop
        simp only [Option.all_eq_true, decide_eq_true_eq]
        intro s hsome
        have hs' : c.pending.Pairwise (fun a b => a.time ≤ b.time) := hs
        rw [hp] at hs' hc1
        have hex : e.time ≤ l.entry.time := by
          rcases List.mem_cons.mp hc1 with h | h
          · rw [h]; exact Nat.le_refl _
          · exact (List.pairwise_cons.mp hs').1 _ h
        exact Nat.le_trans hex (hc3 s hsome)

/-- **The scheduler makes progress**: on a sorted queue it is idle only when nothing is pending. -/
theorem Exec.step_live {sys : Sys} {m : List Bool} {c : Cfg} {b : Book} (hwf : sys.WF) (hs : c.Sorted)
    (h : Exec.step sys (.run m c) b = .idle) : c.pending = [] := by
  simp only [Exec.step] at h
  split at h
  · assumption
  · rename_i e rest hp
    split at h
    · split at h
      · cases h
      · cases h
      · exact absurd ‹deliver sys _ c _ = none›
          (deliver_head_some _ (Exec.drawsOf_ok hwf m c e b) hp hs ‹_›)
    · cases h

/-! ### Runs -/

/-- A run: the states the scheduler reaches, and the records of the steps between them. -/
structure Run where
  states : List State
  recs : List Rec

/-- The run from `s`, at most `fuel` steps: `s` first, then each state the scheduler reaches, the
error state included. -/
def Exec.run (sys : Sys) : Nat → State → Book → Run
  | 0, s, _ => ⟨[s], []⟩
  | fuel + 1, s, b =>
    match Exec.step sys s b with
    | .committed r s' b' =>
      let rest := Exec.run sys fuel s' b'
      ⟨s :: rest.states, r :: rest.recs⟩
    | .failed r => ⟨[s, .err s.mask s.cfg], [r]⟩
    | _ => ⟨[s], []⟩

/-- **Every state of a run is reachable** from a reachable start. -/
theorem run_reach {sys : Sys} (hwf : sys.WF) : (fuel : Nat) → {s : State} → (b : Book) →
    (Sys.lts sys).Reach s → ∀ t ∈ (Exec.run sys fuel s b).states, (Sys.lts sys).Reach t
  | 0, s, b, hr, t, ht => by simp [Exec.run] at ht; subst ht; exact hr
  | fuel + 1, s, b, hr, t, ht => by
    have hsorted : s.cfg.Sorted := sorted_invariant sys hwf s hr
    simp only [Exec.run] at ht
    split at ht
    · rename_i r s' b' h
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hr
      · exact run_reach hwf fuel b' (.step hr (Exec.step_sound hwf hsorted h)) t ht
    · rename_i r h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact hr
      · exact .step hr (Exec.step_failed hwf hsorted h)
    · simp at ht; subst ht; exact hr

/-! ### Successors and the enumeration -/

/-- Every vector of draws: one value of each support. -/
def drawVectors : List Dist → List (List Nat)
  | [] => [[]]
  | d :: ds => d.support.flatMap (fun v => (drawVectors ds).map (v :: ·))

/-- Every vector of draws with each support cut to its first `cap` values. -/
def drawVectorsUpTo (cap : Nat) : List Dist → List (List Nat)
  | [] => [[]]
  | d :: ds => (d.support.take cap).flatMap (fun v => (drawVectorsUpTo cap ds).map (v :: ·))

theorem mem_drawVectors : (D : List Dist) → (ds : List Nat) → ds.length = D.length →
    (∀ p ∈ ds.zip D, p.1 ∈ p.2.support) → ds ∈ drawVectors D
  | [], [], _, _ => by simp [drawVectors]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | d :: D, v :: ds, hl, hz => by
    simp only [drawVectors, List.mem_flatMap, List.mem_map]
    refine ⟨v, hz (v, d) List.mem_cons_self, ds, ?_, rfl⟩
    exact mem_drawVectors D ds (by simpa using hl) (fun p hp => hz p (List.mem_cons_of_mem _ hp))

theorem drawVectorsUpTo_eq (cap : Nat) : (D : List Dist) → (∀ d ∈ D, d.support.length ≤ cap) →
    drawVectorsUpTo cap D = drawVectors D
  | [], _ => rfl
  | d :: D, h => by
    simp only [drawVectorsUpTo, drawVectors]
    rw [List.take_of_length_le (h d List.mem_cons_self),
      drawVectorsUpTo_eq cap D (fun e he => h e (List.mem_cons_of_mem _ he))]

/-- The successors of a state with every support cut to its first `cap` values. -/
def Exec.successorsUpTo (cap : Nat) (sys : Sys) : State → List (Label × State)
  | .run mask c => c.pending.flatMap (fun e => (drawVectorsUpTo cap sys.dists).filterMap
      (fun ds => (deliver sys mask c ⟨e, ds⟩).map (fun r => (⟨e, ds⟩, outcome mask c r))))
  | .err _ _ => []

/-- The successors of a state: every label (delivered entry and draws). -/
def Exec.successors (sys : Sys) : State → List (Label × State)
  | .run mask c => c.pending.flatMap (fun e => (drawVectors sys.dists).filterMap
      (fun ds => (deliver sys mask c ⟨e, ds⟩).map (fun r => (⟨e, ds⟩, outcome mask c r))))
  | .err _ _ => []

/-- **When no support is cut, the capped successors are all of them.** -/
theorem successorsUpTo_eq {cap : Nat} {sys : Sys} (s : State)
    (h : ∀ d ∈ sys.dists, d.support.length ≤ cap) :
    Exec.successorsUpTo cap sys s = Exec.successors sys s := by
  cases s with
  | err => rfl
  | run m c => simp only [Exec.successorsUpTo, Exec.successors, drawVectorsUpTo_eq cap _ h]

theorem successors_complete {sys : Sys} {s t : State} {l : Label}
    (h : (Sys.lts sys).step s l t) : (l, t) ∈ Exec.successors sys s := by
  cases s with
  | err m c => exact absurd h id
  | run m c =>
    have h' : Step sys m c l t := h
    obtain ⟨hd, hr⟩ := Step.ready h'
    have hdel := (deliver_eq_step (sys := sys) (mask := m) (c := c) (l := l) (t := t)).mpr h'
    simp only [Exec.successors, List.mem_flatMap, List.mem_filterMap]
    refine ⟨l.entry, hr.1, l.draws, mem_drawVectors _ _ hd.1 hd.2, ?_⟩
    cases hl : deliver sys m c l with
    | none => rw [hl] at hdel; cases hdel
    | some r =>
      rw [hl] at hdel
      simp only [Option.map_some, Option.some.injEq] at hdel ⊢
      rw [hdel]

theorem successors_sound {sys : Sys} {s t : State} {l : Label}
    (h : (l, t) ∈ Exec.successors sys s) : (Sys.lts sys).step s l t := by
  cases s with
  | err m c => simp [Exec.successors] at h
  | run m c =>
    simp only [Exec.successors, List.mem_flatMap, List.mem_filterMap] at h
    obtain ⟨e, _, ds, _, hk⟩ := h
    cases hd : deliver sys m c ⟨e, ds⟩ with
    | none => rw [hd] at hk; cases hk
    | some r =>
      rw [hd] at hk
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      exact deliver_eq_step.mp (by rw [hd]; rfl)

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

/-- **A counterexample of the list-based search refutes the invariant** (criterion 11): the
kernel-evaluable form of `Exec.cex_refutes`. `searchL` returns what `Gen.search` returns
(`Gen.search_eq_searchL`), and it reduces in the kernel, so the hypothesis can be discharged by
`decide`, with no `native_decide` and no `Lean.ofReduceBool`. -/
theorem Exec.cex_refutesL {sys : Sys} {ok : State → Bool} {bound cap : Nat}
    (h : (Gen.searchL (Exec.gen sys) ok bound cap).isCex = true) :
    ¬ (Sys.lts sys).Invariant (fun s => ok s = true) := by
  obtain ⟨p, hp⟩ := Gen.Result.isCex_iff.mp h
  exact Exec.cex_refutes (p := p) (by rw [Gen.search_eq_searchL]; exact hp)

/-- **A `holds` of the list-based search proves the invariant**: the kernel-evaluable form of
`Exec.holds_invariant`. -/
theorem Exec.holds_invariantL {sys : Sys} {ok : State → Bool} {bound cap : Nat}
    (h : (Gen.searchL (Exec.gen sys) ok bound cap).isHolds = true) :
    (Sys.lts sys).Invariant (fun s => ok s = true) := by
  obtain ⟨n, hn⟩ := Gen.Result.isHolds_iff.mp h
  exact Exec.holds_invariant (n := n) (by rw [Gen.search_eq_searchL]; exact hn)

end Exegra.Core.Behav
