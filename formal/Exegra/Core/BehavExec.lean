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
  /-- The stream of each world draw site (machine, transition, effect). -/
  sites : List ((Nat × Nat × Nat) × String) := []

/-- The draws stream `n` has made. -/
def Book.count (b : Book) (n : String) : Nat := ((b.counts.find? (·.1 == n)).map (·.2)).getD 0

/-- The book after one draw from stream `n` (format 2's `bump`). -/
def Book.bump (b : Book) (n : String) : Book :=
  { b with counts := if b.counts.any (·.1 == n) then b.counts.map fun (k, c) => if k == n then (k, c + 1) else (k, c)
                     else b.counts ++ [(n, 1)] }

/-- The machine and transition of each winner of the delivery of `e`, when `e` is delivered (not
dropped or delayed) and phase 1 succeeds; otherwise none. The draws a step makes are those of the
sampled delays of these transitions, as format 2 draws only for the effects that run. -/
def Exec.fired (sys : Sys) (mask : List Bool) (c : Cfg) (e : Entry) (rv : List Nat) : List (Nat × Nat) :=
  if e.kind != .event then []
  else match routeOf sys c e rv with
    | some (.ok (c1, e1, [])) =>
      let act := sys.active mask
      let att := c1.attemptsOf e1.event + 1
      if act.any (fun p => p.2.hits [.drop, .lose] e1.event att e1.time) then []
      else match delayFault act e1 att with
        | some _ => []
        | none => match winners sys act (c1.popE e) e1 with
          | .ok ws => ws.map (fun w => (w.mach.val, w.idx.val))
          | .error _ => []
    | _ => []

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

/-- The draws of the step delivering `e` from `c` with route draws `rv`, and the book after it. -/
def Exec.drawsOf (sys : Sys) (mask : List Bool) (c : Cfg) (e : Entry) (rv : List Nat) (b : Book) : List Nat × Book :=
  Exec.drawSlots (Exec.fired sys mask c e rv) b 0 sys.samples b

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

theorem Exec.drawsOf_ok {sys : Sys} (hwf : sys.WF) (mask : List Bool) (c : Cfg) (e : Entry) (rv : List Nat)
    (b : Book) : DrawsOk sys (Exec.drawsOf sys mask c e rv b).1 := by
  have hw : ∀ s ∈ sys.samples, s.2.2.2.wf = true := fun s hs =>
    WF.dists hwf _ (List.mem_map_of_mem hs)
  have h := drawSlots_ok (Exec.fired sys mask c e rv) b 0 sys.samples b hw
  unfold Exec.drawsOf
  refine ⟨by rw [h.1]; simp [Sys.dists], ?_⟩
  simpa [Sys.dists] using h.2

/-! ### World draws -/

/-- The draw program of delivering `e` from `c` in system `R` under `mask`: the holes of the step's
settling, in order (none when the step does not settle). It follows `deliverEvent` and
`worldFill`. -/
def holesAt (R : Sys) (mask : List Bool) (c : Cfg) (e : Entry) (rv : List Nat) : List ((Nat × Nat × Nat) × Dist) :=
  match e.kind with
  | .event =>
    match routeOf R c e rv with
    | some (.ok (c1, e1, [])) =>
      let act := R.active mask
      let att := c1.attemptsOf e1.event + 1
      if act.any (fun p => p.2.hits [.drop, .lose] e1.event att e1.time) then []
      else match act.find? (fun p => p.2.hits [.delay, .retry] e1.event att e1.time && !(e1.done.contains p.1)) with
        | some _ => []
        | none => match winners R act (c1.popE e) e1 with
          | .error _ => []
          | .ok ws => match phase2 R (c1.popE e) e1 ws c1.machines with
            | .error _ => []
            | .ok (ms, bs) => holesOf (settle R ((c1.popE e).commit R.sig.machines ms bs).time
                (opsOf R.sig.machines bs) [] ((c1.popE e).commit R.sig.machines ms bs).world).2
    | _ => []
  | _ => holesOf (worldStep R (c.popW e) e).2

/-- The draw program of the label with entry `e`, draws `ds` and route draws `rv`, after the
route draws. -/
def Exec.holes (sys : Sys) (mask : List Bool) (c : Cfg) (e : Entry) (ds rv : List Nat) :
    List ((Nat × Nat × Nat) × Dist) :=
  holesAt (sys.resolve ds) mask c e rv

/-- An entry of the world takes no route draws. -/
theorem nR_world {sys : Sys} {c : Cfg} {e : Entry} (h : e.kind ≠ .event) : sys.nR c e = 0 := by
  have : sys.toRoute e = false := by
    simp only [Sys.toRoute, beq_false_of_ne h, Bool.false_and]
  simp [Sys.nR, routeHoles, this]

theorem routeHoles_world {sys : Sys} {c : Cfg} {e : Entry} (h : e.kind ≠ .event) : routeHoles sys c e = [] :=
  List.length_eq_zero_iff.mp (nR_world h)

/-- **A step's world draws fit its draw program**: first the route draws, then the draws of the
step's settling. -/
theorem Step.holes {sys : Sys} {mask : List Bool} {c : Cfg} {l : Label} {t : State}
    (h : Step sys mask c l t) :
    DrawsFit (l.wdraws.take (sys.nR c l.entry)) (routeHoles sys c l.entry) ∧
    DrawsFit (l.wdraws.drop (sys.nR c l.entry))
      (Exec.holes sys mask c l.entry l.draws (l.wdraws.take (sys.nR c l.entry))) := by
  unfold Exec.holes holesAt
  cases h with
  | drop _ _ hk hro hw0 hdr =>
    refine ⟨routeOf_fit.1.1 _ _ hro, ?_⟩
    rw [hk]; simp only [routeOf_resolve, hro]
    unfold dropHit at hdr; simp only [resolve_active]; simp only [hdr, ↓reduceIte, hw0]; exact ⟨rfl, by simp⟩
  | delay _ _ hk hro hw0 hdr hf _ =>
    refine ⟨routeOf_fit.1.1 _ _ hro, ?_⟩
    rw [hk]; simp only [routeOf_resolve, hro]
    unfold dropHit at hdr; unfold delayFault at hf; simp only [resolve_active]
    simp only [hdr, Bool.false_eq_true, ↓reduceIte, hf, hw0]; exact ⟨rfl, by simp⟩
  | delayTimeErr _ _ hk hro hw0 hdr hf _ =>
    refine ⟨routeOf_fit.1.1 _ _ hro, ?_⟩
    rw [hk]; simp only [routeOf_resolve, hro]
    unfold dropHit at hdr; unfold delayFault at hf; simp only [resolve_active]
    simp only [hdr, Bool.false_eq_true, ↓reduceIte, hf, hw0]; exact ⟨rfl, by simp⟩
  | deliverOk _ _ hk hro hdr hnone hw hp hs hfit _ _ =>
    refine ⟨routeOf_fit.1.1 _ _ hro, ?_⟩
    rw [hk]; simp only [routeOf_resolve, hro]
    unfold dropHit at hdr; unfold delayFault at hnone; simp only [resolve_active]
    simp only [hdr, Bool.false_eq_true, ↓reduceIte, hnone]
    simp only [hw, hp, settle_resolve, resolve_sig, hs]
    exact hfit
  | deliverErr _ _ hk hro hdr hnone hfail =>
    refine ⟨routeOf_fit.1.1 _ _ hro, ?_⟩
    rw [hk]; simp only [routeOf_resolve, hro]
    unfold dropHit at hdr; unfold delayFault at hnone; simp only [resolve_active]
    simp only [hdr, Bool.false_eq_true, ↓reduceIte, hnone]
    have hm : ∀ x : Cfg, (x.popE l.entry).machines = x.machines := fun _ => rfl
    cases hfail with
    | winners hw0 hw => simp only [hw, hw0]; exact ⟨rfl, by simp⟩
    | phase2 hw0 hw hp =>
      rw [hm] at hp
      simp only [hw, hp, hw0]; exact ⟨rfl, by simp⟩
    | settle hw hp hs hfit _ =>
      rw [hm] at hp
      simp only [settle_resolve, resolve_sig] at hs
      simp only [hw, hp, settle_resolve, resolve_sig, hs]; exact hfit
    | dup hw hp hs hfit _ _ _ =>
      rw [hm] at hp
      simp only [settle_resolve, resolve_sig] at hs
      simp only [hw, hp, settle_resolve, resolve_sig, hs]; exact hfit
  | routeErr _ _ hk hro hw0 =>
    refine ⟨routeOf_fit.1.2 _ hro, ?_⟩
    rw [hk]; simp only [routeOf_resolve, hro, hw0]; exact ⟨rfl, by simp⟩
  | worldOk _ _ hk hs hfit _ =>
    rw [nR_world hk, routeHoles_world hk]
    refine ⟨⟨by simp, by simp⟩, ?_⟩
    split
    · rename_i heq; exact absurd heq hk
    · simp only [List.drop_zero, worldStep_resolve, hs]; exact hfit
  | worldErr _ _ hk hs hfit _ =>
    rw [nR_world hk, routeHoles_world hk]
    refine ⟨⟨by simp, by simp⟩, ?_⟩
    split
    · rename_i heq; exact absurd heq hk
    · simp only [List.drop_zero, worldStep_resolve, hs]; exact hfit

/-- A system without resources or routes has no world draws. -/
theorem holesAt_nil_res {R : Sys} (h : R.resources = []) (mask : List Bool) (c : Cfg) (e : Entry) (rv : List Nat) :
    holesAt R mask c e rv = [] := by
  unfold holesAt
  split
  · split
    · simp only []
      split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · split
            · rfl
            · rw [settle_nil_res h]; rfl
    · rfl
  · rw [worldStep_nil_res h]; rfl

/-- A step of a system without resources or routes takes no world draws. -/
theorem wdraws_nil_of_nores {sys : Sys} (h : sys.resources = []) (hr : sys.routes = []) {mask : List Bool}
    {c : Cfg} {l : Label} {t : State} (hs : Step sys mask c l t) : l.wdraws = [] := by
  have hf := (Step.holes hs).2
  rw [Exec.holes, holesAt_nil_res (R := sys.resolve l.draws) h, nR_nil hr, List.drop_zero] at hf
  exact List.length_eq_zero_iff.mp hf.1

theorem Dist.support_nil_of_not_wf {d : Dist} (h : d.wf = false) : d.support = [] := by
  cases d with
  | fixed v => simp [Dist.wf] at h
  | choice vs => simp only [Dist.wf, Bool.not_eq_false', List.isEmpty_iff] at h; subst h; rfl
  | uniform lo hi =>
    simp only [Dist.wf, decide_eq_false_iff_not, Nat.not_le] at h
    simp only [Dist.support, List.range'_eq_nil_iff]; omega
  | table pts =>
    simp only [Dist.wf, Bool.not_eq_false', List.isEmpty_iff] at h; subst h; rfl

/-- The stream of a world draw site, from the book (format 2's `demand:{behavior}:{transition}:{effect}`). -/
def Book.siteName (b : Book) (site : Nat × Nat × Nat) : String :=
  ((b.sites.find? (·.1 == site)).map (·.2)).getD ""

/-- One world draw, as format 2's `sample` makes it: a fixed value without a draw; otherwise the
next draw of the site's stream when a seed is given, else the first value of the support. A
distribution with no value gives `0`. -/
def Exec.drawW (h : (Nat × Nat × Nat) × Dist) (b : Book) : Nat × Book :=
  match h.2 with
  | .fixed v => (v, b)
  | d =>
    if d.wf then
      match b.seed with
      | some sd => (d.sample sd (b.siteName h.1) (b.count (b.siteName h.1)), b.bump (b.siteName h.1))
      | none => (d.support.headD 0, b)
    else (0, b)

/-- The world draws of a draw program, and the book after them. -/
def Exec.drawsW : List ((Nat × Nat × Nat) × Dist) → Book → List Nat × Book
  | [], b => ([], b)
  | h :: hs, b =>
    let (v, b1) := Exec.drawW h b
    let (vs, b2) := Exec.drawsW hs b1
    (v :: vs, b2)

theorem Exec.drawW_mem (h : (Nat × Nat × Nat) × Dist) (b : Book) : (Exec.drawW h b).1 ∈ h.2.drawSupport := by
  obtain ⟨site, d⟩ := h
  have key : ∀ d : Dist, (∀ v, d ≠ .fixed v) →
      (if d.wf then (match b.seed with
        | some sd => (d.sample sd (b.siteName site) (b.count (b.siteName site)), b.bump (b.siteName site))
        | none => (d.support.headD 0, b)) else (0, b)).1 ∈ d.drawSupport := by
    intro d _
    split
    · rename_i hwf
      have hne := Dist.support_ne_nil hwf
      have hds : d.drawSupport = d.support := by
        unfold Dist.drawSupport; split
        · rename_i h0; exact absurd h0 hne
        · rfl
      rw [hds]
      split
      · exact sample_mem_support hwf _ _ _
      · exact Dist.headD_mem hwf
    · rename_i hwf
      have h0 := Dist.support_nil_of_not_wf (by simpa using hwf)
      simp [Dist.drawSupport, h0]
  cases d with
  | fixed v => simp [Exec.drawW, Dist.drawSupport, Dist.support]
  | choice vs => exact key _ (fun v h => by cases h)
  | uniform lo hi => exact key _ (fun v h => by cases h)
  | table pts => exact key _ (fun v h => by cases h)

theorem Exec.drawsW_fit : (hs : List ((Nat × Nat × Nat) × Dist)) → (b : Book) → DrawsFit (Exec.drawsW hs b).1 hs
  | [], b => ⟨rfl, by simp [Exec.drawsW]⟩
  | h :: hs, b => by
    have ih := Exec.drawsW_fit hs (Exec.drawW h b).2
    refine ⟨by simp [Exec.drawsW, ih.1], ?_⟩
    simp only [Exec.drawsW, List.zip_cons_cons, List.mem_cons]
    rintro p (rfl | hp)
    · exact Exec.drawW_mem h b
    · exact ih.2 p hp

/-- What a step records: its label. -/
structure Rec where
  label : Label

def Exec.label (r : Rec) : Label := r.label

inductive XResult where
  | idle
  | stopped
  | committed (r : Rec) (s : State) (b : Book)
  | failed (r : Rec)

/-- The label `Exec.step` delivers the entry `e` with: the route draws, the draws of the sampled
delays of the transitions that fire, then the world draws of the step's settling, each from its
stream, in format 2's order. -/
def Exec.labelOf (sys : Sys) (mask : List Bool) (c : Cfg) (e : Entry) (b : Book) : Label × Book :=
  let rv := Exec.drawsW (routeHoles sys c e) b
  let ds := Exec.drawsOf sys mask c e rv.1 rv.2
  let ws := Exec.drawsW (Exec.holes sys mask c e ds.1 rv.1) ds.2
  (⟨e, ds.1, rv.1 ++ ws.1⟩, ws.2)

/-- The executable step: delivers the head of the queue, drawing for the sampled delays of the
transitions that fire and for the step's settling, from their streams, as format 2 does. -/
def Exec.step (sys : Sys) : State → Book → XResult
  | .err _ _, _ => .idle
  | .run mask c, b =>
    match c.pending with
    | [] => .idle
    | e :: _ =>
      if sys.stopAt.all (fun s => decide (e.time ≤ s)) then
        match deliver sys mask c (Exec.labelOf sys mask c e b).1 with
        | some (.ok c') => .committed ⟨(Exec.labelOf sys mask c e b).1⟩ (.run mask c') (Exec.labelOf sys mask c e b).2
        | some (.error _) => .failed ⟨(Exec.labelOf sys mask c e b).1⟩
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

/-- On a sorted queue whose head is not after `stopAt`, the head can be delivered with world draws
that fit its draw program (the route draws, then the draws of the settling). -/
theorem deliverAt_head_some {sys : Sys} {mask : List Bool} {c : Cfg} {e : Entry} {rest : List Entry}
    {wds : List Nat} (hp : c.pending = e :: rest) (hs : c.Sorted)
    (hstop : sys.stopAt.all (fun s => decide (e.time ≤ s)) = true)
    (hr : DrawsFit (wds.take (sys.nR c e)) (routeHoles sys c e))
    (hw : DrawsFit (wds.drop (sys.nR c e)) (holesAt sys mask c e (wds.take (sys.nR c e)))) :
    deliverAt sys mask c 0 wds ≠ none := by
  have hmin : c.pending.all (fun x => decide (e.time ≤ x.time)) = true := by
    simp only [List.all_eq_true, decide_eq_true_eq]
    intro x hx
    have hs' : c.pending.Pairwise (fun a b => a.time ≤ b.time) := hs
    rw [hp] at hx hs'
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_refl _
    · exact (List.pairwise_cons.mp hs').1 x hx
  have hk : c.pending.idxOf? e = some 0 := by rw [hp]; simp [List.idxOf?_cons]
  have nil_of : ∀ {ws : List Nat}, DrawsFit ws [] → ws = [] := fun h => List.length_eq_zero_iff.mp h.1
  unfold deliverAt deliverWith
  rw [hp]
  simp only [List.getElem?_cons_zero]
  rw [← hp, hmin, hstop]
  simp only [Bool.and_self, ite_true]
  unfold holesAt at hw
  split
  · rename_i hkind
    rw [hkind] at hw
    simp only [] at hw
    rcases routeOf_fit.2 hr with ⟨c1, e1, hro⟩ | ⟨err, hro⟩
    · rw [hro] at hw ⊢
      simp only [] at hw
      simp only [if_true]
      obtain ⟨hfr, he1⟩ := routeOf_frame hro
      have hpop := Frame.pop_eq_popE hfr he1 hk
      unfold deliverEvent
      simp only [hpop]
      by_cases hdr : ((sys.active mask).any fun p => p.snd.hits [FKind.drop, FKind.lose] e1.event
          (c1.attemptsOf e1.event + 1) e1.time) = true
      · simp only [hdr, ↓reduceIte] at hw ⊢; rw [if_pos (nil_of hw)]; simp
      · simp only [hdr, Bool.false_eq_true, ↓reduceIte] at hw ⊢
        cases hf : List.find? (fun p => p.snd.hits [FKind.delay, FKind.retry] e1.event (c1.attemptsOf e1.event + 1)
            e1.time && !e1.done.contains p.fst) (sys.active mask) with
        | some p =>
          rw [hf] at hw; simp only [] at hw ⊢
          rw [if_pos (nil_of hw)]; simp
        | none =>
          rw [hf] at hw; simp only [] at hw ⊢
          cases hwin : winners sys (sys.active mask) (c1.popE e) e1 with
          | error err => rw [hwin] at hw; simp only [] at hw ⊢; rw [if_pos (nil_of hw)]; simp
          | ok ws =>
            rw [hwin] at hw; simp only [] at hw ⊢
            cases hph : phase2 sys (c1.popE e) e1 ws c1.machines with
            | error err => rw [hph] at hw; simp only [] at hw ⊢; rw [if_pos (nil_of hw)]; simp
            | ok r =>
              obtain ⟨ms, bs⟩ := r
              rw [hph] at hw; simp only [] at hw ⊢
              unfold settleFill
              rw [if_pos hw]; simp
    · rw [hro] at hw ⊢
      simp only [] at hw
      simp only [nil_of hw, and_self, if_true]; simp
  · rename_i hkind
    split at hw
    · rename_i h'; exact absurd h' hkind
    · unfold worldFill
      rw [nR_world hkind, List.drop_zero] at hw
      rw [if_pos hw]; simp

/-- The head of a sorted queue is delivered with any draws in the supports and world draws that fit
the step's draw program, unless `stopAt` forbids it. -/
theorem deliver_head_some {sys : Sys} {mask : List Bool} {c : Cfg} {e : Entry} {rest : List Entry}
    (ds : List Nat) (hd : DrawsOk sys ds) (wds : List Nat)
    (hr : DrawsFit (wds.take (sys.nR c e)) (routeHoles sys c e))
    (hw : DrawsFit (wds.drop (sys.nR c e)) (Exec.holes sys mask c e ds (wds.take (sys.nR c e))))
    (hp : c.pending = e :: rest) (hs : c.Sorted) (hstop : sys.stopAt.all (fun s => decide (e.time ≤ s)) = true) :
    deliver sys mask c ⟨e, ds, wds⟩ ≠ none := by
  unfold deliver
  simp only [hd, if_true]
  rw [hp]
  simp only [List.idxOf?_cons, BEq.rfl, if_true]
  exact deliverAt_head_some (sys := sys.resolve ds) hp hs hstop hr hw

theorem drawsW_length (hs : List ((Nat × Nat × Nat) × Dist)) (b : Book) : (Exec.drawsW hs b).1.length = hs.length :=
  (Exec.drawsW_fit hs b).1

theorem Exec.labelOf_ok {sys : Sys} (hwf : sys.WF) (mask : List Bool) (c : Cfg) (e : Entry) (b : Book) :
    DrawsOk sys (Exec.labelOf sys mask c e b).1.draws ∧
      DrawsFit ((Exec.labelOf sys mask c e b).1.wdraws.take (sys.nR c e)) (routeHoles sys c e) ∧
      DrawsFit ((Exec.labelOf sys mask c e b).1.wdraws.drop (sys.nR c e))
        (Exec.holes sys mask c e (Exec.labelOf sys mask c e b).1.draws
          ((Exec.labelOf sys mask c e b).1.wdraws.take (sys.nR c e))) := by
  have hl : (Exec.drawsW (routeHoles sys c e) b).1.length = sys.nR c e := drawsW_length _ _
  simp only [Exec.labelOf]
  rw [← hl, List.take_left, List.drop_left]
  exact ⟨Exec.drawsOf_ok hwf mask c e _ _, Exec.drawsW_fit _ _, Exec.drawsW_fit _ _⟩

theorem Exec.labelOf_entry (sys : Sys) (mask : List Bool) (c : Cfg) (e : Entry) (b : Book) :
    (Exec.labelOf sys mask c e b).1 = ⟨e, (Exec.labelOf sys mask c e b).1.draws,
      (Exec.labelOf sys mask c e b).1.wdraws⟩ := rfl

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
        · rename_i hnone
          obtain ⟨h1, h2⟩ := Exec.labelOf_ok hwf m c e b
          rw [Exec.labelOf_entry] at hnone
          exact absurd hnone (deliver_head_some _ h1 _ h2.1 h2.2 hp hs ‹_›)
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
      · rename_i hnone
        obtain ⟨h1, h2⟩ := Exec.labelOf_ok hwf m c e b
        rw [Exec.labelOf_entry] at hnone
        exact absurd hnone (deliver_head_some _ h1 _ h2.1 h2.2 hp hs ‹_›)
    · cases h

/-! ### Runs -/

/-- How a run ended: `quiescent` when the scheduler had nothing left to do (`Exec.step` returned
`idle` or `stopped`, or the run reached the error state), so the last state is deadlocked
(`run_quiescent_deadlocked`, from `idle_deadlocked` and `stopped_deadlocked`); `boundHit` when the step
bound was reached with a step still possible; `truncated` when a search's state cap cut it off
(`Gen.Reason.cap`; the explorer's counterpart of `boundHit` is `Gen.Reason.bound`). A run that is not
quiescent says nothing about what happens after its last state. -/
inductive RunEnd where
  | quiescent
  | boundHit
  | truncated
  deriving DecidableEq, Repr

/-- A run: the states the scheduler reaches, the records of the steps between them, and how it
ended. -/
structure Run where
  states : List State
  recs : List Rec
  ending : RunEnd := .quiescent

/-- How the scheduler would continue from `s`: quiescent if it has nothing to do. -/
def Exec.endAt (sys : Sys) (s : State) (b : Book) : RunEnd :=
  match Exec.step sys s b with
  | .committed _ _ _ | .failed _ => .boundHit
  | _ => .quiescent

/-- The run from `s`, at most `fuel` steps: `s` first, then each state the scheduler reaches, the
error state included. -/
def Exec.run (sys : Sys) : Nat → State → Book → Run
  | 0, s, b => ⟨[s], [], Exec.endAt sys s b⟩
  | fuel + 1, s, b =>
    match Exec.step sys s b with
    | .committed r s' b' =>
      let rest := Exec.run sys fuel s' b'
      ⟨s :: rest.states, r :: rest.recs, rest.ending⟩
    | .failed r => ⟨[s, .err s.mask s.cfg], [r], .quiescent⟩
    | _ => ⟨[s], [], .quiescent⟩

/-- **A quiescent run ends in a deadlocked state**: the relation has no step from its last state. -/
theorem run_quiescent_deadlocked {sys : Sys} (hwf : sys.WF) : (fuel : Nat) → {s : State} → (b : Book) →
    (Sys.lts sys).Reach s → (Exec.run sys fuel s b).ending = .quiescent →
      ∀ t, (Exec.run sys fuel s b).states.getLast? = some t → (Sys.lts sys).Deadlocked t
  | 0, s, b, hr, he, t, ht => by
    simp only [Exec.run, List.getLast?_singleton, Option.some.injEq] at ht he
    subst ht
    have hs := sorted_invariant sys hwf s hr
    simp only [Exec.endAt] at he
    cases h : Exec.step sys s b with
    | idle => exact Exec.idle_deadlocked hwf hs h
    | stopped => exact Exec.stopped_deadlocked hs h
    | committed => simp [h] at he
    | failed => simp [h] at he
  | fuel + 1, s, b, hr, he, t, ht => by
    have hs := sorted_invariant sys hwf s hr
    cases h : Exec.step sys s b with
    | idle =>
      simp only [Exec.run, h, List.getLast?_singleton, Option.some.injEq] at ht
      subst ht; exact Exec.idle_deadlocked hwf hs h
    | stopped =>
      simp only [Exec.run, h, List.getLast?_singleton, Option.some.injEq] at ht
      subst ht; exact Exec.stopped_deadlocked hs h
    | failed r =>
      simp only [Exec.run, h, List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at ht
      subst ht
      exact err_deadlocked sys _ _
    | committed r s' b' =>
      simp only [Exec.run, h] at he ht
      have hr' : (Sys.lts sys).Reach s' := .step hr (Exec.step_sound hwf hs h)
      have hne : (Exec.run sys fuel s' b').states ≠ [] := by
        cases fuel with
        | zero => simp [Exec.run]
        | succ f => simp only [Exec.run]; split <;> simp
      rw [List.getLast?_cons_of_ne_nil hne] at ht
      exact run_quiescent_deadlocked hwf fuel b' hr' he t ht

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

/-- Every vector of values, one of each list. -/
def choices : List (List Nat) → List (List Nat)
  | [] => [[]]
  | s :: ss => s.flatMap (fun v => (choices ss).map (v :: ·))

theorem mem_choices : (S : List (List Nat)) → (ds : List Nat) → ds.length = S.length →
    (∀ p ∈ ds.zip S, p.1 ∈ p.2) → ds ∈ choices S
  | [], [], _, _ => by simp [choices]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | s :: S, v :: ds, hl, hz => by
    simp only [choices, List.mem_flatMap, List.mem_map]
    refine ⟨v, hz (v, s) List.mem_cons_self, ds, ?_, rfl⟩
    exact mem_choices S ds (by simpa using hl) (fun p hp => hz p (List.mem_cons_of_mem _ hp))

/-- Every vector of draws: one value of each support. -/
def drawVectors (D : List Dist) : List (List Nat) := choices (D.map Dist.support)

/-- Every vector of draws with each support cut to its first `cap` values. -/
def drawVectorsUpTo (cap : Nat) (D : List Dist) : List (List Nat) := choices (D.map fun d => d.support.take cap)

/-- Every vector of world draws of a draw program. -/
def worldVectors (hs : List ((Nat × Nat × Nat) × Dist)) : List (List Nat) :=
  choices (hs.map fun h => h.2.drawSupport)

/-- Every vector of world draws with each set of values cut to its first `cap`. -/
def worldVectorsUpTo (cap : Nat) (hs : List ((Nat × Nat × Nat) × Dist)) : List (List Nat) :=
  choices (hs.map fun h => h.2.drawSupport.take cap)

theorem mem_drawVectors (D : List Dist) (ds : List Nat) (hl : ds.length = D.length)
    (hz : ∀ p ∈ ds.zip D, p.1 ∈ p.2.support) : ds ∈ drawVectors D := by
  refine mem_choices _ ds (by simpa using hl) (fun p hp => ?_)
  rw [List.zip_map_right] at hp
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hp
  exact hz _ hab

theorem mem_worldVectors {hs : List ((Nat × Nat × Nat) × Dist)} {ds : List Nat} (h : DrawsFit ds hs) :
    ds ∈ worldVectors hs := by
  refine mem_choices _ ds (by simpa using h.1) (fun p hp => ?_)
  rw [List.zip_map_right] at hp
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hp
  exact h.2 _ hab

theorem drawVectorsUpTo_eq (cap : Nat) (D : List Dist) (h : ∀ d ∈ D, d.support.length ≤ cap) :
    drawVectorsUpTo cap D = drawVectors D := by
  unfold drawVectorsUpTo drawVectors
  congr 1
  apply List.map_congr_left
  intro d hd
  exact List.take_of_length_le (h d hd)

/-- The successors of a state with every support cut to its first `cap` values. -/
def Exec.successorsUpTo (cap : Nat) (sys : Sys) : State → List (Label × State)
  | .run mask c => c.pending.flatMap (fun e => (drawVectorsUpTo cap sys.dists).flatMap (fun ds =>
      (worldVectorsUpTo cap (routeHoles sys c e)).flatMap (fun rv =>
      (worldVectorsUpTo cap (Exec.holes sys mask c e ds rv)).filterMap
        (fun wv => (deliver sys mask c ⟨e, ds, rv ++ wv⟩).map (fun r => (⟨e, ds, rv ++ wv⟩, outcome mask c r))))))
  | .err _ _ => []

/-- The successors of a state: every label (delivered entry, draws, route draws and world draws). -/
def Exec.successors (sys : Sys) : State → List (Label × State)
  | .run mask c => c.pending.flatMap (fun e => (drawVectors sys.dists).flatMap (fun ds =>
      (worldVectors (routeHoles sys c e)).flatMap (fun rv =>
      (worldVectors (Exec.holes sys mask c e ds rv)).filterMap
        (fun wv => (deliver sys mask c ⟨e, ds, rv ++ wv⟩).map (fun r => (⟨e, ds, rv ++ wv⟩, outcome mask c r))))))
  | .err _ _ => []

theorem worldVectorsUpTo_eq {cap : Nat} {hs : List ((Nat × Nat × Nat) × Dist)}
    (h : ∀ p ∈ hs, p.2.drawSupport.length ≤ cap) : worldVectorsUpTo cap hs = worldVectors hs := by
  unfold worldVectorsUpTo worldVectors
  congr 1
  apply List.map_congr_left
  intro p hp
  exact List.take_of_length_le (h p hp)

/-- **When no support is cut, the capped successors are all of them.** -/
theorem successorsUpTo_eq {cap : Nat} {sys : Sys} (s : State)
    (h : ∀ d ∈ sys.dists, d.support.length ≤ cap)
    (hr : ∀ (c : Cfg) (e : Entry), ∀ p ∈ routeHoles sys c e, p.2.drawSupport.length ≤ cap)
    (hw : ∀ (mask : List Bool) (c : Cfg) (e : Entry) (ds rv : List Nat),
      ∀ p ∈ Exec.holes sys mask c e ds rv, p.2.drawSupport.length ≤ cap) :
    Exec.successorsUpTo cap sys s = Exec.successors sys s := by
  cases s with
  | err => rfl
  | run m c =>
    simp only [Exec.successorsUpTo, Exec.successors, drawVectorsUpTo_eq cap _ h]
    congr 1; funext e; congr 1; funext ds
    rw [worldVectorsUpTo_eq (hr c e)]
    congr 1; funext rv
    rw [worldVectorsUpTo_eq (hw m c e ds rv)]

theorem successors_complete {sys : Sys} {s t : State} {l : Label}
    (h : (Sys.lts sys).step s l t) : (l, t) ∈ Exec.successors sys s := by
  cases s with
  | err m c => exact absurd h id
  | run m c =>
    have h' : Step sys m c l t := h
    obtain ⟨hd, hr⟩ := Step.ready h'
    have hfit := Step.holes h'
    have hdel := (deliver_eq_step (sys := sys) (mask := m) (c := c) (l := l) (t := t)).mpr h'
    have hl : (⟨l.entry, l.draws, l.wdraws.take (sys.nR c l.entry) ++ l.wdraws.drop (sys.nR c l.entry)⟩ : Label) = l := by
      rw [List.take_append_drop]
    simp only [Exec.successors, List.mem_flatMap, List.mem_filterMap]
    refine ⟨l.entry, hr.1, l.draws, mem_drawVectors _ _ hd.1 hd.2, _, mem_worldVectors hfit.1, _,
      mem_worldVectors hfit.2, ?_⟩
    rw [hl]
    cases hl' : deliver sys m c l with
    | none => rw [hl'] at hdel; cases hdel
    | some r =>
      rw [hl'] at hdel
      simp only [Option.map_some, Option.some.injEq] at hdel ⊢
      rw [hdel]

theorem successors_sound {sys : Sys} {s t : State} {l : Label}
    (h : (l, t) ∈ Exec.successors sys s) : (Sys.lts sys).step s l t := by
  cases s with
  | err m c => simp [Exec.successors] at h
  | run m c =>
    simp only [Exec.successors, List.mem_flatMap, List.mem_filterMap] at h
    obtain ⟨e, _, ds, _, rv, _, wv, _, hk⟩ := h
    cases hd : deliver sys m c ⟨e, ds, rv ++ wv⟩ with
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

/-- info: 'Exegra.Core.Behav.run_quiescent_deadlocked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.run_quiescent_deadlocked
