import Exegra.Core.Behav
/-
Resources in the behaviour calculus (WG-5683, criterion 1): `Resource.lean`'s held-at-most-limit
theorem restated over the calculus, with the resource faults.
* `grant_within_limits`: every grant settling makes leaves the held units of the resource within
  the capacity and the class limits in effect when it is granted (the resource as the acting faults
  leave it, `effDecl`, at the capacity they give it, `effCap`; `settleOne` settles from that
  capacity).
* `heldOk_invariant`: for every system whose faults never lower a capacity or class limit
  (`Sys.NoLowering`: no edge of a fault window, from any acting faults, lowers the capacity or a
  class limit of a resource) and whose initial world holds no units, `WorldOk` (every resource's held
  units within the capacity and class limits in effect) is an invariant of `Sys.lts`. The hypothesis
  is needed: a windowed `set-capacity` or `set-class-limit` fault lowers a limit without revoking
  held units (Format2.lean `effDecl`), so the unrestricted invariant is false.
-/
namespace Exegra.Core.Behav
open Exegra.Core.LTS

/-- Every resource of the world holds within the capacity and class limits in effect (under the
resource faults acting in the world). -/
def WorldOk (sys : Sys) (w : World) : Prop :=
  ∀ (ri : Nat) (d : Res.ResourceDecl) (s : RSt), sys.resources[ri]? = some d → w.res[ri]? = some s →
    Res.HeldOk (effDecl (sys.acting w) ri d) { s with capacity := effCap (sys.acting w) ri d }

/-- **Faults never lower a capacity or class limit**: no edge of a fault window (the start or the
end of fault `fi`), from any acting faults, lowers the capacity or a class limit of a resource. -/
def Sys.NoLowering (sys : Sys) : Prop :=
  ∀ (w : World) (fi : Nat) (on : Bool) (ri : Nat) (d : Res.ResourceDecl), sys.resources[ri]? = some d →
    effCap (sys.acting w) ri d ≤
      effCap (sys.acting { w with active := edgeActive sys.faults.length fi on w.active }) ri d ∧
    ∀ c l', (effDecl (sys.acting { w with active := edgeActive sys.faults.length fi on w.active }) ri d).limitOf c
        = some l' → ∃ l, (effDecl (sys.acting w) ri d).limitOf c = some l ∧ l ≤ l'

/-- Setting a resource of a world that holds within its limits to a state that does keeps it so. -/
theorem WorldOk.set {sys : Sys} {w : World} (h : WorldOk sys w) {ri : Nat} {d : Res.ResourceDecl}
    (hd : sys.resources[ri]? = some d) {s' : RSt}
    (hs' : Res.HeldOk (effDecl (sys.acting w) ri d) { s' with capacity := effCap (sys.acting w) ri d })
    (res' : List RSt)
    (hres : ∀ j, res'[j]? = if j = ri ∧ ri < w.res.length then some s' else w.res[j]?) (k : Nat) :
    WorldOk sys { w with res := res', nextReq := k } := by
  intro rj dj sj hdj hsj
  simp only [hres] at hsj
  split at hsj
  · rename_i hj
    obtain ⟨rfl, _⟩ := hj
    rw [hd] at hdj; cases hdj
    cases hsj; exact hs'
  · exact h _ _ _ hdj hsj

theorem getElem?_set_eq (l : List RSt) (i : Nat) (x : RSt) (j : Nat) :
    (l.set i x)[j]? = if j = i ∧ i < l.length then some x else l[j]? := by
  rw [List.getElem?_set]
  by_cases h1 : i = j
  · subst h1; by_cases h2 : i < l.length <;> simp_all
  · have : ¬ (j = i ∧ i < l.length) := fun h => h1 h.1.symm
    simp [h1, this]

theorem releasesOf_heldOk {d : Res.ResourceDecl} {ri : Nat} :
    (rels : List (Nat × Nat × Nat)) → (s : RSt) → (acts : List Act) → Res.HeldOk d s →
    Res.HeldOk d (releasesOf ri rels s acts).1 ∧ (releasesOf ri rels s acts).1.capacity = s.capacity
  | [], s, acts, h => by simpa [releasesOf] using h
  | (m, c, n) :: rest, s, acts, h => by
    simp only [releasesOf]
    split
    · exact ⟨h, rfl⟩
    · exact releasesOf_heldOk rest _ _ (Res.consume_ok m c n h)

theorem grantLoop_capacity (d : Res.ResourceDecl) : (n : Nat) → (s : RSt) → (outs : List (Res.Out Nat RInfo)) →
    (Res.grantLoop d n s outs).1.capacity = s.capacity
  | 0, s, outs => rfl
  | n + 1, s, outs => by
    simp only [Res.grantLoop]
    split
    · rfl
    · exact grantLoop_capacity d n _ _

theorem enqueuesOf_holds {now ri : Nat} {d : Res.ResourceDecl} :
    (reqs : List (Nat × Nat × Nat × Res.ReqKind × RInfo)) → (s : RSt) → (k : Nat) → (acts : List Act) →
    (enqueuesOf now ri d reqs s k acts).1.holds = s.holds ∧
      (enqueuesOf now ri d reqs s k acts).1.capacity = s.capacity
  | [], s, k, acts => by simp [enqueuesOf]
  | (m, c, n, kind, info) :: rest, s, k, acts => by
    simp only [enqueuesOf]
    split
    · split
      · exact ⟨rfl, rfl⟩
      · exact enqueuesOf_holds rest _ _ _
    · exact enqueuesOf_holds rest _ _ _

theorem heldOk_of_holds {d : Res.ResourceDecl} {s s' : RSt} (h1 : s'.holds = s.holds)
    (h2 : s'.capacity = s.capacity) (h : Res.HeldOk d s) : Res.HeldOk d s' := by
  obtain ⟨ha, hc⟩ := h
  exact ⟨by rw [h1, h2]; exact ha, fun c l hl => by rw [h1]; exact hc c l hl⟩

theorem heldOk_of_holds' {d : Res.ResourceDecl} {s s' : RSt} (h : Res.HeldOk d s) (h1 : s'.holds = s.holds)
    (h2 : s'.capacity = s.capacity) : Res.HeldOk d s' := heldOk_of_holds h1 h2 h

/-- **Every grant stays within the limits in effect when it is granted**: settling one resource,
from holdings within the capacity and class limits in effect (the resource as the acting faults `fs`
leave it, `effDecl`), leaves them within those limits; each grant of the grant loop is a `grantOne`
of a request that fits (`Res.grantOne_ok`, `Res.pick_fits`). -/
theorem grant_within_limits {fs : List Fault} {now ri : Nat} {d : Res.ResourceDecl} {w : World}
    {s0 : RSt} (hok : Res.HeldOk (effDecl fs ri d) s0) (rels : List (Nat × Nat × Nat))
    (reqs : List (Nat × Nat × Nat × Res.ReqKind × RInfo)) :
    Res.HeldOk (effDecl fs ri d) (Res.grantLoop (effDecl fs ri d)
      (enqueuesOf now ri d reqs (releasesOf ri rels s0 []).1 w.nextReq (releasesOf ri rels s0 []).2.1).1.waiting.length
      (enqueuesOf now ri d reqs (releasesOf ri rels s0 []).1 w.nextReq (releasesOf ri rels s0 []).2.1).1 []).1 := by
  have h1 := (releasesOf_heldOk (d := effDecl fs ri d) (ri := ri) rels s0 [] hok).1
  have h2 := enqueuesOf_holds (now := now) (ri := ri) (d := d) reqs (releasesOf ri rels s0 []).1 w.nextReq
    (releasesOf ri rels s0 []).2.1
  exact Res.grantLoop_ok _ _ _ [] (heldOk_of_holds h2.1 h2.2 h1)

theorem settleOne_active {fs : List Fault} {now ri : Nat} {d : Res.ResourceDecl} {ops : List (Nat × WOp)}
    {w : World} : (settleOne fs now ri d ops w).1.active = w.active := by
  unfold settleOne
  split
  · rfl
  · simp only []
    split
    · rfl
    · split <;> rfl

theorem settleOne_worldOk {sys : Sys} {now ri : Nat} {d : Res.ResourceDecl} {ops : List (Nat × WOp)}
    {w : World} (hd : sys.resources[ri]? = some d) (h : WorldOk sys w) :
    WorldOk sys (settleOne (sys.acting w) now ri d ops w).1 := by
  unfold settleOne
  cases hs : w.res[ri]? with
  | none => exact h
  | some s =>
    simp only []
    split
    · exact h
    · split
      · exact h
      · refine WorldOk.set h hd ?_ _ (getElem?_set_eq _ _ _) _
        have hok := h _ _ _ hd hs
        refine heldOk_of_holds' (grant_within_limits (w := w) (now := now) hok _ _) rfl ?_
        rw [grantLoop_capacity, (enqueuesOf_holds _ _ _ _).2, (releasesOf_heldOk _ _ [] hok).2]

theorem mem_zip_range' {α : Type} : (l : List α) → (k i : Nat) → (d : α) →
    (i, d) ∈ (List.range' k l.length).zip l → k ≤ i ∧ l[i - k]? = some d
  | [], k, i, d, h => by simp at h
  | x :: xs, k, i, d, h => by
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · simp
    · obtain ⟨h1, h2⟩ := mem_zip_range' xs (k + 1) i d h
      refine ⟨by omega, ?_⟩
      have : i - k = (i - (k + 1)) + 1 := by omega
      rw [this]; simpa using h2

theorem settleAll_worldOk {sys : Sys} {now : Nat} {ops : List (Nat × WOp)} {touched : List Nat}
    {fs : List Fault} : (rs : List (Nat × Res.ResourceDecl)) → (∀ p ∈ rs, sys.resources[p.1]? = some p.2) →
    (w : World) → (acts : List Act) → fs = sys.acting w → WorldOk sys w →
    WorldOk sys (settleAll fs now ops touched rs w acts).1 ∧ (settleAll fs now ops touched rs w acts).1.active = w.active
  | [], _, w, acts, _, h => by simpa [settleAll] using h
  | (ri, d) :: rest, hrs, w, acts, hfs, h => by
    have hd := hrs (ri, d) List.mem_cons_self
    have hrest := fun p hp => hrs p (List.mem_cons_of_mem _ hp)
    have h1 : WorldOk sys (settleOne fs now ri d ops w).1 := hfs ▸ settleOne_worldOk hd h
    have ha : (settleOne fs now ri d ops w).1.active = w.active := settleOne_active
    have hfs' : fs = sys.acting (settleOne fs now ri d ops w).1 := by
      have : sys.acting (settleOne fs now ri d ops w).1 = sys.acting w := by unfold Sys.acting; rw [ha]
      rw [this]; exact hfs
    simp only [settleAll]
    split
    · split
      · exact ⟨h1, ha⟩
      · obtain ⟨h2, h3⟩ := settleAll_worldOk rest hrest _ _ hfs' h1
        exact ⟨h2, h3.trans ha⟩
    · exact settleAll_worldOk rest hrest w acts hfs h

theorem settle_worldOk (sys : Sys) (now : Nat) (ops : List (Nat × WOp)) (touched : List Nat) {w : World}
    (h : WorldOk sys w) : WorldOk sys (settle sys now ops touched w).1 := by
  unfold settle
  refine (settleAll_worldOk _ (fun p hp => ?_) w [] rfl h).1
  have := mem_zip_range' sys.resources 0 p.1 p.2 (by rw [← List.range_eq_range']; exact hp)
  simpa using this.2

/-- The edge of a fault window keeps a world within the limits in effect when faults never lower
a capacity or class limit. -/
theorem WorldOk.edge {sys : Sys} (hlow : sys.NoLowering) {w : World} (h : WorldOk sys w) (fi : Nat)
    (on : Bool) : WorldOk sys { w with active := edgeActive sys.faults.length fi on w.active } := by
  intro ri d s hd hs
  obtain ⟨hcap, hlim⟩ := hlow w fi on ri d hd
  obtain ⟨ha, hc⟩ := h ri d s hd hs
  refine ⟨Nat.le_trans ha hcap, fun c l' hl' => ?_⟩
  obtain ⟨l, hl, hle⟩ := hlim c l' hl'
  exact Nat.le_trans (hc c l hl) hle

/-- The link queues do not bear on the resources' limits. -/
theorem WorldOk.sameRes {sys : Sys} {w w' : World} (h : WorldOk sys w) (hs : w.SameRes w') : WorldOk sys w' := by
  have ha : sys.acting w' = sys.acting w := by unfold Sys.acting; rw [hs.2.2]
  intro ri d s hd hw
  rw [ha]; rw [hs.1] at hw; exact h ri d s hd hw

theorem startOf_sameRes (L : Link) (li : Nat) (k : Option Nat) (m : Msg) (now : Nat) (w : World) :
    w.SameRes (startOf L li k m now w).1 := by
  unfold startOf; simp only []; split
  · exact World.SameRes.refl _
  · exact World.setLq_sameRes _ _ _ _

theorem sendOne_sameRes (L : Link) (li : Nat) (fan : Bool) (k : Option Nat) (m : Msg) (now : Nat) (w : World) :
    w.SameRes (sendOne L li fan k m now w).1 := by
  unfold sendOne; split
  · exact World.SameRes.refl _
  · simp only []; split
    · exact startOf_sameRes _ _ _ _ _ _
    · exact World.setLq_sameRes _ _ _ _

theorem sendTo_sameRes (L : Link) (li : Nat) (fan : Bool) (now : Nat) (m : Msg) :
    (rs : List (Option Nat × Option Nat)) → (w : World) → (acts : List Act) →
    w.SameRes (sendTo L li fan now m rs w acts).1
  | [], w, acts => World.SameRes.refl _
  | (k, tg) :: rest, w, acts => by
    simp only [sendTo]
    split
    · exact sendOne_sameRes _ _ _ _ _ _ _
    · exact (sendOne_sameRes _ _ _ _ _ _ _).trans (sendTo_sameRes L li fan now m rest _ _)

theorem outActs_sameRes (links : List Link) (now : Nat) (ms : List MState) :
    (outs : List Entry) → (w : World) → (acts : List Act) → w.SameRes (outActs links now ms outs w acts).1
  | [], w, acts => World.SameRes.refl _
  | x :: xs, w, acts => by
    simp only [outActs]
    split
    · exact outActs_sameRes links now ms xs _ _
    · split
      · exact outActs_sameRes links now ms xs _ _
      · split
        · exact sendTo_sameRes _ _ _ _ _ _ _ _
        · exact (sendTo_sameRes _ _ _ _ _ _ _ _).trans (outActs_sameRes links now ms xs _ _)
    · exact outActs_sameRes links now ms xs _ _

theorem settleOut_worldOk (sys : Sys) (now : Nat) (ms : List MState) (outs : List Entry) {w : World}
    (h : WorldOk sys w) : WorldOk sys (settleOut sys now ms outs w).1 := by
  unfold settleOut
  exact settle_worldOk _ _ _ _ (h.sameRes (outActs_sameRes _ _ _ _ _ _))

theorem worldStep_worldOk (sys : Sys) (hlow : sys.NoLowering) (c0 : Cfg) (e : Entry) (h : WorldOk sys c0.world) :
    WorldOk sys (worldStep sys c0 e).1 := by
  unfold worldStep
  cases hk : e.kind with
  | event => exact h
  | op o => exact h
  | serviceDone ri r waited served =>
    simp only []
    cases hd : sys.resources[ri]? with
    | none => exact h
    | some d =>
      cases hs : c0.world.res[ri]? with
      | none => exact h
      | some s =>
        simp only []
        exact settle_worldOk _ _ _ _ (WorldOk.set h hd (Res.endService_ok r.id (h _ _ _ hd hs)) _
          (getElem?_set_eq _ _ _) _)
  | waitTimeout ri rid =>
    simp only []
    cases hd : sys.resources[ri]? with
    | none => exact h
    | some d =>
      cases hs : c0.world.res[ri]? with
      | none => exact h
      | some s =>
        simp only []
        cases s.waiting.find? (·.id == rid) with
        | none => exact h
        | some r =>
          simp only []
          refine settle_worldOk _ _ _ _ (WorldOk.set h hd ?_ _ (getElem?_set_eq _ _ _) _)
          exact heldOk_of_holds rfl rfl (h _ _ s hd hs)
  | faultEdge fi on =>
    simp only []
    cases sys.faults[fi]? with
    | none => exact h
    | some f =>
      simp only []
      split
      · cases sys.resources[f.res]? with
        | none => exact WorldOk.edge hlow h fi on
        | some _ => exact settle_worldOk _ _ _ _ (WorldOk.edge hlow h fi on)
      · exact h
  | send _ _ _ => exact h
  | linkDone li k =>
    simp only []
    cases sys.links[li]? with
    | none => exact h
    | some L =>
      simp only []
      cases (c0.world.lq li k).inTransfer with
      | none => exact h
      | some m =>
        simp only []
        cases (c0.world.lq li k).waiting with
        | nil => exact h.sameRes (World.setLq_sameRes _ _ _ _)
        | cons m' rest => exact (h.sameRes (World.setLq_sameRes _ _ _ _)).sameRes (startOf_sameRes _ _ _ _ _ _)

theorem Dup.world {act : List (Nat × Fault)} {e : Entry} {att : Nat} {c1 c2 : Cfg}
    (h : Dup act e att c1 c2) : c2.world = c1.world := by
  cases h <;> rfl

/-- The initial world under any mask holds no units when the system's initial world holds none. -/
theorem initWorld_empty (sys : Sys) (h0 : ∀ s ∈ sys.init.world.res, s.holds = []) (mask : List Bool) :
    ∀ s ∈ (sys.initCfg mask).world.res, s.holds = [] := by
  simp only [Sys.initCfg]
  suffices ∀ (act : List (Nat × Fault)) (w : World), (∀ s ∈ w.res, s.holds = []) →
      ∀ s ∈ (act.foldl sys.initWorldStep w).res, s.holds = [] from this _ _ h0
  intro act
  induction act with
  | nil => intro w hw; exact hw
  | cons p ps ih =>
    intro w hw
    refine ih _ ?_
    unfold Sys.initWorldStep
    by_cases h1 : (sys.edgeOk p.2 && p.2.window.isNone) = true
    · simp only [h1, ↓reduceIte]
      by_cases h2 : (p.2.kind == .setCapacity) = true
      · simp only [h2, ↓reduceIte]
        cases hs' : w.res[p.2.res]? with
        | none => exact hw
        | some s' =>
          intro x hx
          rcases List.mem_or_eq_of_mem_set hx with hx | rfl
          · exact hw x hx
          · exact hw s' (List.mem_of_getElem? hs')
      · simp only [h2]; exact hw
    · simp only [h1]; exact hw

/-- **Held units stay within capacity and class limits** (the task's criterion 1, `Resource.lean`'s
held-at-most-limit theorem over the calculus): "for every system whose faults never lower a
capacity or class limit, `HeldOk` is an invariant of `Sys.lts`" — every resource of every reachable
state holds within the capacity and class limits in effect, for a system whose initial states do
(`heldOk_invariant_of_empty`: for instance, one whose initial world holds no units). -/
theorem heldOk_invariant (sys : Sys) (hlow : sys.NoLowering)
    (h0 : ∀ s, (Sys.lts sys).init s → WorldOk sys s.cfg.world) :
    (Sys.lts sys).Invariant (fun s => WorldOk sys s.cfg.world) := by
  refine safe_of_inductive (I := fun s => WorldOk sys s.cfg.world) ⟨h0, ?_⟩ (fun _ h => h)
  · intro s l t hs hst
    cases s with
    | err m c => exact absurd hst id
    | run m c =>
      have hst' : Step sys m c l t := hst
      cases hst' with
      | drop _ _ _ hro =>
        have hw1 : WorldOk sys _ := (routeOf_frame hro).1.world.symm ▸ hs
        exact hw1
      | delay _ _ _ hro =>
        have hw1 : WorldOk sys _ := (routeOf_frame hro).1.world.symm ▸ hs
        exact hw1
      | delayTimeErr => exact hs
      | @deliverOk c1 e1 ws ms bs w acts c2 c'' _ _ _ hro _ _ _ _ hset _ hfill hdup =>
        simp only [State.cfg]
        rw [Dup.world hdup]
        have hw1 : WorldOk sys c1.world := (routeOf_frame hro).1.world.symm ▸ hs
        have := settleOut_worldOk sys ((c1.popE l.entry).commit sys.sig.machines ms bs).time
          ((c1.popE l.entry).commit sys.sig.machines ms bs).machines (inMachineOrder sys.sig.machines bs)
          (w := ((c1.popE l.entry).commit sys.sig.machines ms bs).world) hw1
        rw [hset] at this
        exact this.sameRes (fill_frame hfill).2.2.2.2
      | deliverErr => exact hs
      | routeErr => exact hs
      | worldOk _ _ _ hws _ hfill =>
        simp only [State.cfg]
        have := worldStep_worldOk sys hlow (c.popW l.entry) l.entry hs
        rw [hws] at this
        exact this.sameRes (fill_frame hfill).2.2.2.2
      | worldErr => exact hs

/-- `heldOk_invariant` for a system whose initial world holds no units (as `Exegra.V2.Elab.elab`
builds it): every initial state then holds within its limits. -/
theorem heldOk_invariant_of_empty (sys : Sys) (hlow : sys.NoLowering)
    (h0 : ∀ s ∈ sys.init.world.res, s.holds = []) :
    (Sys.lts sys).Invariant (fun s => WorldOk sys s.cfg.world) := by
  refine heldOk_invariant sys hlow (fun s hs => ?_)
  obtain ⟨mask, _, rfl⟩ := hs
  intro ri d x _ hx
  have hh := initWorld_empty sys h0 mask x (List.mem_of_getElem? hx)
  refine ⟨?_, fun c l _ => ?_⟩ <;> simp [hh, Res.heldAll, Res.heldC, Res.sumUnits]

end Exegra.Core.Behav

/-- info: 'Exegra.Core.Behav.grant_within_limits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.grant_within_limits

/-- info: 'Exegra.Core.Behav.heldOk_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.heldOk_invariant

/-- info: 'Exegra.Core.Behav.heldOk_invariant_of_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.heldOk_invariant_of_empty
