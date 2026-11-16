import Std.Data.HashSet

/-
A generic breadth-first search of a finite transition system, and its soundness.

`Exegra.Explore` searches the states of a scenario for a violated invariant. Temporal claims
need the same search over a product of that state with a small monitor state, so the search is
stated here once, over any node type `N` with decidable equality and a hash.

A system `Sys N` has initial nodes, and a successor of a node for each pick `k < width n` for
which `next n k` is `some`. `search S ok bound cap` visits nodes breadth first, deduplicated by
a hash set, and checks `ok` on every node it discovers:
* `holds n`: every node reachable in the system at all (not only within the bound) satisfies
  `ok`; the search ended with an empty frontier, so the visited set is closed under successors
  (`search_sound`);
* `counterexample p`: `p.root` is an initial node and replaying `p.picks` from it reaches a node
  where `ok` is false, in at most `bound` steps (`search_counterexample_real`);
* `incomplete n`: the visited set reached `cap`, or the frontier was not empty after `bound`
  layers. Nothing is claimed.
-/

namespace Exegra.Gen

set_option linter.unusedSectionVars false

variable {N : Type} [DecidableEq N] [Hashable N]

structure Sys (N : Type) where
  init : List N
  width : N → Nat
  next : N → Nat → Option N
  /-- A pick that has a successor is below the width. -/
  lt : ∀ n k t, next n k = some t → k < width n

/-- The successors of a node, each with the pick that leads to it. -/
def succs (S : Sys N) (n : N) : List (Nat × N) :=
  (List.range (S.width n)).filterMap fun k => (S.next n k).map (k, ·)

theorem mem_succs {S : Sys N} {n t : N} {k : Nat} :
    (k, t) ∈ succs S n ↔ S.next n k = some t := by
  unfold succs
  constructor
  · intro h
    simp only [List.mem_filterMap, List.mem_range, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨k', hk, t', h1, rfl, rfl⟩ := h
    exact h1
  · intro h
    have hk := S.lt _ _ _ h
    simp only [List.mem_filterMap, List.mem_range, Option.map_eq_some_iff, Prod.mk.injEq]
    exact ⟨k, hk, t, h, rfl, rfl⟩

/-- Replay picks from a node. -/
def greplay (S : Sys N) : N → List Nat → Option N
  | n, [] => some n
  | n, k :: ks => (S.next n k).bind fun t => greplay S t ks

theorem greplay_append (S : Sys N) :
    ∀ (n : N) (ks : List Nat) (k : Nat),
      greplay S n (ks ++ [k]) = (greplay S n ks).bind fun t => S.next t k
  | n, [], k => by simp [greplay]
  | n, j :: ks, k => by
    simp only [greplay, List.cons_append]
    cases S.next n j with
    | none => rfl
    | some t => exact greplay_append S t ks k

/-- Nodes reachable from an initial node in at most `d` steps. -/
inductive Reach (S : Sys N) : Nat → N → Prop where
  | init {d n} : n ∈ S.init → Reach S d n
  | step {d n t} : Reach S d n → (∃ k, (k, t) ∈ succs S n) → Reach S (d + 1) t

theorem greplay_reach (S : Sys N) :
    ∀ (ks : List Nat) (s t : N) (n : Nat), Reach S n s → greplay S s ks = some t →
      Reach S (n + ks.length) t
  | [], s, t, n, hs, h => by simp [greplay] at h; subst h; simpa using hs
  | k :: ks, s, t, n, hs, h => by
    simp only [greplay, Option.bind_eq_some_iff] at h
    obtain ⟨u, hu, hr⟩ := h
    have := greplay_reach S ks u t (n + 1) (.step hs ⟨k, mem_succs.mpr hu⟩) hr
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

/-- Every node a replay from an initial node passes through is reachable (at any depth). -/
theorem greplay_reach_any {S : Sys N} {r t : N} {ks : List Nat} (hr : r ∈ S.init)
    (h : greplay S r ks = some t) : ∃ d, Reach S d t :=
  ⟨0 + ks.length, greplay_reach S ks r t 0 (.init hr) h⟩

/-! ## The search -/

structure Path (N : Type) where
  root : N
  picks : List Nat

inductive Result (N : Type) where
  | holds (states : Nat)
  | counterexample (path : Path N)
  | incomplete (states : Nat)

/-- A frontier entry: a node, the initial node it came from and the picks, latest first. -/
structure Item (N : Type) where
  n : N
  root : N
  picks : List Nat

abbrev Visited (N : Type) [DecidableEq N] [Hashable N] := Std.HashSet N

inductive Out (N : Type) [DecidableEq N] [Hashable N] where
  | ok (V : Visited N) (next : List (Item N))
  | cex (p : Path N)
  | full (states : Nat)

def addAll (ok : N → Bool) (cap : Nat) (mk : α → Item N) (cexOf : α → Path N) :
    List α → Visited N → List (Item N) → Out N
  | [], V, nx => .ok V nx
  | a :: as, V, nx =>
    if V.contains (mk a).n then addAll ok cap mk cexOf as V nx
    else if ok (mk a).n then
      if cap ≤ V.size then .full V.size
      else addAll ok cap mk cexOf as (V.insert (mk a).n) (mk a :: nx)
    else .cex (cexOf a)

def succItem (it : Item N) (a : Nat × N) : Item N :=
  { n := a.2, root := it.root, picks := a.1 :: it.picks }

def succCex (it : Item N) (a : Nat × N) : Path N :=
  { root := it.root, picks := (a.1 :: it.picks).reverse }

def layer (S : Sys N) (ok : N → Bool) (cap : Nat) :
    List (Item N) → Visited N → List (Item N) → Out N
  | [], V, nx => .ok V nx
  | it :: its, V, nx =>
    match addAll ok cap (succItem it) (succCex it) (succs S it.n) V nx with
    | .ok V nx => layer S ok cap its V nx
    | o => o

def bfs (S : Sys N) (ok : N → Bool) (cap : Nat) : Nat → List (Item N) → Visited N → Result N
  | _, [], V => .holds V.size
  | 0, _ :: _, V => .incomplete V.size
  | d + 1, F@(_ :: _), V =>
    match layer S ok cap F V [] with
    | .ok V' F' => bfs S ok cap d F' V'
    | .cex p => .counterexample p
    | .full n => .incomplete n

def initItem (r : N) : Item N := { n := r, root := r, picks := [] }

def initCex (r : N) : Path N := { root := r, picks := [] }

def search (S : Sys N) (ok : N → Bool) (bound cap : Nat) : Result N :=
  match addAll ok cap initItem initCex S.init ∅ [] with
  | .ok V F => bfs S ok cap bound F V
  | .cex p => .counterexample p
  | .full n => .incomplete n

/-! ## Soundness -/

structure Grow (ok : N → Bool) (V V' : Visited N) (nx nx' : List (Item N)) (P : Item N → Prop) :
    Prop where
  sub : ∀ s, s ∈ V → s ∈ V'
  keep : ∀ j, j ∈ nx → j ∈ nx'
  fresh : ∀ s, s ∈ V' → s ∉ V → ok s = true ∧ ∃ j ∈ nx', j.n = s
  items : ∀ j, j ∈ nx' → j ∈ nx ∨ (j.n ∈ V' ∧ P j)

theorem Grow.refl {ok : N → Bool} {V : Visited N} {nx : List (Item N)} {P : Item N → Prop} :
    Grow ok V V nx nx P :=
  ⟨fun _ h => h, fun _ h => h, fun _ h h' => absurd h h', fun _ h => Or.inl h⟩

theorem Grow.trans {ok : N → Bool} {V₁ V₂ V₃ : Visited N} {n₁ n₂ n₃ : List (Item N)}
    {P : Item N → Prop} (g₁ : Grow ok V₁ V₂ n₁ n₂ P) (g₂ : Grow ok V₂ V₃ n₂ n₃ P) :
    Grow ok V₁ V₃ n₁ n₃ P where
  sub s h := g₂.sub s (g₁.sub s h)
  keep j h := g₂.keep j (g₁.keep j h)
  fresh s h3 h1 := by
    by_cases h2 : s ∈ V₂
    · obtain ⟨hi, j, hj, hjs⟩ := g₁.fresh s h2 h1
      exact ⟨hi, j, g₂.keep j hj, hjs⟩
    · exact g₂.fresh s h3 h2
  items j h := by
    rcases g₂.items j h with h2 | ⟨hv, hp⟩
    · rcases g₁.items j h2 with h1 | ⟨hv, hp⟩
      · exact Or.inl h1
      · exact Or.inr ⟨g₂.sub _ hv, hp⟩
    · exact Or.inr ⟨hv, hp⟩

theorem Grow.mono {ok : N → Bool} {V V' : Visited N} {nx nx' : List (Item N)} {P Q : Item N → Prop}
    (g : Grow ok V V' nx nx' P) (hpq : ∀ j, P j → Q j) : Grow ok V V' nx nx' Q where
  sub := g.sub
  keep := g.keep
  fresh := g.fresh
  items j h := (g.items j h).imp id fun ⟨hv, hp⟩ => ⟨hv, hpq j hp⟩

theorem addAll_ok {ok : N → Bool} {cap : Nat} {mk : α → Item N} {cexOf : α → Path N} :
    ∀ (L : List α) (V V' : Visited N) (nx nx' : List (Item N)),
      addAll ok cap mk cexOf L V nx = .ok V' nx' →
      Grow ok V V' nx nx' (fun j => ∃ a ∈ L, j = mk a) ∧ ∀ a ∈ L, (mk a).n ∈ V'
  | [], V, V', nx, nx', h => by
    simp only [addAll, Out.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Grow.refl, by simp⟩
  | a :: as, V, V', nx, nx', h => by
    simp only [addAll] at h
    split at h
    · rename_i hc
      obtain ⟨g, cov⟩ := addAll_ok as V V' nx nx' h
      refine ⟨g.mono fun j ⟨b, hb, e⟩ => ⟨b, List.mem_cons_of_mem _ hb, e⟩, ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact g.sub _ (Std.HashSet.mem_iff_contains.mpr hc)
      · exact cov b hb
    · rename_i hc
      split at h
      · rename_i hi
        split at h
        · cases h
        · obtain ⟨g, cov⟩ := addAll_ok as _ V' _ nx' h
          have g0 : Grow ok V (V.insert (mk a).n) nx (mk a :: nx)
              (fun j => ∃ b ∈ a :: as, j = mk b) :=
            { sub := fun s hs => Std.HashSet.mem_insert.mpr (Or.inr hs)
              keep := fun j hj => List.mem_cons_of_mem _ hj
              fresh := fun s hs hn => by
                rcases Std.HashSet.mem_insert.mp hs with he | he
                · have he := beq_iff_eq.mp he
                  subst he
                  exact ⟨hi, mk a, List.mem_cons_self, rfl⟩
                · exact absurd he hn
              items := fun j hj => by
                rcases List.mem_cons.mp hj with rfl | hj
                · exact Or.inr ⟨Std.HashSet.mem_insert.mpr (Or.inl (beq_self_eq_true _)),
                    a, List.mem_cons_self, rfl⟩
                · exact Or.inl hj }
          refine ⟨g0.trans (g.mono fun j ⟨b, hb, e⟩ => ⟨b, List.mem_cons_of_mem _ hb, e⟩), ?_⟩
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact g.sub _ (Std.HashSet.mem_insert.mpr (Or.inl (beq_self_eq_true _)))
          · exact cov b hb
      · cases h

theorem addAll_cex {ok : N → Bool} {cap : Nat} {mk : α → Item N} {cexOf : α → Path N} :
    ∀ (L : List α) (V : Visited N) (nx : List (Item N)) (p : Path N),
      addAll ok cap mk cexOf L V nx = .cex p → ∃ a ∈ L, ok (mk a).n = false ∧ p = cexOf a
  | [], V, nx, p, h => by simp [addAll] at h
  | a :: as, V, nx, p, h => by
    simp only [addAll] at h
    split at h
    · obtain ⟨b, hb, hi, e⟩ := addAll_cex as V nx p h
      exact ⟨b, List.mem_cons_of_mem _ hb, hi, e⟩
    · split at h
      · split at h
        · cases h
        · obtain ⟨b, hb, hi, e⟩ := addAll_cex as _ _ p h
          exact ⟨b, List.mem_cons_of_mem _ hb, hi, e⟩
      · rename_i hi
        simp only [Out.cex.injEq] at h
        exact ⟨a, List.mem_cons_self, by simpa using hi, h.symm⟩

def FromLayer (S : Sys N) (F : List (Item N)) (j : Item N) : Prop :=
  ∃ it ∈ F, ∃ a ∈ succs S it.n, j = succItem it a

theorem layer_ok {S : Sys N} {ok : N → Bool} {cap : Nat} :
    ∀ (F : List (Item N)) (V V' : Visited N) (nx nx' : List (Item N)),
      layer S ok cap F V nx = .ok V' nx' →
      Grow ok V V' nx nx' (FromLayer S F) ∧
        ∀ it ∈ F, ∀ a ∈ succs S it.n, a.2 ∈ V'
  | [], V, V', nx, nx', h => by
    simp only [layer, Out.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Grow.refl, by simp⟩
  | it :: its, V, V', nx, nx', h => by
    simp only [layer] at h
    cases h1 : addAll ok cap (succItem it) (succCex it) (succs S it.n) V nx with
    | cex => simp [h1] at h
    | full => simp [h1] at h
    | ok V1 nx1 =>
      simp only [h1] at h
      obtain ⟨g1, c1⟩ := addAll_ok _ _ _ _ _ h1
      obtain ⟨g2, c2⟩ := layer_ok its V1 V' nx1 nx' h
      refine ⟨(g1.mono fun j ⟨a, ha, e⟩ => ⟨it, List.mem_cons_self, a, ha, e⟩).trans
        (g2.mono fun j ⟨it', hit, a, ha, e⟩ => ⟨it', List.mem_cons_of_mem _ hit, a, ha, e⟩), ?_⟩
      intro it' hit a ha
      rcases List.mem_cons.mp hit with rfl | hit
      · exact g2.sub _ (c1 a ha)
      · exact c2 it' hit a ha

theorem layer_cex {S : Sys N} {ok : N → Bool} {cap : Nat} :
    ∀ (F : List (Item N)) (V : Visited N) (nx : List (Item N)) (p : Path N),
      layer S ok cap F V nx = .cex p →
      ∃ it ∈ F, ∃ a ∈ succs S it.n, ok a.2 = false ∧ p = succCex it a
  | [], V, nx, p, h => by simp [layer] at h
  | it :: its, V, nx, p, h => by
    simp only [layer] at h
    cases h1 : addAll ok cap (succItem it) (succCex it) (succs S it.n) V nx with
    | ok V1 nx1 =>
      simp only [h1] at h
      obtain ⟨it', hit, a, ha, hi, e⟩ := layer_cex its _ _ p h
      exact ⟨it', List.mem_cons_of_mem _ hit, a, ha, hi, e⟩
    | cex q =>
      simp only [h1, Out.cex.injEq] at h
      subst h
      obtain ⟨a, ha, hi, e⟩ := addAll_cex _ _ _ _ h1
      exact ⟨it, List.mem_cons_self, a, ha, by simpa [succItem] using hi, e⟩
    | full => simp [h1] at h

/-- A frontier entry is the end of a replayable run from an initial node. -/
def PathOK (S : Sys N) (j : Item N) : Prop :=
  j.root ∈ S.init ∧ greplay S j.root j.picks.reverse = some j.n

structure BfsInv (S : Sys N) (ok : N → Bool) (d : Nat) (V : Visited N) (F : List (Item N)) :
    Prop where
  holds : ∀ s, s ∈ V → ok s = true
  covers : ∀ s, Reach S d s → s ∈ V
  frontier : ∀ j ∈ F, j.n ∈ V ∧ PathOK S j ∧ j.picks.length ≤ d
  closed : ∀ s, s ∈ V → (∀ j ∈ F, j.n ≠ s) → ∀ a ∈ succs S s, a.2 ∈ V

theorem BfsInv.next {S : Sys N} {ok : N → Bool} {cap d : Nat} {V V' : Visited N}
    {F F' : List (Item N)} (bi : BfsInv S ok d V F) (h : layer S ok cap F V [] = .ok V' F') :
    BfsInv S ok (d + 1) V' F' := by
  obtain ⟨g, cov⟩ := layer_ok F V V' [] F' h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    by_cases hv : s ∈ V
    · exact bi.holds s hv
    · exact (g.fresh s hs hv).1
  · intro t ht
    cases ht with
    | init hi => exact g.sub _ (bi.covers _ (.init hi))
    | step hs hst =>
      rename_i s
      obtain ⟨k, hk⟩ := hst
      have hsV := bi.covers s hs
      by_cases hf : ∃ j ∈ F, j.n = s
      · obtain ⟨j, hj, rfl⟩ := hf
        exact cov j hj (k, t) hk
      · exact g.sub _ (bi.closed s hsV (fun j hj e => hf ⟨j, hj, e⟩) (k, t) hk)
  · intro j hj
    rcases g.items j hj with h0 | ⟨hv, it, hit, a, ha, rfl⟩
    · cases h0
    · obtain ⟨_, ⟨hm, hr⟩, hl⟩ := bi.frontier it hit
      have hsucc := mem_succs.mp ha
      refine ⟨hv, ⟨?_, ?_⟩, ?_⟩
      · simpa [succItem] using hm
      · simp only [succItem, List.reverse_cons]
        rw [greplay_append, hr]
        simpa using hsucc
      · simp [succItem]; omega
  · intro s hs hnf a ha
    by_cases hv : s ∈ V
    · by_cases hf : ∃ j ∈ F, j.n = s
      · obtain ⟨j, hj, rfl⟩ := hf
        exact cov j hj a ha
      · exact g.sub _ (bi.closed s hv (fun j hj e => hf ⟨j, hj, e⟩) a ha)
    · obtain ⟨_, j, hj, e⟩ := g.fresh s hs hv
      exact absurd e (hnf j hj)

theorem bfs_sound {S : Sys N} {ok : N → Bool} {cap : Nat} :
    ∀ (r d : Nat) (F : List (Item N)) (V : Visited N) (n : Nat),
      BfsInv S ok d V F → bfs S ok cap r F V = .holds n →
      ∀ m s, Reach S m s → ok s = true
  | r, d, [], V, n, bi, _, m, s, hs => by
    apply bi.holds
    have key : ∀ m t, Reach S m t → t ∈ V := by
      intro m t ht
      induction ht with
      | init hi => exact bi.covers _ (.init hi)
      | step _ hst ih =>
        obtain ⟨k, hk⟩ := hst
        exact bi.closed _ ih (by simp) _ hk
    exact key _ _ hs
  | 0, d, _ :: _, V, n, bi, h, m, s, hs => by simp [bfs] at h
  | r + 1, d, it :: its, V, n, bi, h, m, s, hs => by
    simp only [bfs] at h
    split at h
    · rename_i V' F' hl
      exact bfs_sound r (d + 1) F' V' n (bi.next hl) h m s hs
    · cases h
    · cases h

def CexOK (S : Sys N) (ok : N → Bool) (bound : Nat) (p : Path N) : Prop :=
  p.root ∈ S.init ∧ p.picks.length ≤ bound ∧
    ∃ t, greplay S p.root p.picks = some t ∧ ok t = false

theorem bfs_cex {S : Sys N} {ok : N → Bool} {cap : Nat} :
    ∀ (r d : Nat) (F : List (Item N)) (V : Visited N) (p : Path N),
      BfsInv S ok d V F → bfs S ok cap r F V = .counterexample p → CexOK S ok (d + r) p
  | r, d, [], V, p, _, h => by cases r <;> simp [bfs] at h
  | 0, d, _ :: _, V, p, _, h => by simp [bfs] at h
  | r + 1, d, it :: its, V, p, bi, h => by
    simp only [bfs] at h
    split at h
    · rename_i V' F' hl
      have := bfs_cex r (d + 1) F' V' p (bi.next hl) h
      simpa [Nat.add_assoc, Nat.add_comm 1] using this
    · rename_i q hl
      simp only [Result.counterexample.injEq] at h
      subst h
      obtain ⟨j, hj, a, ha, hi, rfl⟩ := layer_cex _ _ _ _ hl
      obtain ⟨_, ⟨hm, hr⟩, hlen⟩ := bi.frontier j hj
      refine ⟨hm, ?_, a.2, ?_, hi⟩
      · simp [succCex]; omega
      · simp only [succCex, List.reverse_cons]
        rw [greplay_append, hr]
        simpa using mem_succs.mp ha
    · cases h

theorem init_inv {S : Sys N} {ok : N → Bool} {cap : Nat} {V : Visited N} {F : List (Item N)}
    (h : addAll ok cap initItem initCex S.init ∅ [] = .ok V F) :
    BfsInv S ok 0 V F := by
  obtain ⟨g, cov⟩ := addAll_ok _ _ _ _ _ h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    exact (g.fresh s hs (Std.HashSet.not_mem_empty)).1
  · intro s hs
    cases hs with
    | init hi => exact cov s hi
  · intro j hj
    rcases g.items j hj with h0 | ⟨hv, m, hm, rfl⟩
    · cases h0
    · exact ⟨hv, ⟨by simpa [initItem] using hm, by simp [initItem, greplay]⟩, by simp [initItem]⟩
  · intro s hs hnf
    obtain ⟨_, j, hj, e⟩ := g.fresh s hs Std.HashSet.not_mem_empty
    exact absurd e (hnf j hj)

/-- **Soundness of the search.** If it reports `holds`, every node reachable in the system
(however many steps) satisfies `ok`. -/
theorem search_sound {S : Sys N} {ok : N → Bool} {bound cap n : Nat}
    (h : search S ok bound cap = .holds n) : ∀ m s, Reach S m s → ok s = true := by
  unfold search at h
  split at h
  · rename_i V F hi
    exact bfs_sound bound 0 F V n (init_inv hi) h
  · cases h
  · cases h

/-- **Counterexamples are real.** The path starts at an initial node and replays to a node
where `ok` is false, in at most `bound` steps. -/
theorem search_counterexample_real {S : Sys N} {ok : N → Bool} {bound cap : Nat}
    {p : Path N} (h : search S ok bound cap = .counterexample p) :
    p.root ∈ S.init ∧ p.picks.length ≤ bound ∧
      ∃ t, greplay S p.root p.picks = some t ∧ ok t = false := by
  unfold search at h
  split at h
  · rename_i V F hi
    have := bfs_cex bound 0 F V p (init_inv hi) h
    rw [Nat.zero_add] at this
    exact this
  · rename_i q hc
    simp only [Result.counterexample.injEq] at h
    subst h
    obtain ⟨m, hm, hi, rfl⟩ := addAll_cex _ _ _ _ hc
    exact ⟨hm, by simp [initCex], m, by simp [initCex, greplay], by simpa [initItem] using hi⟩
  · cases h

end Exegra.Gen
