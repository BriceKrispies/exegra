import Std.Data.HashMap
import Exegra.Core.BehavExec
import Exegra.Core.Live

/-
Liveness on the behaviour calculus (WG-5682): non-Zeno runs, fairness per entry, the lasso search
and the ranking search, each with a Boolean checker proved sound against `Exegra.Core.Live`.

* `NonZeno r`: time grows beyond every bound or the run reaches a deadlocked state. On a finite
  state space every cycle of `Sys.lts` keeps the time (time never decreases and a cycle returns to
  its state), so every lasso whose cycle has a step of the relation is Zeno; the lasso search
  reports it (`zeno` in its result).
* Fairness is per entry: a step is labelled by the entry it delivers (and its draws, P1 criterion 2),
  so a fair set is a set of labels, chosen by a predicate on the delivered entry (`entryFair`). For
  a system with no sampled delay a label is its entry.
* `checkLasso` checks the hypotheses of `lasso_refutes` (form `FG`) or `lasso_refutes_GF` (form
  `GF`) for a candidate lasso `x0, pre, cyc`; `lassoSearch` looks for a candidate over the states of
  `Exec.gen sys` and returns `lasso` only when `checkLasso` accepts it (`lassoSearch_sound`).
* `checkRanking` checks the hypotheses of `response_of_ranking` over a closed list of states;
  `rankProves` computes the list, a ranking and helpful actions and checks them
  (`rankProves_sound`).

The searches themselves are not proved: only the checkers are, and a search returns a positive
result only through its checker.
-/

namespace Exegra.Core.Behav

open Exegra.Core.LTS

/-! ### Non-Zeno runs and fairness per entry -/

/-- A run is non-Zeno when its time exceeds every bound, or it reaches a deadlocked state (after
which it stutters): WG-5682 criterion 6, "`NonZeno r := ∀ T, ∃ i, (r.st i).cfg.time > T ∨
Deadlocked (r.st i)`". -/
def NonZeno {sys : Sys} (r : LTS.Run (Sys.lts sys)) : Prop :=
  ∀ T, ∃ i, (r.st i).cfg.time > T ∨ (Sys.lts sys).Deadlocked (r.st i)

/-- The fair labels of a set of fair entries: a label is fair when the entry it delivers is. -/
def entryFair (E : Entry → Bool) : ActSet Label := fun l => E l.entry = true

/-- The fair labels of a Boolean predicate on labels. -/
def fairOf (f : Label → Bool) : ActSet Label := fun l => f l = true

instance : Inhabited State := ⟨.run [] { time := 0, machines := [], pending := [] }⟩

/-! ### Boolean checks of enabledness, deadlock and steps -/

def enabledB (sys : Sys) (s : State) (l : Label) : Bool :=
  (Exec.successors sys s).any (·.1 == l)

theorem enabledB_iff {sys : Sys} {s : State} {l : Label} :
    enabledB sys s l = true ↔ (Sys.lts sys).Enabled s l := by
  unfold enabledB
  simp only [List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨l', t⟩, hm, rfl⟩
    exact ⟨t, successors_sound hm⟩
  · rintro ⟨t, ht⟩
    exact ⟨(l, t), successors_complete ht, rfl⟩

theorem deadlocked_of_nil {sys : Sys} {s : State} (h : (Exec.successors sys s).isEmpty = true) :
    (Sys.lts sys).Deadlocked s := by
  intro a t hst
  have := successors_complete hst
  rw [List.isEmpty_iff.mp h] at this
  cases this

/-- A step of the relation, or a stutter at a state with no successor. -/
def rstepB (sys : Sys) (s : State) (l : Label) (t : State) : Bool :=
  (Exec.successors sys s).contains (l, t) || ((Exec.successors sys s).isEmpty && t == s)

theorem rstepB_sound {sys : Sys} {s t : State} {l : Label} (h : rstepB sys s l t = true) :
    (Sys.lts sys).RStep s l t := by
  unfold rstepB at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at h
  rcases h with h | ⟨h1, h2⟩
  · exact .inl (successors_sound h)
  · exact .inr ⟨deadlocked_of_nil h1, h2⟩

def checkPath (sys : Sys) : State → List (Label × State) → Bool
  | _, [] => true
  | s, (l, t) :: rest => rstepB sys s l t && checkPath sys t rest

theorem checkPath_sound {sys : Sys} : ∀ {s : State} {pre : List (Label × State)},
    checkPath sys s pre = true → (Sys.lts sys).RPathFrom s pre
  | _, [], _ => trivial
  | s, (l, t) :: rest, h => by
    simp only [checkPath, Bool.and_eq_true] at h
    exact ⟨rstepB_sound h.1, checkPath_sound h.2⟩

/-- The reachability of the end of a checked path from an initial state. -/
theorem reach_of_path {sys : Sys} : ∀ {x : State} {pre : List (Label × State)},
    (Sys.lts sys).Reach x → (Sys.lts sys).RPathFrom x pre →
      (Sys.lts sys).Reach ((pathStates x pre).getLast (by simp [pathStates]))
  | _, [], hx, _ => by simpa [pathStates] using hx
  | x, (l, t) :: rest, hx, ⟨h1, h2⟩ => by
    have ht : (Sys.lts sys).Reach t := by
      rcases h1 with h | ⟨_, rfl⟩
      · exact .step hx h
      · exact hx
    have := reach_of_path ht h2
    simpa [pathStates, List.getLast_cons] using this

/-! ### Lassos -/

/-- The liveness forms a lasso refutes: `FG p` (some state of the cycle violates `p`) and `GF p`
(every state of the cycle does). -/
inductive LForm where
  | FG
  | GF
  deriving DecidableEq, Repr

/-- The end of a path from `x0`. -/
def pathEnd (x0 : State) (pre : List (Label × State)) : State :=
  (pathStates x0 pre).getLast (by simp [pathStates])

/-- The check of a candidate lasso: `x0` is initial, `pre` a path from it to `s`, `cyc` a non-empty
path from `s` back to `s` with the states the form needs violating `p`, and every fair label
enabled at every state of `cyc` is the label of a step of `cyc`. -/
def checkLasso (sys : Sys) (f : Label → Bool) (p : State → Bool) (form : LForm)
    (x0 : State) (pre cyc : List (Label × State)) : Bool :=
  let s := pathEnd x0 pre
  (Exec.inits sys).contains x0 && checkPath sys x0 pre && !cyc.isEmpty && checkPath sys s cyc &&
  ((cyc.getLast?.map (·.2)) == some s) &&
  (match form with
    | .FG => cyc.any (fun q => !p q.2)
    | .GF => cyc.all (fun q => !p q.2)) &&
  ((Exec.successors sys s).map (·.1)).all (fun l =>
    !f l || !cyc.all (fun q => enabledB sys q.2 l) || cyc.any (fun q => q.1 == l))

/-- What a checked lasso gives: the hypotheses of `lasso_refutes` (or `lasso_refutes_GF`). -/
structure LassoFacts (sys : Sys) (f : Label → Bool) (p : State → Bool) (form : LForm)
    (s : State) (cyc : List (Label × State)) : Prop where
  reach : (Sys.lts sys).Reach s
  ne : cyc ≠ []
  path : (Sys.lts sys).RPathFrom s cyc
  back : ∀ h : cyc ≠ [], (cyc.getLast h).2 = s
  viol : match form with
    | .FG => ∃ q ∈ cyc, ¬ p q.2 = true
    | .GF => ∀ q ∈ cyc, ¬ p q.2 = true
  fair : ∀ a ∈ fairOf f, (∀ q ∈ cyc, (Sys.lts sys).Enabled q.2 a) → ∃ q ∈ cyc, q.1 = a

theorem checkLasso_sound {sys : Sys} {f : Label → Bool} {p : State → Bool} {form : LForm}
    {x0 : State} {pre cyc : List (Label × State)} (h : checkLasso sys f p form x0 pre cyc = true) :
    LassoFacts sys f p form (pathEnd x0 pre) cyc := by
  unfold checkLasso at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hi, hpre⟩, hne⟩, hcyc⟩, hback⟩, hviol⟩, hfair⟩ := h
  have hne' : cyc ≠ [] := by simpa using hne
  have hx : (Sys.lts sys).Reach x0 := by
    apply Reach.init
    have := List.contains_iff_mem.mp hi
    simp only [Exec.inits, List.mem_map] at this
    obtain ⟨m, hm, rfl⟩ := this
    exact ⟨m, length_of_mem_masks _ hm, rfl⟩
  refine ⟨reach_of_path hx (checkPath_sound hpre), hne', checkPath_sound hcyc, ?_, ?_, ?_⟩
  · intro h'
    have e := beq_iff_eq.mp hback
    rw [List.getLast?_eq_some_getLast h'] at e
    simpa using e
  · cases form with
    | FG =>
      simp only [List.any_eq_true, Bool.not_eq_true'] at hviol
      obtain ⟨q, hq, hp⟩ := hviol
      exact ⟨q, hq, by simp [hp]⟩
    | GF =>
      simp only [List.all_eq_true, Bool.not_eq_true'] at hviol
      exact fun q hq => by simp [hviol q hq]
  · intro a ha hen
    have hlast : (cyc.getLast hne').2 = pathEnd x0 pre := by
      have e := beq_iff_eq.mp hback
      rw [List.getLast?_eq_some_getLast hne'] at e
      simpa using e
    obtain ⟨t, ht⟩ := hen _ (List.getLast_mem hne')
    rw [hlast] at ht
    have hmem : a ∈ (Exec.successors sys (pathEnd x0 pre)).map (·.1) :=
      List.mem_map.mpr ⟨(a, t), successors_complete ht, rfl⟩
    have := List.all_eq_true.mp hfair a hmem
    simp only [Bool.or_eq_true, Bool.not_eq_true', List.all_eq_false, List.any_eq_true,
      beq_iff_eq] at this
    rcases this with (hf | ⟨q, hq, hnq⟩) | hex
    · exact absurd ha (by simp [fairOf, hf, Membership.mem])
    · exact absurd (enabledB_iff.mpr (hen q hq)) (by simpa using hnq)
    · exact hex

/-- **A checked `FG` lasso refutes `◇□ p` under weak fairness.** -/
theorem checkLasso_refutes_FG {sys : Sys} {f : Label → Bool} {p : State → Bool} {x0 : State}
    {pre cyc : List (Label × State)} (h : checkLasso sys f p .FG x0 pre cyc = true) :
    ¬ ∀ r : LTS.Run (Sys.lts sys), r.WeakFair (fairOf f) → (◇□ (fun s => p s = true)) r := by
  have hf := checkLasso_sound h
  exact lasso_refutes (P := fun s => p s = true) hf.reach hf.ne hf.path (hf.back hf.ne) hf.viol hf.fair

/-- **A checked `GF` lasso refutes `□◇ p` under weak fairness.** -/
theorem checkLasso_refutes_GF {sys : Sys} {f : Label → Bool} {p : State → Bool} {x0 : State}
    {pre cyc : List (Label × State)} (h : checkLasso sys f p .GF x0 pre cyc = true) :
    ¬ ∀ r : LTS.Run (Sys.lts sys), r.WeakFair (fairOf f) → (□◇ (fun s => p s = true)) r := by
  have hf := checkLasso_sound h
  exact lasso_refutes_GF (P := fun s => p s = true) hf.reach hf.ne hf.path (hf.back hf.ne) hf.viol hf.fair

/-! ### The reachable states as a graph -/

/-- The nodes a search visits when it reaches an empty frontier, or none. -/
def bfsV {N : Type} [DecidableEq N] [Hashable N] (S : Gen.Sys N) (cap : Nat) :
    Nat → List (Gen.Item N) → Gen.Visited N → Option (Gen.Visited N)
  | _, [], V => some V
  | 0, _ :: _, _ => none
  | d + 1, F@(_ :: _), V =>
    match Gen.layer S (fun _ => true) cap F V [] with
    | .ok V' F' => bfsV S cap d F' V'
    | _ => none

/-- The reachable nodes of a search system, when the search reaches an empty frontier within the
bound and the cap. -/
def reachable {N : Type} [DecidableEq N] [Hashable N] (S : Gen.Sys N) (bound cap : Nat) :
    Option (List N) :=
  match Gen.addAll (fun _ => true) cap Gen.initItem Gen.initCex S.init ∅ [] with
  | .ok V F => (bfsV S cap bound F V).map (·.toList)
  | _ => none

/-- The reachable states, indexed, with their successors (by index). A state with no successor
is deadlocked and stutters. -/
structure Graph where
  states : Array State
  idx : Std.HashMap State Nat
  succ : Array (List (Label × Nat))

def Graph.ofList (sys : Sys) (L : List State) : Graph :=
  let states := L.toArray
  let idx : Std.HashMap State Nat := (L.zipIdx).foldl (fun m (s, i) => m.insert s i) {}
  let succ := states.map fun s => (Exec.successors sys s).filterMap fun (l, t) => (idx.get? t).map (l, ·)
  { states, idx, succ }

/-- The label a stutter carries (arbitrary: a stutter takes no action). -/
def stutterLabel : Label := ⟨{ time := 0, event := 0, payload := [] }, [], []⟩

/-- The edges of node `i` within the allowed nodes: its successors, or a stutter when it has none. -/
def Graph.edges (g : Graph) (allowed : Nat → Bool) (i : Nat) : List (Label × Nat) :=
  match g.succ[i]? with
  | some [] => if allowed i then [(stutterLabel, i)] else []
  | some es => es.filter (fun e => allowed e.2)
  | none => []

/-- Breadth-first paths from `src` within the allowed nodes: for each node reached, the node and
label it was reached from. -/
def Graph.bfsFrom (g : Graph) (allowed : Nat → Bool) (src : List Nat) : Array (Option (Option (Nat × Label))) := Id.run do
  let n := g.states.size
  let mut par : Array (Option (Option (Nat × Label))) := Array.replicate n none
  let mut queue : Array Nat := #[]
  for s in src do
    if s < n && (par[s]?.join).isNone && allowed s then
      par := par.set! s (some none)
      queue := queue.push s
  let mut head := 0
  for _ in [0:n + 1] do
    if h : head < queue.size then
      let i := queue[head]
      head := head + 1
      for (l, j) in g.edges allowed i do
        if j < n && (par[j]?.join).isNone then
          par := par.set! j (some (some (i, l)))
          queue := queue.push j
  return par

/-- The path (labels and nodes, excluding the start) to `dst` in a breadth-first tree. -/
def Graph.pathTo (par : Array (Option (Option (Nat × Label)))) (dst : Nat) : List (Label × Nat) := Id.run do
  let mut out : List (Label × Nat) := []
  let mut cur := dst
  for _ in [0:par.size + 1] do
    match par[cur]?.join with
    | some (some (i, l)) =>
      out := (l, cur) :: out
      cur := i
    | _ => break
  return out

/-- A non-empty path from `a` to `b` (possibly `a = b`) within the allowed nodes, if any. -/
def Graph.pathBetween (g : Graph) (allowed : Nat → Bool) (a b : Nat) : Option (List (Label × Nat)) :=
  if a = b then some []
  else
    let par := g.bfsFrom allowed [a]
    match par[b]?.join with
    | some _ => some (Graph.pathTo par b)
    | none => none

/-- A cycle from `v` back to `v` through every node of `scc` and through an edge labelled with each
label of `need` (within `scc`). -/
def Graph.cycleThrough (g : Graph) (scc : List Nat) (need : List Label) (v : Nat) :
    Option (List (Label × Nat)) := do
  let inS := fun i => scc.contains i
  let mut cur := v
  let mut out : List (Label × Nat) := []
  for w in scc do
    let p ← g.pathBetween inS cur w
    out := out ++ p
    cur := w
  for l in need do
    if out.any (·.1 == l) then continue
    let some (x, y) := scc.findSome? (fun x => ((g.edges inS x).find? (·.1 == l)).map fun e => (x, e.2))
      | none
    let p ← g.pathBetween inS cur x
    out := out ++ p ++ [(l, y)]
    cur := y
  -- close the cycle: at least one step
  if cur = v && !out.isEmpty then return out
  let p ← g.pathBetween inS cur v
  let res := out ++ p
  if res.isEmpty then
    -- `v` alone: a self-loop or a stutter
    let e ← (g.edges inS v).find? (·.2 == v)
    return [(e.1, v)]
  return res

/-- A candidate lasso: a fair strongly connected set of allowed nodes containing a node violating
`p`, with a path into it from an initial state. -/
def lassoCand (sys : Sys) (f : Label → Bool) (p : State → Bool) (form : LForm) (L : List State) :
    Option (State × List (Label × State) × List (Label × State)) := do
  let g := Graph.ofList sys L
  let n := g.states.size
  let bad := fun i => match g.states[i]? with | some s => !p s | none => false
  let allowed : Nat → Bool := match form with | .GF => bad | .FG => fun i => decide (i < n)
  let toState := fun (ps : List (Label × Nat)) => ps.map fun (l, i) => (l, g.states[i]!)
  let inits := (Exec.inits sys).filterMap g.idx.get?
  let fromInit := g.bfsFrom (fun _ => true) inits
  -- the reverse edges within the allowed nodes
  let rev : Array (List Nat) := (List.range n).foldl (fun acc i =>
    (g.edges allowed i).foldl (fun acc (_, j) => acc.modify j (i :: ·)) acc) (Array.replicate n [])
  let cands := (List.range n).filter fun v => bad v && allowed v
  for v in cands do
    let fwd := g.bfsFrom allowed [v]
    -- backward reachability: breadth first over `rev`
    let back := Id.run do
      let mut seen := Array.replicate n false
      let mut queue := #[v]
      seen := seen.set! v true
      let mut head := 0
      for _ in [0:n + 1] do
        if h : head < queue.size then
          let i := queue[head]
          head := head + 1
          for j in rev[i]!.reverse do
            if !seen[j]! then
              seen := seen.set! j true
              queue := queue.push j
      return seen
    let scc := (List.range n).filter fun i => (fwd[i]?.join).isSome && back[i]!
    -- an edge inside: a non-trivial component
    if !scc.any (fun i => (g.edges allowed i).any (fun e => scc.contains e.2)) then continue
    -- weak fairness: every fair label enabled at every state of the component is taken inside it
    let labelsAt := fun i => ((g.succ[i]?).getD []).map (·.1)
    let need := (labelsAt v).eraseDups.filter fun l => f l && scc.all (fun i => (labelsAt i).contains l)
    let inside := fun l => scc.any fun i => (g.edges (fun j => scc.contains j) i).any (·.1 == l)
    if !need.all inside then continue
    let some cyc := g.cycleThrough scc need v | continue
    let stem := Graph.pathTo fromInit v
    let x0 := match stem with
      | [] => v
      | _ => Id.run do
        -- the first node of the tree path is the initial node
        let mut cur := v
        for _ in [0:n + 1] do
          match fromInit[cur]?.join with
          | some (some (i, _)) => cur := i
          | _ => break
        return cur
    return (g.states[x0]!, toState stem, toState cyc)
  none

/-- The result of the lasso search. -/
inductive LassoResult where
  | lasso (x0 : State) (pre cyc : List (Label × State))
  | noLasso
  | incomplete (reason : Gen.Reason)

def LassoResult.isLasso : LassoResult → Bool
  | .lasso _ _ _ => true
  | _ => false

/-- **The lasso search** over the states of `Exec.gen sys`: the reachable states (an empty frontier
within the bound and the cap), then a candidate lasso, returned only when `checkLasso` accepts it. -/
def lassoSearch (sys : Sys) (f : Label → Bool) (p : State → Bool) (form : LForm) (bound cap : Nat) :
    LassoResult :=
  match reachable (Exec.gen sys) bound cap with
  | none =>
    match Gen.search (Exec.gen sys) (fun _ => true) bound cap with
    | .incomplete why _ => .incomplete why
    | _ => .incomplete .cap
  | some L =>
    match lassoCand sys f p form L with
    | some (x0, pre, cyc) => if checkLasso sys f p form x0 pre cyc then .lasso x0 pre cyc else .noLasso
    | none => .noLasso

/-- **The lasso search is sound**: a `lasso x0 pre cyc` result satisfies the hypotheses of
`lasso_refutes` (form `FG`) or `lasso_refutes_GF` (form `GF`) for `Sys.lts sys`, with `s` the end of
`pre`.

WG-5682 criterion 7: "a `lasso pre cyc` result of the lasso search over `Exec.gen sys` satisfies the
hypotheses of `lasso_refutes` for `Sys.lts sys`" (`LassoFacts` lists them; the search also returns
the initial state `x0` the path `pre` starts from). -/
theorem lassoSearch_sound {sys : Sys} {f : Label → Bool} {p : State → Bool} {form : LForm}
    {bound cap : Nat} {x0 : State} {pre cyc : List (Label × State)}
    (h : lassoSearch sys f p form bound cap = .lasso x0 pre cyc) :
    LassoFacts sys f p form (pathEnd x0 pre) cyc := by
  unfold lassoSearch at h
  split at h
  · split at h <;> cases h
  · split at h
    · split at h
      · cases h; apply checkLasso_sound; assumption
      · cases h
    · cases h

theorem lassoSearch_refutes_FG {sys : Sys} {f : Label → Bool} {p : State → Bool} {bound cap : Nat}
    (h : (lassoSearch sys f p .FG bound cap).isLasso = true) :
    ¬ ∀ r : LTS.Run (Sys.lts sys), r.WeakFair (fairOf f) → (◇□ (fun s => p s = true)) r := by
  cases hl : lassoSearch sys f p .FG bound cap with
  | lasso x0 pre cyc =>
    have hf := lassoSearch_sound hl
    exact lasso_refutes (P := fun s => p s = true) hf.reach hf.ne hf.path (hf.back hf.ne) hf.viol hf.fair
  | noLasso => rw [hl] at h; cases h
  | incomplete => rw [hl] at h; cases h

theorem lassoSearch_refutes_GF {sys : Sys} {f : Label → Bool} {p : State → Bool} {bound cap : Nat}
    (h : (lassoSearch sys f p .GF bound cap).isLasso = true) :
    ¬ ∀ r : LTS.Run (Sys.lts sys), r.WeakFair (fairOf f) → (□◇ (fun s => p s = true)) r := by
  cases hl : lassoSearch sys f p .GF bound cap with
  | lasso x0 pre cyc =>
    have hf := lassoSearch_sound hl
    exact lasso_refutes_GF (P := fun s => p s = true) hf.reach hf.ne hf.path (hf.back hf.ne) hf.viol hf.fair
  | noLasso => rw [hl] at h; cases h
  | incomplete => rw [hl] at h; cases h

/-! ### Rankings -/

/-- The check of a ranking certificate over `L`: `L` holds the initial states and is closed under
successors, and every state of `L` violating `p` has a fair helpful label `h s`, enabled, whose
every step reaches `p` or decreases `V`, while every step reaches `p`, decreases `V`, or keeps `V`
and the helpful label. -/
def checkRanking (sys : Sys) (f : Label → Bool) (p : State → Bool) (L : List State)
    (V : State → Nat) (h : State → Label) : Bool :=
  checkClosed (Exec.enum sys) L (fun _ => true) &&
  L.all fun s => p s ||
    (f (h s) && enabledB sys s (h s) &&
      (Exec.successors sys s).all fun (l, t) =>
        (l != h s || p t || decide (V t < V s)) &&
        (p t || decide (V t < V s) || (V t == V s && h t == h s)))

theorem checkRanking_sound {sys : Sys} {f : Label → Bool} {p : State → Bool} {L : List State}
    {V : State → Nat} {h : State → Label} (hc : checkRanking sys f p L V h = true) :
    ∀ r : LTS.Run (Sys.lts sys), r.WeakFair (fairOf f) → (□◇ (fun s => p s = true)) r := by
  unfold checkRanking at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hcl, hall⟩ := hc
  have hinL : ∀ s, (Sys.lts sys).Reach s → s ∈ L := by
    have := checkClosed_sound (Exec.enum sys) L (fun s => decide (s ∈ L)) (by
      simp only [checkClosed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hcl ⊢
      exact ⟨hcl.1, fun s hs => hs⟩)
    intro s hs
    simpa using this s hs
  have key : ∀ s, (Sys.lts sys).Reach s → ¬ p s = true →
      f (h s) = true ∧ enabledB sys s (h s) = true ∧
      ∀ l t, (l, t) ∈ Exec.successors sys s →
        (l ≠ h s ∨ p t = true ∨ V t < V s) ∧ (p t = true ∨ V t < V s ∨ (V t = V s ∧ h t = h s)) := by
    intro s hs hp
    have := List.all_eq_true.mp hall s (hinL s hs)
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq, beq_iff_eq] at this
    rcases this with h1 | ⟨⟨h1, h2⟩, h3⟩
    · exact absurd h1 hp
    · refine ⟨h1, h2, fun l t hm => ?_⟩
      have := h3 (l, t) hm
      simp only at this
      simpa only [or_assoc] using this
  refine response_of_ranking V h ?_ ?_ ?_
  · intro s hs hp
    obtain ⟨h1, h2, _⟩ := key s hs hp
    exact ⟨h1, enabledB_iff.mp h2⟩
  · intro s t hs hp hst
    obtain ⟨_, _, h3⟩ := key s hs hp
    rcases (h3 _ _ (successors_complete hst)).1 with h | h | h
    · exact absurd rfl h
    · exact .inl h
    · exact .inr h
  · intro s a t hs hp hst
    obtain ⟨_, _, h3⟩ := key s hs hp
    exact (h3 _ _ (successors_complete hst)).2

/-- A ranking of the reachable states `L` towards `p`, computed backwards from the states that
satisfy it: a state violating `p` gets rank `k + 1` and helpful label `l` when `l` is fair, enabled,
and every `l`-step leads to `p` or to a state of rank at most `k`. States that never get a rank keep
none. -/
def rankingOf (sys : Sys) (f : Label → Bool) (p : State → Bool) (L : List State) :
    Std.HashMap State (Nat × Label) := Id.run do
  let mut rk : Std.HashMap State (Nat × Label) := {}
  for s in L do
    if p s then rk := rk.insert s (0, stutterLabel)
  for k in [0:L.length + 1] do
    let mut changed := false
    for s in L do
      if !rk.contains s then
        let succ := Exec.successors sys s
        let labels := (succ.map (·.1)).eraseDups.filter f
        let ok := labels.find? fun l => succ.all fun (l', t) => l' != l ||
          (match rk.get? t with | some (v, _) => decide (v ≤ k) | none => false)
        match ok with
        | some l =>
          rk := rk.insert s (k + 1, l)
          changed := true
        | none => pure ()
    if !changed && k > 0 then break
  return rk

/-- **The ranking search**: the reachable states (an empty frontier within the bound and the cap),
a ranking and helpful labels for them, and the check `checkRanking`. -/
def rankProves (sys : Sys) (f : Label → Bool) (p : State → Bool) (bound cap : Nat) : Bool :=
  match reachable (Exec.gen sys) bound cap with
  | none => false
  | some L =>
    let rk := rankingOf sys f p L
    checkRanking sys f p L (fun s => ((rk.get? s).map (·.1)).getD 0)
      (fun s => ((rk.get? s).map (·.2)).getD stutterLabel)

/-- **The ranking search is sound**: when it succeeds, every weakly fair run is in `p` infinitely
often. -/
theorem rankProves_sound {sys : Sys} {f : Label → Bool} {p : State → Bool} {bound cap : Nat}
    (h : rankProves sys f p bound cap = true) :
    ∀ r : LTS.Run (Sys.lts sys), r.WeakFair (fairOf f) → (□◇ (fun s => p s = true)) r := by
  unfold rankProves at h
  split at h
  · cases h
  · exact checkRanking_sound h

end Exegra.Core.Behav

/-- info: 'Exegra.Core.Behav.checkLasso_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.checkLasso_sound

/-- info: 'Exegra.Core.Behav.lassoSearch_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.lassoSearch_sound

/-- info: 'Exegra.Core.Behav.lassoSearch_refutes_FG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.lassoSearch_refutes_FG

/-- info: 'Exegra.Core.Behav.lassoSearch_refutes_GF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.lassoSearch_refutes_GF

/-- info: 'Exegra.Core.Behav.checkRanking_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.checkRanking_sound

/-- info: 'Exegra.Core.Behav.rankProves_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.Core.Behav.rankProves_sound
