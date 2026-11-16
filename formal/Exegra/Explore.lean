import Exegra.Semantics
import Std.Data.HashSet

/-
Exhaustive exploration of a scenario, and its soundness.

One scenario run is deterministic: its scripted steps and its faults decide every step. A
scenario admits more than that one run, and this file says exactly which other runs:

* **(a) Order of simultaneous events.** When several pending entries have the time of the head
  of the queue, any one of them may be delivered next. The deterministic `step` always delivers
  the head (the entry scheduled first); a choice `k > 0` delivers the `k`-th entry instead, by
  moving it to the front and taking the same deterministic step.
* **(b) Which faults fire.** Each fault the scenario declares either acts in the run or does not.
  A fault with an `occurrence` therefore fires at that occurrence or not at all; a fault without
  one acts at every match or not at all; an `inject-event` fault queues its event or does not.
  The engine input (format version 1) carries no bound of the scenario's fault model, so every
  subset of the declared faults is allowed. The subset is chosen once, at the start of a run, as
  a mask over `env.faults`; the all-true mask is the scenario's own fault set.

A state of the exploration is a `State`: the fault mask and the semantic configuration
(`Config`). `successors` lists the states one step away, `Reachable env n` is the inductive set
of states reachable within `n` steps, and `step_mem_successors` proves that the deterministic
`step` is one of the successors (choice `k = 0` under the all-true mask).

`explore env inv bound maxStates` is a breadth-first search with a visited set (a hash set of
states, compared by decidable equality). It checks `inv` on every state it discovers and returns
* `holds n`: no state reachable within `bound` steps violates `inv`; `n` distinct states were
  visited (`explore_sound`);
* `counterexample p`: `p` is a fault mask and a list of choices that, replayed from the initial
  state of that mask, is a run of the successor relation of at most `bound` steps that ends in a
  state violating `inv` (`explore_counterexample_real`);
* `incomplete n`: the visited set reached `maxStates` before the search finished. Nothing is
  claimed. The search is total: its recursion is on the depth (at most `bound` layers), and the
  visited set never grows past `maxStates`.
-/

namespace Exegra

/-! ## Decidable equality and hashing of configurations -/

mutual
/-- Structural equality of values (identities included; numbers by their IEEE bit pattern as
the logical model of `Float` sees it, so `0` and `-0` differ and NaN equals NaN). -/
def Value.beq : Value → Value → Bool
  | .undef, .undef => true
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .num a, .num b => decide (a = b)
  | .str a, .str b => a == b
  | .arr i xs, .arr j ys => i == j && Value.beqList xs ys
  | .obj i fs, .obj j gs => i == j && Value.beqFields fs gs
  | _, _ => false

def Value.beqList : List Value → List Value → Bool
  | [], [] => true
  | x :: xs, y :: ys => Value.beq x y && Value.beqList xs ys
  | _, _ => false

def Value.beqFields : List (String × Value) → List (String × Value) → Bool
  | [], [] => true
  | (k, x) :: xs, (l, y) :: ys => k == l && Value.beq x y && Value.beqFields xs ys
  | _, _ => false
end

mutual
theorem Value.eq_of_beq : (a b : Value) → Value.beq a b = true → a = b
  | .undef, .undef, _ => rfl
  | .null, .null, _ => rfl
  | .bool a, .bool b, h => by simp [Value.beq] at h; rw [h]
  | .num a, .num b, h => by simp [Value.beq] at h; rw [h]
  | .str a, .str b, h => by simp [Value.beq] at h; rw [h]
  | .arr i xs, .arr j ys, h => by
    simp only [Value.beq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, Value.eq_of_beqList xs ys h.2]
  | .obj i fs, .obj j gs, h => by
    simp only [Value.beq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, Value.eq_of_beqFields fs gs h.2]
  | .undef, .null, h | .undef, .bool _, h | .undef, .num _, h | .undef, .str _, h
  | .undef, .arr .., h | .undef, .obj .., h
  | .null, .undef, h | .null, .bool _, h | .null, .num _, h | .null, .str _, h
  | .null, .arr .., h | .null, .obj .., h
  | .bool _, .undef, h | .bool _, .null, h | .bool _, .num _, h | .bool _, .str _, h
  | .bool _, .arr .., h | .bool _, .obj .., h
  | .num _, .undef, h | .num _, .null, h | .num _, .bool _, h | .num _, .str _, h
  | .num _, .arr .., h | .num _, .obj .., h
  | .str _, .undef, h | .str _, .null, h | .str _, .bool _, h | .str _, .num _, h
  | .str _, .arr .., h | .str _, .obj .., h
  | .arr .., .undef, h | .arr .., .null, h | .arr .., .bool _, h | .arr .., .num _, h
  | .arr .., .str _, h | .arr .., .obj .., h
  | .obj .., .undef, h | .obj .., .null, h | .obj .., .bool _, h | .obj .., .num _, h
  | .obj .., .str _, h | .obj .., .arr .., h => by simp [Value.beq] at h

theorem Value.eq_of_beqList : (xs ys : List Value) → Value.beqList xs ys = true → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [Value.beqList, Bool.and_eq_true] at h
    rw [Value.eq_of_beq x y h.1, Value.eq_of_beqList xs ys h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [Value.beqList] at h

theorem Value.eq_of_beqFields : (xs ys : List (String × Value)) → Value.beqFields xs ys = true → xs = ys
  | [], [], _ => rfl
  | (k, x) :: xs, (l, y) :: ys, h => by
    simp only [Value.beqFields, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1, Value.eq_of_beq x y h.1.2, Value.eq_of_beqFields xs ys h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [Value.beqFields] at h
end

mutual
theorem Value.beq_refl : (a : Value) → Value.beq a a = true
  | .undef | .null => rfl
  | .bool _ | .num _ | .str _ => by simp [Value.beq]
  | .arr i xs => by simp [Value.beq, Value.beqList_refl xs]
  | .obj i fs => by simp [Value.beq, Value.beqFields_refl fs]

theorem Value.beqList_refl : (xs : List Value) → Value.beqList xs xs = true
  | [] => rfl
  | x :: xs => by simp [Value.beqList, Value.beq_refl x, Value.beqList_refl xs]

theorem Value.beqFields_refl : (xs : List (String × Value)) → Value.beqFields xs xs = true
  | [] => rfl
  | (k, x) :: xs => by simp [Value.beqFields, Value.beq_refl x, Value.beqFields_refl xs]
end

instance : DecidableEq Value := fun a b =>
  if h : Value.beq a b = true then Decidable.isTrue (Value.eq_of_beq a b h)
  else Decidable.isFalse (fun e => h (e ▸ Value.beq_refl a))

/-- Floats hash by their bit pattern. -/
instance : Hashable Float := ⟨fun x => hash x.toBits⟩

mutual
def Value.hashV : Value → UInt64
  | .undef => 11
  | .null => 13
  | .bool b => mixHash 17 (hash b)
  | .num x => mixHash 19 (hash x)
  | .str s => mixHash 23 (hash s)
  | .arr i xs => mixHash (mixHash 29 (hash i)) (Value.hashList xs)
  | .obj i fs => mixHash (mixHash 31 (hash i)) (Value.hashFields fs)

def Value.hashList : List Value → UInt64
  | [] => 37
  | x :: xs => mixHash (Value.hashV x) (Value.hashList xs)

def Value.hashFields : List (String × Value) → UInt64
  | [] => 41
  | (k, x) :: xs => mixHash (mixHash (hash k) (Value.hashV x)) (Value.hashFields xs)
end

instance : Hashable Value := ⟨Value.hashV⟩

deriving instance DecidableEq, Hashable for Source
deriving instance DecidableEq, Hashable for Pending
deriving instance DecidableEq, Hashable for Machine
deriving instance DecidableEq, Hashable for Configuration
deriving instance DecidableEq, Hashable for Config

/-! ## The choices a scenario admits -/

/-- The elements of `xs` whose position is `true` in the mask. -/
def pickBy : List Bool → List α → List α
  | b :: bs, x :: xs => if b then x :: pickBy bs xs else pickBy bs xs
  | _, _ => []

theorem pickBy_all : ∀ (xs : List α), pickBy (List.replicate xs.length true) xs = xs
  | [] => rfl
  | x :: xs => by simp [List.replicate, pickBy, pickBy_all xs]

/-- Every mask of length `n`, the all-true mask first. -/
def allMasks : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allMasks n).map (true :: ·) ++ (allMasks n).map (false :: ·)

/-- The fault choices of a scenario: one mask per subset of its active faults. -/
def masks (env : Env) : List (List Bool) := allMasks env.faults.length

/-- The scenario's own fault set: every active fault acts. -/
def fullMask (env : Env) : List Bool := List.replicate env.faults.length true

theorem replicate_mem_allMasks : ∀ n, List.replicate n true ∈ allMasks n
  | 0 => by simp [allMasks]
  | n + 1 => by
    simp only [allMasks, List.replicate, List.mem_append, List.mem_map]
    exact Or.inl ⟨_, replicate_mem_allMasks n, rfl⟩

theorem fullMask_mem (env : Env) : fullMask env ∈ masks env := replicate_mem_allMasks _

/-- The environment of a run in which only the faults of the mask act. -/
def withFaults (env : Env) (mask : List Bool) : Env := { env with faults := pickBy mask env.faults }

theorem withFaults_full (env : Env) : withFaults env (fullMask env) = env := by
  simp [withFaults, fullMask, pickBy_all]

/-- The first semantic configuration of a run with the given active faults: `initialConfig`
with `faults` in place of the input's own active faults. -/
def initialConfigWith (i : SimInput) (faults : List FaultIn) : Config :=
  let (pending, seq) := initialPending i faults
  let initial : Configuration := { time := 0, machines := initialMachines i, pending }
  let (conf, nid) := initial.copy 1
  { conf, seq, nid, attempts := [], delayedBy := [], taken := 0 }

/-- With the input's own faults, the initial configuration is the deterministic one. -/
theorem initialConfigWith_own (i : SimInput) :
    initialConfigWith i (envOf i).faults = (initialConfig i).2 := rfl

/-- A state of the exploration: the fault choice and the configuration. -/
structure State where
  mask : List Bool
  cfg : Config
  deriving DecidableEq, Hashable

/-- The initial state of the run with the fault choice `m`. -/
def initState (env : Env) (m : List Bool) : State :=
  { mask := m, cfg := initialConfigWith env.input (withFaults env m).faults }

/-- Deliver the `k`-th pending entry next: move it to the front of the queue. -/
def moveToFront (c : Config) : Nat → Config
  | 0 => c
  | k + 1 => match c.conf.pending[k + 1]? with
    | none => c
    | some p => { c with conf := { c.conf with pending := p :: c.conf.pending.eraseIdx (k + 1) } }

/-- May the `k`-th pending entry be delivered next? The head always may; another entry may when
its time equals the head's time. -/
def canPick (c : Config) (k : Nat) : Bool :=
  k == 0 || match c.conf.pending.head?, c.conf.pending[k]? with
    | some h, some p => p.time == h.time
    | _, _ => false

/-- The state after delivering the `k`-th pending entry, when that is allowed and the step
commits. A failed step and an empty queue have no successor. -/
def succOf (env : Env) (s : State) (k : Nat) : Option State :=
  if canPick s.cfg k then
    match step (withFaults env s.mask) (moveToFront s.cfg k) with
    | .committed _ c' => some { s with cfg := c' }
    | _ => none
  else none

/-- The successors of a state, each with the choice that leads to it. -/
def successors (env : Env) (s : State) : List (Nat × State) :=
  (List.range s.cfg.conf.pending.length).filterMap fun k => (succOf env s k).map (k, ·)

/-- The successor relation. -/
def Succ (env : Env) (s t : State) : Prop := ∃ k, (k, t) ∈ successors env s

/-- The initial states: one per fault choice. -/
def IsInit (env : Env) (s : State) : Prop := ∃ m ∈ masks env, s = initState env m

/-- States reachable from an initial state in at most `n` steps of the successor relation. -/
inductive Reachable (env : Env) : Nat → State → Prop where
  | init {n s} : IsInit env s → Reachable env n s
  | step {n s t} : Reachable env n s → Succ env s t → Reachable env (n + 1) t

theorem succOf_mask {env : Env} {s t : State} {k : Nat} (h : succOf env s k = some t) :
    t.mask = s.mask := by
  unfold succOf at h
  split at h
  · split at h
    · cases h; rfl
    all_goals cases h
  · cases h

theorem succOf_lt {env : Env} {s t : State} {k : Nat} (h : succOf env s k = some t) :
    k < s.cfg.conf.pending.length := by
  unfold succOf at h
  split at h
  · rename_i hc
    cases k with
    | zero =>
      cases hp : s.cfg.conf.pending with
      | nil =>
        simp only [moveToFront] at h
        unfold step at h
        rw [hp] at h
        cases h
      | cons _ _ => simp
    | succ k =>
      simp only [canPick] at hc
      split at hc
      · rename_i p hk
        exact (List.getElem?_eq_some_iff.mp hk).1
      · cases hc
  · cases h

theorem mem_successors {env : Env} {s t : State} {k : Nat} :
    (k, t) ∈ successors env s ↔ succOf env s k = some t := by
  unfold successors
  constructor
  · intro h
    simp only [List.mem_filterMap, List.mem_range, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨k', _, t', h1, rfl, rfl⟩ := h
    exact h1
  · intro h
    simp only [List.mem_filterMap, List.mem_range, Option.map_eq_some_iff, Prod.mk.injEq]
    exact ⟨k, succOf_lt h, t, h, rfl, rfl⟩

/-- **The deterministic step is a successor.** When no choice is taken (the scenario's own fault
set, the head of the queue delivered), the configuration `step` commits to is a successor. -/
theorem step_mem_successors {env : Env} {c c' : Config} {r : Step}
    (h : step env c = .committed r c') :
    (0, ({ mask := fullMask env, cfg := c' } : State)) ∈
      successors env { mask := fullMask env, cfg := c } := by
  rw [mem_successors]
  simp [succOf, canPick, moveToFront, withFaults_full, h]

/-- The scenario's own first configuration is an initial state. -/
theorem initial_isInit (i : SimInput) :
    IsInit (envOf i) { mask := fullMask (envOf i), cfg := (initialConfig i).2 } := by
  refine ⟨fullMask (envOf i), fullMask_mem _, ?_⟩
  simp only [initState, withFaults_full]
  rfl

theorem Reachable.mono {env : Env} {n m : Nat} {s : State} (h : Reachable env n s) (hle : n ≤ m) :
    Reachable env m s := by
  induction h generalizing m with
  | init hi => exact .init hi
  | step _ hs ih =>
    cases m with
    | zero => omega
    | succ m => exact .step (ih (by omega)) hs

/-! ## Replaying a choice sequence -/

/-- Replay choices from a state. -/
def replay (env : Env) (s : State) : List Nat → Option State
  | [] => some s
  | k :: ks => (succOf env s k).bind fun t => replay env t ks

theorem replay_append (env : Env) :
    ∀ (s : State) (ks : List Nat) (k : Nat),
      replay env s (ks ++ [k]) = (replay env s ks).bind fun t => succOf env t k
  | s, [], k => by simp [replay]
  | s, j :: ks, k => by
    simp only [replay, List.cons_append]
    cases succOf env s j with
    | none => rfl
    | some t => exact replay_append env t ks k

theorem replay_reachable (env : Env) :
    ∀ (ks : List Nat) (s t : State) (n : Nat), Reachable env n s → replay env s ks = some t →
      Reachable env (n + ks.length) t
  | [], s, t, n, hs, h => by simp [replay] at h; subst h; simpa using hs
  | k :: ks, s, t, n, hs, h => by
    simp only [replay, Option.bind_eq_some_iff] at h
    obtain ⟨u, hu, hr⟩ := h
    have := replay_reachable env ks u t (n + 1) (.step hs ⟨k, mem_successors.mpr hu⟩) hr
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem replay_mask (env : Env) :
    ∀ (ks : List Nat) (s t : State), replay env s ks = some t → t.mask = s.mask
  | [], s, t, h => by simp [replay] at h; subst h; rfl
  | k :: ks, s, t, h => by
    simp only [replay, Option.bind_eq_some_iff] at h
    obtain ⟨u, hu, hr⟩ := h
    rw [replay_mask env ks u t hr, succOf_mask hu]

/-! ## The explorer -/

/-- A counterexample: the fault choice and the delivery choices, in order. -/
structure Path where
  mask : List Bool
  picks : List Nat
  deriving DecidableEq, Repr

inductive Result where
  | holds (states : Nat)
  | counterexample (path : Path)
  | incomplete (states : Nat)
  deriving DecidableEq, Repr

/-- A frontier entry: a state and the delivery choices that led to it, latest first. -/
structure Item where
  st : State
  picks : List Nat

abbrev Visited := Std.HashSet State

/-- What adding a batch of states to the visited set gave. -/
inductive Out where
  | ok (V : Visited) (next : List Item)
  | cex (p : Path)
  | full (states : Nat)

/-- Add the states of a batch that are new: check the invariant on each (a violation ends the
search), refuse to grow past `cap`, and queue each new state for the next layer. -/
def addAll (inv : Config → Bool) (cap : Nat) (mk : α → Item) (cexOf : α → Path) :
    List α → Visited → List Item → Out
  | [], V, nx => .ok V nx
  | a :: as, V, nx =>
    if V.contains (mk a).st then addAll inv cap mk cexOf as V nx
    else if inv (mk a).st.cfg then
      if cap ≤ V.size then .full V.size
      else addAll inv cap mk cexOf as (V.insert (mk a).st) (mk a :: nx)
    else .cex (cexOf a)

/-- The frontier entry of a successor of `it`. -/
def succItem (it : Item) (a : Nat × State) : Item := { st := a.2, picks := a.1 :: it.picks }

def succCex (it : Item) (a : Nat × State) : Path := { mask := it.st.mask, picks := (a.1 :: it.picks).reverse }

/-- Expand one layer of the search. -/
def layer (env : Env) (inv : Config → Bool) (cap : Nat) : List Item → Visited → List Item → Out
  | [], V, nx => .ok V nx
  | it :: its, V, nx =>
    match addAll inv cap (succItem it) (succCex it) (successors env it.st) V nx with
    | .ok V nx => layer env inv cap its V nx
    | o => o

/-- Breadth-first search, at most `depth` more layers. -/
def bfs (env : Env) (inv : Config → Bool) (cap : Nat) : Nat → List Item → Visited → Result
  | _, [], V => .holds V.size
  | 0, _ :: _, V => .holds V.size
  | d + 1, F@(_ :: _), V =>
    match layer env inv cap F V [] with
    | .ok V' F' => bfs env inv cap d F' V'
    | .cex p => .counterexample p
    | .full n => .incomplete n

def initItem (env : Env) (m : List Bool) : Item := { st := initState env m, picks := [] }

def initCex (m : List Bool) : Path := { mask := m, picks := [] }

/-- Explore every state reachable within `bound` steps, visiting at most `maxStates` states. -/
def explore (env : Env) (inv : Config → Bool) (bound maxStates : Nat) : Result :=
  match addAll inv maxStates (initItem env) initCex (masks env) ∅ [] with
  | .ok V F => bfs env inv maxStates bound F V
  | .cex p => .counterexample p
  | .full n => .incomplete n

/-! ## Soundness -/

/-- How the visited set and the next frontier grow: nothing is lost, every new state satisfies
the invariant and is queued, and every queued entry was queued before or satisfies `P`. -/
structure Grow (inv : Config → Bool) (V V' : Visited) (nx nx' : List Item) (P : Item → Prop) :
    Prop where
  sub : ∀ s, s ∈ V → s ∈ V'
  keep : ∀ j, j ∈ nx → j ∈ nx'
  fresh : ∀ s, s ∈ V' → s ∉ V → inv s.cfg = true ∧ ∃ j ∈ nx', j.st = s
  items : ∀ j, j ∈ nx' → j ∈ nx ∨ (j.st ∈ V' ∧ P j)

theorem Grow.refl {inv : Config → Bool} {V : Visited} {nx : List Item} {P : Item → Prop} :
    Grow inv V V nx nx P :=
  ⟨fun _ h => h, fun _ h => h, fun _ h h' => absurd h h', fun _ h => Or.inl h⟩

theorem Grow.trans {inv : Config → Bool} {V₁ V₂ V₃ : Visited} {n₁ n₂ n₃ : List Item}
    {P : Item → Prop} (g₁ : Grow inv V₁ V₂ n₁ n₂ P) (g₂ : Grow inv V₂ V₃ n₂ n₃ P) :
    Grow inv V₁ V₃ n₁ n₃ P where
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

theorem Grow.mono {inv : Config → Bool} {V V' : Visited} {nx nx' : List Item} {P Q : Item → Prop}
    (g : Grow inv V V' nx nx' P) (hpq : ∀ j, P j → Q j) : Grow inv V V' nx nx' Q where
  sub := g.sub
  keep := g.keep
  fresh := g.fresh
  items j h := (g.items j h).imp id fun ⟨hv, hp⟩ => ⟨hv, hpq j hp⟩

theorem addAll_ok {inv : Config → Bool} {cap : Nat} {mk : α → Item} {cexOf : α → Path} :
    ∀ (L : List α) (V V' : Visited) (nx nx' : List Item),
      addAll inv cap mk cexOf L V nx = .ok V' nx' →
      Grow inv V V' nx nx' (fun j => ∃ a ∈ L, j = mk a) ∧ ∀ a ∈ L, (mk a).st ∈ V'
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
          have g0 : Grow inv V (V.insert (mk a).st) nx (mk a :: nx)
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

theorem addAll_cex {inv : Config → Bool} {cap : Nat} {mk : α → Item} {cexOf : α → Path} :
    ∀ (L : List α) (V : Visited) (nx : List Item) (p : Path),
      addAll inv cap mk cexOf L V nx = .cex p → ∃ a ∈ L, inv (mk a).st.cfg = false ∧ p = cexOf a
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

/-- What a layer's new entries satisfy: each is a successor of an entry of the layer. -/
def FromLayer (env : Env) (F : List Item) (j : Item) : Prop :=
  ∃ it ∈ F, ∃ a ∈ successors env it.st, j = succItem it a

theorem layer_ok {env : Env} {inv : Config → Bool} {cap : Nat} :
    ∀ (F : List Item) (V V' : Visited) (nx nx' : List Item),
      layer env inv cap F V nx = .ok V' nx' →
      Grow inv V V' nx nx' (FromLayer env F) ∧
        ∀ it ∈ F, ∀ a ∈ successors env it.st, a.2 ∈ V'
  | [], V, V', nx, nx', h => by
    simp only [layer, Out.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Grow.refl, by simp⟩
  | it :: its, V, V', nx, nx', h => by
    simp only [layer] at h
    cases h1 : addAll inv cap (succItem it) (succCex it) (successors env it.st) V nx with
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

theorem layer_cex {env : Env} {inv : Config → Bool} {cap : Nat} :
    ∀ (F : List Item) (V : Visited) (nx : List Item) (p : Path),
      layer env inv cap F V nx = .cex p →
      ∃ it ∈ F, ∃ a ∈ successors env it.st, inv a.2.cfg = false ∧ p = succCex it a
  | [], V, nx, p, h => by simp [layer] at h
  | it :: its, V, nx, p, h => by
    simp only [layer] at h
    cases h1 : addAll inv cap (succItem it) (succCex it) (successors env it.st) V nx with
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

/-- A frontier entry is the end of a replayable run from an initial state. -/
def PathOK (env : Env) (j : Item) : Prop :=
  j.st.mask ∈ masks env ∧ replay env (initState env j.st.mask) j.picks.reverse = some j.st

/-- The invariant of the search after `d` layers with visited set `V` and frontier `F`. -/
structure BfsInv (env : Env) (inv : Config → Bool) (d : Nat) (V : Visited) (F : List Item) :
    Prop where
  holds : ∀ s, s ∈ V → inv s.cfg = true
  covers : ∀ s, Reachable env d s → s ∈ V
  frontier : ∀ j ∈ F, j.st ∈ V ∧ PathOK env j ∧ j.picks.length ≤ d
  closed : ∀ s, s ∈ V → (∀ j ∈ F, j.st ≠ s) → ∀ a ∈ successors env s, a.2 ∈ V

theorem BfsInv.next {env : Env} {inv : Config → Bool} {cap d : Nat} {V V' : Visited}
    {F F' : List Item} (bi : BfsInv env inv d V F) (h : layer env inv cap F V [] = .ok V' F') :
    BfsInv env inv (d + 1) V' F' := by
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
      by_cases hf : ∃ j ∈ F, j.st = s
      · obtain ⟨j, hj, rfl⟩ := hf
        exact cov j hj (k, t) hk
      · exact g.sub _ (bi.closed s hsV (fun j hj e => hf ⟨j, hj, e⟩) (k, t) hk)
  · intro j hj
    rcases g.items j hj with h0 | ⟨hv, it, hit, a, ha, rfl⟩
    · cases h0
    · obtain ⟨_, ⟨hm, hr⟩, hl⟩ := bi.frontier it hit
      have hsucc := mem_successors.mp ha
      have hmask : a.2.mask = it.st.mask := succOf_mask hsucc
      refine ⟨hv, ⟨?_, ?_⟩, ?_⟩
      · simpa [succItem, hmask] using hm
      · simp only [succItem, List.reverse_cons, hmask]
        rw [replay_append, hr]
        simpa using hsucc
      · simp [succItem]; omega
  · intro s hs hnf a ha
    by_cases hv : s ∈ V
    · by_cases hf : ∃ j ∈ F, j.st = s
      · obtain ⟨j, hj, rfl⟩ := hf
        exact cov j hj a ha
      · exact g.sub _ (bi.closed s hv (fun j hj e => hf ⟨j, hj, e⟩) a ha)
    · obtain ⟨_, j, hj, e⟩ := g.fresh s hs hv
      exact absurd e (hnf j hj)

theorem bfs_sound {env : Env} {inv : Config → Bool} {cap : Nat} :
    ∀ (r d : Nat) (F : List Item) (V : Visited) (n : Nat),
      BfsInv env inv d V F → bfs env inv cap r F V = .holds n →
      ∀ s, Reachable env (d + r) s → inv s.cfg = true
  | r, d, [], V, n, bi, _, s, hs => by
    apply bi.holds
    have key : ∀ m t, Reachable env m t → t ∈ V := by
      intro m t ht
      induction ht with
      | init hi => exact bi.covers _ (.init hi)
      | step _ hst ih =>
        obtain ⟨k, hk⟩ := hst
        exact bi.closed _ ih (by simp) _ hk
    exact key _ _ hs
  | 0, d, _ :: _, V, n, bi, _, s, hs => bi.holds s (bi.covers s hs)
  | r + 1, d, it :: its, V, n, bi, h, s, hs => by
    simp only [bfs] at h
    split at h
    · rename_i V' F' hl
      have := bfs_sound r (d + 1) F' V' n (bi.next hl) h s
      exact this (by simpa [Nat.add_assoc, Nat.add_comm 1] using hs)
    · cases h
    · cases h

/-- The run a counterexample stands for: replayed from the initial state of its fault choice, it
ends in a state where the invariant is false, within the bound. -/
def CexOK (env : Env) (inv : Config → Bool) (bound : Nat) (p : Path) : Prop :=
  p.mask ∈ masks env ∧ p.picks.length ≤ bound ∧
    ∃ t, replay env (initState env p.mask) p.picks = some t ∧ inv t.cfg = false

theorem bfs_cex {env : Env} {inv : Config → Bool} {cap : Nat} :
    ∀ (r d : Nat) (F : List Item) (V : Visited) (p : Path),
      BfsInv env inv d V F → bfs env inv cap r F V = .counterexample p → CexOK env inv (d + r) p
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
        rw [replay_append, hr]
        simpa using mem_successors.mp ha
    · cases h

theorem init_inv {env : Env} {inv : Config → Bool} {cap : Nat} {V : Visited} {F : List Item}
    (h : addAll inv cap (initItem env) initCex (masks env) ∅ [] = .ok V F) :
    BfsInv env inv 0 V F := by
  obtain ⟨g, cov⟩ := addAll_ok _ _ _ _ _ h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    exact (g.fresh s hs (Std.HashSet.not_mem_empty)).1
  · intro s hs
    cases hs with
    | init hi =>
      obtain ⟨m, hm, rfl⟩ := hi
      exact cov m hm
  · intro j hj
    rcases g.items j hj with h0 | ⟨hv, m, hm, rfl⟩
    · cases h0
    · exact ⟨hv, ⟨by simpa [initItem, initState] using hm, by simp [initItem, initState, replay]⟩,
        by simp [initItem]⟩
  · intro s hs hnf
    obtain ⟨_, j, hj, e⟩ := g.fresh s hs Std.HashSet.not_mem_empty
    exact absurd e (hnf j hj)

/-- **Soundness of the explorer.** If it reports that the invariant holds, the invariant holds
in every state reachable within the bound: for every fault choice and every order of delivery of
simultaneous events. -/
theorem explore_sound {env : Env} {inv : Config → Bool} {bound maxStates n : Nat}
    (h : explore env inv bound maxStates = .holds n) :
    ∀ s, Reachable env bound s → inv s.cfg = true := by
  unfold explore at h
  split at h
  · rename_i V F hi
    have := bfs_sound bound 0 F V n (init_inv hi) h
    simpa using this
  · cases h
  · cases h

/-- **Counterexamples are real.** A reported counterexample names an initial state (a fault
choice of the scenario) and a sequence of delivery choices that is a run of the successor
relation of at most `bound` steps, ending in a reachable state where the invariant is false. -/
theorem explore_counterexample_real {env : Env} {inv : Config → Bool} {bound maxStates : Nat}
    {p : Path} (h : explore env inv bound maxStates = .counterexample p) :
    IsInit env (initState env p.mask) ∧ p.picks.length ≤ bound ∧
      ∃ t, replay env (initState env p.mask) p.picks = some t ∧ inv t.cfg = false ∧
        Reachable env bound t := by
  have hok : CexOK env inv bound p := by
    unfold explore at h
    split at h
    · rename_i V F hi
      simpa using bfs_cex bound 0 F V p (init_inv hi) h
    · rename_i q hc
      simp only [Result.counterexample.injEq] at h
      subst h
      obtain ⟨m, hm, hi, rfl⟩ := addAll_cex _ _ _ _ hc
      exact ⟨hm, by simp [initCex], initState env m, by simp [initCex, replay],
        by simpa [initItem, initCex] using hi⟩
    · cases h
  obtain ⟨hm, hlen, t, hr, hi⟩ := hok
  have hinit : IsInit env (initState env p.mask) := ⟨p.mask, hm, rfl⟩
  refine ⟨hinit, hlen, t, hr, hi, ?_⟩
  have := replay_reachable env p.picks _ t 0 (.init hinit) hr
  exact this.mono (by omega)

/-- Soundness for configurations: every configuration of every run within the bound satisfies
the invariant. In particular, every configuration of the deterministic run does. -/
theorem explore_sound_config {env : Env} {inv : Config → Bool} {bound maxStates n : Nat}
    (h : explore env inv bound maxStates = .holds n) :
    ∀ m c, Reachable env bound { mask := m, cfg := c } → inv c = true :=
  fun _ _ hr => explore_sound h _ hr

/-! ## Axiom check -/

/-- info: 'Exegra.explore_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms explore_sound

/-- info: 'Exegra.explore_counterexample_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms explore_counterexample_real

/-- info: 'Exegra.step_mem_successors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_mem_successors

end Exegra
