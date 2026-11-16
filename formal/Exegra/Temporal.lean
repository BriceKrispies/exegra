import Exegra.Prove
import Exegra.Search

/-
Temporal claims over every run of a scenario, and the soundness of checking them.

`checkTrace` (`src/core/claims.js`) evaluates three temporal forms on one trace; this file
defines the same forms over every run of the choice relation of `Explore` (the order of
simultaneous events and the fault masks), checks them with the generic search of `Search`, and
proves the check sound.

**Matchers.** `event e` occurs in a step that delivers `e` (a failed delivery counts: its record
is the last step of its trace); `transition t` occurs in a step whose `fired` has `t`.

**Forms** (`TraceHolds`, over the steps of a run and its final configuration):
* `never m`: no step has `m`.
* `precedes a b`: every step with `b` has a step with `a` strictly before it, or, when `a` is an
  event and `b` a transition (the event is delivered before the transition fires), `a` in the
  same step.
* `eventually occurs expr`: some step has `occurs` (when given) and `expr` is true in the final
  configuration (when given). The final configuration is the one the run ends in (for a run
  ended by a failed step, the one before that step).

**Runs.** A run is a fault mask and delivery picks, replayed with `runRec`: the steps taken, the
state it ends in, and whether its last step failed. It is *complete* (`Ended`) when it ended
because its queue is empty (quiescent), its step limit is reached, or its last step failed.

**Monitor.** The search runs over `Node`s: the explorer's state with a monitor (`Mon`: a flag
for the first/occurs matcher seen and a sticky violation flag) and a flag for a failed last
step. The monitor is the fold of `Form.monStep` over the steps (`greplay_nodes`), and agrees
with the trace-level definition (`never_monitor`, `precedes_monitor`, `seen_monitor`).

**Verdicts** (`tcheck`). `holds`: every complete run satisfies the form (`tcheck_sound`);
`counterexample`: a real run violating it (`tcheck_counterexample_real`). A run that ends
without quiescence (step limit, failed step) and would violate or cannot decide an `eventually`
makes the verdict `incomplete`, as does the bound cutting off a path, the state budget and a
non-boolean `expr`.
-/

namespace Exegra

set_option linter.unusedSimpArgs false

open Gen

/-! ## Forms on traces -/

inductive Matcher where
  | event (id : String)
  | transition (id : String)

def Matcher.hit : Matcher → Step → Bool
  | .event e, r => decide (r.kind = .deliver) && r.event.id == e
  | .transition t, r => r.fired.any (·.transition == t)

inductive Form where
  | never (m : Matcher)
  | precedes (first thn : Matcher)
  | eventually (occurs : Option Matcher) (expr : Option String)

/-- An event is delivered before the transitions it triggers fire, so a delivery of the first
event in the same step counts as earlier. -/
def sameStepOk : Matcher → Matcher → Bool
  | .event _, .transition _ => true
  | _, _ => false

/-- Is the expression (source text) `true`, `false`, or neither (it does not parse, errors or
is not a boolean) in a configuration? -/
def evalB (src : String) (c : Config) : Option Bool :=
  match parseExpr src with
  | .ok ast =>
    match eval (claimResolve c.conf) ast with
    | .ok (.bool b) => some b
    | _ => none
  | .error _ => none

def TraceHolds : Form → List Step → Config → Prop
  | .never m, steps, _ => ∀ r ∈ steps, m.hit r = false
  | .precedes a b, steps, _ =>
    ∀ pre r post, steps = pre ++ r :: post → b.hit r = true →
      (∃ q ∈ pre, a.hit q = true) ∨ (sameStepOk a b = true ∧ a.hit r = true)
  | .eventually o e, steps, fin =>
    (∀ m, o = some m → ∃ r ∈ steps, m.hit r = true) ∧
      (∀ x, e = some x → evalB x fin = some true)

/-- What a counterexample shows. `never` and `precedes`: the property is false. `eventually`:
a required occurrence is absent, or the expression is false (not merely undecided) in the
final configuration. -/
def TraceViolates : Form → List Step → Config → Prop
  | .never m, steps, c => ¬ TraceHolds (.never m) steps c
  | .precedes a b, steps, c => ¬ TraceHolds (.precedes a b) steps c
  | .eventually o e, steps, fin =>
    (∃ m, o = some m ∧ ∀ r ∈ steps, m.hit r = false) ∨ (∃ x, e = some x ∧ evalB x fin = some false)

/-! ## The monitor -/

structure Mon where
  seen : Bool
  viol : Bool
  deriving DecidableEq, Hashable

def Form.watch : Form → Option Matcher
  | .never _ => none
  | .precedes a _ => some a
  | .eventually o _ => o

def Form.monInit (f : Form) : Mon :=
  { seen := match f with | .eventually none _ => true | _ => false, viol := false }

def Form.monStep (f : Form) (m : Mon) (r : Step) : Mon :=
  let hitW := match f.watch with | some w => w.hit r | none => false
  let v := match f with
    | .never x => x.hit r
    | .precedes a b => b.hit r && !(m.seen || (sameStepOk a b && hitW))
    | .eventually .. => false
  { seen := m.seen || hitW, viol := m.viol || v }

theorem seen_fold (f : Form) :
    ∀ (steps : List Step) (m : Mon),
      (steps.foldl f.monStep m).seen =
        (m.seen || steps.any fun r => match f.watch with | some w => w.hit r | none => false)
  | [], m => by simp
  | r :: rs, m => by
    simp only [List.foldl_cons, List.any_cons]
    rw [seen_fold f rs]
    simp [Form.monStep, Bool.or_assoc]

theorem viol_fold_never (x : Matcher) :
    ∀ (steps : List Step) (m : Mon),
      (steps.foldl (Form.never x).monStep m).viol = (m.viol || steps.any x.hit)
  | [], m => by simp
  | r :: rs, m => by
    simp only [List.foldl_cons, List.any_cons]
    rw [viol_fold_never x rs]
    simp [Form.monStep, Bool.or_assoc]

/-- The monitor of `never` agrees with the trace-level definition. -/
theorem never_monitor (x : Matcher) (steps : List Step) (c : Config) :
    (steps.foldl (Form.never x).monStep (Form.never x).monInit).viol = false ↔
      TraceHolds (.never x) steps c := by
  rw [viol_fold_never]
  simp [Form.monInit, TraceHolds]


theorem decomp_cons {α : Type} (s : α) (rest : List α) (P : List α → α → Prop) :
    (∀ pre r post, s :: rest = pre ++ r :: post → P pre r) ↔
      (P [] s ∧ ∀ pre r post, rest = pre ++ r :: post → P (s :: pre) r) := by
  constructor
  · intro h
    exact ⟨h [] s rest rfl, fun pre r post he => h (s :: pre) r post (by simp [he])⟩
  · rintro ⟨h0, h1⟩ pre r post he
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      exact h0
    | cons q pre' =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      exact h1 pre' r post he

/-- The monitor of `precedes`, from any monitor state. -/
theorem viol_fold_precedes (a b : Matcher) :
    ∀ (steps : List Step) (m : Mon),
      (steps.foldl (Form.precedes a b).monStep m).viol = false ↔
        m.viol = false ∧ ∀ pre r post, steps = pre ++ r :: post → b.hit r = true →
          (m.seen = true ∨ ∃ q ∈ pre, a.hit q = true) ∨ (sameStepOk a b = true ∧ a.hit r = true)
  | [], m => by simp
  | s :: rest, m => by
    simp only [List.foldl_cons]
    rw [viol_fold_precedes a b rest]
    rw [decomp_cons s rest (fun pre r => b.hit r = true →
          (m.seen = true ∨ ∃ q ∈ pre, a.hit q = true) ∨ (sameStepOk a b = true ∧ a.hit r = true))]
    simp only [Form.monStep, Form.watch]
    have hy : (∀ pre r post, rest = pre ++ r :: post → b.hit r = true →
          ((m.seen || a.hit s) = true ∨ ∃ q ∈ pre, a.hit q = true) ∨ (sameStepOk a b = true ∧ a.hit r = true)) ↔
        (∀ pre r post, rest = pre ++ r :: post → b.hit r = true →
          (m.seen = true ∨ ∃ q ∈ s :: pre, a.hit q = true) ∨ (sameStepOk a b = true ∧ a.hit r = true)) := by
      constructor
      · intro h pre r post he hb
        have := h pre r post he hb
        simp only [Bool.or_eq_true, List.mem_cons, exists_eq_or_imp] at this ⊢
        grind
      · intro h pre r post he hb
        have := h pre r post he hb
        simp only [Bool.or_eq_true, List.mem_cons, exists_eq_or_imp] at this ⊢
        grind
    rw [hy]
    simp only [List.not_mem_nil, false_and, exists_false, or_false, Bool.or_eq_false_iff,
      Bool.or_eq_true]
    cases hv : m.viol <;> cases hs : m.seen <;> cases ha : a.hit s <;> cases hb : b.hit s <;>
      cases hss : sameStepOk a b <;> simp [hv, hs, ha, hb, hss]

theorem precedes_monitor (a b : Matcher) (steps : List Step) (c : Config) :
    (steps.foldl (Form.precedes a b).monStep (Form.precedes a b).monInit).viol = false ↔
      TraceHolds (.precedes a b) steps c := by
  rw [viol_fold_precedes]
  simp [Form.monInit, TraceHolds]

/-- The monitor of `eventually`: the first matcher was seen. -/
theorem seen_monitor (f : Form) (steps : List Step) (m : Matcher) (h : f.watch = some m) :
    (steps.foldl f.monStep f.monInit).seen = true →
      f.monInit.seen = true ∨ ∃ r ∈ steps, m.hit r = true := by
  rw [seen_fold, h]
  simp [List.any_eq_true]

/-! ## Runs of the choice relation -/

/-- One step with its record. A committed step moves on; a failed step ends the run. Nothing
is taken at or after the scenario's step limit. -/
inductive Move where
  | ok (r : Step) (t : State)
  | fail (r : Step)

def move (env : Env) (lim : Nat) (s : State) (k : Nat) : Option Move :=
  if lim ≤ s.cfg.taken then none
  else if canPick s.cfg k then
    match step (withFaults env s.mask) (moveToFront s.cfg k) with
    | .committed r c' => some (.ok r { s with cfg := c' })
    | .failed r => some (.fail r)
    | .idle => none
  else none

/-- The run of the picks `ks` from `s`: its steps (the failed one last), the state it ends in
(for a failed last step, the state before it) and whether the last step failed. -/
def runRec (env : Env) (lim : Nat) : State → List Nat → Option (List Step × State × Bool)
  | s, [] => some ([], s, false)
  | s, k :: ks =>
    match move env lim s k with
    | some (.ok r t) => (runRec env lim t ks).map fun (rs, f, e) => (r :: rs, f, e)
    | some (.fail r) => if ks.isEmpty then some ([r], s, true) else none
    | none => none

/-- A run is complete when its queue is empty (quiescent), its step limit is reached, or its
last step failed. -/
def Ended (lim : Nat) (fin : State) (err : Bool) : Prop :=
  err = true ∨ fin.cfg.conf.pending = [] ∨ lim ≤ fin.cfg.taken

/-- The picks of a run without a failed step are a replay of the explorer's successor relation. -/
theorem runRec_replay (env : Env) (lim : Nat) :
    ∀ (ks : List Nat) (s : State) (steps : List Step) (fin : State),
      runRec env lim s ks = some (steps, fin, false) → replay env s ks = some fin
  | [], s, steps, fin, h => by simp [runRec] at h; obtain ⟨-, rfl, -⟩ := h; rfl
  | k :: ks, s, steps, fin, h => by
    simp only [runRec] at h
    split at h
    · rename_i r t hm
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨rs, f, e⟩, hr, he⟩ := h
      simp only [Prod.mk.injEq] at he
      have ih := runRec_replay env lim ks t rs f (by rw [hr]; simp [he.2.2])
      unfold move at hm
      split at hm
      · cases hm
      · split at hm
        · rename_i hc
          split at hm
          · rename_i r' c' hs
            cases hm
            simp [replay, succOf, hc, hs, ih, he.2.1]
          · cases hm
          · cases hm
        · cases hm
    · split at h
      · simp at h
      · cases h
    · cases h

/-! ## The product system -/

structure Node where
  st : State
  mon : Mon
  err : Bool
  deriving DecidableEq, Hashable

def nstep (f : Form) (env : Env) (lim : Nat) (n : Node) (k : Nat) : Option Node :=
  if n.err then none
  else match move env lim n.st k with
    | some (.ok r t) => some { st := t, mon := f.monStep n.mon r, err := false }
    | some (.fail r) => some { st := n.st, mon := f.monStep n.mon r, err := true }
    | none => none

theorem move_lt {env : Env} {lim : Nat} {s : State} {k : Nat} {m : Move}
    (h : move env lim s k = some m) : k < s.cfg.conf.pending.length + 1 := by
  unfold move at h
  split at h
  · cases h
  · split at h
    · rename_i hc
      cases k with
      | zero => omega
      | succ k =>
        simp only [canPick] at hc
        split at hc
        · rename_i p hk
          have := (List.getElem?_eq_some_iff.mp hk).1
          omega
        · simp at hc
    · cases h


theorem nstep_lt {f : Form} {env : Env} {lim : Nat} {n t : Node} {k : Nat}
    (h : nstep f env lim n k = some t) : k < n.st.cfg.conf.pending.length + 1 := by
  unfold nstep at h
  split at h
  · cases h
  · cases hm : move env lim n.st k with
    | none => rw [hm] at h; cases h
    | some m => exact move_lt hm

/-- The scenario's step limit as a number of steps. -/
def limOf (env : Env) : Nat := stepBound env.input.scenario.stepLimit

/-- The product system of a form: the explorer's states with a monitor. -/
def tsys (f : Form) (env : Env) : Sys Node where
  init := (masks env).map fun m => { st := initState env m, mon := f.monInit, err := false }
  width n := n.st.cfg.conf.pending.length + 1
  next := nstep f env (limOf env)
  lt _ _ _ h := nstep_lt h

/-- The monitor along a replay is the fold over the steps of the run. -/
theorem greplay_nodes (f : Form) (env : Env) :
    ∀ (ks : List Nat) (n : Node), n.err = false →
      greplay (tsys f env) n ks =
        (runRec env (limOf env) n.st ks).map fun (steps, fin, err) =>
          ({ st := fin, mon := steps.foldl f.monStep n.mon, err := err } : Node)
  | [], n, he => by cases n; simp_all [greplay, runRec]
  | k :: ks, n, he => by
    have hn : (tsys f env).next n k = nstep f env (limOf env) n k := rfl
    simp only [greplay, runRec]
    rw [hn]
    unfold nstep
    rw [he]
    simp only [Bool.false_eq_true, ite_false]
    cases hm : move env (limOf env) n.st k with
    | none => simp
    | some m =>
      cases m with
      | ok r t =>
        simp only [Option.bind_some]
        rw [greplay_nodes f env ks _ rfl]
        cases runRec env (limOf env) t ks <;> simp [List.foldl_cons]
      | fail r =>
        simp only [Option.bind_some]
        cases ks with
        | nil => simp [greplay, List.foldl_cons]
        | cons k' ks' =>
          have hn' : (tsys f env).next { st := n.st, mon := f.monStep n.mon r, err := true } k' = none := by
            show nstep f env (limOf env) { st := n.st, mon := f.monStep n.mon r, err := true } k' = none
            simp [nstep]
          simp [greplay, hn']

/-! ## Verdicts on nodes -/

def Node.quiescent (n : Node) : Bool := !n.err && n.st.cfg.conf.pending.isEmpty

def Node.terminal (lim : Nat) (n : Node) : Bool :=
  n.err || n.st.cfg.conf.pending.isEmpty || decide (lim ≤ n.st.cfg.taken)

def Form.holdsEnd (f : Form) (n : Node) : Bool :=
  match f with
  | .eventually _ e =>
    n.mon.seen && (match e with | some x => evalB x n.st.cfg == some true | none => true)
  | _ => true

/-- A node that certainly shows a violation: a violation flag, or a quiescent end of an
`eventually` that lacks its occurrence or whose expression is false. -/
def Form.bad (f : Form) (n : Node) : Bool :=
  match f with
  | .eventually _ e =>
    n.quiescent && (!n.mon.seen || (match e with | some x => evalB x n.st.cfg == some false | none => false))
  | _ => n.mon.viol

/-- A node that ends a run without quiescence, or whose expression is undecided, and does not
satisfy an `eventually`: nothing can be said, so the verdict is `incomplete`. -/
def Form.unk (lim : Nat) (f : Form) (n : Node) : Bool :=
  match f with
  | .eventually .. => n.terminal lim && !f.holdsEnd n && !f.bad n
  | _ => false

def tcheck (f : Form) (env : Env) (bound cap : Nat) : Gen.Result Node :=
  let S := tsys f env
  match search S (fun n => !f.bad n) bound cap with
  | .holds k =>
    match search S (fun n => !(f.bad n || f.unk (limOf env) n)) bound cap with
    | .holds k' => .holds k'
    | .counterexample _ => .incomplete k
    | .incomplete k' => .incomplete k'
  | r => r

theorem tcheck_holds_ok {f : Form} {env : Env} {bound cap n : Nat}
    (h : tcheck f env bound cap = .holds n) :
    ∀ m s, Reach (tsys f env) m s → f.bad s = false ∧ f.unk (limOf env) s = false := by
  unfold tcheck at h
  cases h1 : search (tsys f env) (fun n => !f.bad n) bound cap with
  | holds k =>
    simp only [h1] at h
    cases h2 : search (tsys f env) (fun n => !(f.bad n || f.unk (limOf env) n)) bound cap with
    | holds k' =>
      intro m s hs
      have := search_sound h2 m s hs
      simpa [Bool.or_eq_false_iff] using this
    | counterexample _ => simp only [h2] at h; cases h
    | incomplete _ => simp only [h2] at h; cases h
  | counterexample p => simp only [h1] at h; cases h
  | incomplete k => simp only [h1] at h; cases h

/-- The complete runs of a scenario for a fault mask and picks. -/
def CompleteRun (env : Env) (m : List Bool) (ks : List Nat) (steps : List Step) (fin : State)
    (err : Bool) : Prop :=
  m ∈ masks env ∧ runRec env (limOf env) (initState env m) ks = some (steps, fin, err) ∧
    Ended (limOf env) fin err

theorem holds_of_ok (f : Form) (lim : Nat) (steps : List Step) (fin : State) (err : Bool)
    (hend : Ended lim fin err)
    (hbad : f.bad { st := fin, mon := steps.foldl f.monStep f.monInit, err := err } = false)
    (hunk : f.unk lim { st := fin, mon := steps.foldl f.monStep f.monInit, err := err } = false) :
    TraceHolds f steps fin.cfg := by
  cases f with
  | never x =>
    simp only [Form.bad] at hbad
    exact (never_monitor x steps fin.cfg).mp (by simpa using hbad)
  | precedes a b =>
    simp only [Form.bad] at hbad
    exact (precedes_monitor a b steps fin.cfg).mp (by simpa using hbad)
  | eventually o e =>
    have hterm : Node.terminal lim
        { st := fin, mon := steps.foldl (Form.eventually o e).monStep (Form.eventually o e).monInit,
          err := err } = true := by
      rcases hend with h | h | h <;> simp [Node.terminal, h]
    have hh : (Form.eventually o e).holdsEnd
        { st := fin, mon := steps.foldl (Form.eventually o e).monStep (Form.eventually o e).monInit,
          err := err } = true := by
      simp only [Form.unk, hterm, hbad] at hunk
      cases hh : (Form.eventually o e).holdsEnd
        { st := fin, mon := steps.foldl (Form.eventually o e).monStep (Form.eventually o e).monInit,
          err := err }
      · simp [hh] at hunk
      · rfl
    simp only [Form.holdsEnd, Bool.and_eq_true] at hh
    obtain ⟨hseen, hex⟩ := hh
    rw [seen_fold] at hseen
    refine ⟨?_, ?_⟩
    · intro m hm
      subst hm
      simpa [Form.monInit, Form.watch, List.any_eq_true] using hseen
    · intro x hx
      subst hx
      simpa using hex


theorem init_mem {f : Form} {env : Env} {r : Node} (h : r ∈ (tsys f env).init) :
    ∃ m ∈ masks env, r = { st := initState env m, mon := f.monInit, err := false } := by
  simp only [tsys, List.mem_map] at h
  obtain ⟨m, hm, rfl⟩ := h
  exact ⟨m, hm, rfl⟩

/-- **Soundness of the temporal check.** If `tcheck` reports `holds`, the form holds on every
complete run of the scenario: for every fault mask and every order of delivery of simultaneous
events, each run that ends at quiescence, at the step limit or in a failed step. -/
theorem tcheck_sound {f : Form} {env : Env} {bound cap n : Nat}
    (h : tcheck f env bound cap = .holds n) :
    ∀ m ks steps fin err, CompleteRun env m ks steps fin err → TraceHolds f steps fin.cfg := by
  rintro m ks steps fin err ⟨hm, hr, hend⟩
  have hinit : ({ st := initState env m, mon := f.monInit, err := false } : Node) ∈ (tsys f env).init := by
    simp only [tsys, List.mem_map]
    exact ⟨m, hm, rfl⟩
  have hg := greplay_nodes f env ks { st := initState env m, mon := f.monInit, err := false } rfl
  rw [hr] at hg
  simp only [Option.map_some] at hg
  obtain ⟨d, hd⟩ := greplay_reach_any hinit hg
  obtain ⟨hb, hu⟩ := tcheck_holds_ok h d _ hd
  exact holds_of_ok f (limOf env) steps fin err hend hb hu

theorem tcheck_cex_first {f : Form} {env : Env} {bound cap : Nat} {p : Gen.Path Node}
    (h : tcheck f env bound cap = .counterexample p) :
    search (tsys f env) (fun n => !f.bad n) bound cap = .counterexample p := by
  unfold tcheck at h
  cases h1 : search (tsys f env) (fun n => !f.bad n) bound cap with
  | holds k =>
    simp only [h1] at h
    cases h2 : search (tsys f env) (fun n => !(f.bad n || f.unk (limOf env) n)) bound cap with
    | holds k' => simp only [h2] at h; cases h
    | counterexample _ => simp only [h2] at h; cases h
    | incomplete _ => simp only [h2] at h; cases h
  | counterexample q => simp only [h1] at h; cases h; rfl
  | incomplete k => simp only [h1] at h; cases h

/-- **Counterexamples are real.** A reported counterexample is a fault mask and delivery picks
whose run (`runRec`) violates the form (`TraceViolates`), in at most `bound` steps. For
`never` and `precedes` the run is the violating prefix (any continuation violates too); for
`eventually` it is a complete run that ends at quiescence. -/
theorem tcheck_counterexample_real {f : Form} {env : Env} {bound cap : Nat} {p : Gen.Path Node}
    (h : tcheck f env bound cap = .counterexample p) :
    p.picks.length ≤ bound ∧ ∃ m ∈ masks env, ∃ steps fin err,
      p.root = { st := initState env m, mon := f.monInit, err := false } ∧
      runRec env (limOf env) (initState env m) p.picks = some (steps, fin, err) ∧
      TraceViolates f steps fin.cfg ∧
      (∀ o e, f = .eventually o e → Ended (limOf env) fin err) := by
  obtain ⟨hroot, hlen, t, hg, hok⟩ := search_counterexample_real (tcheck_cex_first h)
  obtain ⟨m, hm, hrt⟩ := init_mem hroot
  have hg' := greplay_nodes f env p.picks p.root (by rw [hrt])
  rw [hg] at hg'
  rw [hrt] at hg'
  simp only at hg'
  cases hr : runRec env (limOf env) (initState env m) p.picks with
  | none => rw [hr] at hg'; simp at hg'
  | some v =>
    obtain ⟨steps, fin, err⟩ := v
    rw [hr] at hg'
    simp only [Option.map_some, Option.some.injEq] at hg'
    subst hg'
    have hbad : f.bad { st := fin, mon := steps.foldl f.monStep f.monInit, err := err } = true := by
      simpa using hok
    refine ⟨hlen, m, hm, steps, fin, err, hrt, hr, ?_, ?_⟩
    · cases f with
      | never x =>
        simp only [Form.bad] at hbad
        intro hh
        have := (never_monitor x steps fin.cfg).mpr hh
        simp_all
      | precedes a b =>
        simp only [Form.bad] at hbad
        intro hh
        have := (precedes_monitor a b steps fin.cfg).mpr hh
        simp_all
      | eventually o e =>
        simp only [Form.bad, Node.quiescent, Bool.and_eq_true, Bool.or_eq_true,
          Bool.not_eq_true'] at hbad
        rcases hbad.2 with hs | hx
        · left
          rw [seen_fold] at hs
          cases o with
          | none => simp [Form.monInit] at hs
          | some mm =>
            refine ⟨mm, rfl, ?_⟩
            intro r hr
            simp [Form.monInit, Form.watch] at hs
            exact hs r hr
        · right
          cases e with
          | none => simp at hx
          | some x => exact ⟨x, rfl, by simpa using hx⟩
    · intro o e hf
      subst hf
      simp only [Form.bad, Node.quiescent, Bool.and_eq_true, Bool.not_eq_true'] at hbad
      right; left
      have := hbad.1.2
      simpa [List.isEmpty_iff] using this

/-- info: 'Exegra.tcheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tcheck_sound

/-- info: 'Exegra.tcheck_counterexample_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tcheck_counterexample_real

/-- info: 'Exegra.never_monitor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms never_monitor

/-- info: 'Exegra.precedes_monitor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms precedes_monitor

/-- info: 'Exegra.seen_monitor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms seen_monitor

/-- info: 'Exegra.greplay_nodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms greplay_nodes

/-- info: 'Exegra.Gen.search_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Gen.search_sound

/-- info: 'Exegra.Gen.search_counterexample_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Gen.search_counterexample_real

/-! ## The `temporal` protocol -/

/-- The verdict of a check in a form that a generated proof file states and evaluates:
`("holds", [], [])`, `("counterexample", mask, picks)` or `("incomplete", [], [])`. -/
def tverdict (f : Form) (env : Env) (bound cap : Nat) : String × List Bool × List Nat :=
  match tcheck f env bound cap with
  | .holds _ => ("holds", [], [])
  | .counterexample p => ("counterexample", p.root.st.mask, p.picks)
  | .incomplete _ => ("incomplete", [], [])

/-- A `holds` verdict means the form holds on every complete run. -/
theorem tverdict_sound {f : Form} {env : Env} {bound cap : Nat}
    (h : tverdict f env bound cap = ("holds", [], [])) :
    ∀ m ks steps fin err, CompleteRun env m ks steps fin err → TraceHolds f steps fin.cfg := by
  unfold tverdict at h
  cases h1 : tcheck f env bound cap with
  | holds n => exact tcheck_sound h1
  | counterexample p => simp [h1] at h
  | incomplete n => simp [h1] at h

/-- A `counterexample` verdict names a real violating run. -/
theorem tverdict_real {f : Form} {env : Env} {bound cap : Nat} {mask : List Bool} {picks : List Nat}
    (h : tverdict f env bound cap = ("counterexample", mask, picks)) :
    picks.length ≤ bound ∧ mask ∈ masks env ∧ ∃ steps fin err,
      runRec env (limOf env) (initState env mask) picks = some (steps, fin, err) ∧
      TraceViolates f steps fin.cfg := by
  unfold tverdict at h
  cases h1 : tcheck f env bound cap with
  | holds n => simp [h1] at h
  | counterexample p =>
    simp only [h1, Prod.mk.injEq, true_and] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hl, m, hm, steps, fin, err, hr, hrun, hv, -⟩ := tcheck_counterexample_real h1
    have hmask : p.root.st.mask = m := by rw [hr]; rfl
    rw [hmask]
    exact ⟨hl, hm, steps, fin, err, by rw [← hmask] at hrun; simpa [hmask] using hrun, hv⟩
  | incomplete n => simp [h1] at h

/-- `{"event": id}` or `{"transition": id}`. -/
def decodeMatcher (v : Value) : Except String Matcher :=
  match v with
  | .obj _ fs =>
    match fieldOr fs "event", fieldOr fs "transition" with
    | .str e, _ => pure (.event e)
    | _, .str t => pure (.transition t)
    | _, _ => throw "temporal: a matcher needs an \"event\" or a \"transition\" string"
  | _ => throw "temporal: a matcher must be an object"

/-- A claim's `evaluate` object: `method` and its fields. -/
def decodeForm (v : Value) : Except String Form :=
  match v with
  | .obj _ fs =>
    match fieldOr fs "method" with
    | .str "never" => do pure (.never (← decodeMatcher (fieldOr fs "occurs")))
    | .str "precedes" => do
      pure (.precedes (← decodeMatcher (fieldOr fs "first")) (← decodeMatcher (fieldOr fs "then")))
    | .str "eventually" => do
      let o ← match fieldOr fs "occurs" with
        | .undef => pure none
        | m => do pure (some (← decodeMatcher m))
      let e ← match fieldOr fs "expr" with
        | .undef => pure none
        | .str x => pure (some x)
        | _ => throw "temporal: \"expr\" must be a string"
      pure (.eventually o e)
    | _ => throw "temporal: \"method\" must be never, precedes or eventually"
  | _ => throw "temporal: a claim form must be an object"

open Encode in
def temporalJson (env : Env) (id : String) (f : Form) (r : Gen.Result Node) : Value :=
  match r with
  | .holds n => o [("id", s id), ("verdict", s "holds"), ("states", nat n)]
  | .incomplete n => o [("id", s id), ("verdict", s "incomplete"), ("states", nat n)]
  | .counterexample p =>
    let m := p.root.st.mask
    let s0 := initState env m
    let steps := match runRec env (limOf env) s0 p.picks with
      | some (rs, _, _) => rs
      | none => []
    o [("id", s id), ("verdict", s "counterexample"),
       ("mask", a (m.map Value.bool)), ("picks", a (p.picks.map nat)),
       ("faults", strings (faultIdsOf env m)),
       ("initial", configuration s0.cfg.conf),
       ("steps", a (steps.map Encode.step))]

/-- One request: `{input, claims: [{id, evaluate}], bound, maxStates, emitLean?}`; the answer is
shaped like that of `runExplore`. -/
def runTemporal (text : String) : Except String String := do
  let req ← Json.parse text
  let root ← match req with
    | .obj _ fs => pure fs
    | _ => throw "temporal: the request must be an object"
  let i ← Decode.input (fieldOr root "input")
  validate i
  let env := envOf i
  let bound ← match fieldOr root "bound" with
    | .num x => pure x.toUInt64.toNat
    | _ => throw "temporal: \"bound\" must be a number"
  let cap ← match fieldOr root "maxStates" with
    | .num x => pure x.toUInt64.toNat
    | _ => throw "temporal: \"maxStates\" must be a number"
  let claims ← match fieldOr root "claims" with
    | .arr _ xs => xs.mapM fun c => match c with
      | .obj _ fs => match fieldOr fs "id" with
        | .str id => do pure (id, ← decodeForm (fieldOr fs "evaluate"))
        | _ => throw "temporal: a claim needs an \"id\" string"
      | _ => throw "temporal: a claim must be an object"
    | _ => throw "temporal: \"claims\" must be an array"
  let results := claims.map fun (id, f) => temporalJson env id f (tcheck f env bound cap)
  let emitLean := match fieldOr root "emitLean" with
    | .bool true => true
    | _ => false
  let out : Value := Encode.o ([("faults", Encode.strings (env.faults.map (·.id))),
      ("results", Encode.a results)] ++
      (if emitLean then [("leanInput", .str i.toLean)] else []))
  pure (Json.write out)

end Exegra
