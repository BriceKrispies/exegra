import Exegra.Json

/-!
# Claim verdicts and evidence status

What a claim's status is, decided from the facts recorded about it. JavaScript produces the facts
(a test run, a model check, a Lean theorem check, an author's document) and formats the result;
this file decides (WG-5684, criteria 1, 2 and 4; the lattice of the 2026-11-26 assessment,
`docs/assessment/2026-11-26/epistemics.md`, cross-challenge C3).

* `Status` is a tuple, not a word: how strong the basis is (`Strength`), what it is about
  (`Subject`), which assumptions are still open, and whether the facts describe the current files
  (`Freshness`).
* `Fact` is the schema every fact producer meets (kind, subject, target, stamps, outcome).
* `status : Claim → List Fact → Status` is the one rule, and the theorems below pin its
  properties: a conjunction takes the meet of its parts, a contradicting fact never raises,
  staleness never raises, a refuted assumption leaves the claim undecided, only a fresh `proved`
  with no open assumption is shown established, the strength never exceeds what the kinds of the
  fresh facts can establish, and a regression is exactly a removal or a move that is not upward.
-/

namespace Exegra.Verdict

/-! ## Strength -/

/-- How strong the basis of a status is. `refuted < undecided`, `refuted < asserted`;
`undecided` and `asserted` are incomparable; both are below
`checkedOnInstances < exploredToBound < proved`. -/
inductive Strength where
  | refuted
  | undecided
  | asserted
  | checkedOnInstances
  | exploredToBound
  | proved
  deriving DecidableEq, Repr, Inhabited

namespace Strength

/-- The height of a strength: `undecided` and `asserted` share a height and are incomparable. -/
def rank : Strength → Nat
  | refuted => 0
  | undecided => 1
  | asserted => 1
  | checkedOnInstances => 2
  | exploredToBound => 3
  | proved => 4

/-- The order: equal, or strictly lower in height. -/
instance : LE Strength := ⟨fun s t => s = t ∨ s.rank < t.rank⟩

instance (s t : Strength) : Decidable (s ≤ t) :=
  inferInstanceAs (Decidable (s = t ∨ s.rank < t.rank))

theorem le_refl (s : Strength) : s ≤ s := Or.inl rfl

theorem le_trans {s t u : Strength} : s ≤ t → t ≤ u → s ≤ u := by
  intro h1 h2
  rcases h1 with rfl | h1
  · exact h2
  rcases h2 with rfl | h2
  · exact Or.inr h1
  · exact Or.inr (Nat.lt_trans h1 h2)

theorem le_antisymm {s t : Strength} : s ≤ t → t ≤ s → s = t := by
  intro h1 h2
  rcases h1 with h1 | h1
  · exact h1
  rcases h2 with h2 | h2
  · exact h2.symm
  · exact absurd (Nat.lt_trans h1 h2) (Nat.lt_irrefl _)

theorem refuted_le (s : Strength) : refuted ≤ s := by cases s <;> decide

theorem undecided_asserted_incomparable : ¬ undecided ≤ asserted ∧ ¬ asserted ≤ undecided := by
  decide

/-- The greatest lower bound of two strengths (`undecided` and `asserted` meet at `refuted`). -/
def meet (s t : Strength) : Strength :=
  if s ≤ t then s else if t ≤ s then t else refuted

/-- The least upper bound of two strengths (`undecided` and `asserted` join at
`checkedOnInstances`). -/
def join (s t : Strength) : Strength :=
  if s ≤ t then t else if t ≤ s then s else checkedOnInstances

theorem meet_le_left (s t : Strength) : meet s t ≤ s := by
  cases s <;> cases t <;> decide

theorem meet_le_right (s t : Strength) : meet s t ≤ t := by
  cases s <;> cases t <;> decide

theorem le_meet {x s t : Strength} : x ≤ s → x ≤ t → x ≤ meet s t := by
  cases x <;> cases s <;> cases t <;> decide

theorem le_join_left (s t : Strength) : s ≤ join s t := by
  cases s <;> cases t <;> decide

theorem le_join_right (s t : Strength) : t ≤ join s t := by
  cases s <;> cases t <;> decide

theorem join_le {s t y : Strength} : s ≤ y → t ≤ y → join s t ≤ y := by
  cases y <;> cases s <;> cases t <;> decide

theorem meet_self (s : Strength) : meet s s = s := by cases s <;> decide

/-- The meet of a list of strengths. An empty conjunction establishes nothing: its meet is
`undecided`. -/
def meetAll : List Strength → Strength
  | [] => undecided
  | s :: ss => ss.foldl meet s

/-- The join of a list of strengths; with nothing to join, `undecided`. -/
def joinAll : List Strength → Strength
  | [] => undecided
  | s :: ss => ss.foldl join s

theorem foldl_meet_le_init (ss : List Strength) (s : Strength) : ss.foldl meet s ≤ s := by
  induction ss generalizing s with
  | nil => exact le_refl s
  | cons t ts ih => exact le_trans (ih (meet s t)) (meet_le_left s t)

theorem foldl_meet_le_mem (ss : List Strength) (s x : Strength) (h : x ∈ ss) :
    ss.foldl meet s ≤ x := by
  induction ss generalizing s with
  | nil => cases h
  | cons t ts ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_trans (foldl_meet_le_init ts (meet s x)) (meet_le_right s x)
    · exact ih (meet s t) h

/-- The meet of a non-empty list is below each member. -/
theorem meetAll_le {ss : List Strength} {x : Strength} (h : x ∈ ss) : meetAll ss ≤ x := by
  cases ss with
  | nil => cases h
  | cons s ss =>
    rcases List.mem_cons.mp h with rfl | h
    · exact foldl_meet_le_init ss x
    · exact foldl_meet_le_mem ss s x h

theorem le_foldl_meet (ss : List Strength) (s x : Strength) (h0 : x ≤ s) (h : ∀ y ∈ ss, x ≤ y) :
    x ≤ ss.foldl meet s := by
  induction ss generalizing s with
  | nil => exact h0
  | cons t ts ih =>
    exact ih (meet s t) (le_meet h0 (h t (List.mem_cons_self ..)))
      (fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- The meet of a non-empty list is above every common lower bound. -/
theorem le_meetAll {ss : List Strength} {x : Strength} (hne : ss ≠ []) (h : ∀ y ∈ ss, x ≤ y) :
    x ≤ meetAll ss := by
  cases ss with
  | nil => exact absurd rfl hne
  | cons s ss =>
    exact le_foldl_meet ss s x (h s (List.mem_cons_self ..)) (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem foldl_join_ge_init (ss : List Strength) (s : Strength) : s ≤ ss.foldl join s := by
  induction ss generalizing s with
  | nil => exact le_refl s
  | cons t ts ih => exact le_trans (le_join_left s t) (ih (join s t))

theorem mem_le_foldl_join (ss : List Strength) (s x : Strength) (h : x ∈ ss) :
    x ≤ ss.foldl join s := by
  induction ss generalizing s with
  | nil => cases h
  | cons t ts ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_trans (le_join_right s x) (foldl_join_ge_init ts (join s x))
    · exact ih (join s t) h

/-- Each member of a list is below its join. -/
theorem le_joinAll {ss : List Strength} {x : Strength} (h : x ∈ ss) : x ≤ joinAll ss := by
  cases ss with
  | nil => cases h
  | cons s ss =>
    rcases List.mem_cons.mp h with rfl | h
    · exact foldl_join_ge_init ss x
    · exact mem_le_foldl_join ss s x h

theorem foldl_join_le (ss : List Strength) (s y : Strength) (h0 : s ≤ y) (h : ∀ x ∈ ss, x ≤ y) :
    ss.foldl join s ≤ y := by
  induction ss generalizing s with
  | nil => exact h0
  | cons t ts ih =>
    exact ih (join s t) (join_le h0 (h t (List.mem_cons_self ..)))
      (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- The join of a non-empty list is below every common upper bound. -/
theorem joinAll_le {ss : List Strength} {y : Strength} (hne : ss ≠ []) (h : ∀ x ∈ ss, x ≤ y) :
    joinAll ss ≤ y := by
  cases ss with
  | nil => exact absurd rfl hne
  | cons s ss =>
    exact foldl_join_le ss s y (h s (List.mem_cons_self ..)) (fun x hx => h x (List.mem_cons_of_mem _ hx))

def name : Strength → String
  | refuted => "refuted"
  | undecided => "undecided"
  | asserted => "asserted"
  | checkedOnInstances => "checkedOnInstances"
  | exploredToBound => "exploredToBound"
  | proved => "proved"

def ofName? : String → Option Strength
  | "refuted" => some refuted
  | "undecided" => some undecided
  | "asserted" => some asserted
  | "checkedOnInstances" => some checkedOnInstances
  | "exploredToBound" => some exploredToBound
  | "proved" => some proved
  | _ => none

end Strength

/-! ## Subject and freshness -/

/-- What a status is about: the model, the implementation (the code), or reality (production,
measurement). Strength never carries across subjects. -/
inductive Subject where
  | model
  | implementation
  | reality
  deriving DecidableEq, Repr, Inhabited

def Subject.name : Subject → String
  | model => "model"
  | implementation => "implementation"
  | reality => "reality"

def Subject.ofName? : String → Option Subject
  | "model" => some .model
  | "implementation" => some .implementation
  | "reality" => some .reality
  | _ => none

/-- Whether the facts describe the current files: `stale < unverifiable < fresh`. -/
inductive Freshness where
  | fresh
  | stale
  | unverifiable
  deriving DecidableEq, Repr, Inhabited

namespace Freshness

def rank : Freshness → Nat
  | stale => 0
  | unverifiable => 1
  | fresh => 2

instance : LE Freshness := ⟨fun a b => a.rank ≤ b.rank⟩

instance (a b : Freshness) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.rank ≤ b.rank))

theorem rank_inj {a b : Freshness} : a.rank = b.rank → a = b := by
  cases a <;> cases b <;> decide

/-- The lower of two freshnesses. -/
def min (a b : Freshness) : Freshness := if a ≤ b then a else b

theorem min_le_left (a b : Freshness) : min a b ≤ a := by cases a <;> cases b <;> decide

theorem stale_le (a : Freshness) : stale ≤ a := by cases a <;> decide

def name : Freshness → String
  | fresh => "fresh"
  | stale => "stale"
  | unverifiable => "unverifiable"

def ofName? : String → Option Freshness
  | "fresh" => some fresh
  | "stale" => some stale
  | "unverifiable" => some unverifiable
  | _ => none

end Freshness

/-! ## Status -/

/-- A status: the strength of the basis, its subject, the assumptions still open (in the order the
claim declares them) and the freshness of the facts it rests on. -/
structure Status where
  strength : Strength
  subject : Subject
  openAssumptions : List String
  freshness : Freshness
  deriving DecidableEq, Repr, Inhabited

namespace Status

/-- `s ≤ t`: `t` is at least as strong, about the same subject, has no open assumption `s` did not
have (a sublist of `s`'s, in declaration order) and is at least as fresh. -/
def le (s t : Status) : Prop :=
  s.strength ≤ t.strength ∧ s.subject = t.subject ∧
    t.openAssumptions.Sublist s.openAssumptions ∧ s.freshness ≤ t.freshness

instance : LE Status := ⟨le⟩

instance decLe (s t : Status) : Decidable (Status.le s t) := by
  unfold Status.le; exact inferInstance

instance (s t : Status) : Decidable (s ≤ t) := decLe s t

theorem le_refl (s : Status) : Status.le s s :=
  ⟨Strength.le_refl _, rfl, List.Sublist.refl _, Nat.le_refl _⟩

theorem le_trans {s t u : Status} : Status.le s t → Status.le t u → Status.le s u := by
  intro ⟨h1, h2, h3, h4⟩ ⟨k1, k2, k3, k4⟩
  exact ⟨Strength.le_trans h1 k1, h2.trans k2, k3.trans h3, Nat.le_trans h4 k4⟩

theorem le_antisymm {s t : Status} : Status.le s t → Status.le t s → s = t := by
  intro ⟨h1, h2, h3, h4⟩ ⟨k1, _, k3, k4⟩
  have hs := Strength.le_antisymm h1 k1
  have ha := k3.eq_of_length_le h3.length_le
  have hf := Freshness.rank_inj (Nat.le_antisymm h4 k4)
  cases s; cases t
  simp_all

end Status

/-! ## Facts -/

/-- What produced a fact. The four kinds the criteria name (`test`, `boundedExploration`,
`leanTheorem`, `document`) and the checks Exegra runs over its own model. -/
inductive FactKind where
  | test
  | boundedExploration
  | leanTheorem
  | document
  /-- A structural check decided over the whole declared model. -/
  | modelCheck
  /-- A check over the listed traces of the model (with their negatives). -/
  | traceCheck
  /-- A statistical test over seeded runs of the model. -/
  | statistical
  /-- An outcome an external verification tool recorded for the claim. -/
  | externalTool
  /-- A scan of the source imports against the declared relationships. -/
  | importScan
  deriving DecidableEq, Repr, Inhabited

def FactKind.name : FactKind → String
  | test => "test"
  | boundedExploration => "boundedExploration"
  | leanTheorem => "leanTheorem"
  | document => "document"
  | modelCheck => "modelCheck"
  | traceCheck => "traceCheck"
  | statistical => "statistical"
  | externalTool => "externalTool"
  | importScan => "importScan"

def FactKind.ofName? : String → Option FactKind
  | "test" => some .test
  | "boundedExploration" => some .boundedExploration
  | "leanTheorem" => some .leanTheorem
  | "document" => some .document
  | "modelCheck" => some .modelCheck
  | "traceCheck" => some .traceCheck
  | "statistical" => some .statistical
  | "externalTool" => some .externalTool
  | "importScan" => some .importScan
  | _ => none

/-- The strongest status a fresh passing fact of a kind can establish. -/
def maxStrength : FactKind → Strength
  | .test => .checkedOnInstances
  | .boundedExploration => .exploredToBound
  | .leanTheorem => .proved
  | .document => .asserted
  | .modelCheck => .exploredToBound
  | .traceCheck => .checkedOnInstances
  | .statistical => .checkedOnInstances
  | .externalTool => .checkedOnInstances
  | .importScan => .checkedOnInstances

theorem maxStrength_test : maxStrength .test = .checkedOnInstances := rfl
theorem maxStrength_boundedExploration : maxStrength .boundedExploration = .exploredToBound := rfl
theorem maxStrength_leanTheorem : maxStrength .leanTheorem = .proved := rfl
theorem maxStrength_document : maxStrength .document = .asserted := rfl

/-- What a fact says: it passed, it failed (a counterexample or a contradiction), it was not run
(skipped, a todo), or it ran and could not decide (a vacuous check). -/
inductive Outcome where
  | pass
  | fail
  | notRun
  | undecided
  deriving DecidableEq, Repr, Inhabited

def Outcome.name : Outcome → String
  | pass => "pass"
  | fail => "fail"
  | notRun => "not-run"
  | undecided => "undecided"

def Outcome.ofName? : String → Option Outcome
  | "pass" => some .pass
  | "fail" => some .fail
  | "not-run" => some .notRun
  | "undecided" => some .undecided
  | _ => none

/-- What a fact is about: one part of a claim (by id), or an assumption (by id). -/
inductive Target where
  | part (id : String)
  | assumption (id : String)
  deriving DecidableEq, Repr, Inhabited

/-- The stamp of the files a fact was recorded on, and the stamp of the current files (none where
no stamp can be computed, as in the browser bundle). -/
structure Stamps where
  recorded : Option String
  current : Option String
  deriving DecidableEq, Repr, Inhabited

/-- One fact: what produced it, what it is about, the files it describes, and what it says. -/
structure Fact where
  kind : FactKind
  subject : Subject
  target : Target
  stamps : Stamps
  outcome : Outcome
  deriving DecidableEq, Repr, Inhabited

namespace Fact

/-- A fact recorded on the current files is fresh, on others (or on none it names) stale; with no
current stamp to compare, unverifiable. -/
def freshness (f : Fact) : Freshness :=
  match f.stamps.current, f.stamps.recorded with
  | none, _ => .unverifiable
  | some c, some r => if c = r then .fresh else .stale
  | some _, none => .stale

end Fact

/-- The same fact, read as recorded on other files than the current ones. -/
def markStale (f : Fact) : Fact :=
  { f with stamps := { recorded := none, current := some (f.stamps.current.getD "") } }

theorem markStale_freshness (f : Fact) : (markStale f).freshness = .stale := by
  simp [markStale, Fact.freshness]

/-! ## Claims -/

/-- A claim as the verdict sees it: an atomic part (its id, its subject, the assumptions it rests
on), or a conjunction of claims. -/
inductive Claim where
  | atom (id : String) (subject : Subject) (assumptions : List String)
  | conj (cs : List Claim)
  deriving Repr, Inhabited

/-- The assumptions every list in a list shares, in the order of the first. -/
def common : List (List String) → List String
  | [] => []
  | l :: ls => l.filter (fun a => ls.all (fun m => m.contains a))

mutual
/-- The assumptions a claim rests on: an atom's own; for a conjunction, those every part rests on. -/
def Claim.assumptions : Claim → List String
  | .atom _ _ as => as
  | .conj cs => common (Claim.assumptionsOf cs)

def Claim.assumptionsOf : List Claim → List (List String)
  | [] => []
  | c :: cs => c.assumptions :: Claim.assumptionsOf cs
end

mutual
/-- Every assumption any part declares, in order (duplicates kept). -/
def Claim.allAssumptions : Claim → List String
  | .atom _ _ as => as
  | .conj cs => Claim.allAssumptionsOf cs

def Claim.allAssumptionsOf : List Claim → List String
  | [] => []
  | c :: cs => c.allAssumptions ++ Claim.allAssumptionsOf cs
end

mutual
/-- The ids of the atomic parts. -/
def Claim.partIds : Claim → List String
  | .atom id _ _ => [id]
  | .conj cs => Claim.partIdsOf cs

def Claim.partIdsOf : List Claim → List String
  | [] => []
  | c :: cs => c.partIds ++ Claim.partIdsOf cs
end

/-- The subject of a claim: an atom's own; a conjunction's is its first part's (the shell encodes a
claim with every part on the claim's subject). -/
def Claim.subject : Claim → Subject
  | .atom _ s _ => s
  | .conj [] => .model
  | .conj (c :: _) => c.subject

/-! ## The rule -/

/-- Whether an assumption is refuted: a fact about it failed (whatever its freshness: staleness
never improves a status). -/
def assumptionRefutedB (a : String) (fs : List Fact) : Bool :=
  fs.any (fun f => decide (f.target = .assumption a) && decide (f.outcome = .fail))

/-- Whether an assumption is refuted by the facts. -/
def assumptionRefuted (a : String) (fs : List Fact) : Prop := assumptionRefutedB a fs = true

/-- Whether an assumption is discharged: a fresh fact about it passed. -/
def discharged (a : String) (fs : List Fact) : Bool :=
  fs.any (fun f => decide (f.target = .assumption a) && decide (f.outcome = .pass) &&
    decide (f.freshness = .fresh))

/-- The facts that bear on a part: those about it that failed (of any subject: evidence can only
worsen a status) or that are about the part's subject. -/
def considered (id : String) (subj : Subject) (fs : List Fact) : List Fact :=
  fs.filter (fun f => decide (f.target = .part id) && (decide (f.outcome = .fail) || decide (f.subject = subj)))

/-- The fresh passing facts a part's strength comes from. -/
def usable (id : String) (subj : Subject) (fs : List Fact) : List Fact :=
  (considered id subj fs).filter (fun f => decide (f.outcome = .pass) && decide (f.freshness = .fresh))

/-- The strength of one part before its assumptions are weighed: a failure refutes it; a stale
pass leaves nothing positive (staleness is the bottom of the order, with the freshness saying why);
otherwise the join of what the fresh passing facts can establish, `undecided` when there are none. -/
def partStrength (id : String) (subj : Subject) (fs : List Fact) : Strength :=
  let rel := considered id subj fs
  if rel.any (fun f => decide (f.outcome = .fail)) then .refuted
  else if rel.any (fun f => decide (f.outcome = .pass) && decide (f.freshness = .stale)) then .refuted
  else Strength.joinAll ((usable id subj fs).map (fun f => maxStrength f.kind))

mutual
/-- The strength of a claim. An atom with a refuted assumption is undecided (the claim may still
be true); a conjunction takes the meet of its parts. -/
def strengthOf (fs : List Fact) : Claim → Strength
  | .atom id subj as =>
    if as.any (fun a => assumptionRefutedB a fs) then .undecided else partStrength id subj fs
  | .conj cs => Strength.meetAll (strengthsOf fs cs)

def strengthsOf (fs : List Fact) : List Claim → List Strength
  | [] => []
  | c :: cs => strengthOf fs c :: strengthsOf fs cs
end

theorem strengthsOf_eq_map (fs : List Fact) (cs : List Claim) :
    strengthsOf fs cs = cs.map (strengthOf fs) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [strengthsOf, ih]

/-- Whether a fact is about the claim: a part of it, or an assumption it declares. -/
def Claim.concerns (c : Claim) (f : Fact) : Bool :=
  match f.target with
  | .part id => c.partIds.contains id
  | .assumption a => c.allAssumptions.contains a

/-- The freshness of a claim's basis: the lowest of the facts about it, fresh when there are none. -/
def freshnessOf (c : Claim) (fs : List Fact) : Freshness :=
  (fs.filter c.concerns).foldl (fun acc f => Freshness.min acc f.freshness) .fresh

/-- The status of a claim given the facts. -/
def status (c : Claim) (fs : List Fact) : Status where
  strength := strengthOf fs c
  subject := c.subject
  openAssumptions := c.allAssumptions.filter (fun a => !discharged a fs)
  freshness := freshnessOf c fs

/-- A fact contradicts a claim when it fails and is about one of its parts. -/
def Contradicts (f : Fact) (c : Claim) : Prop :=
  f.outcome = .fail ∧ ∃ id ∈ c.partIds, f.target = .part id

/-- Shown as established (the positive tone): proved, fresh and with no open assumption. -/
def shownEstablished (s : Status) : Bool :=
  decide (s.strength = .proved) && decide (s.freshness = .fresh) && s.openAssumptions.isEmpty

/-- A move from `old` to `new` (none: the claim was removed) is a regression unless `new` is at
least `old` in the status order. -/
def isRegression (old : Status) (new : Option Status) : Bool :=
  match new with
  | none => true
  | some n => !decide (Status.le old n)

mutual
/-- The facts a claim's strength was taken from (fresh, passing, about each part's subject); none
for an atom whose assumption is refuted, since its strength does not rest on them. -/
def usedFacts (fs : List Fact) : Claim → List Fact
  | .atom id subj as =>
    if as.any (fun a => assumptionRefutedB a fs) then [] else usable id subj fs
  | .conj cs => usedFactsOf fs cs

def usedFactsOf (fs : List Fact) : List Claim → List Fact
  | [] => []
  | c :: cs => usedFacts fs c ++ usedFactsOf fs cs
end

/-- The most the given kinds of facts can establish: the join of their `maxStrength`, `undecided`
for none. -/
def bound (ks : List FactKind) : Strength := Strength.joinAll (ks.map maxStrength)

/-! ## The rule theorems (criterion 2) -/

/-- (a) **A conjunction takes its weakest part**: the strength of `conj cs` is the meet of the
strengths of its parts. -/
theorem status_conj (cs : List Claim) (fs : List Fact) :
    (status (.conj cs) fs).strength = Strength.meetAll (cs.map fun c => (status c fs).strength) := by
  simp [status, strengthOf, strengthsOf_eq_map]

/-! ### (b) contradiction lowers -/

theorem considered_append_fail_other {id : String} {subj : Subject} {fs : List Fact} {f : Fact}
    (h : f.target ≠ .part id) : considered id subj (fs ++ [f]) = considered id subj fs := by
  simp [considered, List.filter_append, h]

theorem usable_append_fail {id : String} {subj : Subject} {fs : List Fact} {f : Fact}
    (hf : f.outcome = .fail) : usable id subj (fs ++ [f]) = usable id subj fs := by
  simp [usable, considered, List.filter_append, List.filter_filter, hf]

theorem partStrength_append_fail_le (id : String) (subj : Subject) (fs : List Fact) (f : Fact)
    (hf : f.outcome = .fail) : partStrength id subj (fs ++ [f]) ≤ partStrength id subj fs := by
  by_cases ht : f.target = .part id
  · have : partStrength id subj (fs ++ [f]) = .refuted := by
      simp [partStrength, considered, List.filter_append, ht, hf]
    rw [this]; exact Strength.refuted_le _
  · have : partStrength id subj (fs ++ [f]) = partStrength id subj fs := by
      simp only [partStrength, considered_append_fail_other ht, usable_append_fail hf]
    rw [this]; exact Strength.le_refl _

theorem assumptionRefutedB_append_part {a : String} {fs : List Fact} {f : Fact} {id : String}
    (ht : f.target = .part id) : assumptionRefutedB a (fs ++ [f]) = assumptionRefutedB a fs := by
  simp [assumptionRefutedB, ht]

theorem discharged_append_fail {a : String} {fs : List Fact} {f : Fact} (hf : f.outcome = .fail) :
    discharged a (fs ++ [f]) = discharged a fs := by
  simp [discharged, hf]

/-- Two lists of strengths of the same length, pointwise ordered. -/
inductive LeAll : List Strength → List Strength → Prop
  | nil : LeAll [] []
  | cons {x y : Strength} {xs ys : List Strength} : x ≤ y → LeAll xs ys → LeAll (x :: xs) (y :: ys)

theorem meetAll_mono : ∀ {xs ys : List Strength}, LeAll xs ys →
    Strength.meetAll xs ≤ Strength.meetAll ys
  | [], [], .nil => Strength.le_refl _
  | x :: xs, y :: ys, .cons hxy hrest => by
    apply Strength.le_meetAll (List.cons_ne_nil _ _)
    intro z hz
    -- every member of ys is above some member of xs, which is above the meet of xs
    have key : ∀ {as bs : List Strength}, LeAll as bs → ∀ b ∈ bs, ∃ a ∈ as, a ≤ b := by
      intro as bs h
      induction h with
      | nil => intro b hb; cases hb
      | cons hab _ ih =>
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨_, List.mem_cons_self .., hab⟩
        · obtain ⟨a, ha, hle⟩ := ih b hb
          exact ⟨a, List.mem_cons_of_mem _ ha, hle⟩
    obtain ⟨a, ha, hle⟩ := key (.cons hxy hrest) z hz
    exact Strength.le_trans (Strength.meetAll_le ha) hle

mutual
theorem strengthOf_append_fail_le (fs : List Fact) (f : Fact) (hf : f.outcome = .fail)
    (hp : ∃ id, f.target = .part id) : ∀ c : Claim, strengthOf (fs ++ [f]) c ≤ strengthOf fs c
  | .atom id subj as => by
    obtain ⟨pid, hpid⟩ := hp
    have hA : (as.any fun a => assumptionRefutedB a (fs ++ [f])) =
        (as.any fun a => assumptionRefutedB a fs) := by
      simp [assumptionRefutedB_append_part hpid]
    simp only [strengthOf, hA]
    split
    · exact Strength.le_refl _
    · exact partStrength_append_fail_le id subj fs f hf
  | .conj cs => by
    simp only [strengthOf]
    exact meetAll_mono (strengthsOf_append_fail_le fs f hf hp cs)

theorem strengthsOf_append_fail_le (fs : List Fact) (f : Fact) (hf : f.outcome = .fail)
    (hp : ∃ id, f.target = .part id) :
    ∀ cs : List Claim, LeAll (strengthsOf (fs ++ [f]) cs) (strengthsOf fs cs)
  | [] => .nil
  | c :: cs => .cons (strengthOf_append_fail_le fs f hf hp c) (strengthsOf_append_fail_le fs f hf hp cs)
end

theorem foldl_min_le_init (l : List Fact) (a : Freshness) :
    l.foldl (fun acc f => Freshness.min acc f.freshness) a ≤ a := by
  induction l generalizing a with
  | nil => exact Nat.le_refl _
  | cons g gs ih => exact Nat.le_trans (ih _) (Freshness.min_le_left _ _)

/-- (b) **A contradicting fact never raises a status.** -/
theorem contradict_lowers {f : Fact} {c : Claim} {fs : List Fact} (h : Contradicts f c) :
    status c (fs ++ [f]) ≤ status c fs := by
  obtain ⟨hf, id, _, ht⟩ := h
  refine ⟨strengthOf_append_fail_le fs f hf ⟨id, ht⟩ c, rfl, ?_, ?_⟩
  · simp only [status, discharged_append_fail hf]; exact List.Sublist.refl _
  · show freshnessOf c (fs ++ [f]) ≤ freshnessOf c fs
    unfold freshnessOf
    rw [List.filter_append, List.foldl_append]
    by_cases hc : c.concerns f = true
    · simp only [List.filter_cons, hc, ite_true, List.filter_nil, List.foldl_cons, List.foldl_nil]
      exact Freshness.min_le_left _ _
    · simp [hc]
      exact Nat.le_refl _

/-! ### (c) staleness never raises -/

theorem considered_markStale (id : String) (subj : Subject) (fs : List Fact) :
    considered id subj (fs.map markStale) = (considered id subj fs).map markStale := by
  simp only [considered, List.filter_map]
  rfl

theorem partStrength_markStale_le (id : String) (subj : Subject) (fs : List Fact) :
    partStrength id subj (fs.map markStale) ≤ partStrength id subj fs := by
  unfold partStrength
  simp only [considered_markStale, usable, List.any_map, Function.comp_def]
  have hm : ∀ g : Fact, (markStale g).outcome = g.outcome := fun _ => rfl
  simp only [hm, markStale_freshness]
  by_cases h1 : ((considered id subj fs).any fun f => decide (f.outcome = .fail)) = true
  · simp [h1]; exact Strength.le_refl _
  · simp only [h1]
    by_cases h2 : ((considered id subj fs).any fun f => decide (f.outcome = .pass)) = true
    · simp [h2]; exact Strength.refuted_le _
    · have hnil : ((considered id subj fs).filter fun f =>
          decide (f.outcome = .pass) && decide (f.freshness = .fresh)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro g hg hp
        apply h2
        rw [List.any_eq_true]
        exact ⟨g, hg, by simp at hp ⊢; exact hp.1⟩
      have hst : ((considered id subj fs).any fun f => decide (f.outcome = .pass) && decide (f.freshness = .stale)) = false := by
        rw [Bool.eq_false_iff]
        intro hx
        apply h2
        rw [List.any_eq_true] at hx ⊢
        obtain ⟨g, hg, hp⟩ := hx
        exact ⟨g, hg, by simp at hp ⊢; exact hp.1⟩
      have hnil2 : ((List.map markStale (considered id subj fs)).filter fun f =>
          decide (f.outcome = .pass) && decide (f.freshness = .fresh)) = [] := by
        simp [List.filter_map, Function.comp_def, markStale_freshness]
      simp [h2, hst, hnil, hnil2]
      exact Strength.le_refl _


theorem assumptionRefutedB_markStale (a : String) (fs : List Fact) :
    assumptionRefutedB a (fs.map markStale) = assumptionRefutedB a fs := by
  simp only [assumptionRefutedB, List.any_map, Function.comp_def]
  rfl

mutual
theorem strengthOf_markStale_le (fs : List Fact) :
    ∀ c : Claim, strengthOf (fs.map markStale) c ≤ strengthOf fs c
  | .atom id subj as => by
    simp only [strengthOf, assumptionRefutedB_markStale]
    split
    · exact Strength.le_refl _
    · exact partStrength_markStale_le id subj fs
  | .conj cs => by
    simp only [strengthOf]
    exact meetAll_mono (strengthsOf_markStale_le fs cs)

theorem strengthsOf_markStale_le (fs : List Fact) :
    ∀ cs : List Claim, LeAll (strengthsOf (fs.map markStale) cs) (strengthsOf fs cs)
  | [] => .nil
  | c :: cs => .cons (strengthOf_markStale_le fs c) (strengthsOf_markStale_le fs cs)
end

theorem discharged_markStale (a : String) (fs : List Fact) : discharged a (fs.map markStale) = false := by
  simp [discharged, List.any_map, Function.comp_def, markStale_freshness]

theorem freshnessOf_markStale_le (c : Claim) (fs : List Fact) :
    freshnessOf c (fs.map markStale) ≤ freshnessOf c fs := by
  unfold freshnessOf
  have hf : (fs.map markStale).filter c.concerns = (fs.filter c.concerns).map markStale := by
    simp only [List.filter_map]; rfl
  rw [hf]
  cases h : fs.filter c.concerns with
  | nil => exact Nat.le_refl _
  | cons g gs =>
    simp only [List.map_cons, List.foldl_cons]
    have h1 := foldl_min_le_init (gs.map markStale) (Freshness.min .fresh (markStale g).freshness)
    have h2 : Freshness.min .fresh (markStale g).freshness = .stale := by
      rw [markStale_freshness]; decide
    rw [h2] at h1 ⊢
    have h3 : (List.foldl (fun acc f => Freshness.min acc f.freshness) Freshness.stale (gs.map markStale)) = .stale := by
      have := h1
      revert this
      generalize List.foldl (fun acc f => Freshness.min acc f.freshness) Freshness.stale (gs.map markStale) = x
      cases x <;> decide
    rw [h3]
    exact Freshness.stale_le _

/-- (c) **Staleness never raises a status**: reading every fact as stale gives a status at most
the one the facts give as recorded. -/
theorem stale_never_raises (c : Claim) (fs : List Fact) :
    status c (fs.map markStale) ≤ status c fs := by
  refine ⟨strengthOf_markStale_le fs c, rfl, ?_, freshnessOf_markStale_le c fs⟩
  show (c.allAssumptions.filter fun a => !discharged a fs).Sublist
    (c.allAssumptions.filter fun a => !discharged a (fs.map markStale))
  simp only [discharged_markStale, Bool.not_false]
  rw [List.filter_eq_self.mpr (fun _ _ => rfl)]
  exact List.filter_sublist

/-! ### (d) a refuted assumption leaves the claim undecided -/

theorem meetAll_all_undecided {ss : List Strength} (hne : ss ≠ []) (h : ∀ s ∈ ss, s = .undecided) :
    Strength.meetAll ss = .undecided := by
  apply Strength.le_antisymm
  · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil ss hne
    have := Strength.meetAll_le hx
    rwa [h x hx] at this
  · exact Strength.le_meetAll hne (fun y hy => by rw [h y hy]; exact Strength.le_refl _)

mutual
theorem strengthOf_refuted_assumption (fs : List Fact) (a : String) (ha : assumptionRefuted a fs) :
    ∀ c : Claim, a ∈ c.assumptions → strengthOf fs c = .undecided
  | .atom _ _ as, hmem => by
    have : (as.any fun a => assumptionRefutedB a fs) = true := List.any_eq_true.mpr ⟨a, hmem, ha⟩
    simp [strengthOf, this]
  | .conj [], hmem => by simp [Claim.assumptions, Claim.assumptionsOf, common] at hmem
  | .conj (c :: rest), hmem => by
    simp only [strengthOf]
    simp only [Claim.assumptions, Claim.assumptionsOf, common, List.mem_filter, List.all_eq_true,
      List.contains_iff_mem] at hmem
    apply meetAll_all_undecided (by simp [strengthsOf])
    intro s hs
    simp only [strengthsOf, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact strengthOf_refuted_assumption fs a ha c hmem.1
    · exact strengthsOf_refuted_assumption fs a ha rest (fun m hm => by simpa using hmem.2 m hm) s hs

theorem strengthsOf_refuted_assumption (fs : List Fact) (a : String) (ha : assumptionRefuted a fs) :
    ∀ cs : List Claim, (∀ m ∈ Claim.assumptionsOf cs, a ∈ m) → ∀ s ∈ strengthsOf fs cs, s = .undecided
  | [], _, s, hs => by simp [strengthsOf] at hs
  | c :: rest, hall, s, hs => by
    simp only [strengthsOf, List.mem_cons] at hs
    simp only [Claim.assumptionsOf, List.mem_cons, forall_eq_or_imp] at hall
    rcases hs with rfl | hs
    · exact strengthOf_refuted_assumption fs a ha c hall.1
    · exact strengthsOf_refuted_assumption fs a ha rest hall.2 s hs
end

/-- (d) **A refuted assumption leaves the claim undecided**, not refuted: the claim may still be
true. -/
theorem refuted_assumption_undecided {a : String} {c : Claim} {fs : List Fact}
    (hmem : a ∈ c.assumptions) (ha : assumptionRefuted a fs) : (status c fs).strength = .undecided :=
  strengthOf_refuted_assumption fs a ha c hmem

/-! ### (e) what is shown established -/

/-- (e) **Only a fresh `proved` with no open assumption is shown established.** -/
theorem established_iff (c : Claim) (fs : List Fact) :
    shownEstablished (status c fs) = true ↔
      (status c fs).strength = .proved ∧ (status c fs).freshness = .fresh ∧
        (status c fs).openAssumptions = [] := by
  simp [shownEstablished, List.isEmpty_iff, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-! ### (f) strength never exceeds what the kinds of the fresh facts can establish -/

theorem bound_mono {l L : List FactKind} (hne : l ≠ []) (hsub : ∀ k ∈ l, k ∈ L) : bound l ≤ bound L := by
  unfold bound
  apply Strength.joinAll_le (by simpa using hne)
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
  exact Strength.le_joinAll (List.mem_map.mpr ⟨k, hsub k hk, rfl⟩)

theorem partStrength_le_bound (id : String) (subj : Subject) (fs : List Fact) :
    partStrength id subj fs ≤ bound ((usable id subj fs).map Fact.kind) := by
  dsimp only [partStrength]
  split
  · exact Strength.refuted_le _
  split
  · exact Strength.refuted_le _
  simp only [bound, List.map_map, Function.comp_def]
  exact Strength.le_refl _

mutual
theorem strengthOf_le_bound (fs : List Fact) :
    ∀ c : Claim, strengthOf fs c ≤ bound ((usedFacts fs c).map Fact.kind)
  | .atom id subj as => by
    simp only [strengthOf, usedFacts]
    split
    · exact Strength.le_refl _
    · exact partStrength_le_bound id subj fs
  | .conj [] => Strength.le_refl _
  | .conj (c :: rest) => by
    simp only [strengthOf, usedFacts]
    obtain ⟨x, hx, hle⟩ := strengthsOf_le_bound fs (c :: rest) (List.cons_ne_nil _ _)
    exact Strength.le_trans (Strength.meetAll_le hx) hle

theorem strengthsOf_le_bound (fs : List Fact) :
    ∀ cs : List Claim, cs ≠ [] →
      ∃ x ∈ strengthsOf fs cs, x ≤ bound ((usedFactsOf fs cs).map Fact.kind)
  | [], h => absurd rfl h
  | [c], _ => by
    refine ⟨strengthOf fs c, by simp [strengthsOf], ?_⟩
    simpa [usedFactsOf] using strengthOf_le_bound fs c
  | c :: d :: ds, _ => by
    by_cases hu : usedFacts fs c = []
    · obtain ⟨x, hx, hle⟩ := strengthsOf_le_bound fs (d :: ds) (List.cons_ne_nil _ _)
      refine ⟨x, by simp only [strengthsOf, List.mem_cons] at hx ⊢; exact Or.inr hx, ?_⟩
      have : usedFactsOf fs (c :: d :: ds) = usedFactsOf fs (d :: ds) := by
        simp [usedFactsOf, hu]
      rw [this]; exact hle
    · refine ⟨strengthOf fs c, by simp [strengthsOf], Strength.le_trans (strengthOf_le_bound fs c) ?_⟩
      apply bound_mono (by simpa using hu)
      intro k hk
      simp only [usedFactsOf, List.map_append, List.mem_append]
      exact Or.inl hk
end

theorem usable_fresh {id : String} {subj : Subject} {fs : List Fact} {f : Fact}
    (h : f ∈ usable id subj fs) : f.freshness = .fresh := by
  simp only [usable, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2.2

mutual
/-- The facts a status is taken from are all fresh. -/
theorem usedFacts_fresh (fs : List Fact) :
    ∀ (c : Claim) (f : Fact), f ∈ usedFacts fs c → f.freshness = .fresh
  | .atom id subj as, f, h => by
    simp only [usedFacts] at h
    split at h
    · cases h
    · exact usable_fresh h
  | .conj cs, f, h => by
    simp only [usedFacts] at h
    exact usedFactsOf_fresh fs cs f h

theorem usedFactsOf_fresh (fs : List Fact) :
    ∀ (cs : List Claim) (f : Fact), f ∈ usedFactsOf fs cs → f.freshness = .fresh
  | [], f, h => by simp [usedFactsOf] at h
  | c :: rest, f, h => by
    simp only [usedFactsOf, List.mem_append] at h
    rcases h with h | h
    · exact usedFacts_fresh fs c f h
    · exact usedFactsOf_fresh fs rest f h
end

/-- (f) **The strength never exceeds what the kinds of the fresh facts used can establish**: at
most the join of `maxStrength` over the kinds of `usedFacts` (all fresh, by `usedFacts_fresh`), with
`maxStrength test = checkedOnInstances`, `maxStrength boundedExploration = exploredToBound`,
`maxStrength leanTheorem = proved` and `maxStrength document = asserted`. -/
theorem strength_le_kind (c : Claim) (fs : List Fact) :
    (status c fs).strength ≤ bound ((usedFacts fs c).map Fact.kind) :=
  strengthOf_le_bound fs c

/-! ### (g) regressions -/

/-- (g) **A regression is a removal or a move that is not upward**: `isRegression old new ↔
(new = none ∨ ¬ Status.le old new)`, with `new` optional (none: the claim was removed). -/
theorem regression_iff (old : Status) (new : Option Status) :
    isRegression old new = true ↔ (new = none ∨ ∃ n, new = some n ∧ ¬ Status.le old n) := by
  cases new with
  | none => simp [isRegression]
  | some n => simp [isRegression]

/-! ## The label the shell shows -/

/-- The word a status is shown with. Refuted with a failing fact about a part: `violated`;
refuted only by staleness: `not-evaluated` (the freshness says why). Undecided: `inconclusive` when
facts about the claim exist, `not-evaluated` when none do. `asserted`. Positive strengths: `proved`;
about the model, `model-holds` when every fact used is statistical, `verified` otherwise; about the
implementation or reality, `supported`. -/
def label (c : Claim) (fs : List Fact) : String :=
  let s := status c fs
  let mine := fs.filter c.concerns
  match s.strength with
  | .refuted =>
    if mine.any (fun f => decide (f.outcome = .fail) && (match f.target with | .part _ => true | _ => false))
    then "violated" else "not-evaluated"
  | .undecided => if mine.isEmpty then "not-evaluated" else "inconclusive"
  | .asserted => "asserted"
  | .proved => "proved"
  | _ =>
    if s.subject = .model then
      let used := usedFacts fs c
      if !used.isEmpty && used.all (fun f => decide (f.kind = .statistical)) then "model-holds" else "verified"
    else "supported"

/-! ## Lean theorem checks as facts

What `tools/lean-theorems.js` reports about a theorem (found, kind, kernel, axioms, and per `about`
constant its kind, whether the statement mentions it, and whether its runtime body is another one)
decides whether the theorem is accepted as a proof of its claim. The rule is applied here. -/

/-- The axioms a proof may depend on. -/
def standardAxioms : List String := ["propext", "Classical.choice", "Quot.sound"]

/-- Whether an axiom comes from `native_decide`. -/
def nativeAxiom (a : String) : Bool :=
  a == "Lean.ofReduceBool" || a == "Lean.ofReduceNat" || a == "Lean.trustCompiler" ||
    decide ((a.splitOn "._native.native_decide.").length > 1)

def field (v : Value) (k : String) : Value :=
  match v with
  | .obj _ fs => (objGet? fs k).getD .undef
  | _ => .undef

def strField (v : Value) (k : String) : Option String := (field v k).asString?

def boolField (v : Value) (k : String) : Bool :=
  match field v k with
  | .bool b => b
  | _ => false

def items : Value → List Value
  | .arr _ xs => xs
  | _ => []

def strings (v : Value) : List String := (items v).filterMap Value.asString?

/-- What is wrong with one `about` constant of a theorem check, if anything. -/
def aboutProblem (info : Value) (a : String) : Option (String × String) :=
  let kind := (strField info "kind").getD ""
  if kind == "missing" then some ("about-missing", a)
  else if kind == "opaque" then some ("about-opaque", a)
  else if kind != "definition" then some ("about-kind", a ++ ":" ++ kind)
  else match strField info "implementedBy" with
    | some impl => if impl.isEmpty then none else some ("about-implemented-by", a ++ ":" ++ impl)
    | none =>
      if boolField info "extern" then some ("about-extern", a)
      else if boolField info "partial" then some ("about-partial", a)
      else if !boolField info "inStatement" then some ("about-not-in-statement", a)
      else none

/-- The outcome of a recorded theorem check for a claim about the given constants, with the reason
(a code) and its detail. `not-run`: there is no usable check (none recorded, or one that does not
cover every `about` constant). -/
def theoremOutcome (check : Value) (about : List String) : Outcome × String × String :=
  match check with
  | .obj _ _ =>
    if !boolField check "found" then (.fail, "not-found", "")
    else if strField check "kind" != some "theorem" then (.fail, "not-a-theorem", (strField check "kind").getD "")
    else if strField check "kernel" != some "ok" then (.fail, "kernel", (strField check "kernel").getD "")
    else
      let extra := (strings (field check "axioms")).filter (fun a => !standardAxioms.contains a)
      if !extra.isEmpty then
        (.fail, "axioms", ",".intercalate (extra.map fun a =>
          if a == "sorryAx" then a ++ ":sorry" else if nativeAxiom a then a ++ ":native" else a ++ ":extra"))
      else if about.isEmpty then (.fail, "no-about", "")
      else
        let rec_ := field check "about"
        let unchecked := about.filter (fun a => match field rec_ a with | .obj _ _ => false | _ => true)
        if !unchecked.isEmpty then (.notRun, "about-unchecked", ",".intercalate unchecked)
        else
          match about.findSome? (fun a => aboutProblem (field rec_ a) a) with
          | some (code, d) => (.fail, code, d)
          | none => (.pass, "ok", "")
  | _ => (.notRun, "no-check", "")

/-! ## Decoding (criterion 4: a fact that does not decode is refused with a diagnostic) -/

def decodeSubject (v : Value) : Except String Subject :=
  match v.asString? >>= Subject.ofName? with
  | some s => .ok s
  | none => .error "subject must be \"model\", \"implementation\" or \"reality\""

def decodeOptStr (v : Value) (what : String) : Except String (Option String) :=
  match v with
  | .str s => .ok (some s)
  | .null | .undef => .ok none
  | _ => .error s!"{what} must be a string or null"

/-- A fact as JSON: `{kind, subject, target: {part} | {assumption}, stamps: {recorded, current},
outcome}`. A `leanTheorem` fact may carry `{check, about}` instead of `outcome`: the outcome is then
decided by `theoremOutcome`. Returns the fact and, for a theorem check, the reason and detail. -/
def decodeFact (v : Value) : Except String (Fact × Option (String × String)) := do
  let .obj _ _ := v | throw "a fact must be an object"
  let kind ← match strField v "kind" >>= FactKind.ofName? with
    | some k => pure k
    | none => throw s!"unknown fact kind {Json.write (field v "kind")}"
  let subject ← decodeSubject (field v "subject")
  let target ← match strField (field v "target") "part", strField (field v "target") "assumption" with
    | some id, none => pure (Target.part id)
    | none, some id => pure (Target.assumption id)
    | _, _ => throw "target must be {\"part\": id} or {\"assumption\": id}"
  let st := field v "stamps"
  let .obj _ _ := st | throw "stamps must be an object {recorded, current}"
  let recorded ← decodeOptStr (field st "recorded") "stamps.recorded"
  let current ← decodeOptStr (field st "current") "stamps.current"
  let (outcome, why) ← match field v "outcome", kind with
    | .undef, .leanTheorem =>
      let (o, code, d) := theoremOutcome (field v "check") (strings (field v "about"))
      pure (o, some (code, d))
    | o, _ => match o.asString? >>= Outcome.ofName? with
      | some o => pure (o, none)
      | none => throw "outcome must be \"pass\", \"fail\", \"not-run\" or \"undecided\""
  pure ({ kind, subject, target, stamps := { recorded, current }, outcome }, why)

/-- A claim as JSON: `{part, subject, assumptions}` for an atom, `{all: [claims]}` for a
conjunction. -/
partial def decodeClaim (v : Value) : Except String Claim := do
  match field v "all" with
  | .arr _ cs => return .conj (← cs.mapM decodeClaim)
  | _ =>
    let some id := strField v "part" | throw "a claim must be {part, subject, assumptions} or {all}"
    let subject ← decodeSubject (field v "subject")
    return .atom id subject (strings (field v "assumptions"))

def decodeStatus (v : Value) : Except String Status := do
  let some strength := strField v "strength" >>= Strength.ofName? | throw "status.strength is not a strength"
  let subject ← decodeSubject (field v "subject")
  let some freshness := strField v "freshness" >>= Freshness.ofName? | throw "status.freshness is not a freshness"
  return { strength, subject, openAssumptions := strings (field v "openAssumptions"), freshness }

def strArr (xs : List String) : Value := .arr 0 (xs.map .str)

def statusJson (s : Status) : List (String × Value) :=
  [("strength", .str s.strength.name), ("subject", .str s.subject.name),
   ("openAssumptions", strArr s.openAssumptions), ("freshness", .str s.freshness.name)]

/-- One claim's verdict: decode its claim and facts (refusing each fact that does not decode, with
its index and the reason), decide the status, and say how it is shown, with the freshness of each
fact (null for a refused one) and the outcome Lean decided for each theorem check. -/
def verdictJson (item : Value) : Except String Value := do
  let c ← decodeClaim (field item "claim")
  let decoded := (items (field item "facts")).zipIdx.map fun (f, i) => (i, decodeFact f)
  let facts := decoded.filterMap fun (_, r) => match r with | .ok (f, _) => some f | .error _ => none
  let refused := decoded.filterMap fun (i, r) => match r with
    | .error e => some (Value.obj 0 [("index", .num i.toFloat), ("error", .str e)])
    | .ok _ => none
  let reasons := decoded.filterMap fun (i, r) => match r with
    | .ok (f, some (code, d)) => some (Value.obj 0 [("index", .num i.toFloat), ("outcome", .str f.outcome.name),
        ("reason", .str code), ("detail", .str d)])
    | _ => none
  let fresh := decoded.map fun (_, r) => match r with
    | .ok (f, _) => Value.str f.freshness.name
    | .error _ => .null
  let s := status c facts
  return .obj 0 (statusJson s ++
    [("established", .bool (shownEstablished s)), ("label", .str (label c facts)),
     ("refused", .arr 0 refused), ("theorems", .arr 0 reasons), ("factFreshness", .arr 0 fresh)])

/-- `claims.status`: `{claims: [{claim, facts}]}` to `[verdict]`, in order; each verdict is
`{strength, subject, openAssumptions, freshness, established, label, refused, theorems,
factFreshness}`. -/
def statusValue (args : Value) : Except String String := do
  let out ← (items (field args "claims")).mapM verdictJson
  return Json.write (.arr 0 out)

/-- `verdict.isRegression`: `{pairs: [{old: status, new: status | null}]}` to `[bool]`. -/
def regressionValue (args : Value) : Except String String := do
  let out ← (items (field args "pairs")).mapM fun p => do
    let old ← decodeStatus (field p "old")
    let new ← match field p "new" with
      | .null | .undef => pure none
      | v => some <$> decodeStatus v
    return Value.bool (isRegression old new)
  return Json.write (.arr 0 out)

/-- `facts.decode`: `{facts: [fact]}` to `[{ok: true} | {error}]`: the check a fact producer's
output is held to. -/
def decodeValue (args : Value) : Except String String :=
  .ok (Json.write (.arr 0 ((items (field args "facts")).map fun f => match decodeFact f with
    | .ok _ => .obj 0 [("ok", .bool true)]
    | .error e => .obj 0 [("error", .str e)])))

/-! ## Axioms -/

/-- info: 'Exegra.Verdict.status_conj' depends on axioms: [propext] -/
#guard_msgs in #print axioms status_conj
/-- info: 'Exegra.Verdict.contradict_lowers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms contradict_lowers
/-- info: 'Exegra.Verdict.stale_never_raises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stale_never_raises
/-- info: 'Exegra.Verdict.refuted_assumption_undecided' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms refuted_assumption_undecided
/-- info: 'Exegra.Verdict.established_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms established_iff
/-- info: 'Exegra.Verdict.strength_le_kind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms strength_le_kind
/-- info: 'Exegra.Verdict.regression_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms regression_iff
/-- info: 'Exegra.Verdict.Status.le_antisymm' depends on axioms: [propext] -/
#guard_msgs in #print axioms Status.le_antisymm

end Exegra.Verdict
