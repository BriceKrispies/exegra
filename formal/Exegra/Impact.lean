import Exegra.Verdict

/-!
# Change impact and theorem weakening

The dependency graph of a specification's claims (WG-5684, criteria 7 to 11). A node is a claim, an
assumption, a specification entity, a Lean declaration, a file, a measurement or an evidence entity; an
edge `(a, b)` says that `a` depends on `b`:

* a claim on each assumption it cites, and on each specification entity its `evaluate` names;
* an assumption on the claim that discharges it;
* a claim on its evidence, and an evidence entity on the files its test covers;
* a `lean-theorem` claim on its theorem, a declaration on the declarations its statement uses and on the
  file that defines it;
* a measurement claim on its measurements, a measurement on its files.

The shell builds the graph (`src/core/impact.js`); this file decides which claims a change re-marks: those
from which a changed node is reachable (a changed claim re-marks itself). It also defines when a change of a
`lean-theorem` claim's theorem is a weakening (criterion 11).
-/

namespace Exegra.Impact

open Exegra.Verdict (field strField boolField items strings)

/-- The kinds of node of the dependency graph. -/
inductive NodeKind where
  | claim
  | assumption
  | specEntity
  | leanDecl
  | file
  | measurement
  | evidence
  deriving DecidableEq, Repr, Inhabited

def NodeKind.ofName? : String → Option NodeKind
  | "claim" => some .claim
  | "assumption" => some .assumption
  | "specEntity" => some .specEntity
  | "leanDecl" => some .leanDecl
  | "file" => some .file
  | "measurement" => some .measurement
  | "evidence" => some .evidence
  | _ => none

/-- A node: its kind and its id (an entity id, a declaration name, a repository path). -/
structure Node where
  kind : NodeKind
  id : String
  deriving DecidableEq, Repr, Inhabited

/-- The graph: `(a, b)` means `a` depends on `b`. -/
structure Graph where
  edges : List (Node × Node)
  deriving Inhabited

/-- What `n` depends on directly. -/
def Graph.succ (g : Graph) (n : Node) : List Node :=
  (g.edges.filter (·.1 == n)).map (·.2)

/-- The nodes reachable from `frontier` within `fuel` rounds (each round adds the direct dependencies of
the nodes found so far). -/
def reachN (g : Graph) : Nat → List Node → List Node
  | 0, seen => seen
  | fuel + 1, seen =>
    let next := (seen.flatMap g.succ).filter (fun m => !seen.contains m)
    if next.isEmpty then seen else reachN g fuel (seen ++ next.eraseDups)

/-- Everything a node depends on, itself included. With one round per edge the search is complete. -/
def reach (g : Graph) (n : Node) : List Node := reachN g (g.edges.length + 1) [n]

/-- The claims a change re-marks: every claim from which a changed node is reachable, in the order given. -/
def impacted (g : Graph) (claims : List String) (changed : List Node) : List String :=
  claims.filter fun c => (reach g ⟨.claim, c⟩).any (changed.contains ·)

theorem reachN_mem_self (g : Graph) (fuel : Nat) (seen : List Node) (n : Node) (h : n ∈ seen) :
    n ∈ reachN g fuel seen := by
  induction fuel generalizing seen with
  | zero => exact h
  | succ k ih =>
    simp only [reachN]
    split
    · exact h
    · exact ih _ (List.mem_append_left _ h)

/-- **A changed claim re-marks itself.** -/
theorem changed_claim_impacted (g : Graph) (claims : List String) (changed : List Node) (c : String)
    (hc : c ∈ claims) (hch : ⟨.claim, c⟩ ∈ changed) : c ∈ impacted g claims changed := by
  simp only [impacted, List.mem_filter]
  refine ⟨hc, List.any_eq_true.mpr ⟨⟨.claim, c⟩, reachN_mem_self g _ _ _ (List.mem_singleton.mpr rfl), ?_⟩⟩
  simpa using hch

theorem reachN_mono (g : Graph) (fuel : Nat) (seen : List Node) (m : Node) (h : m ∈ seen) :
    m ∈ reachN g fuel seen := reachN_mem_self g fuel seen m h

/-- One round finds every direct dependency of a node already found, unless nothing new is left. -/
theorem reachN_succ_closed (g : Graph) (fuel : Nat) (seen : List Node) (n m : Node) (hn : n ∈ seen)
    (hm : m ∈ g.succ n) : m ∈ reachN g (fuel + 1) seen := by
  simp only [reachN]
  by_cases hs : m ∈ seen
  · split
    · exact hs
    · exact reachN_mem_self g fuel _ m (List.mem_append_left _ hs)
  · have hnext : m ∈ (seen.flatMap g.succ).filter (fun x => !seen.contains x) := by
      simp only [List.mem_filter, List.mem_flatMap]
      exact ⟨⟨n, hn, hm⟩, by simpa using hs⟩
    split
    · next he =>
      rw [List.isEmpty_iff] at he
      rw [he] at hnext
      cases hnext
    · exact reachN_mem_self g fuel _ m (List.mem_append_right _ (by
        rw [List.mem_eraseDups]; exact hnext))

/-- **A claim that depends directly on a changed node is re-marked.** -/
theorem direct_dependency_impacted (g : Graph) (claims : List String) (changed : List Node) (c : String)
    (n : Node) (hc : c ∈ claims) (he : (⟨.claim, c⟩, n) ∈ g.edges) (hn : n ∈ changed) :
    c ∈ impacted g claims changed := by
  simp only [impacted, List.mem_filter]
  refine ⟨hc, List.any_eq_true.mpr ⟨n, ?_, by simpa using hn⟩⟩
  unfold reach
  apply reachN_succ_closed g g.edges.length [⟨.claim, c⟩] ⟨.claim, c⟩ n (List.mem_singleton.mpr rfl)
  simp only [Graph.succ, List.mem_map, List.mem_filter]
  exact ⟨(⟨.claim, c⟩, n), ⟨he, by simp⟩, rfl⟩

/-! ## Theorem weakening (criterion 11)

A `lean-theorem` claim's theorem, between the check recorded for it before a change and the check after:
the change weakens it when the theorem is removed; or its axiom set gains a member; or its `about` set
changes; or its statement hash changes and the new tree has no theorem, named by the claim's `supersedes`,
whose type is `new statement → old statement` and which passes the Lean gate (a kernel-checked theorem
depending only on the standard axioms). -/

/-- A theorem check, as far as weakening is concerned. `supersedes` is what the checker reported about the
claim's `supersedes` theorem: whether it is a theorem the kernel accepts, its axioms, whether its premise
is the new statement, and the hash of its conclusion. -/
structure Check where
  found : Bool
  axioms : List String
  statementHash : String
  deriving Repr, Inhabited

structure Supersedes where
  found : Bool
  isTheorem : Bool
  kernelOk : Bool
  axioms : List String
  premiseIsNew : Bool
  conclusionHash : String
  deriving Repr, Inhabited

/-- Why a change weakens a theorem. -/
inductive Weakening where
  | removed
  | axiomsGained (extra : List String)
  | aboutChanged
  | statementChanged
  deriving DecidableEq, Repr

def Weakening.code : Weakening → String
  | .removed => "removed"
  | .axiomsGained _ => "axioms-gained"
  | .aboutChanged => "about-changed"
  | .statementChanged => "statement-changed"

/-- Whether a `supersedes` theorem shows that the new statement implies the old one and passes the gate. -/
def Supersedes.implies (s : Supersedes) (oldHash : String) : Bool :=
  s.found && s.isTheorem && s.kernelOk && s.axioms.all (Verdict.standardAxioms.contains ·) &&
    s.premiseIsNew && s.conclusionHash == oldHash

/-- Whether two lists hold the same members. -/
def sameSet (a b : List String) : Bool := a.all (b.contains ·) && b.all (a.contains ·)

/-- The weakening a change makes, if any. -/
def weakening (old : Check) (new : Option Check) (oldAbout newAbout : List String)
    (sup : Option Supersedes) : Option Weakening :=
  match new with
  | none => some .removed
  | some n =>
    if !n.found then some .removed
    else
      let extra := n.axioms.filter (fun a => !old.axioms.contains a)
      if !extra.isEmpty then some (.axiomsGained extra)
      else if !sameSet oldAbout newAbout then some .aboutChanged
      else if n.statementHash == old.statementHash then none
      else match sup with
        | some s => if s.implies old.statementHash then none else some .statementChanged
        | none => some .statementChanged

/-- Whether the change is a change of the guarantee (the statement changed), weakening or not. -/
def statementChanged (old : Check) (new : Option Check) : Bool :=
  match new with
  | none => true
  | some n => n.statementHash != old.statementHash

/-- **A proof-only change is no weakening**: same statement, axioms and `about` set. -/
theorem proof_only_not_weakened (old new : Check) (about : List String) (sup : Option Supersedes)
    (hf : new.found = true) (ha : new.axioms = old.axioms) (hs : new.statementHash = old.statementHash) :
    weakening old (some new) about about sup = none := by
  have hsame : sameSet about about = true := by
    simp [sameSet, List.all_eq_true]
  simp [weakening, hf, ha, hsame, hs]

/-- **A changed statement without a superseding implication is a weakening.** -/
theorem statement_change_weakens (old new : Check) (about : List String)
    (hf : new.found = true) (ha : new.axioms = old.axioms) (hs : new.statementHash ≠ old.statementHash) :
    weakening old (some new) about about none = some .statementChanged := by
  have hsame : sameSet about about = true := by
    simp [sameSet, List.all_eq_true]
  simp [weakening, hf, ha, hsame, hs]

/-! ## Decoding and the call boundary -/

def decodeNode (v : Value) : Except String Node := do
  let some kind := strField v "kind" >>= NodeKind.ofName? | throw s!"unknown node kind {Json.write (field v "kind")}"
  let some id := strField v "id" | throw "a node needs an id"
  return { kind, id }

def decodeGraph (v : Value) : Except String Graph := do
  let edges ← (items (field v "edges")).mapM fun e => do
    match items e with
    | [a, b] => return (← decodeNode a, ← decodeNode b)
    | _ => throw "an edge is [from, to]"
  return { edges }

/-- `impact.claims`: `{edges: [[from, to]], claims: [id], changed: [node]}` to the ids of the claims the
change re-marks, in the order given. -/
def impactValue (args : Value) : Except String String := do
  let g ← decodeGraph args
  let changed ← (items (field args "changed")).mapM decodeNode
  return Json.write (Verdict.strArr (impacted g (strings (field args "claims")) changed))

def decodeCheck (v : Value) : Option Check :=
  match v with
  | .obj _ _ => some (Check.mk (boolField v "found") (strings (field v "axioms"))
      ((strField v "statementHash").getD ""))
  | _ => none

def decodeSupersedes (v : Value) : Option Supersedes :=
  match v with
  | .obj _ _ => some (Supersedes.mk (boolField v "found") (strField v "kind" == some "theorem")
      (strField v "kernel" == some "ok") (strings (field v "axioms"))
      (boolField v "premiseIsNew") ((strField v "conclusionHash").getD ""))
  | _ => none

/-- `theorem.weakening`: `{items: [{old, new, oldAbout, newAbout}]}` (checks as `tools/lean-theorems.js`
records them; `new` null when the theorem is gone, its `supersedes` the report on the claim's superseding
theorem) to `[{weakened: code | null, statementChanged}]`. -/
def weakeningValue (args : Value) : Except String String := do
  let out ← (items (field args "items")).mapM fun it => do
    let some old := decodeCheck (field it "old") | throw "an item needs the old check"
    let new := decodeCheck (field it "new")
    let sup := decodeSupersedes (field (field it "new") "supersedes")
    let w := weakening old new (strings (field it "oldAbout")) (strings (field it "newAbout")) sup
    return Value.obj 0 [("weakened", match w with | some w => .str w.code | none => .null),
      ("statementChanged", .bool (statementChanged old new))]
  return Json.write (.arr 0 out)

/-- info: 'Exegra.Impact.changed_claim_impacted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms changed_claim_impacted
/-- info: 'Exegra.Impact.direct_dependency_impacted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms direct_dependency_impacted
/-- info: 'Exegra.Impact.proof_only_not_weakened' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms proof_only_not_weakened
/-- info: 'Exegra.Impact.statement_change_weakens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms statement_change_weakens

end Exegra.Impact
