import Exegra.Core.LTS

/-
A minimal guarded-command calculus whose semantics is an `LTS` (docs/foundations.md, M1).

It is the smallest language in which the safety theory of `Exegra.Core.LTS` can be exercised on
programs rather than on hand-written relations. It fixes the choices the behaviour calculus of M2
keeps:

* **Integers.** Values are `Int`, so arithmetic facts are provable (`omega`); a `Float` semantics
  admits no such proof.
* **Total, well-scoped expressions.** A program over `n` variables has expressions `IExpr n` whose
  variables are `Fin n`: a reference to a variable that does not exist cannot be written. Evaluation
  is total; nothing is parsed inside a step.
* **Snapshot reads, by construction.** A command gives each variable at most one new value
  (`update : Fin n → Option (IExpr n)`), every right-hand side evaluated in the state before the
  step (`exec_get`). There is no list of assignments, so neither duplicate assignments nor their
  order exist to be got wrong.
* **Steps labelled by command.** A step of `p.lts` is labelled by the index of the command that
  made it (`Fin p.cmds.length`), so two commands are distinguishable even when they do the same
  thing, as fairness per command (M5) needs.

It is single-sorted (every variable is an `Int`; Booleans occur only as guards). A typed calculus
with several sorts is M2.

A state is the list of the `n` variable values. Every reachable state has length `n`
(`length_invariant`), so `getAt` never reads past the end of a reachable state.
-/

namespace Exegra.Core

/-- Integer expressions over `n` variables. -/
inductive IExpr (n : Nat) where
  | lit (v : Int)
  | var (i : Fin n)
  | add (a b : IExpr n)
  | sub (a b : IExpr n)
  deriving Repr, DecidableEq

/-- Boolean expressions over `n` variables. -/
inductive BExpr (n : Nat) where
  | tt
  | ff
  | lt (a b : IExpr n)
  | le (a b : IExpr n)
  | eq (a b : IExpr n)
  | not (p : BExpr n)
  | and (p q : BExpr n)
  | or (p q : BExpr n)
  deriving Repr, DecidableEq

/-- The value at position `i` of a state (`0` past the end, which a reachable state never is). -/
def getAt (s : List Int) (i : Nat) : Int := (s[i]?).getD 0

variable {n : Nat}

def IExpr.eval (s : List Int) : IExpr n → Int
  | .lit v => v
  | .var i => getAt s i.val
  | .add a b => a.eval s + b.eval s
  | .sub a b => a.eval s - b.eval s

def BExpr.eval (s : List Int) : BExpr n → Bool
  | .tt => true
  | .ff => false
  | .lt a b => decide (a.eval s < b.eval s)
  | .le a b => decide (a.eval s ≤ b.eval s)
  | .eq a b => decide (a.eval s = b.eval s)
  | .not p => !p.eval s
  | .and p q => p.eval s && q.eval s
  | .or p q => p.eval s || q.eval s

/-- A guarded command over `n` variables: when `guard` holds, each variable `i` with
`update i = some e` takes the value of `e` in the state before the step; the others keep theirs. -/
structure Cmd (n : Nat) where
  guard : BExpr n
  update : Fin n → Option (IExpr n)

/-- The new value of variable `j` (`0` for a position that is not a variable). -/
def Cmd.newValue (c : Cmd n) (s : List Int) (j : Nat) : Int :=
  if h : j < n then
    match c.update ⟨j, h⟩ with
    | some e => e.eval s
    | none => getAt s j
  else 0

/-- The state after executing `c` from `s`: the `n` new values. -/
def Cmd.exec (c : Cmd n) (s : List Int) : List Int :=
  (List.range n).map (c.newValue s)

theorem Cmd.exec_length (c : Cmd n) (s : List Int) : (c.exec s).length = n := by
  simp [Cmd.exec]

/-- **Snapshot semantics.** After a command, each variable holds the value its update denotes in
the state *before* the step, or its old value if the command does not update it. -/
theorem Cmd.exec_get (c : Cmd n) (s : List Int) (i : Fin n) :
    getAt (c.exec s) i.val =
      match c.update i with
      | some e => e.eval s
      | none => getAt s i.val := by
  have hi := i.isLt
  simp [Cmd.exec, getAt, Cmd.newValue, hi]

/-- A program over `n` variables: an initial state of length `n` and a list of guarded commands. -/
structure Prog (n : Nat) where
  init : List Int
  init_length : init.length = n
  cmds : List (Cmd n)

/-- The transition system of a program. There is one initial state. A step labelled `i` executes
command `i` when its guard holds; several enabled commands are nondeterministic alternatives. -/
def Prog.lts (p : Prog n) : LTS (List Int) (Fin p.cmds.length) where
  init s := s = p.init
  step s i t := p.cmds[i].guard.eval s = true ∧ t = p.cmds[i].exec s

/-- A program's transition system always has an initial state. -/
theorem Prog.nonVacuous (p : Prog n) : p.lts.NonVacuous := ⟨p.init, rfl⟩

/-- Every reachable state has exactly `n` values. -/
theorem Prog.length_invariant (p : Prog n) : p.lts.Invariant (fun s => s.length = n) := by
  refine LTS.safe_of_inductive (I := fun s => s.length = n) ⟨?_, ?_⟩ (fun _ h => h)
  · intro s hs
    have hs' : s = p.init := hs
    rw [hs']
    exact p.init_length
  · intro s i t _ hst
    rw [hst.2]
    exact Cmd.exec_length _ _

/-- The successors of `s`: one per enabled command. -/
def Prog.succ (p : Prog n) (s : List Int) : List (List Int) :=
  p.cmds.filterMap (fun c => if c.guard.eval s = true then some (c.exec s) else none)

/-- The enumeration of a program's transition system is complete. -/
def Prog.enum (p : Prog n) : LTS.Enum p.lts where
  inits := [p.init]
  succ := p.succ
  init_complete := by
    intro s hs
    have hs' : s = p.init := hs
    simp [hs']
  succ_complete := by
    intro s i t h
    obtain ⟨hg, rfl⟩ := h
    have hg' : p.cmds[i.val].guard.eval s = true := hg
    simp only [Prog.succ, List.mem_filterMap]
    exact ⟨p.cmds[i.val], List.getElem_mem _, by simp [hg']⟩

end Exegra.Core
