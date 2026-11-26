import Exegra.Core.LTS

/-
A minimal guarded-command calculus whose semantics is an `LTS` (docs/foundations.md, M1).

It is the smallest language in which the safety theory of `Exegra.Core.LTS` can be exercised on
programs rather than on hand-written relations, and it fixes three choices that the behaviour
calculus of M2 keeps:

* values are integers (`Int`), so arithmetic facts are provable (`omega`), unlike `Float`;
* expressions are syntax trees with a total denotation (`IExpr.eval`, `BExpr.eval`); nothing is
  parsed inside a step, and no evaluation can fail;
* a command assigns all of its variables simultaneously from the state before the step (snapshot
  reads), so the effect of a command does not depend on the order in which its assignments are
  listed when they assign distinct variables.

A state is the list of variable values; variable `i` is position `i`, reading `0` past the end.
-/

namespace Exegra.Core

/-- Integer expressions. -/
inductive IExpr where
  | lit (n : Int)
  | var (i : Nat)
  | add (a b : IExpr)
  | sub (a b : IExpr)
  deriving Repr, DecidableEq

/-- Boolean expressions. -/
inductive BExpr where
  | tt
  | ff
  | lt (a b : IExpr)
  | le (a b : IExpr)
  | eq (a b : IExpr)
  | not (p : BExpr)
  | and (p q : BExpr)
  | or (p q : BExpr)
  deriving Repr, DecidableEq

/-- The value of variable `i` in state `s` (`0` past the end). -/
def getAt : List Int → Nat → Int
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => getAt xs i

/-- State `s` with variable `i` set to `v` (unchanged past the end). -/
def setAt : List Int → Nat → Int → List Int
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, i + 1, v => x :: setAt xs i v

def IExpr.eval (s : List Int) : IExpr → Int
  | .lit n => n
  | .var i => getAt s i
  | .add a b => a.eval s + b.eval s
  | .sub a b => a.eval s - b.eval s

def BExpr.eval (s : List Int) : BExpr → Bool
  | .tt => true
  | .ff => false
  | .lt a b => decide (a.eval s < b.eval s)
  | .le a b => decide (a.eval s ≤ b.eval s)
  | .eq a b => decide (a.eval s = b.eval s)
  | .not p => !p.eval s
  | .and p q => p.eval s && q.eval s
  | .or p q => p.eval s || q.eval s

/-- A guarded command: when `guard` holds, assign each listed variable the value of its expression,
all evaluated in the state before the step. -/
structure Cmd where
  label : String
  guard : BExpr
  updates : List (Nat × IExpr)

/-- The state after executing `c` from `s`. Every right-hand side reads `s`, not the partially
updated state. -/
def Cmd.exec (c : Cmd) (s : List Int) : List Int :=
  c.updates.foldl (fun acc u => setAt acc u.1 (u.2.eval s)) s

/-- A program: an initial state and a list of guarded commands. -/
structure Prog where
  init : List Int
  cmds : List Cmd

/-- The transition system of a program: one initial state; a step labelled `l` executes an enabled
command labelled `l`. Several enabled commands are nondeterministic alternatives. -/
def Prog.lts (p : Prog) : LTS (List Int) String where
  init s := s = p.init
  step s l t := ∃ c, c ∈ p.cmds ∧ c.label = l ∧ c.guard.eval s = true ∧ t = c.exec s

/-- The successors of `s`: one per enabled command. -/
def Prog.succ (p : Prog) (s : List Int) : List (List Int) :=
  p.cmds.filterMap (fun c => if c.guard.eval s = true then some (c.exec s) else none)

/-- The enumeration of a program's transition system is complete. -/
def Prog.enum (p : Prog) : LTS.Enum p.lts where
  inits := [p.init]
  succ := p.succ
  init_complete := by
    intro s hs
    simp [Prog.lts] at hs
    simp [hs]
  succ_complete := by
    intro s a t h
    obtain ⟨c, hc, -, hg, rfl⟩ := h
    simp only [Prog.succ, List.mem_filterMap]
    exact ⟨c, hc, by simp [hg]⟩

/-- **Snapshot reads.** Two updates to distinct variables give the same state in either order. -/
theorem exec_swap (g : BExpr) (l : String) (i j : Nat) (e f : IExpr) (hij : i ≠ j)
    (s : List Int) :
    Cmd.exec ⟨l, g, [(i, e), (j, f)]⟩ s = Cmd.exec ⟨l, g, [(j, f), (i, e)]⟩ s := by
  simp only [Cmd.exec, List.foldl]
  exact setAt_comm hij
where
  setAt_comm {i j : Nat} (hij : i ≠ j) {s : List Int} {v w : Int} :
      setAt (setAt s i v) j w = setAt (setAt s j w) i v := by
    induction s generalizing i j with
    | nil => simp [setAt]
    | cons x xs ih =>
      cases i with
      | zero =>
        cases j with
        | zero => exact absurd rfl hij
        | succ j => simp [setAt]
      | succ i =>
        cases j with
        | zero => simp [setAt]
        | succ j =>
          simp only [setAt]
          rw [ih (fun h => hij (by rw [h]))]

end Exegra.Core
