import Exegra.Core.LTS

/-
The instantaneous behaviour calculus (docs/foundations.md, M2; docs/assessment/2026-11-26/plan-M2.md,
increment M2.1).

Exegra's behaviours (machines with control states and typed variables, reacting to events by
guarded transitions whose effects set the machine's own variables and emit events) as a typed
calculus whose semantics is an `LTS` of `Exegra.Core.LTS`. It keeps the choices of
`Exegra.Core.Calculus` and adds sorts, events, payloads and errors:

* **Values** are `Int`, `Bool` or `String`; integer arithmetic is exact. No error is turned into a
  default value.
* **Arithmetic as format 2 computes it** (formal/Exegra/Expr.lean). Every arithmetic node (`+`, `-`,
  `*`, `/`, `%` and unary `-`) carries its arithmetic sort `ATy`: the declared integer type format 2's
  `staticTy` gives the node (Expr.lean:267-277: the type of its first operand that has one), or
  `untyped`. On a typed node both operands and the exact result must lie in the type's range, as
  format 2's `intResult` checks on every operator (Expr.lean:289-297; unary minus checks `x`, `0` and
  `-x`, Expr.lean:324): an operand out of range is the error `operand`, a result out of range
  `overflow`. `%` is the truncated remainder `Int.tmod` (sign of the dividend), format 2's `Num.fmod`
  (Number.lean:67-69, Expr.lean:364), and typed `/` is the truncated quotient `Int.tdiv`, format 2's
  `divIn` (Expr.lean:299-304, 363); a zero divisor is `divZero`, before any range check, as in format
  2. Untyped arithmetic is checked in the range `±(2^53 - 1)` (`Ty.num`), operands and result, and an
  untyped `/` with a remainder is the error `inexact`. Where format 2 computes an untyped value the
  calculus does not represent (a fraction, an IEEE result beyond `2^53`), the calculus reports an
  error, never another value; on every success its value is the one format 2 computes, because
  format 2's doubles are exact on integers within `2^53` (the comment of `intResult`).
* **Scoped references.** A machine's expressions are `Expr S me`: its own variables are
  `Fin (S.vars me).length`, other machines `Fin S.machines`, so a reference to a variable or machine
  that does not exist cannot be written. A state of the wrong shape (a variable list shorter than
  the signature says) is not excluded by typing; reading or writing past its end is the error
  `shape`, never `0` and never a no-op. From a configuration of the right shape (`Cfg.Shaped`) no
  step fails with `shape` and every step keeps the shape (`shaped_invariant`, `deliver_ne_shape`).
* **Snapshot reads.** During the step that delivers an entry, every guard reads the configuration
  at the start of the step, and every effect reads other machines, their control states and the
  time from that snapshot; only the machine's own variables are read as its earlier effects in the
  same transition left them. Writes are confined to the winner's own machine.
* **The queue.** Phase 2 returns the entries each winner emitted, as one block per winner tagged
  with its machine. The step puts them into the pending list in machine-index order (whatever the
  order the winners fired in), each inserted after every pending entry of no later time, as format
  2's `insertE` does (Format2.lean:1022-1025). Format 2 fires winners in listing order, which is
  machine-index order here, so for a given listing the queue is format 2's.
* **Errors are states.** A delivery that fails leads to the explicit state `.err c` (the
  configuration before the step), which has no successor (`err_deadlocked`). A safety property is
  stated so that `.err` violates it, so a failing run is a counterexample, never silently absent
  (review-M1, finding 6).
* **Labels.** A step is labelled by the position of the delivered entry in the pending list; any
  entry of minimal time may be delivered.

What is proved here:

* `lts_nonVacuous`: every system has an initial state, so its invariants are not vacuous;
* `err_deadlocked`: the error state has no successor;
* `deliver_none_of_length_le`: only an index into the pending list labels a step;
* `deadlocked_of_pending_nil`: a running configuration with nothing pending has no successor;
* `phase2_perm` (with `phase2_perm_emitted`): when the winners of a step are on distinct machines,
  the machines after phase 2 do not depend on the order in which the winners fire, and when both
  orders succeed the emitted blocks are permutations of each other. It holds for every starting list
  of machines, not only the snapshot;
* `winners_nodup`: the winners a step computes are on distinct machines, so `phase2_perm` applies to
  every step;
* `deliver_perm`: **the whole delivery does not depend on the order of the winners**. Firing the
  winners a step computes in any order (any permutation, chosen per configuration and entry) gives
  the same successor state as `deliver`: the same configuration (time, machines and pending list,
  equal, not only up to a permutation), or the error state in both. Which error is reported may
  depend on the order; the state, which does not carry it, does not;
* `shaped_invariant`, `deliver_ne_shape`, `shape_unreachable`: from a shaped initial configuration
  every reachable state is shaped (each machine with a control state of its own and one value of the
  declared sort per variable), and no step from a reachable configuration fails with `shape`;
* `Expr.eval_fits`: the static sort `Expr.ty?` is sound for evaluation: in a context whose snapshot is
  shaped, whose own variables fit their sorts and whose time is within `maxSafe`, a value an
  expression evaluates to fits the sort `ty?` gives it (an integer literal has the one-point range of
  its value, an arithmetic node the range of its arithmetic sort, a payload field is checked against
  its sort when read).

What is not here (later increments of the plan): timers, faults, the bound on time, `stopAt` and
draws (M2.2, M2.8); payload literals beyond integers, Booleans and strings (`Lit`, M2.2); a static
well-formedness predicate `Sys.WF` (M2.2: guards of sort `bool`, effects that fit the sorts they
write, from which no step fails with `sort`; `Expr.eval_fits` is the lemma it rests on); the executable scheduler and `step_sound`, `successors_complete` (M2.3); the
elaboration of format-2 input (M2.4), which must give each arithmetic node format 2's `staticTy`. No
theorem here is about the format-2 interpreter (`Exegra.V2`), which still computes with `Float`.
-/

namespace Exegra.Core.Behav

/-! ### Sorts and values -/

/-- The largest magnitude of an integer without a declared range (`2^53 - 1`). -/
def maxSafe : Int := 9007199254740991

/-- Sorts. An integer sort carries its range. -/
inductive Ty where
  | int (lo hi : Int)
  | bool
  | str
  deriving DecidableEq, Repr

/-- The integer sort of untyped numbers. -/
def Ty.num : Ty := .int (-maxSafe) maxSafe

inductive Val where
  | int (v : Int)
  | bool (b : Bool)
  | str (s : String)
  deriving DecidableEq, Repr

/-- Errors of a step. -/
inductive Err where
  | divZero
  | inexact
  /-- An arithmetic result outside the range of the node's sort. -/
  | overflow
  /-- An operand of an arithmetic node outside the range of the node's sort (format 2: "operand
  … is not a …", Expr.lean:292-293). -/
  | operand
  | absentField (f : Nat)
  | fieldSort (f : Nat)
  | sort
  | shape
  deriving DecidableEq, Repr

/-- `v` is a value of sort `τ` (for an integer sort: within its range). -/
def Val.fits : Val → Ty → Bool
  | .int v, .int lo hi => decide (lo ≤ v) && decide (v ≤ hi)
  | .bool _, .bool => true
  | .str _, .str => true
  | _, _ => false

/-- The same sort, ignoring integer ranges. -/
def Val.sameSort : Val → Ty → Bool
  | .int _, .int _ _ => true
  | .bool _, .bool => true
  | .str _, .str => true
  | _, _ => false

/-- Checks that `v` fits `τ`: an integer out of range is `overflow`, another sort `sort`. -/
def Val.check (τ : Ty) (v : Val) : Except Err Val :=
  if v.fits τ then .ok v else if v.sameSort τ then .error .overflow else .error .sort

/-! ### Arithmetic sorts and operators -/

/-- The sort an arithmetic node computes in: a declared integer type, or none (format 2's `STy`
restricted to arithmetic, Value.lean:201-206; the range of each `IntKind` is `[lo, hi]`). -/
inductive ATy where
  | untyped
  | int (lo hi : Int)
  deriving DecidableEq, Repr

def ATy.lo : ATy → Int
  | .untyped => -maxSafe
  | .int lo _ => lo

def ATy.hi : ATy → Int
  | .untyped => maxSafe
  | .int _ hi => hi

/-- `v` lies in the range of `τ`. -/
def ATy.holds (τ : ATy) (v : Int) : Bool := decide (τ.lo ≤ v) && decide (v ≤ τ.hi)

/-- The sort of the values an arithmetic node of sort `τ` produces. -/
def ATy.ty : ATy → Ty
  | .untyped => .num
  | .int lo hi => .int lo hi

inductive AOp where
  | add | sub | mul | div | mod
  deriving DecidableEq, Repr

/-- The result `r` of an arithmetic operator on `a` and `b` in sort `τ`: format 2's `intResult`
(Expr.lean:289-297), which checks the left operand, then the right one, then the result. -/
def checked (τ : ATy) (a b r : Int) : Except Err Val :=
  if !τ.holds a then .error .operand
  else if !τ.holds b then .error .operand
  else if τ.holds r then .ok (.int r) else .error .overflow

/-- An arithmetic operator in sort `τ` (format 2: Expr.lean:359-364). `/` and `%` by zero are
`divZero` before any range check; `%` is truncated (`Int.tmod`, format 2's `Num.fmod`); a typed `/`
truncates (`Int.tdiv`, format 2's `divIn`); an untyped `/` must be exact. -/
def AOp.apply (op : AOp) (τ : ATy) (a b : Int) : Except Err Val :=
  match op with
  | .add => checked τ a b (a + b)
  | .sub => checked τ a b (a - b)
  | .mul => checked τ a b (a * b)
  | .div =>
    if b = 0 then .error .divZero
    else match τ with
      | .untyped => if a.tmod b = 0 then checked τ a b (a.tdiv b) else .error .inexact
      | .int _ _ => checked τ a b (a.tdiv b)
  | .mod => if b = 0 then .error .divZero else checked τ a b (a.tmod b)

/-! ### Signatures, references, expressions -/

/-- The machines of a system, their variables' sorts and their control-state names. -/
structure Sig where
  machines : Nat
  vars : Fin machines → List Ty
  states : Fin machines → List String

/-- What an expression of machine `me` can read. -/
inductive Ref (S : Sig) (me : Fin S.machines) where
  /-- One of the machine's own variables, as its earlier effects in this transition left it. -/
  | own (v : Fin (S.vars me).length)
  /-- A variable of machine `m`, in the snapshot. -/
  | other (m : Fin S.machines) (v : Fin (S.vars m).length)
  /-- The name of the control state of machine `m`, in the snapshot. -/
  | state (m : Fin S.machines)
  /-- Field `f` of the delivered entry's payload, at sort `τ`. -/
  | field (f : Nat) (τ : Ty)
  /-- The time of the step. -/
  | time

inductive UOp where
  /-- Unary minus in an arithmetic sort. -/
  | neg (τ : ATy)
  | not
  deriving DecidableEq, Repr

inductive BOp where
  /-- An arithmetic operator in an arithmetic sort. -/
  | arith (op : AOp) (τ : ATy)
  | lt | le | eq | ne
  | and | or | imp
  deriving DecidableEq, Repr

inductive Expr (S : Sig) (me : Fin S.machines) where
  | val (v : Val)
  | ref (r : Ref S me)
  | un (op : UOp) (a : Expr S me)
  | bin (op : BOp) (a b : Expr S me)

/-! ### Configurations and states -/

/-- A machine at run time: the index of its control state and its variable values. -/
structure MState where
  ctrl : Nat
  vars : List Val
  deriving DecidableEq, Repr

/-- A pending delivery: its time, its event and its payload fields. -/
structure Entry where
  time : Nat
  event : Nat
  payload : List (Nat × Val)
  deriving DecidableEq, Repr

structure Cfg where
  time : Nat
  machines : List MState
  pending : List Entry
  deriving DecidableEq, Repr

/-- A state of the transition system: running, or failed with the configuration before the
failing step. -/
inductive State where
  | run (c : Cfg)
  | err (c : Cfg)
  deriving DecidableEq, Repr

def State.ok : State → Bool
  | .run _ => true
  | .err _ => false

/-! ### Static typing (sound for evaluation: `Expr.eval_fits`) -/

def Ref.ty? {S : Sig} {me : Fin S.machines} : Ref S me → Option Ty
  | .own v => some ((S.vars me).get v)
  | .other m v => some ((S.vars m).get v)
  | .state _ => some .str
  | .field _ τ => some τ
  | .time => some (.int 0 maxSafe)

def Ty.isInt : Ty → Bool
  | .int _ _ => true
  | _ => false

/-- Two sorts are comparable: both integers, both Booleans or both strings. -/
def Ty.comparable : Ty → Ty → Bool
  | .int _ _, .int _ _ => true
  | .bool, .bool => true
  | .str, .str => true
  | _, _ => false

/-- The sort of a literal: an integer literal has the one-point range of its value. -/
def Val.ty : Val → Ty
  | .int v => .int v v
  | .bool _ => .bool
  | .str _ => .str

def BOp.ty? (op : BOp) (a b : Ty) : Option Ty :=
  match op with
  | .arith _ τ => if a.isInt && b.isInt then some τ.ty else none
  | .lt | .le => if a.isInt && b.isInt then some .bool else none
  | .eq | .ne => if a.comparable b then some .bool else none
  | .and | .or | .imp => if a == .bool && b == .bool then some .bool else none

def Expr.ty? {S : Sig} {me : Fin S.machines} : Expr S me → Option Ty
  | .val v => some v.ty
  | .ref r => r.ty?
  | .un (.neg τ) a => match a.ty? with
    | some υ => if υ.isInt then some τ.ty else none
    | none => none
  | .un .not a => match a.ty? with
    | some .bool => some .bool
    | _ => none
  | .bin op a b => match a.ty?, b.ty? with
    | some τ, some υ => op.ty? τ υ
    | _, _ => none

/-! ### Evaluation -/

/-- What an expression is evaluated against: the snapshot (the start-of-step machines and time),
the machine's own state as its earlier effects left it, and the payload of the delivered entry. -/
structure Ctx where
  snap : List MState
  time : Nat
  own : MState
  payload : List (Nat × Val)

/-- The value of field `f` of a payload. -/
def lookupField (f : Nat) : List (Nat × Val) → Option Val
  | [] => none
  | (g, v) :: rest => if f = g then some v else lookupField f rest

/-- Element `i` of a list, or the error `shape`. -/
def at? {β : Type} (l : List β) (i : Nat) : Except Err β :=
  match l[i]? with
  | some x => .ok x
  | none => .error .shape

/-- A payload field is read at its sort: a value that does not fit it (another sort, or an integer
outside its range) is the error `fieldSort`. -/
def Ref.eval {S : Sig} {me : Fin S.machines} (cx : Ctx) : Ref S me → Except Err Val
  | .own v => at? cx.own.vars v.val
  | .other m v => match at? cx.snap m.val with
    | .ok ms => at? ms.vars v.val
    | .error e => .error e
  | .state m => match at? cx.snap m.val with
    | .ok ms => match at? (S.states m) ms.ctrl with
      | .ok name => .ok (.str name)
      | .error e => .error e
    | .error e => .error e
  | .field f τ => match lookupField f cx.payload with
    | none => .error (.absentField f)
    | some v => if v.fits τ then .ok v else .error (.fieldSort f)
  | .time => .ok (.int cx.time)

def UOp.apply : UOp → Val → Except Err Val
  | .neg τ, .int v => checked τ v 0 (-v)
  | .not, .bool b => .ok (.bool (!b))
  | _, _ => .error .sort

/-- A strict binary operator on two values (every operator except `and`, `or`, `imp`). -/
def BOp.apply : BOp → Val → Val → Except Err Val
  | .arith op τ, .int a, .int b => op.apply τ a b
  | .lt, .int a, .int b => .ok (.bool (decide (a < b)))
  | .le, .int a, .int b => .ok (.bool (decide (a ≤ b)))
  | .eq, a, b => if Val.sameSort a b.ty then .ok (.bool (a == b)) else .error .sort
  | .ne, a, b => if Val.sameSort a b.ty then .ok (.bool (a != b)) else .error .sort
  | _, _, _ => .error .sort

/-- Evaluation. `and`, `or` and `imp` short-circuit: the right operand is not evaluated, and so
cannot fail, when the left one decides the result. -/
def Expr.eval {S : Sig} {me : Fin S.machines} (cx : Ctx) : Expr S me → Except Err Val
  | .val v => .ok v
  | .ref r => r.eval cx
  | .un op a => match a.eval cx with
    | .ok v => op.apply v
    | .error e => .error e
  | .bin .and a b => match a.eval cx with
    | .ok (.bool false) => .ok (.bool false)
    | .ok (.bool true) => match b.eval cx with
      | .ok (.bool q) => .ok (.bool q)
      | .ok _ => .error .sort
      | .error e => .error e
    | .ok _ => .error .sort
    | .error e => .error e
  | .bin .or a b => match a.eval cx with
    | .ok (.bool true) => .ok (.bool true)
    | .ok (.bool false) => match b.eval cx with
      | .ok (.bool q) => .ok (.bool q)
      | .ok _ => .error .sort
      | .error e => .error e
    | .ok _ => .error .sort
    | .error e => .error e
  | .bin .imp a b => match a.eval cx with
    | .ok (.bool false) => .ok (.bool true)
    | .ok (.bool true) => match b.eval cx with
      | .ok (.bool q) => .ok (.bool q)
      | .ok _ => .error .sort
      | .error e => .error e
    | .ok _ => .error .sort
    | .error e => .error e
  | .bin op a b => match a.eval cx, b.eval cx with
    | .ok x, .ok y => op.apply x y
    | .error e, _ => .error e
    | .ok _, .error e => .error e

/-! ### Effects, transitions, systems -/

inductive Effect (S : Sig) (me : Fin S.machines) where
  /-- Set one of the machine's own variables. -/
  | set (v : Fin (S.vars me).length) (rhs : Expr S me)
  /-- Emit `event`, `after` time units from now, with the given payload fields. -/
  | emit (event : Nat) (after : Nat) (payload : List (Nat × Expr S me))

/-- A transition of machine `me`: from control state `src`, on `event`, when `guard` holds, run
`effects` in order and move to `dst`. -/
structure Trans (S : Sig) (me : Fin S.machines) where
  src : Fin (S.states me).length
  dst : Fin (S.states me).length
  event : Nat
  guard : Expr S me
  effects : List (Effect S me)

/-- A system: a signature, the transitions of each machine in declaration order, and the initial
configuration. -/
structure Sys where
  sig : Sig
  trans : (m : Fin sig.machines) → List (Trans sig m)
  init : Cfg

/-- A transition chosen to fire in a step: the machine and the index of its transition. -/
structure Winner (sys : Sys) where
  mach : Fin sys.sig.machines
  idx : Fin (sys.trans mach).length

/-- The entries emitted in a step, one block per winner that fired: the index of its machine and
the entries its transition emitted, in emission order. -/
abbrev Emitted := List (Nat × List Entry)

/-! ### One step -/

/-- The context of machine state `own` for the step delivering `e` from configuration `c`. -/
def ctxOf (c : Cfg) (e : Entry) (own : MState) : Ctx :=
  { snap := c.machines, time := c.time, own := own, payload := e.payload }

def evalPayload {S : Sig} {me : Fin S.machines} (cx : Ctx) :
    List (Nat × Expr S me) → Except Err (List (Nat × Val))
  | [] => .ok []
  | (f, x) :: rest => match x.eval cx with
    | .error err => .error err
    | .ok v => match evalPayload cx rest with
      | .error err => .error err
      | .ok vs => .ok ((f, v) :: vs)

/-- Runs effects in order. Each reads the snapshot of `c` for other machines and time, and `own`
as the earlier effects left it; it writes only `own` and the emitted entries. -/
def runEffects {S : Sig} {me : Fin S.machines} (c : Cfg) (e : Entry) :
    List (Effect S me) → MState → Except Err (MState × List Entry)
  | [], own => .ok (own, [])
  | .set v rhs :: rest, own =>
    match rhs.eval (ctxOf c e own) with
    | .error err => .error err
    | .ok x => match Val.check ((S.vars me).get v) x with
      | .error err => .error err
      | .ok x =>
        if v.val < own.vars.length then
          runEffects c e rest { own with vars := own.vars.set v.val x }
        else .error .shape
  | .emit ev after pl :: rest, own =>
    match evalPayload (ctxOf c e own) pl with
    | .error err => .error err
    | .ok vs => match runEffects c e rest own with
      | .error err => .error err
      | .ok (st, outs) => .ok (st, { time := c.time + after, event := ev, payload := vs } :: outs)

/-- Fires winner `w` from its machine state `own`: the effects, then the move to `dst`. It reads
only `own` and the snapshot `c`. -/
def fireOne (sys : Sys) (c : Cfg) (e : Entry) (w : Winner sys) (own : MState) :
    Except Err (MState × List Entry) :=
  let t := (sys.trans w.mach).get w.idx
  match runEffects c e t.effects own with
  | .error err => .error err
  | .ok (st, outs) => .ok ({ st with ctrl := t.dst.val }, outs)

/-- Phase 2: the winners fire in list order, each from its machine as the list `ms` holds it, and
each writes its result back into `ms`. Other machines are read from the snapshot `c` only. The
entries each winner emits are returned as a block tagged with its machine. -/
def phase2 (sys : Sys) (c : Cfg) (e : Entry) :
    List (Winner sys) → List MState → Except Err (List MState × Emitted)
  | [], ms => .ok (ms, [])
  | w :: ws, ms =>
    match ms[w.mach.val]? with
    | none => .error .shape
    | some own =>
      match fireOne sys c e w own with
      | .error err => .error err
      | .ok (st, out) =>
        match phase2 sys c e ws (ms.set w.mach.val st) with
        | .error err => .error err
        | .ok (ms', outs) => .ok (ms', (w.mach.val, out) :: outs)

/-- For contrast, the calculus's model of today's rule (format 1 and format 2): each winner reads
other machines from the configuration being written, `ms`, as earlier winners left it. It is not
linked to `Exegra.V2` by any theorem. -/
def phase2Next (sys : Sys) (c : Cfg) (e : Entry) :
    List (Winner sys) → List MState → Except Err (List MState × Emitted)
  | [], ms => .ok (ms, [])
  | w :: ws, ms =>
    match ms[w.mach.val]? with
    | none => .error .shape
    | some own =>
      match fireOne sys { c with machines := ms } e w own with
      | .error err => .error err
      | .ok (st, out) =>
        match phase2Next sys c e ws (ms.set w.mach.val st) with
        | .error err => .error err
        | .ok (ms', outs) => .ok (ms', (w.mach.val, out) :: outs)

/-- The list `[0, …, n - 1]` of `Fin n`, by structural recursion (so that kernel evaluation unfolds
it). -/
def finList : (n : Nat) → List (Fin n)
  | 0 => []
  | n + 1 => ⟨0, Nat.succ_pos n⟩ :: (finList n).map Fin.succ

/-- The first transition of machine `m`, among the candidate indices `is`, that leaves `own`'s
control state on the delivered event and whose guard evaluates to `true` on the snapshot. A guard
that fails, or yields a non-Boolean, is an error. -/
def scan (sys : Sys) (c : Cfg) (e : Entry) (m : Fin sys.sig.machines) (own : MState) :
    List (Fin (sys.trans m).length) → Except Err (Option (Fin (sys.trans m).length))
  | [] => .ok none
  | i :: is =>
    let t := (sys.trans m).get i
    if t.src.val = own.ctrl ∧ t.event = e.event then
      match t.guard.eval (ctxOf c e own) with
      | .ok (.bool true) => .ok (some i)
      | .ok (.bool false) => scan sys c e m own is
      | .ok _ => .error .sort
      | .error err => .error err
    else scan sys c e m own is

/-- Phase 1 for machine `m`: its winning transition, if any, with guards on the snapshot. -/
def choose (sys : Sys) (c : Cfg) (e : Entry) (m : Fin sys.sig.machines) :
    Except Err (Option (Winner sys)) :=
  match at? c.machines m.val with
  | .error err => .error err
  | .ok own => match scan sys c e m own (finList (sys.trans m).length) with
    | .error err => .error err
    | .ok none => .ok none
    | .ok (some i) => .ok (some { mach := m, idx := i })

/-- Phase 1 over the machines `ms`, in list order. -/
def winnersOf (sys : Sys) (c : Cfg) (e : Entry) :
    List (Fin sys.sig.machines) → Except Err (List (Winner sys))
  | [] => .ok []
  | m :: ms => match choose sys c e m with
    | .error err => .error err
    | .ok w => match winnersOf sys c e ms with
      | .error err => .error err
      | .ok ws => .ok (match w with | some w => w :: ws | none => ws)

/-- The winners of a step, in machine-index order. -/
def winners (sys : Sys) (c : Cfg) (e : Entry) : Except Err (List (Winner sys)) :=
  winnersOf sys c e (finList sys.sig.machines)

/-- The block of machine `m`: the entries it emitted, or none. -/
def blockOf (m : Nat) : Emitted → List Entry
  | [] => []
  | (i, out) :: bs => if i = m then out else blockOf m bs

/-- The emitted entries of a system of `n` machines in machine-index order, whatever the order of
the blocks. -/
def inMachineOrder (n : Nat) (bs : Emitted) : List Entry :=
  (List.range n).flatMap (fun m => blockOf m bs)

/-- Inserts `e` after every entry of `q` whose time is not later than its own: format 2's `insertE`
(Format2.lean:1022-1025), on the same key. -/
def insertByTime (q : List Entry) (e : Entry) : List Entry :=
  let later := (q.reverse.takeWhile fun p => decide (p.time > e.time)).length
  let pos := q.length - later
  q.take pos ++ [e] ++ q.drop pos

/-- The configuration after a step from `c0` (time advanced, delivered entry removed) whose phase 2
gave `r`: the machines phase 2 left, and the emitted entries inserted into the pending list by time,
in machine-index order. -/
def afterPhase2 (sys : Sys) (c0 : Cfg) : Except Err (List MState × Emitted) → Except Err Cfg
  | .error err => .error err
  | .ok (ms, bs) =>
    .ok { c0 with machines := ms,
                  pending := (inMachineOrder sys.sig.machines bs).foldl insertByTime c0.pending }

/-- The delivery of the pending entry at index `k`, with phase 2 given by `p2`. -/
def deliverWith (sys : Sys)
    (p2 : Cfg → Entry → List (Winner sys) → List MState → Except Err (List MState × Emitted))
    (c : Cfg) (k : Nat) : Option (Except Err Cfg) :=
  match c.pending[k]? with
  | none => none
  | some e =>
    if c.pending.all (fun x => decide (e.time ≤ x.time)) then
      let c0 : Cfg := { c with time := e.time, pending := c.pending.eraseIdx k }
      some (match winners sys c0 e with
        | .error err => .error err
        | .ok ws => afterPhase2 sys c0 (p2 c0 e ws c0.machines))
    else none

/-- Delivers the pending entry at index `k`. `none`: `k` is not the index of an entry of minimal
time, so no step has this label. `some (.error _)`: the step fails. Guards read the configuration
at the start of the step, with the time advanced to the entry's; the winners fire in machine order
under snapshot reads (`phase2`); emitted entries are inserted by time, in machine-index order. -/
def deliver (sys : Sys) (c : Cfg) (k : Nat) : Option (Except Err Cfg) :=
  deliverWith sys (phase2 sys) c k

/-- For contrast, the same delivery under the next-configuration reads of `phase2Next`. -/
def deliverNext (sys : Sys) (c : Cfg) (k : Nat) : Option (Except Err Cfg) :=
  deliverWith sys (phase2Next sys) c k

/-- The state a delivery leads to from `c`: the new configuration, or the error state carrying
`c`. -/
def outcome (c : Cfg) : Except Err Cfg → State
  | .ok c' => .run c'
  | .error _ => .err c

/-- The transition system of a system: one initial state; a step labelled `k` delivers the pending
entry at index `k` when its time is minimal. The error state has no successor. -/
def Sys.lts (sys : Sys) : LTS State Nat where
  init s := s = .run sys.init
  step s k t := match s with
    | .run c => (deliver sys c k).map (outcome c) = some t
    | .err _ => False

/-! ### Basic facts -/

/-- **Non-vacuity.** Every system has an initial state. -/
theorem lts_nonVacuous (sys : Sys) : (Sys.lts sys).NonVacuous := ⟨.run sys.init, rfl⟩

/-- **The error state has no successor.** -/
theorem err_deadlocked (sys : Sys) (c : Cfg) : (Sys.lts sys).Deadlocked (.err c) :=
  fun _ _ h => h

/-- Only an index into the pending list labels a step. -/
theorem deliver_none_of_length_le (sys : Sys) (c : Cfg) {k : Nat} (h : c.pending.length ≤ k) :
    deliver sys c k = none := by
  simp only [deliver, deliverWith, List.getElem?_eq_none h]

/-- A configuration with nothing pending has no successor. -/
theorem deadlocked_of_pending_nil (sys : Sys) (c : Cfg) (h : c.pending = []) :
    (Sys.lts sys).Deadlocked (.run c) := by
  intro k t hst
  have hn : deliver sys c k = none :=
    deliver_none_of_length_le sys c (by rw [h]; exact Nat.zero_le k)
  have hst' : (deliver sys c k).map (outcome c) = some t := hst
  rw [hn] at hst'
  cases hst'

/-- Inserting an entry into the queue only reorders: the result is a permutation of `e :: q`. -/
theorem insertByTime_perm (q : List Entry) (e : Entry) : (insertByTime q e).Perm (e :: q) := by
  simp only [insertByTime, List.append_assoc, List.singleton_append]
  exact List.perm_middle.trans (by rw [List.take_append_drop])

/-! ### Phase 2 does not depend on the order of the winners -/

/-- The machines after phase 2, if it succeeds. -/
def machinesAfter (r : Except Err (List MState × Emitted)) : Option (List MState) :=
  r.toOption.map Prod.fst

theorem machinesAfter_cons_ok {sys : Sys} {c : Cfg} {e : Entry} {w : Winner sys}
    {ws : List (Winner sys)} {ms : List MState} {own st : MState} {out : List Entry}
    (hown : ms[w.mach.val]? = some own) (hf : fireOne sys c e w own = .ok (st, out)) :
    machinesAfter (phase2 sys c e (w :: ws) ms) =
      machinesAfter (phase2 sys c e ws (ms.set w.mach.val st)) := by
  simp only [phase2, hown, hf]
  cases phase2 sys c e ws (ms.set w.mach.val st) with
  | error err => rfl
  | ok r => rfl

/-- Two winners on distinct machines can be swapped. -/
theorem phase2_swap {sys : Sys} {c : Cfg} {e : Entry} (w₁ w₂ : Winner sys)
    (ws : List (Winner sys)) (ms : List MState) (hne : w₁.mach.val ≠ w₂.mach.val) :
    machinesAfter (phase2 sys c e (w₁ :: w₂ :: ws) ms) =
      machinesAfter (phase2 sys c e (w₂ :: w₁ :: ws) ms) := by
  have hne' : w₂.mach.val ≠ w₁.mach.val := fun h => hne h.symm
  have g₁ : ∀ s, (ms.set w₂.mach.val s)[w₁.mach.val]? = ms[w₁.mach.val]? :=
    fun _ => List.getElem?_set_ne hne'
  have g₂ : ∀ s, (ms.set w₁.mach.val s)[w₂.mach.val]? = ms[w₂.mach.val]? :=
    fun _ => List.getElem?_set_ne hne
  cases h₁ : ms[w₁.mach.val]? with
  | none =>
    cases h₂ : ms[w₂.mach.val]? with
    | none => simp [machinesAfter, Except.toOption, phase2, h₁, h₂]
    | some o₂ =>
      cases f₂ : fireOne sys c e w₂ o₂ with
      | error err => simp [machinesAfter, Except.toOption, phase2, h₁, h₂, f₂]
      | ok r₂ => simp [machinesAfter, Except.toOption, phase2, h₁, h₂, f₂, g₁]
  | some o₁ =>
    cases f₁ : fireOne sys c e w₁ o₁ with
    | error err =>
      cases h₂ : ms[w₂.mach.val]? with
      | none => simp [machinesAfter, Except.toOption, phase2, h₁, h₂, f₁]
      | some o₂ =>
        cases f₂ : fireOne sys c e w₂ o₂ with
        | error err₂ => simp [machinesAfter, Except.toOption, phase2, h₁, h₂, f₁, f₂]
        | ok r₂ => simp [machinesAfter, Except.toOption, phase2, h₁, h₂, f₁, f₂, g₁]
    | ok r₁ =>
      obtain ⟨s₁, out₁⟩ := r₁
      cases h₂ : ms[w₂.mach.val]? with
      | none => simp [machinesAfter, Except.toOption, phase2, h₁, h₂, f₁, g₂]
      | some o₂ =>
        cases f₂ : fireOne sys c e w₂ o₂ with
        | error err => simp [machinesAfter, Except.toOption, phase2, h₁, h₂, f₁, f₂, g₂]
        | ok r₂ =>
          obtain ⟨s₂, out₂⟩ := r₂
          have h₂' : (ms.set w₁.mach.val s₁)[w₂.mach.val]? = some o₂ := by rw [g₂, h₂]
          have h₁' : (ms.set w₂.mach.val s₂)[w₁.mach.val]? = some o₁ := by rw [g₁, h₁]
          rw [machinesAfter_cons_ok h₁ f₁, machinesAfter_cons_ok h₂' f₂,
            machinesAfter_cons_ok h₂ f₂, machinesAfter_cons_ok h₁' f₁,
            List.set_comm s₁ s₂ hne]

/-- The machines of two winner lists are distinct when the second is a permutation of the first. -/
theorem nodup_map_of_perm {sys : Sys} {ws ws' : List (Winner sys)} (hp : ws.Perm ws')
    (hnd : (ws.map (·.mach)).Nodup) : (ws'.map (·.mach)).Nodup :=
  (hp.map (·.mach)).nodup hnd

/-- **Phase 2 is independent of the order of the winners, for every starting list.** -/
theorem phase2_perm_from {sys : Sys} {c : Cfg} {e : Entry} {ws ws' : List (Winner sys)}
    (hp : ws.Perm ws') (hnd : (ws.map (·.mach)).Nodup) (ms : List MState) :
    machinesAfter (phase2 sys c e ws ms) = machinesAfter (phase2 sys c e ws' ms) := by
  induction hp generalizing ms with
  | nil => rfl
  | cons w _ ih =>
    have hnd' := (List.nodup_cons.mp hnd).2
    cases h : ms[w.mach.val]? with
    | none => simp only [machinesAfter, phase2, h]
    | some own =>
      cases f : fireOne sys c e w own with
      | error err => simp only [machinesAfter, phase2, h, f]
      | ok r =>
        obtain ⟨st, out⟩ := r
        rw [machinesAfter_cons_ok h f, machinesAfter_cons_ok h f]
        exact ih hnd' _
  | swap x y l =>
    have hne : y.mach ≠ x.mach := by
      have := (List.nodup_cons.mp hnd).1
      intro heq
      apply this
      simp only [List.map_cons, heq]
      exact List.mem_cons_self
    exact phase2_swap y x l ms (fun h => hne (Fin.ext h))
  | trans h₁₂ _ ih₁ ih₂ =>
    exact (ih₁ hnd ms).trans (ih₂ (nodup_map_of_perm h₁₂ hnd) ms)

/-- **Snapshot phase 2 is order-independent** (plan-M2, M2.1). When the winners are on distinct
machines, the machines after phase 2 are the same for every order of the winners (or phase 2 fails
in both orders; which error is reported may depend on the order). The emitted blocks are
`phase2_perm_emitted`; the whole delivery is `deliver_perm`. -/
theorem phase2_perm {sys : Sys} {c : Cfg} {e : Entry}
    {ws ws' : List (Winner sys)} (hp : ws.Perm ws') (hnd : (ws.map (·.mach)).Nodup) :
    (phase2 sys c e ws c.machines).toOption.map Prod.fst =
      (phase2 sys c e ws' c.machines).toOption.map Prod.fst :=
  phase2_perm_from hp hnd c.machines

/-! ### The emitted blocks are permutations -/

/-- `phase2` succeeds exactly when `machinesAfter` is defined. -/
theorem phase2_ok_iff {sys : Sys} {c : Cfg} {e : Entry} {ws : List (Winner sys)}
    {ms : List MState} : (∃ r, phase2 sys c e ws ms = .ok r) ↔ (machinesAfter (phase2 sys c e ws ms)).isSome := by
  cases phase2 sys c e ws ms with
  | error err => simp [machinesAfter, Except.toOption]
  | ok r => simp [machinesAfter, Except.toOption]

theorem phase2_swap_emitted {sys : Sys} {c : Cfg} {e : Entry} (w₁ w₂ : Winner sys)
    (ws : List (Winner sys)) (ms : List MState) (hne : w₁.mach.val ≠ w₂.mach.val)
    {r r' : List MState × Emitted}
    (h : phase2 sys c e (w₁ :: w₂ :: ws) ms = .ok r)
    (h' : phase2 sys c e (w₂ :: w₁ :: ws) ms = .ok r') : r.2.Perm r'.2 := by
  have hne' : w₂.mach.val ≠ w₁.mach.val := fun h => hne h.symm
  -- In both orders the first two fires and the recursive call must succeed.
  cases h₁ : ms[w₁.mach.val]? with
  | none => simp only [phase2, h₁] at h; simp at h
  | some o₁ =>
  cases f₁ : fireOne sys c e w₁ o₁ with
  | error err => simp only [phase2, h₁, f₁] at h; simp at h
  | ok p₁ =>
  obtain ⟨s₁, out₁⟩ := p₁
  cases h₂ : ms[w₂.mach.val]? with
  | none => simp only [phase2, h₂] at h'; simp at h'
  | some o₂ =>
  cases f₂ : fireOne sys c e w₂ o₂ with
  | error err => simp only [phase2, h₂, f₂] at h'; simp at h'
  | ok p₂ =>
  obtain ⟨s₂, out₂⟩ := p₂
  have h₂' : (ms.set w₁.mach.val s₁)[w₂.mach.val]? = some o₂ := by
    rw [List.getElem?_set_ne hne, h₂]
  have h₁' : (ms.set w₂.mach.val s₂)[w₁.mach.val]? = some o₁ := by
    rw [List.getElem?_set_ne hne', h₁]
  have hc : (ms.set w₂.mach.val s₂).set w₁.mach.val s₁ =
      (ms.set w₁.mach.val s₁).set w₂.mach.val s₂ := (List.set_comm s₁ s₂ hne).symm
  simp only [phase2, h₁, f₁, h₂', f₂] at h
  simp only [phase2, h₂, f₂, h₁', f₁, hc] at h'
  cases hr : phase2 sys c e ws ((ms.set w₁.mach.val s₁).set w₂.mach.val s₂) with
  | error err => rw [hr] at h; simp at h
  | ok q =>
    obtain ⟨ms', outs⟩ := q
    rw [hr] at h h'
    have e1 := Except.ok.inj h
    have e2 := Except.ok.inj h'
    subst e1; subst e2
    exact List.Perm.swap _ _ _

/-- The emitted blocks in two orders are permutations, when both succeed. -/
theorem phase2_perm_emitted_from {sys : Sys} {c : Cfg} {e : Entry} {ws ws' : List (Winner sys)}
    (hp : ws.Perm ws') (hnd : (ws.map (·.mach)).Nodup) (ms : List MState)
    {r r' : List MState × Emitted}
    (h : phase2 sys c e ws ms = .ok r) (h' : phase2 sys c e ws' ms = .ok r') : r.2.Perm r'.2 := by
  induction hp generalizing ms r r' with
  | nil =>
    simp only [phase2] at h h'
    rw [← Except.ok.inj h, ← Except.ok.inj h']
  | cons w _ ih =>
    have hnd' := (List.nodup_cons.mp hnd).2
    cases ho : ms[w.mach.val]? with
    | none => simp only [phase2, ho] at h; simp at h
    | some own =>
      cases f : fireOne sys c e w own with
      | error err => simp only [phase2, ho, f] at h; simp at h
      | ok p =>
        obtain ⟨st, out⟩ := p
        simp only [phase2, ho, f] at h h'
        cases hr : phase2 sys c e _ (ms.set w.mach.val st) with
        | error err => rw [hr] at h; simp at h
        | ok q =>
          cases hr' : phase2 sys c e _ (ms.set w.mach.val st) with
          | error err => rw [hr'] at h'; simp at h'
          | ok q' =>
            rw [hr] at h
            rw [hr'] at h'
            rw [← Except.ok.inj h, ← Except.ok.inj h']
            exact (ih hnd' _ hr hr').cons _
  | swap x y l =>
    have hne : y.mach ≠ x.mach := by
      have := (List.nodup_cons.mp hnd).1
      intro heq
      apply this
      simp only [List.map_cons, heq]
      exact List.mem_cons_self
    exact phase2_swap_emitted y x l ms (fun h => hne (Fin.ext h)) h h'
  | @trans l₁ l₂ l₃ h₁₂ _ ih₁ ih₂ =>
    have hnd₂ := nodup_map_of_perm h₁₂ hnd
    -- the middle order succeeds too, since its machines agree with the first
    have hm := phase2_perm_from (c := c) (e := e) h₁₂ hnd ms
    have hs : (machinesAfter (phase2 sys c e l₂ ms)).isSome := by
      rw [← hm]; simp [machinesAfter, h, Except.toOption]
    obtain ⟨r₂, h₂⟩ := phase2_ok_iff.mpr hs
    exact (ih₁ hnd ms h h₂).trans (ih₂ hnd₂ ms h₂ h')

/-- **The emitted blocks do not depend on the order of the winners** beyond a permutation, when
phase 2 succeeds in both orders. -/
theorem phase2_perm_emitted {sys : Sys} {c : Cfg} {e : Entry}
    {ws ws' : List (Winner sys)} (hp : ws.Perm ws') (hnd : (ws.map (·.mach)).Nodup)
    {r r' : List MState × Emitted}
    (h : phase2 sys c e ws c.machines = .ok r) (h' : phase2 sys c e ws' c.machines = .ok r') :
    r.2.Perm r'.2 :=
  phase2_perm_emitted_from hp hnd c.machines h h'

/-! ### The winners of a step are on distinct machines -/

theorem finList_nodup : (n : Nat) → (finList n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
    simp only [finList]
    refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · simp only [List.mem_map, not_exists, not_and]
      intro x _ h; exact absurd h (Fin.succ_ne_zero x)
    · exact List.pairwise_map.mpr ((finList_nodup n).imp fun h e => h (Fin.succ_inj.mp e))

theorem choose_mach {sys : Sys} {c : Cfg} {e : Entry} {m : Fin sys.sig.machines} {w : Winner sys}
    (h : choose sys c e m = .ok (some w)) : w.mach = m := by
  unfold choose at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
    · cases h; rfl

theorem winnersOf_sublist {sys : Sys} {c : Cfg} {e : Entry} :
    (ms : List (Fin sys.sig.machines)) → (ws : List (Winner sys)) →
    winnersOf sys c e ms = .ok ws → (ws.map (·.mach)).Sublist ms
  | [], ws, h => by simp [winnersOf] at h; subst h; simp
  | m :: ms, ws, h => by
    simp only [winnersOf] at h
    split at h
    · cases h
    · rename_i w hw
      split at h
      · cases h
      · rename_i ws' hws
        have ih := winnersOf_sublist ms ws' hws
        cases h
        cases w with
        | none => exact ih.cons m
        | some w =>
          simp only [List.map_cons, choose_mach hw]
          exact ih.cons_cons m

/-- **The winners of a step are on distinct machines**, so `phase2_perm` and `phase2_perm_emitted`
apply to the winners every step computes. -/
theorem winners_nodup {sys : Sys} {c : Cfg} {e : Entry} {ws : List (Winner sys)}
    (h : winners sys c e = .ok ws) : (ws.map (·.mach)).Nodup :=
  (winnersOf_sublist _ ws h).nodup (finList_nodup _)

/-! ### The whole delivery does not depend on the order of the winners -/

/-- The blocks phase 2 returns are tagged with the winners' machines, in firing order. -/
theorem phase2_keys {sys : Sys} {c : Cfg} {e : Entry} :
    (ws : List (Winner sys)) → (ms : List MState) → (r : List MState × Emitted) →
    phase2 sys c e ws ms = .ok r → r.2.map (·.1) = ws.map (·.mach.val)
  | [], ms, r, h => by
    simp only [phase2] at h; cases h; rfl
  | w :: ws, ms, r, h => by
    simp only [phase2] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i hr
          cases h
          simp only [List.map_cons]
          rw [phase2_keys ws _ _ hr]

/-- With distinct tags, the block of each machine does not depend on the order of the blocks. -/
theorem blockOf_perm {bs bs' : Emitted} (hp : bs.Perm bs') (hnd : (bs.map (·.1)).Nodup)
    (m : Nat) : blockOf m bs = blockOf m bs' := by
  induction hp with
  | nil => rfl
  | cons x _ ih =>
    obtain ⟨i, out⟩ := x
    simp only [blockOf]
    rw [ih (List.nodup_cons.mp hnd).2]
  | swap x y l =>
    obtain ⟨i, out⟩ := x
    obtain ⟨j, out'⟩ := y
    have hne : j ≠ i := by
      have := (List.nodup_cons.mp hnd).1
      intro heq; apply this; simp [heq]
    simp only [blockOf]
    by_cases hj : j = m
    · by_cases hi : i = m
      · exact absurd (hj.trans hi.symm) hne
      · simp [hj, hi]
    · simp [hj]
  | trans h₁₂ _ ih₁ ih₂ =>
    exact (ih₁ hnd).trans (ih₂ ((h₁₂.map (·.1)).nodup hnd))

/-- The state a step leads to does not depend on the order of the winners phase 2 fires. -/
theorem afterPhase2_perm {sys : Sys} {c0 : Cfg} {e : Entry} {ws ws' : List (Winner sys)}
    (hp : ws.Perm ws') (hnd : (ws.map (·.mach)).Nodup) (d : Cfg) :
    outcome d (afterPhase2 sys c0 (phase2 sys c0 e ws' c0.machines)) =
      outcome d (afterPhase2 sys c0 (phase2 sys c0 e ws c0.machines)) := by
  have hm := phase2_perm (c := c0) (e := e) hp hnd
  cases h : phase2 sys c0 e ws c0.machines with
  | error err =>
    cases h' : phase2 sys c0 e ws' c0.machines with
    | error err' => rfl
    | ok r' => rw [h, h'] at hm; simp [Except.toOption] at hm
  | ok r =>
    cases h' : phase2 sys c0 e ws' c0.machines with
    | error err' => rw [h, h'] at hm; simp [Except.toOption] at hm
    | ok r' =>
      obtain ⟨ms, bs⟩ := r
      obtain ⟨ms', bs'⟩ := r'
      rw [h, h'] at hm
      simp only [Except.toOption, Option.map_some, Option.some.injEq] at hm
      have hb : bs.Perm bs' := phase2_perm_emitted hp hnd h h'
      have hk : (bs.map (·.1)).Nodup := by
        rw [phase2_keys ws _ _ h]
        exact List.pairwise_map.mpr
          ((List.pairwise_map.mp hnd).imp fun hne heq => hne (Fin.ext heq))
      have hio : inMachineOrder sys.sig.machines bs' = inMachineOrder sys.sig.machines bs := by
        simp only [inMachineOrder]
        congr 1
        funext m
        exact (blockOf_perm hb hk m).symm
      simp only [afterPhase2, outcome, hm, hio]

/-- **The delivery does not depend on the order of the winners.** Firing the winners a step
computes in any order `σ` chooses (any permutation, per configuration and entry) leads to the same
state as `deliver`: the same configuration (time, machines and pending list all equal), or the
error state in both. Which error is reported may depend on the order. -/
theorem deliver_perm (sys : Sys) (σ : Cfg → Entry → List (Winner sys) → List (Winner sys))
    (hσ : ∀ c e ws, (σ c e ws).Perm ws) (c : Cfg) (k : Nat) :
    (deliverWith sys (fun c e ws ms => phase2 sys c e (σ c e ws) ms) c k).map (outcome c) =
      (deliver sys c k).map (outcome c) := by
  unfold deliver deliverWith
  cases c.pending[k]? with
  | none => rfl
  | some e =>
    simp only []
    split
    · simp only [Option.map_some]
      cases hw : winners sys { c with time := e.time, pending := c.pending.eraseIdx k } e with
      | error err => rfl
      | ok ws =>
        simp only [Option.some.injEq]
        exact afterPhase2_perm (hσ _ _ ws).symm (winners_nodup hw) c
    · rfl

/-! ### Shape: every reachable configuration has the shape of the signature -/

/-- `vs` holds one value of each sort of `tys`, in order. -/
def VarsFit (tys : List Ty) (vs : List Val) : Prop :=
  vs.length = tys.length ∧
    ∀ (i : Nat) (h : i < vs.length) (h' : i < tys.length), vs[i].fits tys[i] = true

/-- Machine state `x` has the shape of machine `m`: a control state of `m`, and one value of the
declared sort per variable. -/
def Sig.MShaped (S : Sig) (m : Fin S.machines) (x : MState) : Prop :=
  x.ctrl < (S.states m).length ∧ VarsFit (S.vars m) x.vars

/-- A list of machine states has the shape of the signature: one per machine, each shaped. -/
def Sig.Shaped (S : Sig) (ms : List MState) : Prop :=
  ms.length = S.machines ∧ ∀ (m : Fin S.machines) (x : MState), ms[m.val]? = some x → S.MShaped m x

/-- A configuration has the shape of its system's signature. -/
def Cfg.Shaped (sys : Sys) (c : Cfg) : Prop := sys.sig.Shaped c.machines

/-- The configuration of a state (the one before the failing step, for the error state) is
shaped. -/
def State.Shaped (sys : Sys) : State → Prop
  | .run c => c.Shaped sys
  | .err c => c.Shaped sys

theorem at?_of_lt {β : Type} {l : List β} {i : Nat} (h : i < l.length) : at? l i = .ok l[i] := by
  simp [at?, List.getElem?_eq_getElem h]

theorem Sig.Shaped.get {S : Sig} {ms : List MState} (h : S.Shaped ms) (m : Fin S.machines) :
    ∃ x, ms[m.val]? = some x ∧ S.MShaped m x := by
  have hl : m.val < ms.length := by rw [h.1]; exact m.isLt
  exact ⟨ms[m.val], List.getElem?_eq_getElem hl, h.2 m _ (List.getElem?_eq_getElem hl)⟩

theorem Sig.Shaped.set {S : Sig} {ms : List MState} (h : S.Shaped ms) {m : Fin S.machines}
    {x : MState} (hx : S.MShaped m x) : S.Shaped (ms.set m.val x) := by
  refine ⟨by rw [List.length_set]; exact h.1, fun m' y hy => ?_⟩
  by_cases hm : m.val = m'.val
  · have hl : m.val < ms.length := by rw [h.1]; exact m.isLt
    rw [← hm, List.getElem?_set_self hl] at hy
    cases hy
    have : m = m' := Fin.ext hm
    subst this; exact hx
  · rw [List.getElem?_set_ne hm] at hy
    exact h.2 m' y hy

theorem Val.check_fits {τ : Ty} {v x : Val} (h : Val.check τ v = .ok x) : x.fits τ = true := by
  unfold Val.check at h
  split at h
  · cases h; assumption
  · split at h <;> cases h

theorem Val.check_ne_shape (τ : Ty) (v : Val) : Val.check τ v ≠ .error .shape := by
  unfold Val.check
  split
  · intro h; cases h
  · split <;> intro h <;> cases h

theorem VarsFit.set {tys : List Ty} {vs : List Val} (h : VarsFit tys vs) {i : Nat}
    (hi : i < tys.length) {x : Val} (hx : x.fits tys[i] = true) : VarsFit tys (vs.set i x) := by
  refine ⟨by rw [List.length_set]; exact h.1, fun j hj hj' => ?_⟩
  by_cases hij : i = j
  · subst hij; simp [hx]
  · rw [List.getElem_set_ne hij]
    exact h.2 j (by rw [List.length_set] at hj; exact hj) hj'

/-- Effects keep the machine's variables of their declared sorts. -/
theorem runEffects_fit {S : Sig} {me : Fin S.machines} {c : Cfg} {e : Entry} :
    (effs : List (Effect S me)) → (own : MState) → (r : MState × List Entry) →
    VarsFit (S.vars me) own.vars → runEffects c e effs own = .ok r → VarsFit (S.vars me) r.1.vars
  | [], own, r, hf, h => by simp only [runEffects] at h; cases h; exact hf
  | .set v rhs :: rest, own, r, hf, h => by
    simp only [runEffects] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i x hx
        split at h
        · refine runEffects_fit rest _ r ?_ h
          have hfx := Val.check_fits hx
          rw [List.get_eq_getElem] at hfx
          exact hf.set v.isLt hfx
        · cases h
  | .emit ev after pl :: rest, own, r, hf, h => by
    simp only [runEffects] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i st outs hr
        cases h
        exact runEffects_fit rest own (st, outs) hf hr

/-- Firing a winner keeps its machine shaped. -/
theorem fireOne_shaped {sys : Sys} {c : Cfg} {e : Entry} {w : Winner sys} {own : MState}
    {r : MState × List Entry} (hs : sys.sig.MShaped w.mach own) (h : fireOne sys c e w own = .ok r) :
    sys.sig.MShaped w.mach r.1 := by
  simp only [fireOne] at h
  split at h
  · cases h
  · rename_i st outs hr
    cases h
    exact ⟨((sys.trans w.mach).get w.idx).dst.isLt, runEffects_fit _ own (st, outs) hs.2 hr⟩

/-- Phase 2 keeps the machines shaped. -/
theorem phase2_shaped {sys : Sys} {c : Cfg} {e : Entry} :
    (ws : List (Winner sys)) → (ms : List MState) → (r : List MState × Emitted) →
    sys.sig.Shaped ms → phase2 sys c e ws ms = .ok r → sys.sig.Shaped r.1
  | [], ms, r, hs, h => by simp only [phase2] at h; cases h; exact hs
  | w :: ws, ms, r, hs, h => by
    simp only [phase2] at h
    split at h
    · cases h
    · rename_i own ho
      split at h
      · cases h
      · rename_i st out hf
        split at h
        · cases h
        · rename_i ms' outs hr
          cases h
          have hown := hs.2 w.mach own ho
          exact phase2_shaped ws _ (ms', outs) (hs.set (fireOne_shaped hown hf)) hr

/-- A successful delivery keeps the configuration shaped. -/
theorem deliver_shaped {sys : Sys} {c c' : Cfg} {k : Nat} (hs : c.Shaped sys)
    (h : deliver sys c k = some (.ok c')) : c'.Shaped sys := by
  unfold deliver deliverWith at h
  split at h
  · cases h
  · split at h
    · simp only [Option.some.injEq] at h
      split at h
      · cases h
      · unfold afterPhase2 at h
        split at h
        · cases h
        · rename_i ms bs hr
          cases h
          exact phase2_shaped _ _ _ hs hr
    · cases h

/-- **Shape is invariant.** From a shaped initial configuration, every reachable state is shaped:
each machine has a control state of its own and one value of the declared sort per variable. -/
theorem shaped_invariant (sys : Sys) (h : sys.init.Shaped sys) :
    (Sys.lts sys).Invariant (fun s => s.Shaped sys) := by
  refine LTS.safe_of_inductive (I := fun s => s.Shaped sys) ⟨?_, ?_⟩ (fun _ h => h)
  · intro s hs
    subst hs; exact h
  · intro s k t hs hst
    cases s with
    | err c => exact absurd hst id
    | run c =>
      have hst' : (deliver sys c k).map (outcome c) = some t := hst
      cases hd : deliver sys c k with
      | none => rw [hd] at hst'; cases hst'
      | some r =>
        rw [hd] at hst'
        cases r with
        | error err => cases hst'; exact hs
        | ok c' => cases hst'; exact deliver_shaped hs hd

/-! ### From a shaped configuration no step fails with `shape` -/

theorem checked_ne_shape (τ : ATy) (a b r : Int) : checked τ a b r ≠ .error .shape := by
  unfold checked
  split
  · intro h; cases h
  · split
    · intro h; cases h
    · split <;> intro h <;> cases h

theorem AOp.apply_ne_shape (op : AOp) (τ : ATy) (a b : Int) : op.apply τ a b ≠ .error .shape := by
  cases op <;> simp only [AOp.apply]
  · exact checked_ne_shape _ _ _ _
  · exact checked_ne_shape _ _ _ _
  · exact checked_ne_shape _ _ _ _
  · split
    · intro h; cases h
    · split
      · split
        · exact checked_ne_shape _ _ _ _
        · intro h; cases h
      · exact checked_ne_shape _ _ _ _
  · split
    · intro h; cases h
    · exact checked_ne_shape _ _ _ _

theorem UOp.apply_ne_shape (op : UOp) (v : Val) : op.apply v ≠ .error .shape := by
  unfold UOp.apply
  split
  · exact checked_ne_shape _ _ _ _
  · intro h; cases h
  · intro h; cases h

theorem BOp.apply_ne_shape (op : BOp) (v w : Val) : op.apply v w ≠ .error .shape := by
  unfold BOp.apply
  split
  · exact AOp.apply_ne_shape _ _ _ _
  · intro h; cases h
  · intro h; cases h
  · split <;> intro h <;> cases h
  · split <;> intro h <;> cases h
  · intro h; cases h

theorem ne_shape_of {α β : Type} {x : Except Err α} {err : Err} (hx : x ≠ .error .shape)
    (h : x = .error err) : (Except.error err : Except Err β) ≠ .error .shape := by
  intro h'; injection h' with h'; subst h'; exact hx h

/-- What evaluation needs to read no state past its end: the snapshot is shaped, and the own
machine has one value per declared variable. -/
def Ctx.Shaped (S : Sig) (me : Fin S.machines) (cx : Ctx) : Prop :=
  S.Shaped cx.snap ∧ cx.own.vars.length = (S.vars me).length

theorem Ref.eval_ne_shape {S : Sig} {me : Fin S.machines} {cx : Ctx} (hcx : cx.Shaped S me) :
    (r : Ref S me) → r.eval cx ≠ .error .shape
  | .own v => by
    simp only [Ref.eval]
    rw [at?_of_lt (by rw [hcx.2]; exact v.isLt)]
    intro h; cases h
  | .other m v => by
    obtain ⟨x, hx, hxs⟩ := hcx.1.get m
    have hl : m.val < cx.snap.length := by rw [hcx.1.1]; exact m.isLt
    have hxe : cx.snap[m.val] = x := by
      rw [List.getElem?_eq_getElem hl] at hx; exact Option.some.inj hx
    simp only [Ref.eval, at?_of_lt hl, hxe]
    rw [at?_of_lt (by rw [hxs.2.1]; exact v.isLt)]
    intro h; cases h
  | .state m => by
    obtain ⟨x, hx, hxs⟩ := hcx.1.get m
    have hl : m.val < cx.snap.length := by rw [hcx.1.1]; exact m.isLt
    have hxe : cx.snap[m.val] = x := by
      rw [List.getElem?_eq_getElem hl] at hx; exact Option.some.inj hx
    simp only [Ref.eval, at?_of_lt hl, hxe, at?_of_lt hxs.1]
    intro h; cases h
  | .field f τ => by
    simp only [Ref.eval]
    split
    · intro h; cases h
    · split <;> intro h <;> cases h
  | .time => by simp [Ref.eval]

theorem Expr.eval_ne_shape {S : Sig} {me : Fin S.machines} {cx : Ctx} (hcx : cx.Shaped S me) :
    (x : Expr S me) → x.eval cx ≠ .error .shape
  | .val v => by simp [Expr.eval]
  | .ref r => by simp only [Expr.eval]; exact Ref.eval_ne_shape hcx r
  | .un op a => by
    have iha := Expr.eval_ne_shape hcx a
    simp only [Expr.eval]
    split
    · exact UOp.apply_ne_shape _ _
    · rename_i err hr; exact ne_shape_of (iha) hr
  | .bin op a b => by
    have iha := Expr.eval_ne_shape hcx a
    have ihb := Expr.eval_ne_shape hcx b
    cases op <;> simp only [Expr.eval]
    all_goals
      repeat' split
      all_goals first
        | exact BOp.apply_ne_shape _ _ _
        | (intro h; injection h with h; subst h; first | exact iha ‹_› | exact ihb ‹_›)
        | (intro h; cases h)

theorem evalPayload_ne_shape {S : Sig} {me : Fin S.machines} {cx : Ctx} (hcx : cx.Shaped S me) :
    (pl : List (Nat × Expr S me)) → evalPayload cx pl ≠ .error .shape
  | [] => by simp [evalPayload]
  | (f, x) :: rest => by
    simp only [evalPayload]
    split
    · rename_i err hr; exact ne_shape_of (Expr.eval_ne_shape hcx x) hr
    · split
      · rename_i err hr; exact ne_shape_of (evalPayload_ne_shape hcx rest) hr
      · intro h; cases h

theorem runEffects_ne_shape {S : Sig} {me : Fin S.machines} {c : Cfg} {e : Entry}
    (hsnap : S.Shaped c.machines) :
    (effs : List (Effect S me)) → (own : MState) → own.vars.length = (S.vars me).length →
    runEffects c e effs own ≠ .error .shape
  | [], own, _ => by simp [runEffects]
  | .set v rhs :: rest, own, hl => by
    simp only [runEffects]
    split
    · rename_i err hr; exact ne_shape_of (Expr.eval_ne_shape ⟨hsnap, hl⟩ rhs) hr
    · split
      · rename_i err hr; exact ne_shape_of (Val.check_ne_shape _ _) hr
      · have hv : v.val < own.vars.length := by rw [hl]; exact v.isLt
        simp only [hv, ↓reduceIte]
        exact runEffects_ne_shape hsnap rest _ (by simp only [List.length_set]; exact hl)
  | .emit ev after pl :: rest, own, hl => by
    simp only [runEffects]
    split
    · rename_i err hr; exact ne_shape_of (evalPayload_ne_shape ⟨hsnap, hl⟩ pl) hr
    · split
      · rename_i err hr; exact ne_shape_of (runEffects_ne_shape hsnap rest own hl) hr
      · intro h; cases h

theorem fireOne_ne_shape {sys : Sys} {c : Cfg} {e : Entry} {w : Winner sys} {own : MState}
    (hsnap : sys.sig.Shaped c.machines) (hl : own.vars.length = (sys.sig.vars w.mach).length) :
    fireOne sys c e w own ≠ .error .shape := by
  simp only [fireOne]
  split
  · rename_i err hr; exact ne_shape_of (runEffects_ne_shape hsnap _ own hl) hr
  · intro h; cases h

theorem phase2_ne_shape {sys : Sys} {c : Cfg} {e : Entry} (hsnap : sys.sig.Shaped c.machines) :
    (ws : List (Winner sys)) → (ms : List MState) → sys.sig.Shaped ms →
    phase2 sys c e ws ms ≠ .error .shape
  | [], ms, _ => by simp [phase2]
  | w :: ws, ms, hs => by
    obtain ⟨own, ho, hown⟩ := hs.get w.mach
    simp only [phase2, ho]
    split
    · rename_i err hr; exact ne_shape_of (fireOne_ne_shape hsnap hown.2.1) hr
    · rename_i st out hf
      split
      · rename_i err hr
        exact ne_shape_of (phase2_ne_shape hsnap ws _ (hs.set (fireOne_shaped hown hf))) hr
      · intro h; cases h

theorem scan_ne_shape {sys : Sys} {c : Cfg} {e : Entry} {m : Fin sys.sig.machines} {own : MState}
    (hsnap : sys.sig.Shaped c.machines) (hl : own.vars.length = (sys.sig.vars m).length) :
    (is : List (Fin (sys.trans m).length)) → scan sys c e m own is ≠ .error .shape
  | [] => by simp [scan]
  | i :: is => by
    simp only [scan]
    split
    · split
      · intro h; cases h
      · exact scan_ne_shape hsnap hl is
      · intro h; cases h
      · rename_i err hr; exact ne_shape_of (Expr.eval_ne_shape ⟨hsnap, hl⟩ _) hr
    · exact scan_ne_shape hsnap hl is

theorem winnersOf_ne_shape {sys : Sys} {c : Cfg} {e : Entry} (hsnap : sys.sig.Shaped c.machines) :
    (ms : List (Fin sys.sig.machines)) → winnersOf sys c e ms ≠ .error .shape
  | [] => by simp [winnersOf]
  | m :: ms => by
    obtain ⟨own, ho, hown⟩ := hsnap.get m
    have hl : m.val < c.machines.length := by rw [hsnap.1]; exact m.isLt
    have hoe : c.machines[m.val] = own := by
      rw [List.getElem?_eq_getElem hl] at ho; exact Option.some.inj ho
    simp only [winnersOf, choose, at?_of_lt hl, hoe]
    split
    · rename_i err hr
      split at hr
      · rename_i err' hr'; cases hr; exact ne_shape_of (scan_ne_shape hsnap hown.2.1 _) hr'
      · cases hr
      · cases hr
    · split
      · rename_i err hr; exact ne_shape_of (winnersOf_ne_shape hsnap ms) hr
      · intro h; cases h

theorem winners_ne_shape {sys : Sys} {c : Cfg} {e : Entry} (hsnap : sys.sig.Shaped c.machines) :
    winners sys c e ≠ .error .shape :=
  winnersOf_ne_shape hsnap _

/-- **No step from a shaped configuration fails with `shape`.** -/
theorem deliver_ne_shape {sys : Sys} {c : Cfg} (hs : c.Shaped sys) (k : Nat) :
    deliver sys c k ≠ some (.error .shape) := by
  unfold deliver deliverWith
  split
  · intro h; cases h
  · split
    · simp only [ne_eq, Option.some.injEq]
      split
      · rename_i err hr
        refine ne_shape_of ?_ hr; exact winners_ne_shape hs
      · unfold afterPhase2
        split
        · rename_i err hr
          refine ne_shape_of ?_ hr; apply phase2_ne_shape <;> exact hs
        · intro h; cases h
    · intro h; cases h

/-- **`shape` is unreachable from a shaped initial configuration**: no step from a reachable
configuration fails with `shape`. -/
theorem shape_unreachable (sys : Sys) (h : sys.init.Shaped sys) {c : Cfg}
    (hr : (Sys.lts sys).Reach (.run c)) (k : Nat) : deliver sys c k ≠ some (.error .shape) :=
  deliver_ne_shape (shaped_invariant sys h _ hr) k

/-! ### The static sort of an expression is sound for evaluation -/

/-- What evaluation needs for values to fit their static sorts: the snapshot is shaped, the own
variables hold values of their declared sorts, and the time is within `maxSafe` (the sort of
`.time`; the bound on time is M2.2's). -/
def Ctx.Typed (S : Sig) (me : Fin S.machines) (cx : Ctx) : Prop :=
  S.Shaped cx.snap ∧ VarsFit (S.vars me) cx.own.vars ∧ (cx.time : Int) ≤ maxSafe

theorem checked_fits {τ : ATy} {a b r : Int} {v : Val} (h : checked τ a b r = .ok v) :
    v.fits τ.ty = true := by
  unfold checked at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · rename_i hr
        cases h
        cases τ <;> exact hr
      · cases h

theorem AOp.apply_fits {op : AOp} {τ : ATy} {a b : Int} {v : Val} (h : op.apply τ a b = .ok v) :
    v.fits τ.ty = true := by
  cases op <;> simp only [AOp.apply] at h
  all_goals
    repeat' split at h
    all_goals first
      | exact checked_fits h
      | cases h

theorem UOp.apply_neg_fits {σ : ATy} {w v : Val} (h : UOp.apply (.neg σ) w = .ok v) :
    v.fits σ.ty = true := by
  cases w <;> simp only [UOp.apply] at h
  · exact checked_fits h
  all_goals cases h

theorem UOp.apply_not_fits {w v : Val} (h : UOp.apply .not w = .ok v) : v.fits .bool = true := by
  cases w <;> simp only [UOp.apply] at h
  all_goals first
    | (cases h; rfl)
    | cases h

theorem BOp.apply_arith_fits {op : AOp} {σ : ATy} {x y v : Val}
    (h : BOp.apply (.arith op σ) x y = .ok v) : v.fits σ.ty = true := by
  cases x <;> cases y <;> simp only [BOp.apply] at h
  all_goals first
    | exact AOp.apply_fits h
    | cases h

theorem BOp.apply_bool_fits {op : BOp} (hop : ∀ o σ, op ≠ .arith o σ) {x y v : Val}
    (h : BOp.apply op x y = .ok v) : v.fits .bool = true := by
  cases op
  · exact absurd rfl (hop _ _)
  all_goals
    cases x <;> cases y <;> simp only [BOp.apply] at h
    all_goals
      (try split at h)
      all_goals first
        | (cases h; rfl)
        | cases h

theorem at?_eq_ok {β : Type} {l : List β} {i : Nat} {x : β} (h : at? l i = .ok x) :
    ∃ hi : i < l.length, l[i] = x := by
  unfold at? at h
  split at h
  · rename_i y hy
    cases h
    obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.mp hy
    exact ⟨hi, hx⟩
  · cases h

theorem Ref.eval_fits {S : Sig} {me : Fin S.machines} {cx : Ctx} (hcx : cx.Typed S me)
    {τ : Ty} {v : Val} : (r : Ref S me) → r.ty? = some τ → r.eval cx = .ok v → v.fits τ = true
  | .own i, hty, h => by
    simp only [Ref.ty?, Option.some.injEq] at hty
    subst hty
    simp only [Ref.eval] at h
    obtain ⟨hi, hx⟩ := at?_eq_ok h
    subst hx
    rw [List.get_eq_getElem]
    exact hcx.2.1.2 i.val hi i.isLt
  | .other m i, hty, h => by
    simp only [Ref.ty?, Option.some.injEq] at hty
    subst hty
    simp only [Ref.eval] at h
    split at h
    · rename_i x hx
      obtain ⟨hm, hxe⟩ := at?_eq_ok hx
      have hxs := hcx.1.2 m x (by rw [List.getElem?_eq_getElem hm, hxe])
      obtain ⟨hi, hv⟩ := at?_eq_ok h
      subst hv
      rw [List.get_eq_getElem]
      exact hxs.2.2 i.val hi i.isLt
    · cases h
  | .state m, hty, h => by
    simp only [Ref.ty?, Option.some.injEq] at hty
    subst hty
    simp only [Ref.eval] at h
    repeat' split at h
    all_goals first
      | (cases h; rfl)
      | cases h
  | .field f σ, hty, h => by
    simp only [Ref.ty?, Option.some.injEq] at hty
    subst hty
    simp only [Ref.eval] at h
    split at h
    · cases h
    · split at h
      · cases h; assumption
      · cases h
  | .time, hty, h => by
    simp only [Ref.ty?, Option.some.injEq] at hty
    subst hty
    simp only [Ref.eval, Except.ok.injEq] at h
    subst h
    simp only [Val.fits, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨Int.natCast_nonneg _, hcx.2.2⟩

/-- **The static sort of an expression is sound for evaluation.** In a typed context, when
`Expr.ty?` gives an expression a sort, every value it evaluates to fits that sort: it is of that
sort, and an integer lies within the sort's range (an integer literal has the one-point range of its
value; an arithmetic node, the range of its arithmetic sort). -/
theorem Expr.eval_fits {S : Sig} {me : Fin S.machines} {cx : Ctx} (hcx : cx.Typed S me) :
    (x : Expr S me) → {τ : Ty} → {v : Val} → x.ty? = some τ → x.eval cx = .ok v → v.fits τ = true
  | .val w, τ, v, hty, h => by
    simp only [Expr.ty?, Option.some.injEq] at hty
    simp only [Expr.eval, Except.ok.injEq] at h
    subst hty; subst h
    cases w <;> simp [Val.ty, Val.fits]
  | .ref r, τ, v, hty, h => Ref.eval_fits hcx r hty h
  | .un (.neg σ) a, τ, v, hty, h => by
    simp only [Expr.ty?] at hty
    split at hty
    · split at hty
      · cases hty
        simp only [Expr.eval] at h
        split at h
        · exact UOp.apply_neg_fits h
        · cases h
      · cases hty
    · cases hty
  | .un .not a, τ, v, hty, h => by
    simp only [Expr.ty?] at hty
    split at hty
    · cases hty
      simp only [Expr.eval] at h
      split at h
      · exact UOp.apply_not_fits h
      · cases h
    · cases hty
  | .bin op a b, τ, v, hty, h => by
    simp only [Expr.ty?] at hty
    split at hty
    · cases op <;> simp only [BOp.ty?] at hty <;> simp only [Expr.eval] at h
      · split at hty
        · cases hty
          split at h
          · exact BOp.apply_arith_fits h
          all_goals cases h
        · cases hty
      iterate 4
        (split at hty
         · cases hty
           split at h
           · exact BOp.apply_bool_fits (by intro o σ hc; cases hc) h
           all_goals cases h
         · cases hty)
      all_goals
        split at hty
        · cases hty
          repeat' split at h
          all_goals first
            | (cases h; rfl)
            | cases h
        · cases hty
    · cases hty

end Exegra.Core.Behav
