import Exegra.Core.LTS

/-
The instantaneous behaviour calculus (docs/foundations.md, M2; docs/assessment/2026-11-26/plan-M2.md,
increment M2.1).

Exegra's behaviours (machines with control states and typed variables, reacting to events by
guarded transitions whose effects set the machine's own variables and emit events) as a typed
calculus whose semantics is an `LTS` of `Exegra.Core.LTS`. It keeps the choices of
`Exegra.Core.Calculus` and adds sorts, events, payloads and errors:

* **Values** are `Int`, `Bool` or `String`; integer arithmetic is exact. A division with a remainder
  is the error `inexact`, a division by zero `divZero`, an integer outside the range of its sort
  `overflow`. No error is turned into a default value.
* **Scoped references.** A machine's expressions are `Expr S me`: its own variables are
  `Fin (S.vars me).length`, other machines `Fin S.machines`, so a reference to a variable or machine
  that does not exist cannot be written. A state of the wrong shape (a variable list shorter than
  the signature says) is not excluded by typing; reading or writing past its end is the error
  `shape`, never `0` and never a no-op.
* **Snapshot reads.** During the step that delivers an entry, every guard reads the configuration
  at the start of the step, and every effect reads other machines, their control states and the
  time from that snapshot; only the machine's own variables are read as its earlier effects in the
  same transition left them. Writes are confined to the winner's own machine.
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
  orders succeed the emitted entries are permutations of each other. It holds for every starting
  list of machines, not only the snapshot. This is what lets the relation fire winners in machine
  order without quantifying over orders.

What is not here (later increments of the plan): timers, faults, the bound on time, `stopAt` and
draws (M2.2, M2.8); payload literals beyond integers, Booleans and strings (`Lit`, M2.2); a static
well-formedness predicate `Sys.WF` with theorems that use it (M2.2: `Expr.ty?` is defined here but no
theorem rests on it); the executable scheduler and `step_sound`, `successors_complete` (M2.3); the
elaboration of format-2 input (M2.4). No theorem here is about the format-2 interpreter
(`Exegra.V2`), which still computes with `Float`.
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
  | overflow
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
  | neg
  | not
  deriving DecidableEq, Repr

inductive BOp where
  | add | sub | mul | div | mod
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

/-! ### Static typing (defined; no theorem rests on it in M2.1) -/

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

def Val.ty : Val → Ty
  | .int _ => .num
  | .bool _ => .bool
  | .str _ => .str

def BOp.ty? (op : BOp) (a b : Ty) : Option Ty :=
  match op with
  | .add | .sub | .mul | .div | .mod => if a.isInt && b.isInt then some .num else none
  | .lt | .le => if a.isInt && b.isInt then some .bool else none
  | .eq | .ne => if a.comparable b then some .bool else none
  | .and | .or | .imp => if a == .bool && b == .bool then some .bool else none

def Expr.ty? {S : Sig} {me : Fin S.machines} : Expr S me → Option Ty
  | .val v => some v.ty
  | .ref r => r.ty?
  | .un .neg a => match a.ty? with
    | some τ => if τ.isInt then some .num else none
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
    | some v => if v.sameSort τ then .ok v else .error (.fieldSort f)
  | .time => .ok (.int cx.time)

/-- An integer result: within `±maxSafe`, or `overflow`. -/
def intRes (v : Int) : Except Err Val :=
  if decide (-maxSafe ≤ v) && decide (v ≤ maxSafe) then .ok (.int v) else .error .overflow

def UOp.apply : UOp → Val → Except Err Val
  | .neg, .int v => intRes (-v)
  | .not, .bool b => .ok (.bool (!b))
  | _, _ => .error .sort

/-- A strict binary operator on two values (every operator except `and`, `or`, `imp`). -/
def BOp.apply : BOp → Val → Val → Except Err Val
  | .add, .int a, .int b => intRes (a + b)
  | .sub, .int a, .int b => intRes (a - b)
  | .mul, .int a, .int b => intRes (a * b)
  | .div, .int a, .int b =>
    if b = 0 then .error .divZero
    else if a % b = 0 then intRes (a / b) else .error .inexact
  | .mod, .int a, .int b => if b = 0 then .error .divZero else intRes (a % b)
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
each writes its result back into `ms`. Other machines are read from the snapshot `c` only. -/
def phase2 (sys : Sys) (c : Cfg) (e : Entry) :
    List (Winner sys) → List MState → Except Err (List MState × List Entry)
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
        | .ok (ms', outs) => .ok (ms', out ++ outs)

/-- For contrast, today's rule (format 1 and format 2): each winner reads other machines from the
configuration being written, `ms`, as earlier winners left it. -/
def phase2Next (sys : Sys) (c : Cfg) (e : Entry) :
    List (Winner sys) → List MState → Except Err (List MState × List Entry)
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
        | .ok (ms', outs) => .ok (ms', out ++ outs)

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

/-- The delivery of the pending entry at index `k`, with phase 2 given by `p2`. -/
def deliverWith (sys : Sys)
    (p2 : Cfg → Entry → List (Winner sys) → List MState → Except Err (List MState × List Entry))
    (c : Cfg) (k : Nat) : Option (Except Err Cfg) :=
  match c.pending[k]? with
  | none => none
  | some e =>
    if c.pending.all (fun x => decide (e.time ≤ x.time)) then
      let c0 : Cfg := { c with time := e.time, pending := c.pending.eraseIdx k }
      some (match winners sys c0 e with
        | .error err => .error err
        | .ok ws => match p2 c0 e ws c0.machines with
          | .error err => .error err
          | .ok (ms, out) => .ok { c0 with machines := ms, pending := c0.pending ++ out })
    else none

/-- Delivers the pending entry at index `k`. `none`: `k` is not the index of an entry of minimal
time, so no step has this label. `some (.error _)`: the step fails. Guards read the configuration
at the start of the step, with the time advanced to the entry's; the winners fire in machine order
under snapshot reads (`phase2`); emitted entries are appended to the queue in that order. -/
def deliver (sys : Sys) (c : Cfg) (k : Nat) : Option (Except Err Cfg) :=
  deliverWith sys (phase2 sys) c k

/-- For contrast, the same delivery under today's next-configuration reads (`phase2Next`). -/
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

/-! ### Phase 2 does not depend on the order of the winners -/

/-- The machines after phase 2, if it succeeds. -/
def machinesAfter (r : Except Err (List MState × List Entry)) : Option (List MState) :=
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
in both orders; which error is reported may depend on the order). -/
theorem phase2_perm {sys : Sys} {c : Cfg} {e : Entry}
    {ws ws' : List (Winner sys)} (hp : ws.Perm ws') (hnd : (ws.map (·.mach)).Nodup) :
    (phase2 sys c e ws c.machines).toOption.map Prod.fst =
      (phase2 sys c e ws' c.machines).toOption.map Prod.fst :=
  phase2_perm_from hp hnd c.machines

/-! ### The emitted entries are permutations -/

/-- `phase2` succeeds exactly when `machinesAfter` is defined. -/
theorem phase2_ok_iff {sys : Sys} {c : Cfg} {e : Entry} {ws : List (Winner sys)}
    {ms : List MState} : (∃ r, phase2 sys c e ws ms = .ok r) ↔ (machinesAfter (phase2 sys c e ws ms)).isSome := by
  cases phase2 sys c e ws ms with
  | error err => simp [machinesAfter, Except.toOption]
  | ok r => simp [machinesAfter, Except.toOption]

theorem phase2_swap_emitted {sys : Sys} {c : Cfg} {e : Entry} (w₁ w₂ : Winner sys)
    (ws : List (Winner sys)) (ms : List MState) (hne : w₁.mach.val ≠ w₂.mach.val)
    {r r' : List MState × List Entry}
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
    show (out₁ ++ (out₂ ++ outs)).Perm (out₂ ++ (out₁ ++ outs))
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_append_comm.append_right outs

/-- The emitted entries in two orders are permutations, when both succeed. -/
theorem phase2_perm_emitted_from {sys : Sys} {c : Cfg} {e : Entry} {ws ws' : List (Winner sys)}
    (hp : ws.Perm ws') (hnd : (ws.map (·.mach)).Nodup) (ms : List MState)
    {r r' : List MState × List Entry}
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
            exact (ih hnd' _ hr hr').append_left out
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

/-- **The emitted entries do not depend on the order of the winners** beyond a permutation, when
phase 2 succeeds in both orders. -/
theorem phase2_perm_emitted {sys : Sys} {c : Cfg} {e : Entry}
    {ws ws' : List (Winner sys)} (hp : ws.Perm ws') (hnd : (ws.map (·.mach)).Nodup)
    {r r' : List MState × List Entry}
    (h : phase2 sys c e ws c.machines = .ok r) (h' : phase2 sys c e ws' c.machines = .ok r') :
    r.2.Perm r'.2 :=
  phase2_perm_emitted_from hp hnd c.machines h h'

end Exegra.Core.Behav
