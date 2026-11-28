import Exegra.Core.LTS

/-
The instantaneous behaviour calculus (docs/foundations.md, M2; docs/assessment/2026-11-26/plan-M2.md,
increments M2.1 and M2.2).

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
  at the start of the step, and every effect reads other machines, their control states, the
  aggregates over instances and the time from that snapshot; only the machine's own variables are
  read as its earlier effects in the same transition left them. Writes are confined to the winner's
  own machine.
* **Counted instances, targets and replies** (M2.7). A machine is one instance: the instances of a
  counted behaviour are distinct machines with the same transitions, which `Exegra.Elab` lays out.
  `Ref.count g s` is the number of machines of `g` in the control state named `s`, `Ref.agg op g`
  the `sum`, `min` or `max` of one integer variable over `g`, both read from the snapshot; a sum,
  minimum or maximum outside `±(2^53 - 1)` is `overflow`, and the minimum or maximum of no instance
  is not typed (format 2 gives `null`). An entry a transition emits carries its sender; a `reply`
  effect addresses the sender of the delivered entry, and replying to an entry without a sender is
  the error `noRequester` (Format2.lean:1444-1448). A targeted entry is delivered only to its
  target (`target_only`).
* **The queue.** Phase 2 returns, per winner, the entries it emitted and the timers it set or
  cancelled, as one block tagged with its machine. The step removes the pending entries of those
  timers and puts the emitted entries into the pending list in machine-index order (whatever the
  order the winners fired in), each inserted before the first entry of a later time: on a sorted
  queue the position format 2's `insertE` gives (Format2.lean:1022-1025). Format 2 fires winners in
  listing order, which is machine-index order here.
* **Timers** (M2.2). `timer n after event` drops the machine's pending entry of timer `n`, if any,
  and queues `event` addressed to the machine; `cancel n` drops it (Format2.lean:1527-1547). Entries
  carry an optional target machine, and only the target takes part in the step that delivers them.
* **Faults** (M2.2), all-or-nothing per fault as in format 2: a fault mask is chosen in the initial
  state and kept (`mask_const`); format 2's run is the all-true mask over the scenario's faults.
  `drop`/`lose` drop the attempt of the event they act on; `delay`/`retry` re-queue it `by` later,
  once per fault and entry; `duplicate` queues a copy after a committed delivery, once per fault and
  entry; `enable`/`disable` make a `faultOnly` transition a candidate or skip an enabled one;
  `inject` adds an entry to the initial queue. Occurrences count attempts per event (`Cfg.attempts`);
  windows restrict a fault to entries delivered in them (Format2.lean:2098-2140, 2259-2305,
  1235-1258, 2374-2376).
* **Time.** Scheduling an entry at `2^53` or later is the error `timeBound`, as format 2's "Value time
  exceeds 2^53"; no entry is delivered after `stopAt`.
* **Errors are states.** A delivery that fails leads to the explicit state `.err mask c` (the
  configuration before the step), which has no successor (`err_deadlocked`). A safety property is
  stated so that `.err` violates it, so a failing run is a counterexample, never silently absent
  (review-M1, finding 6).
* **Labels.** A step is labelled by the delivered entry itself (not its position, so a label does
  not change when other entries are inserted or removed) and by its draws, one per sampled delay
  (`Sys.samples`, `Dist`), each in the support of its distribution. Any entry of minimal time not
  after `stopAt` may be delivered. `Step` is the declarative relation; `deliver` is the executable
  delivery of a label and `deliver_iff_step` proves it equal to `Step`; `pending_perm_bisim`: the
  pending list is a multiset.
* **Well-formedness** (`Sys.WF`, decidable: `Sys.wf`): the initial configuration has the shape of the
  signature, starts at time 0 with a sorted queue of entries below `2^53`, injected entries are below
  `2^53`, guards are Boolean and every effect is well-typed.

What is proved here:

* `lts_nonVacuous`, `err_deadlocked`, `mask_const`, `deliver_none_of_length_le`,
  `deadlocked_of_pending_nil`;
* `phase2_perm`, `phase2_perm_emitted`, `winners_nodup`, `deliver_perm`: **the whole delivery does
  not depend on the order of the winners** under every fault mask: firing the winners a step computes
  in any order gives the same successor state (time, machines, pending list and attempts all equal,
  or the error state in both); which error is reported may depend on the order;
* `shaped_invariant`, `deliver_ne_shape`, `shape_unreachable`: from a shaped initial configuration
  every reachable state is shaped, and no step from a reachable configuration fails with `shape`;
* `time_invariant`: times stay in order (no pending entry before the current time) and below `2^53`;
  `sorted_invariant`: the queue stays sorted by time;
* `Expr.eval_fits` (the static sort is sound for evaluation), `Expr.eval_ne_sort`, `deliver_ne_sort`,
  `sort_unreachable`: **no step of a well-formed system fails with `sort`**, from any reachable state;
* the forms of a step, `deliver_ok_form` and `deliver_error_form`, on which the invariants rest.

`Exegra.Core.BehavExec` adds the executable scheduler with `step_sound` and the complete successor
function with `successors_complete` (M2.3).

What is not here: resources, links, workloads, keyed instances and routes (after M2), payload
literals beyond integers, Booleans and strings. No theorem here is about the format-2
interpreter (`Exegra.V2`), which still computes with `Float`; `Exegra.Elab` (M2.4) maps format-2
input into the calculus.
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
  /-- JSON constants without expressions (objects, arrays, `null`): payload and `set` literals. -/
  | lit
  deriving DecidableEq, Repr

/-- The integer sort of untyped numbers. -/
def Ty.num : Ty := .int (-maxSafe) maxSafe

inductive Val where
  | int (v : Int)
  | bool (b : Bool)
  | str (s : String)
  /-- A JSON constant (object, array or `null`): its canonical text (object keys sorted), so that
  structurally equal constants (format 2's `==`) have equal canonical texts, and its text as
  written, which a trace reports. -/
  | lit (canon json : String)
  deriving DecidableEq, Repr, Hashable

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
  /-- A time at or beyond `2^53` (format 2: "Value time exceeds 2^53."). -/
  | timeBound
  /-- A `reply` to an entry that has no sender (format 2: "Effect replies to …, which has no
  requester.", Format2.lean:1444-1448). -/
  | noRequester
  /-- A reference to nothing: a name that is not a variable, a behaviour with several instances read
  as one, an aggregate of a single behaviour (format 2: an unknown or ambiguous reference). -/
  | unknownRef
  deriving DecidableEq, Repr

/-- `v` is a value of sort `τ` (for an integer sort: within its range). -/
def Val.fits : Val → Ty → Bool
  | .int v, .int lo hi => decide (lo ≤ v) && decide (v ≤ hi)
  | .bool _, .bool => true
  | .str _, .str => true
  | .lit _ _, .lit => true
  | _, _ => false

/-- The same sort, ignoring integer ranges. -/
def Val.sameSort : Val → Ty → Bool
  | .int _, .int _ _ => true
  | .bool _, .bool => true
  | .str _, .str => true
  | .lit _ _, .lit => true
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
@[inline] def ATy.holds (τ : ATy) (v : Int) : Bool :=
  match τ with
  | .untyped => (decide (-2147483647 ≤ v) && decide (v ≤ 2147483647)) || (decide (-maxSafe ≤ v) && decide (v ≤ maxSafe))
  | .int lo hi => decide (lo ≤ v) && decide (v ≤ hi)

/-- `ATy.holds` is the range test; its first disjunct, for an untyped node, only avoids comparing a
small integer with the big bounds `±(2^53 - 1)` at run time. -/
theorem ATy.holds_eq (τ : ATy) (v : Int) : τ.holds v = (decide (τ.lo ≤ v) && decide (v ≤ τ.hi)) := by
  cases τ with
  | untyped =>
    simp only [ATy.holds, ATy.lo, ATy.hi, maxSafe]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨h1, h2⟩ | h)
      · exact ⟨decide_eq_true (by omega), decide_eq_true (by omega)⟩
      · exact h
    · exact Or.inr
  | int lo hi => rfl

/-- The sort of the values an arithmetic node of sort `τ` produces. -/
def ATy.ty : ATy → Ty
  | .untyped => .num
  | .int lo hi => .int lo hi

inductive AOp where
  | add | sub | mul | div | mod
  deriving DecidableEq, Repr

/-- The result `r` of an arithmetic operator on `a` and `b` in sort `τ`: format 2's `intResult`
(Expr.lean:289-297), which checks the left operand, then the right one, then the result. -/
@[inline] def checked (τ : ATy) (a b r : Int) : Except Err Val :=
  if !τ.holds a then .error .operand
  else if !τ.holds b then .error .operand
  else if τ.holds r then .ok (.int r) else .error .overflow

/-- An arithmetic operator in sort `τ` (format 2: Expr.lean:359-364). `/` and `%` by zero are
`divZero` before any range check; `%` is truncated (`Int.tmod`, format 2's `Num.fmod`); a typed `/`
truncates (`Int.tdiv`, format 2's `divIn`); an untyped `/` must be exact. -/
@[inline] def AOp.apply (op : AOp) (τ : ATy) (a b : Int) : Except Err Val :=
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

/-- An aggregate over the instances of a counted behaviour (format 2's `b.sum.x`, `b.min.x`,
`b.max.x`, Format2.lean:1182-1196). -/
inductive AggOp where
  | sum | min | max
  deriving DecidableEq, Repr

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
  /-- The number of machines of `group` (the instances of a counted behaviour) whose control state
  is named `name`, in the snapshot (format 2's `b.count.s`). -/
  | count (group : List (Fin S.machines)) (name : String)
  /-- `op` over one integer variable of each machine of `group`, in the snapshot (format 2's
  `b.sum.x`, `b.min.x`, `b.max.x`). -/
  | agg (op : AggOp) (group : List ((m : Fin S.machines) × Fin (S.vars m).length))
  /-- A reference to nothing, read at sort `τ`: evaluating it is the error `unknownRef`
  (`Exegra.Elab` gives it the sort its context needs, so a well-typed system can contain it). -/
  | absent (τ : Ty)

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
  /-- `+` on two strings (format 2's string concatenation, Expr.lean:344-347). -/
  | concat
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
  deriving DecidableEq, Repr, Hashable

/-- A pending delivery: its time, its event and its payload fields; the machine it is addressed
to (`none`: every machine); for a timer entry, the timer's name (the entry is then addressed to the
machine that set it); and the faults that already delayed or duplicated it or the entry it was
copied from (format 2 keeps this in a table keyed by sequence number, `delayedBy`,
Format2.lean:2280, 2293, 2139). -/
structure Entry where
  time : Nat
  event : Nat
  payload : List (Nat × Val)
  target : Option Nat := none
  timer : Option Nat := none
  done : List Nat := []
  /-- The machine whose transition emitted the entry, which a `reply` addresses (format 2's
  `Entry.sender`, Format2.lean:1455). -/
  sender : Option Nat := none
  deriving DecidableEq, Repr, Hashable

/-- A configuration: the time, the machines, the pending entries and, per event, the number of
delivery attempts so far (format 2's `attempts`, Format2.lean:2270-2271). -/
structure Cfg where
  time : Nat
  machines : List MState
  pending : List Entry
  attempts : List Nat := []
  deriving DecidableEq, Repr, Hashable

/-- A state of the transition system: running, or failed with the configuration before the
failing step. Each carries the fault mask, chosen in the initial state and constant. -/
inductive State where
  | run (mask : List Bool) (c : Cfg)
  | err (mask : List Bool) (c : Cfg)
  deriving DecidableEq, Repr, Hashable

def State.ok : State → Bool
  | .run _ _ => true
  | .err _ _ => false

def State.mask : State → List Bool
  | .run m _ => m
  | .err m _ => m

def State.cfg : State → Cfg
  | .run _ c => c
  | .err _ c => c

/-! ### Static typing (sound for evaluation: `Expr.eval_fits`) -/

def Ty.isInt : Ty → Bool
  | .int _ _ => true
  | _ => false

def Ref.ty? {S : Sig} {me : Fin S.machines} : Ref S me → Option Ty
  | .own v => some ((S.vars me).get v)
  | .other m v => some ((S.vars m).get v)
  | .state _ => some .str
  | .field _ τ => some τ
  | .time => some (.int 0 maxSafe)
  | .absent τ => some τ
  | .count g _ => some (.int 0 g.length)
  | .agg op g =>
    if g.all (fun p => ((S.vars p.1).get p.2).isInt) && (op == .sum || !g.isEmpty) then some Ty.num
    else none

/-- Two sorts are comparable: both integers, both Booleans or both strings. -/
def Ty.comparable : Ty → Ty → Bool
  | .int _ _, .int _ _ => true
  | .bool, .bool => true
  | .str, .str => true
  | .lit, .lit => true
  | _, _ => false

/-- The sort of a literal: an integer literal has the one-point range of its value. -/
def Val.ty : Val → Ty
  | .int v => .int v v
  | .bool _ => .bool
  | .str _ => .str
  | .lit _ _ => .lit

def BOp.ty? (op : BOp) (a b : Ty) : Option Ty :=
  match op with
  | .arith _ τ => if a.isInt && b.isInt then some τ.ty else none
  | .lt | .le => if a.isInt && b.isInt then some .bool else none
  | .eq | .ne => if a.comparable b then some .bool else none
  | .and | .or | .imp => if a == .bool && b == .bool then some .bool else none
  | .concat => if a == .str && b == .str then some .str else none

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
@[inline] def at? {β : Type} (l : List β) (i : Nat) : Except Err β :=
  match l[i]? with
  | some x => .ok x
  | none => .error .shape

/-- The number of machines of `g` whose control state in `snap` is named `name`. -/
def countIn (S : Sig) (snap : List MState) (name : String) : List (Fin S.machines) → Except Err Nat
  | [] => .ok 0
  | m :: g => match at? snap m.val with
    | .error e => .error e
    | .ok x => match at? (S.states m) x.ctrl with
      | .error e => .error e
      | .ok nm => match countIn S snap name g with
        | .error e => .error e
        | .ok k => .ok (if nm = name then k + 1 else k)

/-- The integer values of the variables `g` names in `snap`; a value of another sort is `sort`. -/
def intsIn {S : Sig} (snap : List MState) : List ((m : Fin S.machines) × Fin (S.vars m).length) →
    Except Err (List Int)
  | [] => .ok []
  | p :: g => match at? snap p.1.val with
    | .error e => .error e
    | .ok x => match at? x.vars p.2.val with
      | .error e => .error e
      | .ok (.int n) => match intsIn snap g with
        | .error e => .error e
        | .ok ns => .ok (n :: ns)
      | .ok _ => .error .sort

/-- An aggregate of integers, checked in the range of untyped numbers. The minimum or maximum of
no value is `sort` (format 2 gives `null`, which has no integer sort). -/
def AggOp.apply : AggOp → List Int → Except Err Val
  | .sum, ns => Val.check Ty.num (.int (ns.foldl (· + ·) 0))
  | .min, [] => .error .sort
  | .min, n :: ns => Val.check Ty.num (.int (ns.foldl Min.min n))
  | .max, [] => .error .sort
  | .max, n :: ns => Val.check Ty.num (.int (ns.foldl Max.max n))

/-- A payload field is read at its sort: a value that does not fit it (another sort, or an integer
outside its range) is the error `fieldSort`. -/
@[inline] def Ref.eval {S : Sig} {me : Fin S.machines} (cx : Ctx) : Ref S me → Except Err Val
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
  | .count g name => match countIn S cx.snap name g with
    | .ok k => .ok (.int k)
    | .error e => .error e
  | .agg op g => match intsIn cx.snap g with
    | .ok ns => op.apply ns
    | .error e => .error e
  | .absent _ => .error .unknownRef

@[inline] def UOp.apply : UOp → Val → Except Err Val
  | .neg τ, .int v => checked τ v 0 (-v)
  | .not, .bool b => .ok (.bool (!b))
  | _, _ => .error .sort

/-- Equality of values (format 2's `==`): JSON constants by their canonical texts, other values
by value. -/
def Val.equiv : Val → Val → Bool
  | .lit a _, .lit b _ => a == b
  | a, b => a == b

/-- A strict binary operator on two values (every operator except `and`, `or`, `imp`). -/
@[inline] def BOp.apply : BOp → Val → Val → Except Err Val
  | .arith op τ, .int a, .int b => op.apply τ a b
  | .lt, .int a, .int b => .ok (.bool (decide (a < b)))
  | .le, .int a, .int b => .ok (.bool (decide (a ≤ b)))
  | .eq, a, b => if Val.sameSort a b.ty then .ok (.bool (a.equiv b)) else .error .sort
  | .ne, a, b => if Val.sameSort a b.ty then .ok (.bool (!a.equiv b)) else .error .sort
  | .concat, .str x, .str y => .ok (.str (x ++ y))
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

/-! ### Effects, transitions, faults, systems -/

/-- The bound on times: format 2 fails a step that schedules an entry at `2^53` or later
(Format2.lean:1320, 1449, 1532, 2131, 2283). -/
def timeLimit : Nat := 9007199254740992

inductive Effect (S : Sig) (me : Fin S.machines) where
  /-- Set one of the machine's own variables. -/
  | set (v : Fin (S.vars me).length) (rhs : Expr S me)
  /-- Emit `event`, `after` time units from now, with the given payload fields. -/
  | emit (event : Nat) (after : Nat) (payload : List (Nat × Expr S me))
  /-- (Re)set the machine's timer `name`: drop its pending entry, if any, and queue `event`
  `after` time units from now, addressed to this machine (format 2's `timer` effect,
  Format2.lean:1527-1543). -/
  | timer (name : Nat) (after : Nat) (event : Nat) (payload : List (Nat × Expr S me))
  /-- Cancel the machine's timer `name` (Format2.lean:1544-1547). -/
  | cancel (name : Nat)
  /-- Emit `event` to the sender of the delivered entry (format 2's `emit` with `"target":
  "reply"`, Format2.lean:1444-1448). -/
  | reply (event : Nat) (after : Nat) (payload : List (Nat × Expr S me))

/-- A transition of machine `me`: from control state `src`, on `event`, when `guard` holds, run
`effects` in order and move to `dst`. A `faultOnly` transition is a candidate only while an active
`enable` fault targets it (Format2.lean:1242-1244). -/
structure Trans (S : Sig) (me : Fin S.machines) where
  src : Fin (S.states me).length
  dst : Fin (S.states me).length
  event : Nat
  guard : Expr S me
  effects : List (Effect S me)
  faultOnly : Bool := false

/-- The fault kinds of format 2's event and transition faults (Format2.lean:2098-2140, 1231-1258,
2375-2376). `lose` acts as `drop`, `retry` as `delay`. -/
inductive FKind where
  | drop | lose | delay | retry | duplicate | enable | disable | inject
  deriving DecidableEq, Repr

/-- Which delivery attempts of the event a fault acts on (`Occurrence`, Input.lean:61-73). -/
inductive Occ where
  | any
  | exactly (n : Nat)
  | never
  deriving DecidableEq, Repr

def Occ.matches : Occ → Nat → Bool
  | .any, _ => true
  | .exactly n, k => n == k
  | .never, _ => false

/-- A fault. `event` is the event a delivery fault acts on or an `inject` fault injects; `targets`
the transitions (machine, index) an `enable`/`disable` fault acts on; `by_` the delay of a
`delay`, `retry` or `duplicate`; `window` the times of the delivered entry it acts at; `at_` and
`payload` the time and payload of an injected entry. -/
structure Fault where
  kind : FKind
  event : Nat := 0
  targets : List (Nat × Nat) := []
  occ : Occ := .any
  by_ : Nat := 0
  window : Option (Nat × Option Nat) := none
  at_ : Nat := 0
  payload : List (Nat × Val) := []
  deriving DecidableEq, Repr

/-- The fault acts on an entry of time `t` (`FaultIn.actsAt`, Format2.lean:150-153). -/
def Fault.actsAt (f : Fault) (t : Nat) : Bool :=
  match f.window with
  | none => true
  | some (a, u) => decide (a ≤ t) && (u.all fun u => decide (t < u))

/-- The fault, of one of `kinds`, acts on attempt `att` of event `ev` delivered at time `t`
(`faultMatches`, Format2.lean:2098-2099). -/
def Fault.hits (f : Fault) (kinds : List FKind) (ev att t : Nat) : Bool :=
  decide (f.kind ∈ kinds) && f.event == ev && f.occ.matches att && f.actsAt t

/-- The fault, of kind `k`, targets transition `i` of machine `m` at time `t` (`targeting`,
Format2.lean:1231-1232). -/
def Fault.targets? (f : Fault) (k : FKind) (m i t : Nat) : Bool :=
  f.kind == k && decide ((m, i) ∈ f.targets) && f.actsAt t

/-- A distribution of a sampled delay (docs/simulation.md, "Randomness"). -/
inductive Dist where
  | fixed (v : Nat)
  | choice (vs : List Nat)
  | uniform (lo hi : Nat)
  | table (pts : List (Nat × Nat))
  deriving DecidableEq, Repr

/-- The values a distribution can produce: `fixed v` gives `v`, `choice vs` one of `vs`, `uniform lo
hi` any of `lo, …, hi`, and a table any value between the smallest and the largest of its
points. A degenerate distribution (an empty choice, `uniform` with `hi < lo`, an empty table)
has an empty support; `Dist.wf` excludes them and `Sys.WF` refuses a system that has one. -/
def Dist.support : Dist → List Nat
  | .fixed v => [v]
  | .choice vs => vs
  | .uniform lo hi => List.range' lo (hi + 1 - lo)
  | .table pts =>
    match pts.map Prod.snd with
    | [] => []
    | x :: xs => List.range' (xs.foldl min x) (xs.foldl max x + 1 - xs.foldl min x)

/-- A well-formed distribution has a value to draw. -/
def Dist.wf : Dist → Bool
  | .fixed _ => true
  | .choice vs => !vs.isEmpty
  | .uniform lo hi => decide (lo ≤ hi)
  | .table pts => !pts.isEmpty

/-- The effect with its delay replaced (an `emit` or a `timer`; other effects are unchanged). -/
def Effect.withAfter {S : Sig} {me : Fin S.machines} (a : Nat) : Effect S me → Effect S me
  | .emit ev _ pl => .emit ev a pl
  | .timer n _ ev pl => .timer n a ev pl
  | .reply ev _ pl => .reply ev a pl
  | e => e

/-- A system: a signature, the transitions of each machine in declaration order, the initial
configuration (the scenario's entries), the faults it may run with, and the time after which
nothing is delivered (`stopAt`). -/
structure Sys where
  sig : Sig
  trans : (m : Fin sig.machines) → List (Trans sig m)
  init : Cfg
  faults : List Fault := []
  stopAt : Option Nat := none
  /-- The sampled delays (M2.8): the `emit` or `timer` effect number `j` of transition `i` of
  machine `m` takes its `after` from a draw of the distribution given, instead of from the
  effect's own `after`. Draw slot `k` of a label belongs to the `k`-th entry of this list. -/
  samples : List (Nat × Nat × Nat × Dist) := []

/-- The distributions of a system's sampled delays, in draw-slot order. -/
def Sys.dists (sys : Sys) : List Dist := sys.samples.map (fun s => s.2.2.2)

/-- The draw of the sampled effect `j` of transition `i` of machine `m`, if it is one. -/
def Sys.siteDraw (sys : Sys) (ds : List Nat) (m i j : Nat) : Option Nat :=
  (sys.samples.findIdx? (fun s => s.1 == m && s.2.1 == i && s.2.2.1 == j)).bind (fun k => ds[k]?)

/-- The system with every sampled delay replaced by the draw `ds` gives it. The signature, the
initial configuration, the faults, `stopAt` and the shape of every transition are those of `sys`:
the delivery of a label with draws `ds` is the delivery in `sys.resolve ds`. -/
def Sys.resolve (sys : Sys) (ds : List Nat) : Sys :=
  { sys with
    trans := fun m => (sys.trans m).mapIdx (fun i t =>
      { t with effects := t.effects.mapIdx (fun j eff =>
          match sys.siteDraw ds m.val i j with
          | some a => eff.withAfter a
          | none => eff) }) }

/-- The faults active under `mask`, with their indices, in order. -/
def Sys.active (sys : Sys) (mask : List Bool) : List (Nat × Fault) :=
  ((List.range sys.faults.length).zip sys.faults).filter (fun p => mask.getD p.1 false)

/-- A transition chosen to fire in a step: the machine and the index of its transition. -/
structure Winner (sys : Sys) where
  mach : Fin sys.sig.machines
  idx : Fin (sys.trans mach).length

/-- What a winner's effects produce besides its new state: the entries it emitted, in emission
order, and the names of its timers it set or cancelled. -/
abbrev Out := List Entry × List Nat

/-- The output of phase 2, one block per winner that fired, tagged with its machine. -/
abbrev Emitted := List (Nat × Out)

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
as the earlier effects left it; it writes only `own`, the entries it emits and its own timers. A
timer entry survives only if no later effect of the transition sets or cancels the same timer. -/
def runEffects {S : Sig} {me : Fin S.machines} (c : Cfg) (e : Entry) :
    List (Effect S me) → MState → Except Err (MState × Out)
  | [], own => .ok (own, [], [])
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
    if timeLimit ≤ c.time + after then .error .timeBound else
    match evalPayload (ctxOf c e own) pl with
    | .error err => .error err
    | .ok vs => match runEffects c e rest own with
      | .error err => .error err
      | .ok (st, outs, tn) =>
        .ok (st, { time := c.time + after, event := ev, payload := vs, sender := some me.val } :: outs, tn)
  | .timer n after ev pl :: rest, own =>
    if timeLimit ≤ c.time + after then .error .timeBound else
    match evalPayload (ctxOf c e own) pl with
    | .error err => .error err
    | .ok vs => match runEffects c e rest own with
      | .error err => .error err
      | .ok (st, outs, tn) =>
        let ent : Entry :=
          { time := c.time + after, event := ev, payload := vs, target := some me.val, timer := some n }
        .ok (st, (if n ∈ tn then outs else ent :: outs), n :: tn)
  | .cancel n :: rest, own =>
    match runEffects c e rest own with
    | .error err => .error err
    | .ok (st, outs, tn) => .ok (st, outs, n :: tn)
  | .reply ev after pl :: rest, own =>
    if timeLimit ≤ c.time + after then .error .timeBound else
    match evalPayload (ctxOf c e own) pl with
    | .error err => .error err
    | .ok vs => match e.sender with
      | none => .error .noRequester
      | some to => match runEffects c e rest own with
        | .error err => .error err
        | .ok (st, outs, tn) =>
          .ok (st, { time := c.time + after, event := ev, payload := vs, target := some to,
                     sender := some me.val } :: outs, tn)

/-- Fires winner `w` from its machine state `own`: the effects, then the move to `dst`. It reads
only `own` and the snapshot `c`. -/
def fireOne (sys : Sys) (c : Cfg) (e : Entry) (w : Winner sys) (own : MState) :
    Except Err (MState × Out) :=
  let t := (sys.trans w.mach).get w.idx
  match runEffects c e t.effects own with
  | .error err => .error err
  | .ok (st, out) => .ok ({ st with ctrl := t.dst.val }, out)

/-- Phase 2: the winners fire in list order, each from its machine as the list `ms` holds it, and
each writes its result back into `ms`. Other machines are read from the snapshot `c` only. What
each winner emits is returned as a block tagged with its machine. -/
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
control state on the delivered event, is a candidate (not `faultOnly`, or enabled by an active
fault), whose guard evaluates to `true` on the snapshot and that no active fault disables (format
2's `scan`, Format2.lean:1235-1258: the guard is evaluated before the disabling faults are
consulted). A guard that fails, or yields a non-Boolean, is an error. -/
def scan (sys : Sys) (act : List (Nat × Fault)) (c : Cfg) (e : Entry) (m : Fin sys.sig.machines)
    (own : MState) : List (Fin (sys.trans m).length) → Except Err (Option (Fin (sys.trans m).length))
  | [] => .ok none
  | i :: is =>
    let t := (sys.trans m).get i
    if t.src.val = own.ctrl ∧ t.event = e.event then
      if t.faultOnly && !(act.any fun p => p.2.targets? .enable m.val i.val e.time) then
        scan sys act c e m own is
      else
        match t.guard.eval (ctxOf c e own) with
        | .ok (.bool true) =>
          if act.any (fun p => p.2.targets? .disable m.val i.val e.time) then scan sys act c e m own is
          else .ok (some i)
        | .ok (.bool false) => scan sys act c e m own is
        | .ok _ => .error .sort
        | .error err => .error err
    else scan sys act c e m own is

/-- Phase 1 for machine `m`: its winning transition, if any, with guards on the snapshot. -/
def choose (sys : Sys) (act : List (Nat × Fault)) (c : Cfg) (e : Entry) (m : Fin sys.sig.machines) :
    Except Err (Option (Winner sys)) :=
  match at? c.machines m.val with
  | .error err => .error err
  | .ok own => match scan sys act c e m own (finList (sys.trans m).length) with
    | .error err => .error err
    | .ok none => .ok none
    | .ok (some i) => .ok (some { mach := m, idx := i })

/-- Phase 1 over the machines `ms`, in list order. -/
def winnersOf (sys : Sys) (act : List (Nat × Fault)) (c : Cfg) (e : Entry) :
    List (Fin sys.sig.machines) → Except Err (List (Winner sys))
  | [] => .ok []
  | m :: ms => match choose sys act c e m with
    | .error err => .error err
    | .ok w => match winnersOf sys act c e ms with
      | .error err => .error err
      | .ok ws => .ok (match w with | some w => w :: ws | none => ws)

/-- The machines an entry is delivered to: its target, or every machine, in index order. -/
def addressed (n : Nat) (e : Entry) : List (Fin n) :=
  (finList n).filter (fun m => e.target.all (· == m.val))

/-- The winners of a step, in machine-index order. -/
def winners (sys : Sys) (act : List (Nat × Fault)) (c : Cfg) (e : Entry) :
    Except Err (List (Winner sys)) :=
  winnersOf sys act c e (addressed sys.sig.machines e)

/-- The entries machine `m` emitted, or none. -/
def blockOf (m : Nat) : Emitted → List Entry
  | [] => []
  | (i, out) :: bs => if i = m then out.1 else blockOf m bs

/-- The emitted entries of a system of `n` machines in machine-index order, whatever the order of
the blocks. -/
def inMachineOrder (n : Nat) (bs : Emitted) : List Entry :=
  (List.range n).flatMap (fun m => blockOf m bs)

/-- The timers (machine, name) the winners set or cancelled. -/
def touchedOf (bs : Emitted) : List (Nat × Nat) :=
  bs.flatMap (fun b => b.2.2.map (fun n => (b.1, n)))

/-- A pending entry is the entry of one of the timers `ts`. -/
def isTimerOf (ts : List (Nat × Nat)) (x : Entry) : Bool :=
  match x.target, x.timer with
  | some m, some n => decide ((m, n) ∈ ts)
  | _, _ => false

/-- Inserts `e` before the first entry of `q` whose time is later than its own. On a queue sorted
by time this is the position format 2's `insertE` (Format2.lean:1022-1025) gives: after every entry
of no later time. -/
def insertByTime (q : List Entry) (e : Entry) : List Entry :=
  match q with
  | [] => [e]
  | x :: xs => if e.time < x.time then e :: x :: xs else x :: insertByTime xs e

/-- The configuration after a delivery from `c0` (time advanced, delivered entry removed) whose
phase 2 gave `r`: the machines phase 2 left; the pending entries of the timers the winners set or
cancelled removed; the emitted entries inserted by time, in machine-index order. -/
def Cfg.commit (n : Nat) (c0 : Cfg) (ms : List MState) (bs : Emitted) : Cfg :=
  { c0 with machines := ms,
            pending := (inMachineOrder n bs).foldl insertByTime
              (c0.pending.filter (fun x => !isTimerOf (touchedOf bs) x)) }

def afterPhase2 (sys : Sys) (c0 : Cfg) : Except Err (List MState × Emitted) → Except Err Cfg
  | .error err => .error err
  | .ok (ms, bs) => .ok (c0.commit sys.sig.machines ms bs)

/-- `c` with entry `x` inserted into its pending list by time. -/
def Cfg.enq (c : Cfg) (x : Entry) : Cfg := { c with pending := insertByTime c.pending x }

/-- The number of earlier delivery attempts of event `ev`. -/
def Cfg.attemptsOf (c : Cfg) (ev : Nat) : Nat := c.attempts.getD ev 0

/-- `l` with element `i` set to `v`, padded with zeros. -/
def setAt (l : List Nat) (i v : Nat) : List Nat :=
  if i < l.length then l.set i v else l ++ List.replicate (i - l.length) 0 ++ [v]

/-- `c` with the entry `e` at index `k` taken for delivery: the time advanced to the entry's, the
entry removed, the attempt count of its event advanced. -/
def Cfg.pop (c : Cfg) (k : Nat) (e : Entry) : Cfg :=
  { c with time := e.time, pending := c.pending.eraseIdx k,
           attempts := setAt c.attempts e.event (c.attemptsOf e.event + 1) }

/-- A copy of entry `e`, `by_` later, marked as done by fault `i`; `timeBound` at or beyond
`2^53`. -/
def later (e : Entry) (i by_ : Nat) : Except Err Entry :=
  if timeLimit ≤ e.time + by_ then .error .timeBound
  else .ok { e with time := e.time + by_, done := e.done ++ [i] }

/-- After a delivery that committed, the first active `duplicate` fault that acts on the attempt
and has not acted on this entry queues a copy (`duplicateAfter`, Format2.lean:2122-2140). -/
def duplicate (act : List (Nat × Fault)) (e : Entry) (att : Nat) : Except Err Cfg → Except Err Cfg
  | .error err => .error err
  | .ok c' =>
    match act.find? (fun p => p.2.hits [.duplicate] e.event att e.time && !(e.done.contains p.1)) with
    | none => .ok c'
    | some (i, f) => match later e i f.by_ with
      | .error err => .error err
      | .ok cp => .ok (c'.enq cp)

/-- The delivery of the pending entry at index `k` under fault mask `mask`, with phase 2 given by
`p2` (format 2's `stepHead` for an event, Format2.lean:2259-2305, in calculus terms). The entry
must have minimal time and not be after `stopAt`. The attempt count of its event is advanced; an
active `drop`/`lose` fault acting on the attempt drops it; otherwise the first active
`delay`/`retry` fault acting on it that has not delayed it yet re-queues it later; otherwise it is
delivered (phase 1 on the snapshot, phase 2), and then a `duplicate` fault may queue a copy. -/
def deliverWith (sys : Sys)
    (p2 : Cfg → Entry → List (Winner sys) → List MState → Except Err (List MState × Emitted))
    (mask : List Bool) (c : Cfg) (k : Nat) : Option (Except Err Cfg) :=
  match c.pending[k]? with
  | none => none
  | some e =>
    if c.pending.all (fun x => decide (e.time ≤ x.time)) && sys.stopAt.all (fun s => decide (e.time ≤ s)) then
      let act := sys.active mask
      let att := c.attemptsOf e.event + 1
      some (
        if act.any (fun p => p.2.hits [.drop, .lose] e.event att e.time) then .ok (c.pop k e)
        else match act.find? (fun p => p.2.hits [.delay, .retry] e.event att e.time && !(e.done.contains p.1)) with
          | some (i, f) => match later e i f.by_ with
            | .error err => .error err
            | .ok cp => .ok ((c.pop k e).enq cp)
          | none => match winners sys act (c.pop k e) e with
            | .error err => .error err
            | .ok ws => duplicate act e att (afterPhase2 sys (c.pop k e) (p2 (c.pop k e) e ws c.machines)))
    else none

/-- Delivers the pending entry at index `k` under fault mask `mask`. `none`: no step has this
label (`k` is not the index of an entry of minimal time, or the entry is after `stopAt`).
`some (.error _)`: the step fails. Guards read the configuration at the start of the step, with
the time advanced to the entry's; the winners fire under snapshot reads (`phase2`). -/
def deliverAt (sys : Sys) (mask : List Bool) (c : Cfg) (k : Nat) : Option (Except Err Cfg) :=
  deliverWith sys (phase2 sys) mask c k

/-- For contrast, the same delivery under the next-configuration reads of `phase2Next`. -/
def deliverNext (sys : Sys) (mask : List Bool) (c : Cfg) (k : Nat) : Option (Except Err Cfg) :=
  deliverWith sys (phase2Next sys) mask c k

/-- The state a delivery leads to from `c`: the new configuration, or the error state carrying
`c`. -/
def outcome (mask : List Bool) (c : Cfg) : Except Err Cfg → State
  | .ok c' => .run mask c'
  | .error _ => .err mask c

/-- Adds the entry of an `inject` fault to a queue; other faults add nothing. -/
def injectStep (q : List Entry) (p : Nat × Fault) : List Entry :=
  if p.2.kind = .inject then insertByTime q { time := p.2.at_, event := p.2.event, payload := p.2.payload }
  else q

/-- The initial configuration under `mask`: the scenario's entries, then the entries of the
active `inject` faults, in fault order (`initialConf`, Format2.lean:2374-2376). -/
def Sys.initCfg (sys : Sys) (mask : List Bool) : Cfg :=
  { sys.init with pending := (sys.active mask).foldl injectStep sys.init.pending }

@[simp] theorem resolve_active (sys : Sys) (ds : List Nat) (mask : List Bool) :
    (sys.resolve ds).active mask = sys.active mask := rfl
@[simp] theorem resolve_stopAt (sys : Sys) (ds : List Nat) : (sys.resolve ds).stopAt = sys.stopAt := rfl
@[simp] theorem resolve_sig (sys : Sys) (ds : List Nat) : (sys.resolve ds).sig = sys.sig := rfl
@[simp] theorem resolve_init (sys : Sys) (ds : List Nat) : (sys.resolve ds).init = sys.init := rfl
@[simp] theorem resolve_faults (sys : Sys) (ds : List Nat) : (sys.resolve ds).faults = sys.faults := rfl
theorem resolve_nil {sys : Sys} (h : sys.samples = []) (ds : List Nat) : sys.resolve ds = sys := by
  obtain ⟨sig, tr, init, fa, st, sa⟩ := sys
  simp only at h
  subst h
  have key : ∀ (m : Fin sig.machines) (l : List (Exegra.Core.Behav.Trans sig m)),
      l.mapIdx (fun i t => { t with effects := t.effects.mapIdx (fun j (eff : Effect sig m) =>
          match (Sys.siteDraw { sig := sig, trans := tr, init := init, faults := fa, stopAt := st, samples := [] } ds m.val i j) with
          | some a => eff.withAfter a
          | none => eff) }) = l := by
    intro m l
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_mapIdx, Sys.siteDraw, List.findIdx?_nil, Option.bind_none]
      cases l[i] with
      | mk a b c d e f =>
        simp only [Trans.mk.injEq, true_and, and_true]
        apply List.ext_getElem
        · simp
        · intro j _ _; simp
  simp only [Sys.resolve]
  congr 1
  funext m
  exact key m (tr m)

/-! ### Labels and the declarative step relation -/

/-- A label of a step: the delivered entry, identified by itself (so by something that does not
change when other entries are inserted or removed), and the draws of the step, one per sampled
delay of the system (`Sys.samples`), in order. -/
structure Label where
  entry : Entry
  draws : List Nat := []
  deriving DecidableEq, Repr

/-- The draws are one per sampled delay, each in the support of its distribution. -/
def DrawsOk (sys : Sys) (ds : List Nat) : Prop :=
  ds.length = sys.dists.length ∧ ∀ p ∈ ds.zip sys.dists, p.1 ∈ p.2.support

instance (sys : Sys) (ds : List Nat) : Decidable (DrawsOk sys ds) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The entry `e` may be delivered from `c`: it is pending, of minimal time, and not after
`stopAt`. -/
def Ready (sys : Sys) (c : Cfg) (e : Entry) : Prop :=
  e ∈ c.pending ∧ (∀ x ∈ c.pending, e.time ≤ x.time) ∧ ∀ s ∈ sys.stopAt, e.time ≤ s

/-- `c` with the entry `e` taken for delivery: the time advanced to the entry's, its first
occurrence removed, the attempt count of its event advanced. -/
def Cfg.popE (c : Cfg) (e : Entry) : Cfg :=
  { c with time := e.time, pending := c.pending.erase e,
           attempts := setAt c.attempts e.event (c.attemptsOf e.event + 1) }

/-- The first active `duplicate` fault that acts on attempt `att` of `e` and has not acted on it
yet, if any. -/
def dupFault (act : List (Nat × Fault)) (e : Entry) (att : Nat) : Option (Nat × Fault) :=
  act.find? (fun p => p.2.hits [.duplicate] e.event att e.time && !(e.done.contains p.1))

/-- The first active `delay` or `retry` fault that acts on attempt `att` of `e` and has not
delayed it yet, if any. -/
def delayFault (act : List (Nat × Fault)) (e : Entry) (att : Nat) : Option (Nat × Fault) :=
  act.find? (fun p => p.2.hits [.delay, .retry] e.event att e.time && !(e.done.contains p.1))

/-- A drop fault acts on the attempt. -/
def dropHit (act : List (Nat × Fault)) (e : Entry) (att : Nat) : Prop :=
  act.any (fun p => p.2.hits [.drop, .lose] e.event att e.time) = true

/-- After a committed delivery, the copy the first active `duplicate` fault queues (or none). -/
inductive Dup (act : List (Nat × Fault)) (e : Entry) (att : Nat) (c' : Cfg) : Cfg → Prop
  | none : dupFault act e att = none → Dup act e att c' c'
  | some {i : Nat} {f : Fault} {cp : Entry} : dupFault act e att = some (i, f) →
      later e i f.by_ = .ok cp → Dup act e att c' (c'.enq cp)

/-- A delivery of `e` fails: phase 1, phase 2 or the copy a `duplicate` fault queues fails. -/
inductive Fails (sys : Sys) (act : List (Nat × Fault)) (c0 : Cfg) (e : Entry) (att : Nat) : Prop
  | winners {err : Err} : winners sys act c0 e = .error err → Fails sys act c0 e att
  | phase2 {ws : List (Winner sys)} {err : Err} : winners sys act c0 e = .ok ws →
      phase2 sys c0 e ws c0.machines = .error err → Fails sys act c0 e att
  | dup {ws : List (Winner sys)} {ms : List MState} {bs : Emitted} {i : Nat} {f : Fault}
      {err : Err} : winners sys act c0 e = .ok ws → phase2 sys c0 e ws c0.machines = .ok (ms, bs) →
      dupFault act e att = some (i, f) → later e i f.by_ = .error err → Fails sys act c0 e att

/-- **The step relation of the calculus**, stated without the executable delivery. A step delivers
the entry `l.entry`, which has minimal time among the pending entries and is not after `stopAt`,
with draws `l.draws` in the supports of the distributions; the faults of the mask then act on the
attempt in the order format 2 gives them. Evaluation (phase 1 and phase 2) is the calculus's own
`winners` and `phase2` on the system with the draws substituted. **This is the boundary of the
independence**: `Step` does not mention the executable `deliver`, but guard and effect evaluation,
winner selection and the commit are the functions `deliver` also uses, so `deliver_iff_step` checks
the scheduling, faults, draws and queue handling against a second statement, not the evaluation. -/
inductive Step (sys : Sys) (mask : List Bool) (c : Cfg) : Label → State → Prop
  | drop {l : Label} : DrawsOk sys l.draws → Ready sys c l.entry →
      dropHit (sys.active mask) l.entry (c.attemptsOf l.entry.event + 1) →
      Step sys mask c l (.run mask (c.popE l.entry))
  | delay {l : Label} {i : Nat} {f : Fault} {cp : Entry} : DrawsOk sys l.draws → Ready sys c l.entry →
      ¬ dropHit (sys.active mask) l.entry (c.attemptsOf l.entry.event + 1) →
      delayFault (sys.active mask) l.entry (c.attemptsOf l.entry.event + 1) = some (i, f) →
      later l.entry i f.by_ = .ok cp →
      Step sys mask c l (.run mask ((c.popE l.entry).enq cp))
  | delayTimeErr {l : Label} {i : Nat} {f : Fault} {err : Err} : DrawsOk sys l.draws →
      Ready sys c l.entry →
      ¬ dropHit (sys.active mask) l.entry (c.attemptsOf l.entry.event + 1) →
      delayFault (sys.active mask) l.entry (c.attemptsOf l.entry.event + 1) = some (i, f) →
      later l.entry i f.by_ = .error err →
      Step sys mask c l (.err mask c)
  | deliverOk {l : Label} {ws : List (Winner (sys.resolve l.draws))} {ms : List MState}
      {bs : Emitted} {c'' : Cfg} : DrawsOk sys l.draws → Ready sys c l.entry →
      ¬ dropHit (sys.active mask) l.entry (c.attemptsOf l.entry.event + 1) →
      delayFault (sys.active mask) l.entry (c.attemptsOf l.entry.event + 1) = none →
      winners (sys.resolve l.draws) (sys.active mask) (c.popE l.entry) l.entry = .ok ws →
      phase2 (sys.resolve l.draws) (c.popE l.entry) l.entry ws c.machines = .ok (ms, bs) →
      Dup (sys.active mask) l.entry (c.attemptsOf l.entry.event + 1)
        ((c.popE l.entry).commit sys.sig.machines ms bs) c'' →
      Step sys mask c l (.run mask c'')
  | deliverErr {l : Label} : DrawsOk sys l.draws → Ready sys c l.entry →
      ¬ dropHit (sys.active mask) l.entry (c.attemptsOf l.entry.event + 1) →
      delayFault (sys.active mask) l.entry (c.attemptsOf l.entry.event + 1) = none →
      Fails (sys.resolve l.draws) (sys.active mask) (c.popE l.entry) l.entry
        (c.attemptsOf l.entry.event + 1) →
      Step sys mask c l (.err mask c)

/-- The delivery of a label: `none` when the draws are not in the supports or the entry is not
pending, minimal and not after `stopAt`; otherwise the executable delivery of the entry in the
system with the draws substituted. -/
def deliver (sys : Sys) (mask : List Bool) (c : Cfg) (l : Label) : Option (Except Err Cfg) :=
  if DrawsOk sys l.draws then
    match c.pending.idxOf? l.entry with
    | none => none
    | some k => deliverAt (sys.resolve l.draws) mask c k
  else none

/-- The transition system of a system: an initial state per fault mask (all-or-nothing per fault:
the mask is chosen once and kept; format 2's run is the all-true mask over the scenario's faults);
a step is `Step`. The error state has no successor. -/
def Sys.lts (sys : Sys) : LTS State Label where
  init s := ∃ mask, mask.length = sys.faults.length ∧ s = .run mask (sys.initCfg mask)
  step s l t := match s with
    | .run mask c => Step sys mask c l t
    | .err _ _ => False

/-! ### Basic facts -/

/-- **Non-vacuity.** Every system has an initial state (the all-true fault mask, for one). -/
theorem lts_nonVacuous (sys : Sys) : (Sys.lts sys).NonVacuous :=
  ⟨.run (List.replicate sys.faults.length true) (sys.initCfg _), _, List.length_replicate, rfl⟩

/-- **The error state has no successor.** -/
theorem err_deadlocked (sys : Sys) (m : List Bool) (c : Cfg) : (Sys.lts sys).Deadlocked (.err m c) :=
  fun _ _ h => h

/-- A step delivers a ready entry, with draws in the supports. -/
theorem Step.ready {sys : Sys} {m : List Bool} {c : Cfg} {l : Label} {t : State}
    (h : Step sys m c l t) : DrawsOk sys l.draws ∧ Ready sys c l.entry := by
  cases h <;> exact ⟨‹_›, ‹_›⟩

/-- **The fault mask is constant along steps.** -/
theorem mask_const {sys : Sys} {m : List Bool} {c : Cfg} {l : Label} {t : State}
    (h : (Sys.lts sys).step (.run m c) l t) : t.mask = m := by
  have h' : Step sys m c l t := h
  cases h' <;> rfl

/-- Under the empty mask no fault is active, and the initial configuration is the scenario's. -/
theorem initCfg_nil (sys : Sys) : sys.initCfg [] = sys.init := by
  have hf : ∀ l : List (Nat × Fault), l.filter (fun _ => false) = [] := by
    intro l; induction l with
    | nil => rfl
    | cons _ _ ih => simp only [List.filter, ih]
  simp [Sys.initCfg, Sys.active, hf]

/-- A system with no faults has exactly one initial state. -/
theorem init_of_no_faults {sys : Sys} (hf : sys.faults = []) {s : State} (h : (Sys.lts sys).init s) :
    s = .run [] sys.init := by
  obtain ⟨m, hm, rfl⟩ := h
  rw [hf] at hm
  rw [List.length_eq_zero_iff.mp hm, initCfg_nil]

/-- Only an index into the pending list labels a step. -/
theorem deliver_none_of_length_le (sys : Sys) (m : List Bool) (c : Cfg) {k : Nat}
    (h : c.pending.length ≤ k) : deliverAt sys m c k = none := by
  simp only [deliverAt, deliverWith, List.getElem?_eq_none h]

/-- A configuration with nothing pending has no successor. -/
theorem deadlocked_of_pending_nil (sys : Sys) (m : List Bool) (c : Cfg) (h : c.pending = []) :
    (Sys.lts sys).Deadlocked (.run m c) := by
  intro l t hst
  have hr := (Step.ready (show Step sys m c l t from hst)).2.1
  rw [h] at hr
  cases hr

theorem idxOf?_facts : ∀ {l : List Entry} {e : Entry} {k : Nat}, l.idxOf? e = some k →
    l[k]? = some e ∧ l.eraseIdx k = l.erase e
  | [], e, k, h => by simp [List.idxOf?] at h
  | x :: xs, e, k, h => by
    by_cases hx : x = e
    · subst hx
      simp only [List.idxOf?_cons, beq_self_eq_true, if_true, Option.some.injEq] at h
      subst h
      simp [List.erase_cons]
    · have hb : (x == e) = false := by simpa using hx
      simp only [List.idxOf?_cons, hb, Bool.false_eq_true, if_false] at h
      cases hr : xs.idxOf? e with
      | none => rw [hr] at h; cases h
      | some j =>
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨h1, h2⟩ := idxOf?_facts hr
        refine ⟨by simpa using h1, ?_⟩
        simp [List.erase_cons, hb, h2]

theorem Cfg.pop_eq_popE {c : Cfg} {e : Entry} {k : Nat} (h : c.pending.idxOf? e = some k) :
    c.pop k e = c.popE e := by
  simp only [Cfg.pop, Cfg.popE, (idxOf?_facts h).2]

/-- A ready entry is at some index. -/
theorem Ready.idx {sys : Sys} {c : Cfg} {e : Entry} (h : Ready sys c e) :
    ∃ k, c.pending.idxOf? e = some k := by
  cases hk : c.pending.idxOf? e with
  | some k => exact ⟨k, rfl⟩
  | none => exact absurd h.1 (List.idxOf?_eq_none_iff.mp hk)

theorem ready_iff {sys : Sys} {c : Cfg} {e : Entry} :
    (c.pending.all (fun x => decide (e.time ≤ x.time)) && sys.stopAt.all (fun s => decide (e.time ≤ s))) = true ↔
      (∀ x ∈ c.pending, e.time ≤ x.time) ∧ ∀ s ∈ sys.stopAt, e.time ≤ s := by
  cases hs : sys.stopAt <;> simp [List.all_eq_true]


/-- **The executable delivery is proved against the relation**: a label delivers to `t` exactly
when it is a step of `Step`. -/
theorem deliver_eq_step {sys : Sys} {mask : List Bool} {c : Cfg} {l : Label} {t : State} :
    (deliver sys mask c l).map (outcome mask c) = some t ↔ Step sys mask c l t := by
  constructor
  · intro h
    unfold deliver at h
    split at h
    · rename_i hd
      split at h
      · cases h
      · rename_i k hk
        obtain ⟨hget, _⟩ := idxOf?_facts hk
        have hpop := Cfg.pop_eq_popE hk
        unfold deliverAt deliverWith at h
        rw [hget] at h
        simp only [] at h
        split at h
        · rename_i hc
          rw [ready_iff] at hc
          have hready : Ready sys c l.entry := ⟨List.mem_of_getElem? hget, hc⟩
          simp only [hpop, resolve_active, Option.map_some, Option.some.injEq] at h
          have hd' := hd
          split at h
          · rename_i hdr
            subst h
            exact Step.drop hd hready hdr
          · rename_i hdr
            split at h
            · rename_i i f hf
              split at h
              · rename_i err hl
                subst h
                exact Step.delayTimeErr hd hready hdr hf hl
              · rename_i cp hl
                subst h
                exact Step.delay hd hready hdr hf hl
            · rename_i hnone
              split at h
              · rename_i err hw
                subst h
                exact Step.deliverErr hd hready hdr hnone (Fails.winners hw)
              · rename_i ws hw
                cases hp : phase2 (sys.resolve l.draws) (c.popE l.entry) l.entry ws c.machines with
                | error err =>
                  rw [hp] at h
                  simp only [afterPhase2, duplicate] at h
                  subst h
                  exact Step.deliverErr hd hready hdr hnone (Fails.phase2 hw hp)
                | ok r =>
                  obtain ⟨ms, bs⟩ := r
                  rw [hp] at h
                  simp only [afterPhase2, duplicate] at h
                  split at h
                  · rename_i hdup
                    subst h
                    exact Step.deliverOk hd hready hdr hnone hw hp (Dup.none hdup)
                  · rename_i i f hdup
                    split at h
                    · rename_i err hl
                      subst h
                      exact Step.deliverErr hd hready hdr hnone (Fails.dup hw hp hdup hl)
                    · rename_i cp hl
                      subst h
                      exact Step.deliverOk hd hready hdr hnone hw hp (Dup.some hdup hl)
        · cases h
    · cases h
  · intro h
    obtain ⟨hd, hready⟩ := Step.ready h
    obtain ⟨k, hk⟩ := hready.idx
    obtain ⟨hget, _⟩ := idxOf?_facts hk
    have hpop := Cfg.pop_eq_popE hk
    have hc := (ready_iff (sys := sys) (c := c) (e := l.entry)).mpr hready.2
    unfold deliver
    rw [if_pos hd]
    simp only [hk]
    unfold deliverAt deliverWith
    rw [hget]
    simp only [resolve_active, resolve_stopAt, hc, hpop, if_true, Option.map_some, Option.some.injEq]
    cases h with
    | drop _ _ hdr => unfold dropHit at hdr; rw [if_pos hdr]; rfl
    | delay _ _ hdr hf hl =>
      unfold dropHit at hdr; rw [if_neg hdr]; unfold delayFault at hf; rw [hf]; simp only [hl]; rfl
    | delayTimeErr _ _ hdr hf hl =>
      unfold dropHit at hdr; rw [if_neg hdr]; unfold delayFault at hf; rw [hf]; simp only [hl]; rfl
    | deliverOk _ _ hdr hnone hw hp hdup =>
      unfold dropHit at hdr; rw [if_neg hdr]; unfold delayFault at hnone; rw [hnone]; simp only [hw, hp, afterPhase2]
      cases hdup with
      | none h0 => unfold dupFault at h0; simp only [duplicate, h0]; rfl
      | some h0 hl => unfold dupFault at h0; simp only [duplicate, h0, hl]; rfl
    | deliverErr _ _ hdr hnone hfail =>
      unfold dropHit at hdr; rw [if_neg hdr]; unfold delayFault at hnone; rw [hnone]
      cases hfail with
      | winners hw => simp only [hw]; rfl
      | phase2 hw hp => replace hp : phase2 (sys.resolve l.draws) (c.popE l.entry) l.entry _ c.machines = _ := hp; simp only [hw, hp, afterPhase2, duplicate]; rfl
      | dup hw hp h0 hl => replace hp : phase2 (sys.resolve l.draws) (c.popE l.entry) l.entry _ c.machines = _ := hp; unfold dupFault at h0; simp only [hw, hp, afterPhase2, duplicate, h0, hl]; rfl
/-- A step is a successful lookup in the executable delivery of the resolved system, at the index
of the entry. -/
theorem step_deliverAt {sys : Sys} {m : List Bool} {c : Cfg} {l : Label} {t : State}
    (h : Step sys m c l t) :
    ∃ k, (deliverAt (sys.resolve l.draws) m c k).map (outcome m c) = some t := by
  have h1 := (deliver_eq_step (sys := sys) (mask := m) (c := c) (l := l) (t := t)).mpr h
  unfold deliver at h1
  rw [if_pos (Step.ready h).1] at h1
  obtain ⟨k, hk⟩ := (Step.ready h).2.idx
  exact ⟨k, by simpa [hk] using h1⟩

/-- Inserting an entry into the queue only reorders: the result is a permutation of `e :: q`. -/
theorem insertByTime_perm (q : List Entry) (e : Entry) : (insertByTime q e).Perm (e :: q) := by
  induction q with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
    simp only [insertByTime]
    split
    · exact List.Perm.refl _
    · exact ((ih.cons x).trans (List.Perm.swap e x xs))

/-! ### Phase 2 does not depend on the order of the winners -/

/-- The machines after phase 2, if it succeeds. -/
def machinesAfter (r : Except Err (List MState × Emitted)) : Option (List MState) :=
  r.toOption.map Prod.fst

theorem machinesAfter_cons_ok {sys : Sys} {c : Cfg} {e : Entry} {w : Winner sys}
    {ws : List (Winner sys)} {ms : List MState} {own st : MState} {out : Out}
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

/-- **Snapshot phase 2 is order-independent** (plan-M2, M2.1 and M2.7). When the winners are on
distinct machines (a machine is one instance: the instances of a counted behaviour are distinct
machines), the machines after phase 2 are the same for every order of the winners (or phase 2 fails
in both orders; which error is reported may depend on the order). Every expression reads other
machines, their control states and the aggregates `count`, `sum`, `min`, `max` over instances from
the start-of-step snapshot `c` (`Ref.eval`, `ctxOf`), so this holds with aggregates and replies.
The emitted blocks are `phase2_perm_emitted`; the whole delivery is `deliver_perm`. -/
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

theorem choose_mach {sys : Sys} {act : List (Nat × Fault)} {c : Cfg} {e : Entry}
    {m : Fin sys.sig.machines} {w : Winner sys}
    (h : choose sys act c e m = .ok (some w)) : w.mach = m := by
  unfold choose at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
    · cases h; rfl

theorem winnersOf_sublist {sys : Sys} {act : List (Nat × Fault)} {c : Cfg} {e : Entry} :
    (ms : List (Fin sys.sig.machines)) → (ws : List (Winner sys)) →
    winnersOf sys act c e ms = .ok ws → (ws.map (·.mach)).Sublist ms
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
theorem winners_nodup {sys : Sys} {act : List (Nat × Fault)} {c : Cfg} {e : Entry}
    {ws : List (Winner sys)} (h : winners sys act c e = .ok ws) : (ws.map (·.mach)).Nodup :=
  ((winnersOf_sublist _ ws h).trans List.filter_sublist).nodup (finList_nodup _)

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

/-- Two results lead to the same state when they are both errors or the same configuration. -/
theorem outcome_eq_of_toOption {m : List Bool} {d : Cfg} {r r' : Except Err Cfg}
    (h : r.toOption = r'.toOption) : outcome m d r = outcome m d r' := by
  cases r <;> cases r' <;> simp_all [Except.toOption, outcome]

theorem duplicate_toOption {act : List (Nat × Fault)} {e : Entry} {att : Nat}
    {r r' : Except Err Cfg} (h : r.toOption = r'.toOption) :
    (duplicate act e att r).toOption = (duplicate act e att r').toOption := by
  cases r <;> cases r' <;> simp_all [Except.toOption, duplicate]

/-- The configuration after phase 2 does not depend on the order of the winners it fires. -/
theorem afterPhase2_perm {sys : Sys} {c0 : Cfg} {e : Entry} {ws ws' : List (Winner sys)}
    (hp : ws.Perm ws') (hnd : (ws.map (·.mach)).Nodup) :
    (afterPhase2 sys c0 (phase2 sys c0 e ws' c0.machines)).toOption =
      (afterPhase2 sys c0 (phase2 sys c0 e ws c0.machines)).toOption := by
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
      have ht : ∀ x, isTimerOf (touchedOf bs') x = isTimerOf (touchedOf bs) x := by
        intro x
        have hp' : (touchedOf bs).Perm (touchedOf bs') := hb.flatMap_right _
        unfold isTimerOf
        split
        · simp only [decide_eq_decide]; exact hp'.mem_iff.symm
        · rfl
      have hf : c0.pending.filter (fun x => !isTimerOf (touchedOf bs') x) =
          c0.pending.filter (fun x => !isTimerOf (touchedOf bs) x) :=
        List.filter_congr (fun x _ => by rw [ht x])
      simp only [afterPhase2, Cfg.commit, hm, hio, hf]

/-- **The delivery does not depend on the order of the winners.** Firing the winners a step
computes in any order `σ` chooses (any permutation, per configuration and entry) leads to the same
state as `deliverAt`: the same configuration (time, machines, pending list and attempt counts all
equal), or the error state in both, under every fault mask. Which error is reported may depend on
the order. Winners are instances (machines), and aggregates over instances are read from the
start-of-step snapshot, so the statement covers counted instances, aggregates and replies. -/
theorem deliver_perm (sys : Sys) (σ : Cfg → Entry → List (Winner sys) → List (Winner sys))
    (hσ : ∀ c e ws, (σ c e ws).Perm ws) (mask : List Bool) (c : Cfg) (k : Nat) :
    (deliverWith sys (fun c e ws ms => phase2 sys c e (σ c e ws) ms) mask c k).map (outcome mask c) =
      (deliverAt sys mask c k).map (outcome mask c) := by
  unfold deliverAt deliverWith
  cases c.pending[k]? with
  | none => rfl
  | some e =>
    simp only []
    split
    · simp only [Option.map_some, Option.some.injEq]
      split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · rename_i ws hw
            exact outcome_eq_of_toOption (duplicate_toOption
              (afterPhase2_perm (hσ _ _ ws).symm (winners_nodup hw)))
    · rfl


/-! ### A targeted entry is delivered only to its target -/

theorem winnersOf_mach {sys : Sys} {act : List (Nat × Fault)} {c : Cfg} {e : Entry} :
    (ms : List (Fin sys.sig.machines)) → {ws : List (Winner sys)} →
    winnersOf sys act c e ms = .ok ws → ∀ w ∈ ws, w.mach ∈ ms
  | [], ws, h => by
    simp only [winnersOf] at h; cases h; intro w hw; simp at hw
  | m :: ms, ws, h => by
    simp only [winnersOf] at h
    split at h
    · cases h
    · rename_i w0 hc
      split at h
      · cases h
      · rename_i ws0 hrest
        have ih := winnersOf_mach ms hrest
        cases w0 with
        | none =>
          simp only [Except.ok.injEq] at h; subst h
          intro w hw; exact List.mem_cons_of_mem _ (ih w hw)
        | some w1 =>
          simp only [Except.ok.injEq] at h; subst h
          intro w hw
          rcases List.mem_cons.mp hw with rfl | hw
          · have : w.mach = m := by
              simp only [choose] at hc
              split at hc
              · cases hc
              · split at hc
                · cases hc
                · cases hc
                · cases hc; rfl
            rw [this]; exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih w hw)

theorem winners_target {sys : Sys} {act : List (Nat × Fault)} {c : Cfg} {e : Entry} {i : Nat}
    {ws : List (Winner sys)} (h : winners sys act c e = .ok ws) (ht : e.target = some i) :
    ∀ w ∈ ws, w.mach.val = i := by
  intro w hw
  have := winnersOf_mach _ h w hw
  simp only [addressed, List.mem_filter, ht] at this
  exact (by simpa using this.2 : i = _).symm

theorem phase2_get {sys : Sys} {c : Cfg} {e : Entry} {j : Nat} :
    (ws : List (Winner sys)) → (ms : List MState) → {ms' : List MState} → {bs : Emitted} →
    phase2 sys c e ws ms = .ok (ms', bs) → (∀ w ∈ ws, w.mach.val ≠ j) → ms'[j]? = ms[j]?
  | [], ms, ms', bs, h, _ => by simp only [phase2] at h; cases h; rfl
  | w :: ws, ms, ms', bs, h, hj => by
    simp only [phase2] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i own _ st out _ ms2 outs hrec
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          rw [phase2_get ws _ hrec (fun x hx => hj x (List.mem_cons_of_mem _ hx))]
          exact List.getElem?_set_ne (fun h => hj w List.mem_cons_self h)

/-- **A targeted entry (reply, timer) is delivered only to its target instance**: no other
machine changes in a step that delivers an entry with target `i`. -/
theorem target_only {sys : Sys} {m : List Bool} {c c' : Cfg} {l : Label} {i : Nat}
    (h : Step sys m c l (.run m c')) (ht : l.entry.target = some i) :
    ∀ j, j ≠ i → c'.machines[j]? = c.machines[j]? := by
  intro j hj
  cases h with
  | drop => rfl
  | delay => rfl
  | deliverOk _ _ _ _ hw hp hdup =>
    have hms := phase2_get _ _ hp (fun w hw' => by
      rw [winners_target hw ht w hw']; exact fun h => hj h.symm)
    have hc : ∀ cc : Cfg, ∀ cc', (Dup (sys.active m) l.entry (c.attemptsOf l.entry.event + 1) cc cc') →
        cc'.machines = cc.machines := by
      intro cc cc' hd
      cases hd <;> rfl
    rw [hc _ _ hdup]
    exact hms

/-! ### The pending list is a multiset: bisimulation up to permutation -/

/-- Configurations equal up to a permutation of the pending list. -/
def Cfg.Approx (c c' : Cfg) : Prop :=
  c.time = c'.time ∧ c.machines = c'.machines ∧ c.attempts = c'.attempts ∧ c.pending.Perm c'.pending

/-- States equal up to a permutation of the pending list. -/
def State.Approx : State → State → Prop
  | .run m c, .run m' c' => m = m' ∧ c.Approx c'
  | .err m c, .err m' c' => m = m' ∧ c.Approx c'
  | _, _ => False

theorem Cfg.Approx.refl (c : Cfg) : c.Approx c := ⟨rfl, rfl, rfl, List.Perm.refl _⟩

theorem foldl_insertByTime_perm (l : List Entry) :
    ∀ p q : List Entry, p.Perm q → (l.foldl insertByTime p).Perm (l.foldl insertByTime q) := by
  induction l with
  | nil => intro p q h; exact h
  | cons x xs ih =>
    intro p q h
    exact ih _ _ ((insertByTime_perm p x).trans ((h.cons x).trans (insertByTime_perm q x).symm))

theorem Cfg.enq_approx {c c' : Cfg} (h : c.Approx c') (x : Entry) : (c.enq x).Approx (c'.enq x) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, h3, (insertByTime_perm _ _).trans ((h4.cons x).trans (insertByTime_perm _ _).symm)⟩

theorem Cfg.commit_approx {c c' : Cfg} (h : c.Approx c') (n : Nat) (ms : List MState) (bs : Emitted) :
    (c.commit n ms bs).Approx (c'.commit n ms bs) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, rfl, h3, foldl_insertByTime_perm _ _ _ (h4.filter _)⟩

theorem Cfg.popE_approx {c c' : Cfg} (h : c.Approx c') (e : Entry) : (c.popE e).Approx (c'.popE e) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨rfl, h2, by simp only [Cfg.popE, h3, Cfg.attemptsOf], h4.erase e⟩

theorem ctxOf_congr {c1 c2 : Cfg} (e : Entry) (own : MState) (h1 : c1.machines = c2.machines)
    (h2 : c1.time = c2.time) : ctxOf c1 e own = ctxOf c2 e own := by
  simp only [ctxOf, h1, h2]

theorem runEffects_congr {S : Sig} {me : Fin S.machines} {c1 c2 : Cfg} (e : Entry)
    (h1 : c1.machines = c2.machines) (h2 : c1.time = c2.time) :
    ∀ (effs : List (Effect S me)) (own : MState), runEffects c1 e effs own = runEffects c2 e effs own
  | [], own => by simp only [runEffects]
  | .set v rhs :: rest, own => by
    simp only [runEffects, ctxOf_congr e own h1 h2, runEffects_congr e h1 h2 rest]
  | .emit ev after pl :: rest, own => by
    simp only [runEffects, ctxOf_congr e own h1 h2, runEffects_congr e h1 h2 rest, h2]
  | .timer n after ev pl :: rest, own => by
    simp only [runEffects, ctxOf_congr e own h1 h2, runEffects_congr e h1 h2 rest, h2]
  | .cancel n :: rest, own => by
    simp only [runEffects, runEffects_congr e h1 h2 rest]
  | .reply ev after pl :: rest, own => by
    simp only [runEffects, ctxOf_congr e own h1 h2, runEffects_congr e h1 h2 rest, h2]

theorem fireOne_congr {sys : Sys} {c1 c2 : Cfg} (e : Entry) (w : Winner sys) (own : MState)
    (h1 : c1.machines = c2.machines) (h2 : c1.time = c2.time) :
    fireOne sys c1 e w own = fireOne sys c2 e w own := by
  simp only [fireOne, runEffects_congr e h1 h2]

theorem phase2_congr {sys : Sys} {c1 c2 : Cfg} (e : Entry) (h1 : c1.machines = c2.machines)
    (h2 : c1.time = c2.time) :
    ∀ (ws : List (Winner sys)) (ms : List MState), phase2 sys c1 e ws ms = phase2 sys c2 e ws ms
  | [], ms => by simp only [phase2]
  | w :: ws, ms => by
    simp only [phase2, fireOne_congr e w _ h1 h2]
    cases ms[w.mach.val]? with
    | none => rfl
    | some own =>
      simp only []
      cases fireOne sys c2 e w own with
      | error err => rfl
      | ok r => simp only [phase2_congr e h1 h2 ws]

theorem scan_congr {sys : Sys} {act : List (Nat × Fault)} {c1 c2 : Cfg} (e : Entry)
    (m : Fin sys.sig.machines) (own : MState) (h1 : c1.machines = c2.machines)
    (h2 : c1.time = c2.time) :
    ∀ is : List (Fin (sys.trans m).length), scan sys act c1 e m own is = scan sys act c2 e m own is
  | [] => by simp only [scan]
  | i :: is => by
    simp only [scan, ctxOf_congr e own h1 h2, scan_congr e m own h1 h2 is]

theorem winnersOf_congr {sys : Sys} {act : List (Nat × Fault)} {c1 c2 : Cfg} (e : Entry)
    (h1 : c1.machines = c2.machines) (h2 : c1.time = c2.time) :
    ∀ ms : List (Fin sys.sig.machines), winnersOf sys act c1 e ms = winnersOf sys act c2 e ms
  | [] => by simp only [winnersOf]
  | m :: ms => by
    simp only [winnersOf, choose, h1, scan_congr e m _ h1 h2, winnersOf_congr e h1 h2 ms]

theorem winners_congr {sys : Sys} {act : List (Nat × Fault)} {c1 c2 : Cfg} (e : Entry)
    (h1 : c1.machines = c2.machines) (h2 : c1.time = c2.time) :
    winners sys act c1 e = winners sys act c2 e := by
  simp only [winners, winnersOf_congr e h1 h2]

theorem Cfg.Approx.symm {c c' : Cfg} (h : c.Approx c') : c'.Approx c :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

theorem Dup.approx {act : List (Nat × Fault)} {e : Entry} {att : Nat} {c1 c1' c2 : Cfg}
    (h : c1.Approx c1') (hd : Dup act e att c1 c2) : ∃ c2', Dup act e att c1' c2' ∧ c2.Approx c2' := by
  cases hd with
  | none h0 => exact ⟨c1', Dup.none h0, h⟩
  | some h0 hl => exact ⟨c1'.enq _, Dup.some h0 hl, Cfg.enq_approx h _⟩

/-- **The pending list is a multiset**: configurations that differ only by a permutation of the
pending list have the same steps, with the same labels, up to a permutation of the pending list of
the successors (the label names the entry, not its position). -/
theorem pending_perm_bisim {sys : Sys} {m : List Bool} {c c' : Cfg} {l : Label} {t : State}
    (hp : c.pending.Perm c'.pending) (ht : c.time = c'.time) (hm : c.machines = c'.machines)
    (ha : c.attempts = c'.attempts) (h : Step sys m c l t) :
    ∃ t', Step sys m c' l t' ∧ t'.Approx t := by
  have hca : c.Approx c' := ⟨ht, hm, ha, hp⟩
  have hca' : c'.Approx c := ⟨ht.symm, hm.symm, ha.symm, hp.symm⟩
  have hatt : c'.attemptsOf l.entry.event = c.attemptsOf l.entry.event := by
    simp only [Cfg.attemptsOf, ha]
  have hrdy : ∀ {e}, Ready sys c e → Ready sys c' e := by
    intro e ⟨h1, h2, h3⟩
    exact ⟨hp.mem_iff.mp h1, fun x hx => h2 x (hp.mem_iff.mpr hx), h3⟩
  have hpop := Cfg.popE_approx hca' l.entry
  have hwin : ∀ (act : List (Nat × Fault)) (s : Sys),
      winners s act (c'.popE l.entry) l.entry = winners s act (c.popE l.entry) l.entry := fun act s =>
    winners_congr _ hpop.2.1 hpop.1
  have hph : ∀ (s : Sys) (ws : List (Winner s)) (ms : List MState),
      phase2 s (c'.popE l.entry) l.entry ws ms = phase2 s (c.popE l.entry) l.entry ws ms := fun s ws ms =>
    phase2_congr _ hpop.2.1 hpop.1 ws ms
  cases h with
  | drop hd hr hdr =>
    refine ⟨_, Step.drop hd (hrdy hr) (by rwa [hatt]), ?_⟩
    exact ⟨rfl, Cfg.popE_approx hca' _⟩
  | delay hd hr hdr hf hl =>
    refine ⟨_, Step.delay hd (hrdy hr) (by rwa [hatt]) (by rwa [hatt]) hl, ?_⟩
    exact ⟨rfl, Cfg.enq_approx (Cfg.popE_approx hca' _) _⟩
  | delayTimeErr hd hr hdr hf hl =>
    exact ⟨_, Step.delayTimeErr hd (hrdy hr) (by rwa [hatt]) (by rwa [hatt]) hl, rfl, hca'⟩
  | deliverOk hd hr hdr hnone hw hp2 hdup =>
    have hpop0 := Cfg.popE_approx hca l.entry
    have hdup2 := hdup
    rw [← hatt] at hdup2
    obtain ⟨c2', hd2, hc2⟩ := Dup.approx (Cfg.commit_approx hpop0 sys.sig.machines _ _) hdup2
    refine ⟨_, Step.deliverOk hd (hrdy hr) (by rwa [hatt]) (by rwa [hatt]) (by rw [hwin]; exact hw)
      (by rw [hph, ← hm]; exact hp2) hd2, rfl, hc2.symm⟩
  | deliverErr hd hr hdr hnone hfail =>
    refine ⟨_, Step.deliverErr hd (hrdy hr) (by rwa [hatt]) (by rwa [hatt]) ?_, rfl, hca'⟩
    rw [hatt]
    have hmach : (c'.popE l.entry).machines = (c.popE l.entry).machines := hpop.2.1
    cases hfail with
    | winners hw => exact Fails.winners ((hwin _ _).trans hw)
    | phase2 hw hp2 =>
      exact Fails.phase2 ((hwin _ _).trans hw)
        ((hph _ _ _).trans ((congrArg (phase2 _ _ _ _) hmach).trans hp2))
    | dup hw hp2 h0 hl =>
      exact Fails.dup ((hwin _ _).trans hw)
        ((hph _ _ _).trans ((congrArg (phase2 _ _ _ _) hmach).trans hp2)) h0 hl
/-! ### The forms of a delivery -/

/-- **What a successful delivery can produce**: the delivered entry `e` has minimal time and is not
after `stopAt`, and the new configuration is `c` with `e` popped (a drop), plus a later copy of `e`
(a delay), or the commit of phase 2's result, possibly plus a later copy of `e` (a duplicate). -/
theorem deliver_ok_form {sys : Sys} {mask : List Bool} {c c' : Cfg} {k : Nat}
    (h : deliverAt sys mask c k = some (.ok c')) :
    ∃ e, c.pending[k]? = some e ∧ (∀ x ∈ c.pending, e.time ≤ x.time) ∧
      (c' = c.pop k e ∨
       (∃ i b cp, later e i b = .ok cp ∧ c' = (c.pop k e).enq cp) ∨
       ∃ ws ms bs, phase2 sys (c.pop k e) e ws c.machines = .ok (ms, bs) ∧
         (c' = (c.pop k e).commit sys.sig.machines ms bs ∨
          ∃ i b cp, later e i b = .ok cp ∧ c' = ((c.pop k e).commit sys.sig.machines ms bs).enq cp)) := by
  unfold deliverAt deliverWith at h
  split at h
  · cases h
  · rename_i e he
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
      simp only [Option.some.injEq] at h
      refine ⟨e, he, hc.1, ?_⟩
      split at h
      · cases h; exact Or.inl rfl
      · split at h
        · split at h
          · cases h
          · rename_i cp hcp; cases h; exact Or.inr (Or.inl ⟨_, _, cp, hcp, rfl⟩)
        · split at h
          · cases h
          · rename_i ws _
            refine Or.inr (Or.inr ⟨ws, ?_⟩)
            cases hr : phase2 sys (c.pop k e) e ws c.machines with
            | error err => rw [hr] at h; simp [afterPhase2, duplicate] at h
            | ok r =>
              obtain ⟨ms, bs⟩ := r
              rw [hr] at h
              refine ⟨ms, bs, rfl, ?_⟩
              simp only [afterPhase2, duplicate] at h
              split at h
              · cases h; exact Or.inl rfl
              · split at h
                · cases h
                · rename_i cp hcp; cases h; exact Or.inr ⟨_, _, cp, hcp, rfl⟩
    · cases h

/-- **Where a failing delivery's error comes from**: a time at or beyond `2^53`, phase 1 or
phase 2. -/
theorem deliver_error_form {sys : Sys} {mask : List Bool} {c : Cfg} {k : Nat} {err : Err}
    (h : deliverAt sys mask c k = some (.error err)) :
    ∃ e, c.pending[k]? = some e ∧ (∀ x ∈ c.pending, e.time ≤ x.time) ∧
      (err = .timeBound ∨ (∃ act, winners sys act (c.pop k e) e = .error err) ∨
       ∃ ws, phase2 sys (c.pop k e) e ws c.machines = .error err) := by
  unfold deliverAt deliverWith at h
  split at h
  · cases h
  · rename_i e he
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
      simp only [Option.some.injEq] at h
      refine ⟨e, he, hc.1, ?_⟩
      have later_err : ∀ {i b : Nat} {er : Err}, later e i b = .error er → er = .timeBound := by
        intro i b er hl
        unfold later at hl
        split at hl
        · cases hl; rfl
        · cases hl
      split at h
      · cases h
      · split at h
        · split at h
          · rename_i er hl; cases h; exact Or.inl (later_err hl)
          · cases h
        · split at h
          · rename_i er hw; cases h; exact Or.inr (Or.inl ⟨_, hw⟩)
          · rename_i ws _
            cases hr : phase2 sys (c.pop k e) e ws c.machines with
            | error er =>
              rw [hr] at h; simp only [afterPhase2, duplicate] at h; cases h
              exact Or.inr (Or.inr ⟨ws, hr⟩)
            | ok r =>
              obtain ⟨ms, bs⟩ := r
              rw [hr] at h
              simp only [afterPhase2, duplicate] at h
              split at h
              · cases h
              · split at h
                · rename_i er hl; cases h; exact Or.inl (later_err hl)
                · cases h
    · cases h

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
def State.Shaped (sys : Sys) (s : State) : Prop := s.cfg.Shaped sys

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
    (effs : List (Effect S me)) → (own : MState) → (r : MState × Out) →
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
      · split at h
        · cases h
        · rename_i st outs tn hr
          cases h
          exact runEffects_fit rest own (st, outs, tn) hf hr
  | .timer n after ev pl :: rest, own, r, hf, h => by
    simp only [runEffects] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i st outs tn hr
          cases h
          exact runEffects_fit rest own (st, outs, tn) hf hr
  | .cancel n :: rest, own, r, hf, h => by
    simp only [runEffects] at h
    split at h
    · cases h
    · rename_i st outs tn hr
      cases h
      exact runEffects_fit rest own (st, outs, tn) hf hr
  | .reply ev after pl :: rest, own, r, hf, h => by
    simp only [runEffects] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · rename_i st outs tn hr
            cases h
            exact runEffects_fit rest own (st, outs, tn) hf hr

/-- Firing a winner keeps its machine shaped. -/
theorem fireOne_shaped {sys : Sys} {c : Cfg} {e : Entry} {w : Winner sys} {own : MState}
    {r : MState × Out} (hs : sys.sig.MShaped w.mach own) (h : fireOne sys c e w own = .ok r) :
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
          exact phase2_shaped ws _ (ms', outs) (hs.set (fireOne_shaped (r := (st, out)) hown hf)) hr

/-- A successful delivery keeps the configuration shaped. -/
theorem deliver_shaped {sys : Sys} {mask : List Bool} {c c' : Cfg} {k : Nat} (hs : c.Shaped sys)
    (h : deliverAt sys mask c k = some (.ok c')) : c'.Shaped sys := by
  obtain ⟨e, _, _, hf⟩ := deliver_ok_form h
  rcases hf with rfl | ⟨_, _, _, _, rfl⟩ | ⟨ws, ms, bs, hp, rfl | ⟨_, _, _, _, rfl⟩⟩
  · exact hs
  · exact hs
  · exact phase2_shaped ws c.machines (ms, bs) hs hp
  · exact phase2_shaped ws c.machines (ms, bs) hs hp

/-- **Shape is invariant.** From a shaped initial configuration, every reachable state is shaped:
each machine has a control state of its own and one value of the declared sort per variable. -/
theorem shaped_invariant (sys : Sys) (h : sys.init.Shaped sys) :
    (Sys.lts sys).Invariant (fun s => s.Shaped sys) := by
  refine LTS.safe_of_inductive (I := fun s => s.Shaped sys) ⟨?_, ?_⟩ (fun _ h => h)
  · intro s hs
    obtain ⟨mask, _, rfl⟩ := hs
    exact h
  · intro s l t hs hst
    cases s with
    | err m c => exact absurd hst id
    | run m c =>
      obtain ⟨k, hst'⟩ := step_deliverAt (show Step sys m c l t from hst)
      cases hd : deliverAt (sys.resolve l.draws) m c k with
      | none => rw [hd] at hst'; cases hst'
      | some r =>
        rw [hd] at hst'
        cases r with
        | error err => cases hst'; exact hs
        | ok c' => cases hst'; exact deliver_shaped (sys := sys.resolve l.draws) hs hd

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
  · intro h; cases h

theorem ne_shape_of {α β : Type} {x : Except Err α} {err : Err} (hx : x ≠ .error .shape)
    (h : x = .error err) : (Except.error err : Except Err β) ≠ .error .shape := by
  intro h'; injection h' with h'; subst h'; exact hx h

/-- What evaluation needs to read no state past its end: the snapshot is shaped, and the own
machine has one value per declared variable. -/
def Ctx.Shaped (S : Sig) (me : Fin S.machines) (cx : Ctx) : Prop :=
  S.Shaped cx.snap ∧ cx.own.vars.length = (S.vars me).length

theorem countIn_ne_shape {S : Sig} {snap : List MState} (hs : S.Shaped snap) (name : String) :
    (g : List (Fin S.machines)) → countIn S snap name g ≠ .error .shape
  | [] => by simp [countIn]
  | m :: g => by
    obtain ⟨x, hx, hxs⟩ := hs.get m
    have hl : m.val < snap.length := by rw [hs.1]; exact m.isLt
    have hxe : snap[m.val] = x := by
      rw [List.getElem?_eq_getElem hl] at hx; exact Option.some.inj hx
    simp only [countIn, at?_of_lt hl, hxe, at?_of_lt hxs.1]
    have ih := countIn_ne_shape hs name g
    cases h : countIn S snap name g with
    | error e => intro h'; injection h' with h'; subst h'; exact ih h
    | ok k => simp

theorem intsIn_ne_shape {S : Sig} {snap : List MState} (hs : S.Shaped snap) :
    (g : List ((m : Fin S.machines) × Fin (S.vars m).length)) → intsIn snap g ≠ .error .shape
  | [] => by simp [intsIn]
  | p :: g => by
    obtain ⟨x, hx, hxs⟩ := hs.get p.1
    have hl : p.1.val < snap.length := by rw [hs.1]; exact p.1.isLt
    have hxe : snap[p.1.val] = x := by
      rw [List.getElem?_eq_getElem hl] at hx; exact Option.some.inj hx
    have hv : p.2.val < x.vars.length := by rw [hxs.2.1]; exact p.2.isLt
    simp only [intsIn, at?_of_lt hl, hxe, at?_of_lt hv]
    have ih := intsIn_ne_shape hs g
    cases hval : x.vars[p.2.val] with
    | int n =>
      intro h'
      cases h : intsIn snap g with
      | error e => simp only [h] at h'; injection h' with h'; subst h'; exact ih h
      | ok ns => simp only [h] at h'; cases h'
    | bool b => intro h'; cases h'
    | str s => intro h'; cases h'
    | lit s t => intro h'; cases h'

theorem AggOp.apply_ne_shape (op : AggOp) (ns : List Int) : op.apply ns ≠ .error .shape := by
  cases op <;> cases ns <;> simp only [AggOp.apply] <;>
    first | exact Val.check_ne_shape _ _ | (intro h; cases h)

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
  | .count g name => by
    simp only [Ref.eval]
    cases h : countIn S cx.snap name g with
    | ok k => simp
    | error e =>
      simp only []; intro h'; injection h' with h'; subst h'; exact countIn_ne_shape hcx.1 name g h
  | .agg op g => by
    simp only [Ref.eval]
    cases h : intsIn cx.snap g with
    | ok ns => exact AggOp.apply_ne_shape op ns
    | error e =>
      simp only []; intro h'; injection h' with h'; subst h'; exact intsIn_ne_shape hcx.1 g h
  | .absent _ => by simp [Ref.eval]

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
    · intro h; cases h
    · split
      · rename_i err hr; exact ne_shape_of (evalPayload_ne_shape ⟨hsnap, hl⟩ pl) hr
      · split
        · rename_i err hr; exact ne_shape_of (runEffects_ne_shape hsnap rest own hl) hr
        · intro h; cases h
  | .timer n after ev pl :: rest, own, hl => by
    simp only [runEffects]
    split
    · intro h; cases h
    · split
      · rename_i err hr; exact ne_shape_of (evalPayload_ne_shape ⟨hsnap, hl⟩ pl) hr
      · split
        · rename_i err hr; exact ne_shape_of (runEffects_ne_shape hsnap rest own hl) hr
        · intro h; cases h
  | .cancel n :: rest, own, hl => by
    simp only [runEffects]
    split
    · rename_i err hr; exact ne_shape_of (runEffects_ne_shape hsnap rest own hl) hr
    · intro h; cases h
  | .reply ev after pl :: rest, own, hl => by
    simp only [runEffects]
    split
    · intro h; cases h
    · split
      · rename_i err hr; exact ne_shape_of (evalPayload_ne_shape ⟨hsnap, hl⟩ pl) hr
      · split
        · intro h; cases h
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
        exact ne_shape_of (phase2_ne_shape hsnap ws _ (hs.set (fireOne_shaped (r := (st, out)) hown hf))) hr
      · intro h; cases h

theorem scan_ne_shape {sys : Sys} {act : List (Nat × Fault)} {c : Cfg} {e : Entry}
    {m : Fin sys.sig.machines} {own : MState}
    (hsnap : sys.sig.Shaped c.machines) (hl : own.vars.length = (sys.sig.vars m).length) :
    (is : List (Fin (sys.trans m).length)) → scan sys act c e m own is ≠ .error .shape
  | [] => by simp [scan]
  | i :: is => by
    have ih := scan_ne_shape (act := act) (e := e) hsnap hl is
    simp only [scan]
    split
    · split
      · exact ih
      · split
        · split
          · exact ih
          · intro h; cases h
        · exact ih
        · intro h; cases h
        · rename_i err hr; exact ne_shape_of (Expr.eval_ne_shape ⟨hsnap, hl⟩ _) hr
    · exact ih

theorem winnersOf_ne_shape {sys : Sys} {act : List (Nat × Fault)} {c : Cfg} {e : Entry}
    (hsnap : sys.sig.Shaped c.machines) :
    (ms : List (Fin sys.sig.machines)) → winnersOf sys act c e ms ≠ .error .shape
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

theorem winners_ne_shape {sys : Sys} {act : List (Nat × Fault)} {c : Cfg} {e : Entry}
    (hsnap : sys.sig.Shaped c.machines) : winners sys act c e ≠ .error .shape :=
  winnersOf_ne_shape hsnap _

/-- **No step from a shaped configuration fails with `shape`.** -/
theorem deliver_ne_shape {sys : Sys} {mask : List Bool} {c : Cfg} (hs : c.Shaped sys) (k : Nat) :
    deliverAt sys mask c k ≠ some (.error .shape) := by
  intro h
  obtain ⟨e, _, _, hf⟩ := deliver_error_form h
  rcases hf with hf | ⟨act, hw⟩ | ⟨ws, hp⟩
  · cases hf
  · exact winners_ne_shape (c := c.pop k e) hs hw
  · exact phase2_ne_shape (c := c.pop k e) hs ws c.machines hs hp

/-- The initial configuration under every mask has the machines of `sys.init`. -/
theorem initCfg_machines (sys : Sys) (mask : List Bool) : (sys.initCfg mask).machines = sys.init.machines :=
  rfl

/-- **`shape` is unreachable from a shaped initial configuration**: no step from a reachable
configuration fails with `shape`. -/
theorem shape_unreachable (sys : Sys) (h : sys.init.Shaped sys) {m : List Bool} {c : Cfg}
    (hr : (Sys.lts sys).Reach (.run m c)) (l : Label) : deliver sys m c l ≠ some (.error .shape) := by
  intro hd
  unfold deliver at hd
  split at hd
  · split at hd
    · cases hd
    · exact deliver_ne_shape (sys := sys.resolve l.draws) (shaped_invariant sys h _ hr) _ hd
  · cases hd

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
        rw [ATy.holds_eq] at hr
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

theorem BOp.apply_concat_fits {x y v : Val} (h : BOp.apply .concat x y = .ok v) : v.fits .str = true := by
  cases x <;> cases y <;> simp only [BOp.apply] at h
  all_goals first
    | (cases h; rfl)
    | cases h

theorem Val.str_of_fits {v : Val} (h : v.fits .str = true) : ∃ s, v = .str s := by
  cases v <;> simp_all [Val.fits]

theorem BOp.apply_bool_fits {op : BOp} (hop : ∀ o σ, op ≠ .arith o σ) (hc : op ≠ .concat) {x y v : Val}
    (h : BOp.apply op x y = .ok v) : v.fits .bool = true := by
  cases op
  · exact absurd rfl (hop _ _)
  case concat => exact absurd rfl hc
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

theorem countIn_le {S : Sig} {snap : List MState} {name : String} :
    (g : List (Fin S.machines)) → {k : Nat} → countIn S snap name g = .ok k → k ≤ g.length
  | [], k, h => by simp only [countIn, Except.ok.injEq] at h; subst h; exact Nat.le_refl _
  | m :: g, k, h => by
    simp only [countIn] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i k' hk
          have := countIn_le g hk
          simp only [Except.ok.injEq] at h
          subst h
          simp only [List.length_cons]
          split <;> omega

theorem AggOp.apply_fits {op : AggOp} {ns : List Int} {v : Val} (h : op.apply ns = .ok v) :
    v.fits Ty.num = true := by
  cases op <;> cases ns <;> simp only [AggOp.apply] at h <;>
    first | exact Val.check_fits h | cases h

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
  | .count g name, hty, h => by
    simp only [Ref.ty?, Option.some.injEq] at hty
    subst hty
    simp only [Ref.eval] at h
    split at h
    · rename_i k hk
      cases h
      have := countIn_le g hk
      simp only [Val.fits, Bool.and_eq_true, decide_eq_true_eq]
      omega
    · cases h
  | .agg op g, hty, h => by
    simp only [Ref.ty?] at hty
    split at hty
    · cases hty
      simp only [Ref.eval] at h
      split at h
      · exact AggOp.apply_fits h
      · cases h
    · cases hty
  | .absent _, _, h => by simp [Ref.eval] at h

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
           · exact BOp.apply_bool_fits (by intro o σ hc; cases hc) (by intro hc; cases hc) h
           all_goals cases h
         · cases hty)
      case concat =>
        split at hty
        · cases hty
          split at h
          · exact BOp.apply_concat_fits h
          all_goals cases h
        · cases hty
      all_goals
        split at hty
        · cases hty
          repeat' split at h
          all_goals first
            | (cases h; rfl)
            | cases h
        · cases hty
    · cases hty


/-! ### Times: below `2^53`, and no pending entry before the current time -/

/-- The times of a configuration are in order and bounded: the current time is below `2^53` and
no later than any pending entry's, and every pending entry's time is below `2^53`. -/
def Cfg.TimeOK (c : Cfg) : Prop :=
  c.time < timeLimit ∧ ∀ x ∈ c.pending, c.time ≤ x.time ∧ x.time < timeLimit

theorem mem_insertByTime {q : List Entry} {y x : Entry} : x ∈ insertByTime q y ↔ x = y ∨ x ∈ q := by
  rw [(insertByTime_perm q y).mem_iff]; simp

theorem mem_foldl_insertByTime {x : Entry} : (l q : List Entry) →
    x ∈ l.foldl insertByTime q → x ∈ q ∨ x ∈ l
  | [], q, h => Or.inl h
  | y :: ys, q, h => by
    rcases mem_foldl_insertByTime ys _ h with h | h
    · rcases mem_insertByTime.mp h with rfl | h
      · exact Or.inr List.mem_cons_self
      · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem later_ok {e cp : Entry} {i b : Nat} (h : later e i b = .ok cp) :
    e.time ≤ cp.time ∧ cp.time < timeLimit := by
  unfold later at h
  split at h
  · cases h
  · rename_i hl; cases h; exact ⟨Nat.le_add_right _ _, Nat.lt_of_not_le hl⟩

/-- The entries a transition emits are at the snapshot's time or later, and below `2^53`. -/
theorem runEffects_times {S : Sig} {me : Fin S.machines} {c : Cfg} {e : Entry} :
    (effs : List (Effect S me)) → (own : MState) → (r : MState × Out) →
    runEffects c e effs own = .ok r → ∀ x ∈ r.2.1, c.time ≤ x.time ∧ x.time < timeLimit
  | [], own, r, h => by simp only [runEffects] at h; cases h; simp
  | .set v rhs :: rest, own, r, h => by
    simp only [runEffects] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · exact runEffects_times rest _ r h
        · cases h
  | .emit ev after pl :: rest, own, r, h => by
    simp only [runEffects] at h
    split at h
    · cases h
    · rename_i hl
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i st outs tn hr
          cases h
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨Nat.le_add_right _ _, Nat.lt_of_not_le hl⟩
          · exact runEffects_times rest own (st, outs, tn) hr x hx
  | .timer n after ev pl :: rest, own, r, h => by
    simp only [runEffects] at h
    split at h
    · cases h
    · rename_i hl
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i st outs tn hr
          cases h
          intro x hx
          have ih := runEffects_times rest own (st, outs, tn) hr
          split at hx
          · exact ih x hx
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact ⟨Nat.le_add_right _ _, Nat.lt_of_not_le hl⟩
            · exact ih x hx
  | .cancel n :: rest, own, r, h => by
    simp only [runEffects] at h
    split at h
    · cases h
    · rename_i st outs tn hr
      cases h
      exact runEffects_times rest own (st, outs, tn) hr
  | .reply ev after pl :: rest, own, r, h => by
    simp only [runEffects] at h
    split at h
    · cases h
    · rename_i hl
      split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · rename_i st outs tn hr
            cases h
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact ⟨Nat.le_add_right _ _, Nat.lt_of_not_le hl⟩
            · exact runEffects_times rest own (st, outs, tn) hr x hx

theorem phase2_times {sys : Sys} {c : Cfg} {e : Entry} :
    (ws : List (Winner sys)) → (ms : List MState) → (r : List MState × Emitted) →
    phase2 sys c e ws ms = .ok r → ∀ b ∈ r.2, ∀ x ∈ b.2.1, c.time ≤ x.time ∧ x.time < timeLimit
  | [], ms, r, h => by simp only [phase2] at h; cases h; simp
  | w :: ws, ms, r, h => by
    simp only [phase2] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i st out hf
        split at h
        · cases h
        · rename_i ms' outs hr
          cases h
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · simp only [fireOne] at hf
            split at hf
            · cases hf
            · rename_i st' out' hre
              cases hf
              exact runEffects_times _ _ (st', out) hre
          · exact phase2_times ws _ (ms', outs) hr b hb

theorem blockOf_mem {x : Entry} {m : Nat} : (bs : Emitted) → x ∈ blockOf m bs → ∃ b ∈ bs, x ∈ b.2.1
  | [], h => by simp [blockOf] at h
  | (i, out) :: bs, h => by
    simp only [blockOf] at h
    split at h
    · exact ⟨(i, out), List.mem_cons_self, h⟩
    · obtain ⟨b, hb, hx⟩ := blockOf_mem bs h
      exact ⟨b, List.mem_cons_of_mem _ hb, hx⟩

theorem inMachineOrder_mem {x : Entry} {n : Nat} {bs : Emitted} (h : x ∈ inMachineOrder n bs) :
    ∃ b ∈ bs, x ∈ b.2.1 := by
  simp only [inMachineOrder, List.mem_flatMap] at h
  obtain ⟨m, _, hx⟩ := h
  exact blockOf_mem bs hx

/-- A successful delivery keeps the times in order and bounded. -/
theorem deliver_timeOK {sys : Sys} {mask : List Bool} {c c' : Cfg} {k : Nat} (ht : c.TimeOK)
    (h : deliverAt sys mask c k = some (.ok c')) : c'.TimeOK := by
  obtain ⟨e, he, hmin, hf⟩ := deliver_ok_form h
  have hek : e ∈ c.pending := List.mem_of_getElem? he
  have hel : e.time < timeLimit := (ht.2 e hek).2
  -- every entry left of the old queue is at `e.time` or later
  have hold : ∀ x ∈ (c.pop k e).pending, e.time ≤ x.time ∧ x.time < timeLimit := by
    intro x hx
    have hx' : x ∈ c.pending := List.mem_of_mem_eraseIdx hx
    exact ⟨hmin x hx', (ht.2 x hx').2⟩
  have henq : ∀ (d : Cfg) (cp : Entry), d.time = e.time →
      (∀ x ∈ d.pending, e.time ≤ x.time ∧ x.time < timeLimit) →
      e.time ≤ cp.time ∧ cp.time < timeLimit → (d.enq cp).TimeOK := by
    intro d cp hd hp hcp
    refine ⟨by simp only [Cfg.enq]; rw [hd]; exact hel, fun x hx => ?_⟩
    simp only [Cfg.enq] at hx ⊢
    rw [hd]
    rcases mem_insertByTime.mp hx with rfl | hx
    · exact hcp
    · exact hp x hx
  have hcommit : ∀ ws ms bs, phase2 sys (c.pop k e) e ws c.machines = .ok (ms, bs) →
      ∀ x ∈ ((c.pop k e).commit sys.sig.machines ms bs).pending, e.time ≤ x.time ∧ x.time < timeLimit := by
    intro ws ms bs hp x hx
    simp only [Cfg.commit] at hx
    rcases mem_foldl_insertByTime _ _ hx with hx | hx
    · exact hold x (List.mem_filter.mp hx).1
    · obtain ⟨b, hb, hxb⟩ := inMachineOrder_mem hx
      exact phase2_times ws c.machines (ms, bs) hp b hb x hxb
  rcases hf with rfl | ⟨i, b, cp, hcp, rfl⟩ | ⟨ws, ms, bs, hp, rfl | ⟨i, b, cp, hcp, rfl⟩⟩
  · exact ⟨hel, hold⟩
  · exact henq _ cp rfl hold (later_ok hcp)
  · exact ⟨hel, hcommit ws ms bs hp⟩
  · exact henq _ cp rfl (hcommit ws ms bs hp) (later_ok hcp)

/-! ### The queue stays sorted by time -/

/-- The pending entries are sorted by time. -/
def Cfg.Sorted (c : Cfg) : Prop := c.pending.Pairwise (fun a b => a.time ≤ b.time)

theorem insertByTime_sorted {q : List Entry} (hq : q.Pairwise (fun a b => a.time ≤ b.time))
    (y : Entry) : (insertByTime q y).Pairwise (fun a b => a.time ≤ b.time) := by
  induction q with
  | nil => exact List.pairwise_singleton _ _
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := List.pairwise_cons.mp hq
    simp only [insertByTime]
    split
    · rename_i hlt
      refine List.pairwise_cons.mpr ⟨fun z hz => ?_, hq⟩
      rcases List.mem_cons.mp hz with rfl | hz
      · exact Nat.le_of_lt hlt
      · exact Nat.le_trans (Nat.le_of_lt hlt) (hx z hz)
    · rename_i hlt
      refine List.pairwise_cons.mpr ⟨fun z hz => ?_, ih hxs⟩
      rcases mem_insertByTime.mp hz with rfl | hz
      · exact Nat.le_of_not_lt hlt
      · exact hx z hz

theorem foldl_insertByTime_sorted : (l : List Entry) → {q : List Entry} →
    q.Pairwise (fun a b => a.time ≤ b.time) →
    (l.foldl insertByTime q).Pairwise (fun a b => a.time ≤ b.time)
  | [], _, hq => hq
  | y :: ys, _, hq => foldl_insertByTime_sorted ys (insertByTime_sorted hq y)

/-- A successful delivery keeps the queue sorted. -/
theorem deliver_sorted {sys : Sys} {mask : List Bool} {c c' : Cfg} {k : Nat} (hs : c.Sorted)
    (h : deliverAt sys mask c k = some (.ok c')) : c'.Sorted := by
  obtain ⟨e, _, _, hf⟩ := deliver_ok_form h
  have hp : (c.pop k e).pending.Pairwise (fun a b => a.time ≤ b.time) :=
    hs.sublist (List.eraseIdx_sublist _ _)
  have hc : ∀ ms bs, ((c.pop k e).commit sys.sig.machines ms bs).pending.Pairwise
      (fun a b => a.time ≤ b.time) := fun ms bs =>
    foldl_insertByTime_sorted _ (hp.sublist List.filter_sublist)
  rcases hf with rfl | ⟨i, b, cp, _, rfl⟩ | ⟨ws, ms, bs, _, rfl | ⟨i, b, cp, _, rfl⟩⟩
  · exact hp
  · exact insertByTime_sorted hp cp
  · exact hc ms bs
  · exact insertByTime_sorted (hc ms bs) cp

theorem initCfg_pending (sys : Sys) (mask : List Bool) :
    (sys.initCfg mask).pending = (sys.active mask).foldl injectStep sys.init.pending := rfl

theorem foldl_injectStep_sorted : (l : List (Nat × Fault)) → {q : List Entry} →
    q.Pairwise (fun a b => a.time ≤ b.time) →
    (l.foldl injectStep q).Pairwise (fun a b => a.time ≤ b.time)
  | [], _, hq => hq
  | p :: ps, _, hq => foldl_injectStep_sorted ps (by
      unfold injectStep; split
      · exact insertByTime_sorted hq _
      · exact hq)

theorem mem_foldl_injectStep {x : Entry} : (l : List (Nat × Fault)) → (q : List Entry) →
    x ∈ l.foldl injectStep q → x ∈ q ∨ ∃ p ∈ l, x.time = p.2.at_
  | [], q, h => Or.inl h
  | p :: ps, q, h => by
    rcases mem_foldl_injectStep ps _ h with h | ⟨p', hp', ht⟩
    · unfold injectStep at h
      split at h
      · rcases mem_insertByTime.mp h with rfl | h
        · exact Or.inr ⟨p, List.mem_cons_self, rfl⟩
        · exact Or.inl h
      · exact Or.inl h
    · exact Or.inr ⟨p', List.mem_cons_of_mem _ hp', ht⟩

/-- Inserting the injected entries keeps a sorted queue sorted. -/
theorem initCfg_sorted (sys : Sys) (mask : List Bool) (h : sys.init.Sorted) :
    (sys.initCfg mask).Sorted := by
  simp only [Cfg.Sorted, initCfg_pending]
  exact foldl_injectStep_sorted _ h

/-- **The queue is sorted in every reachable state** when it is sorted initially. -/
theorem sorted_invariant_of_init (sys : Sys) (h : sys.init.Sorted) :
    (Sys.lts sys).Invariant (fun s => s.cfg.Sorted) := by
  refine LTS.safe_of_inductive (I := fun s => s.cfg.Sorted) ⟨?_, ?_⟩ (fun _ h => h)
  · intro s hs
    obtain ⟨mask, _, rfl⟩ := hs
    exact initCfg_sorted sys mask h
  · intro s l t hs hst
    cases s with
    | err m c => exact absurd hst id
    | run m c =>
      obtain ⟨k, hst'⟩ := step_deliverAt (show Step sys m c l t from hst)
      cases hd : deliverAt (sys.resolve l.draws) m c k with
      | none => rw [hd] at hst'; cases hst'
      | some r =>
        rw [hd] at hst'
        cases r with
        | error err => cases hst'; exact hs
        | ok c' => cases hst'; exact deliver_sorted hs hd

/-- The initial time is 0, and every initial pending entry and injected entry is below `2^53`. -/
def Sys.TimesOK (sys : Sys) : Prop :=
  sys.init.time = 0 ∧ (∀ x ∈ sys.init.pending, x.time < timeLimit) ∧ ∀ f ∈ sys.faults, f.at_ < timeLimit

theorem initCfg_timeOK (sys : Sys) (mask : List Bool) (h : sys.TimesOK) : (sys.initCfg mask).TimeOK := by
  obtain ⟨h0, hp, hf⟩ := h
  refine ⟨by simp only [Sys.initCfg]; rw [h0]; decide, fun x hx => ?_⟩
  rw [initCfg_pending] at hx
  simp only [Sys.initCfg]
  rw [h0]
  refine ⟨Nat.zero_le _, ?_⟩
  rcases mem_foldl_injectStep _ _ hx with hx | ⟨p, hpm, ht⟩
  · exact hp x hx
  · rw [ht]
    have hmem : p.2 ∈ sys.faults := (List.of_mem_zip (List.mem_filter.mp hpm).1).2
    exact hf _ hmem

/-- **Times stay in order and below `2^53`** in every reachable state. -/
theorem time_invariant (sys : Sys) (h : sys.TimesOK) :
    (Sys.lts sys).Invariant (fun s => s.cfg.TimeOK) := by
  refine LTS.safe_of_inductive (I := fun s => s.cfg.TimeOK) ⟨?_, ?_⟩ (fun _ h => h)
  · intro s hs
    obtain ⟨mask, _, rfl⟩ := hs
    exact initCfg_timeOK sys mask h
  · intro s l t hs hst
    cases s with
    | err m c => exact absurd hst id
    | run m c =>
      obtain ⟨k, hst'⟩ := step_deliverAt (show Step sys m c l t from hst)
      cases hd : deliverAt (sys.resolve l.draws) m c k with
      | none => rw [hd] at hst'; cases hst'
      | some r =>
        rw [hd] at hst'
        cases r with
        | error err => cases hst'; exact hs
        | ok c' => cases hst'; exact deliver_timeOK hs hd

/-! ### Well-formedness: no step of a well-formed system fails with `sort` -/

/-- A well-typed effect: the right-hand side of a `set` has the sort of the variable (ranges
aside: a value out of the variable's range is `overflow`, not `sort`); every payload expression
has a sort. -/
def Effect.wt {S : Sig} {me : Fin S.machines} : Effect S me → Bool
  | .set v rhs => match rhs.ty? with
    | some υ => υ.comparable ((S.vars me).get v)
    | none => false
  | .emit _ _ pl => pl.all (fun p => p.2.ty?.isSome)
  | .timer _ _ _ pl => pl.all (fun p => p.2.ty?.isSome)
  | .cancel _ => true
  | .reply _ _ pl => pl.all (fun p => p.2.ty?.isSome)

/-- A well-typed transition: a Boolean guard and well-typed effects. -/
def Trans.wt {S : Sig} {me : Fin S.machines} (t : Trans S me) : Bool :=
  t.guard.ty? == some .bool && t.effects.all Effect.wt

def varsFitb : List Ty → List Val → Bool
  | [], [] => true
  | τ :: ts, v :: vs => v.fits τ && varsFitb ts vs
  | _, _ => false

def Sig.shapedb (S : Sig) (ms : List MState) : Bool :=
  decide (ms.length = S.machines) &&
    (finList S.machines).all (fun m => match ms[m.val]? with
      | some x => decide (x.ctrl < (S.states m).length) && varsFitb (S.vars m) x.vars
      | none => false)

/-- The well-formedness check of a system, decidable: the initial configuration has the shape of
the signature, starts at time 0 with a time-sorted queue of entries below `2^53`, injected entries
are below `2^53`, and every transition is well-typed. -/
def Sys.wfCore (sys : Sys) : Bool :=
  sys.sig.shapedb sys.init.machines && sys.init.time == 0 &&
  sys.init.pending.all (fun x => decide (x.time < timeLimit)) &&
  sys.faults.all (fun f => decide (f.at_ < timeLimit)) &&
  decide (sys.init.pending.Pairwise (fun a b => a.time ≤ b.time)) &&
  (finList sys.sig.machines).all (fun m => (sys.trans m).all Trans.wt)

/-- The well-formedness check: the core check and every sampled distribution has a value to draw
(an empty choice, `uniform` with `hi < lo` and an empty table are refused). -/
def Sys.wf (sys : Sys) : Bool := sys.wfCore && sys.dists.all Dist.wf

/-- A well-formed system (`Sys.wf` holds). -/
def Sys.WF (sys : Sys) : Prop := sys.wf = true

theorem WF.core {sys : Sys} (h : sys.WF) : sys.wfCore = true := by
  simp only [Sys.WF, Sys.wf, Bool.and_eq_true] at h; exact h.1

theorem WF.dists {sys : Sys} (h : sys.WF) : ∀ d ∈ sys.dists, d.wf = true := by
  simp only [Sys.WF, Sys.wf, Bool.and_eq_true, List.all_eq_true] at h; exact h.2

instance (sys : Sys) : Decidable sys.WF := inferInstanceAs (Decidable (sys.wf = true))

theorem mem_finList : (n : Nat) → (m : Fin n) → m ∈ finList n
  | n + 1, m => by
    simp only [finList, List.mem_cons, List.mem_map]
    cases m using Fin.cases with
    | zero => exact Or.inl rfl
    | succ j => exact Or.inr ⟨j, mem_finList n j, rfl⟩

theorem varsFitb_sound : (ts : List Ty) → (vs : List Val) → varsFitb ts vs = true → VarsFit ts vs
  | [], [], _ => ⟨rfl, fun i h => absurd h (Nat.not_lt_zero _)⟩
  | τ :: ts, v :: vs, h => by
    simp only [varsFitb, Bool.and_eq_true] at h
    obtain ⟨hl, hi⟩ := varsFitb_sound ts vs h.2
    refine ⟨by simp [hl], fun i h1 h2 => ?_⟩
    cases i with
    | zero => exact h.1
    | succ i => exact hi i (by simpa using h1) (by simpa using h2)
  | [], _ :: _, h => by simp [varsFitb] at h
  | _ :: _, [], h => by simp [varsFitb] at h

theorem shapedb_sound {S : Sig} {ms : List MState} (h : S.shapedb ms = true) : S.Shaped ms := by
  simp only [Sig.shapedb, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  refine ⟨h.1, fun m x hx => ?_⟩
  have := h.2 m (mem_finList _ m)
  rw [hx] at this
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1, varsFitb_sound _ _ this.2⟩

theorem WF.shaped {sys : Sys} (h : sys.WF) : sys.init.Shaped sys := by
  replace h := WF.core h
  simp only [Sys.wfCore, Bool.and_eq_true] at h
  exact shapedb_sound h.1.1.1.1.1

theorem WF.timesOK {sys : Sys} (h : sys.WF) : sys.TimesOK := by
  replace h := WF.core h
  simp only [Sys.wfCore, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.2, h.1.1.1.2, h.1.1.2⟩

theorem WF.sorted {sys : Sys} (h : sys.WF) : sys.init.Sorted := by
  replace h := WF.core h
  simp only [Sys.wfCore, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

theorem Effect.wt_withAfter {S : Sig} {me : Fin S.machines} (a : Nat) (e : Effect S me) :
    (e.withAfter a).wt = e.wt := by
  cases e <;> rfl

theorem mapIdx_all {α β : Type} (f : Nat → α → β) (p : β → Bool) (q : α → Bool)
    (h : ∀ i x, p (f i x) = q x) (l : List α) : (l.mapIdx f).all p = l.all q := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, List.mem_mapIdx]
  constructor
  · intro H x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have := H _ ⟨i, hi, rfl⟩
    rwa [h] at this
  · rintro H b ⟨i, hi, rfl⟩
    rw [h]
    exact H _ (List.getElem_mem hi)

/-- Substituting draws keeps a system well-formed: it changes only the delays of effects. -/
theorem resolve_wf {sys : Sys} (h : sys.WF) (ds : List Nat) : (sys.resolve ds).WF := by
  have key : (sys.resolve ds).wfCore = sys.wfCore := by
    unfold Sys.wfCore
    simp only [resolve_sig, resolve_init]
    congr 1
    congr 1
    funext m
    simp only [Sys.resolve]
    apply mapIdx_all
    intro i t
    simp only [Trans.wt]
    congr 1
    apply mapIdx_all
    intro j eff
    cases sys.siteDraw ds m.val i j with
    | none => rfl
    | some a => exact Effect.wt_withAfter a eff
  have hd : (sys.resolve ds).dists = sys.dists := rfl
  have h1 := WF.core h
  have h2 := WF.dists h
  unfold Sys.WF Sys.wf
  rw [key, h1, hd]
  simpa [List.all_eq_true] using h2

/-- **The executable delivery is proved against the relation** (`deliver_eq_step`, for a
well-formed system). -/
theorem deliver_iff_step {sys : Sys} (_hwf : sys.WF) {mask : List Bool} {c : Cfg} {l : Label}
    {t : State} :
    (deliver sys mask c l).map (outcome mask c) = some t ↔ Step sys mask c l t :=
  deliver_eq_step

/-- **The queue is sorted in every reachable state** of a well-formed system. -/
theorem sorted_invariant (sys : Sys) (h : sys.WF) :
    (Sys.lts sys).Invariant (fun s => s.cfg.Sorted) :=
  sorted_invariant_of_init sys (WF.sorted h)

theorem WF.trans {sys : Sys} (h : sys.WF) (m : Fin sys.sig.machines) :
    ∀ t ∈ sys.trans m, t.wt = true := by
  replace h := WF.core h
  simp only [Sys.wfCore, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 m (mem_finList _ m)

/-! #### Well-typed expressions do not fail with `sort` -/

theorem Val.int_of_fits {v : Val} {τ : Ty} (h : v.fits τ = true) (hi : τ.isInt = true) :
    ∃ n, v = .int n := by
  cases v <;> cases τ <;> simp_all [Val.fits, Ty.isInt]

theorem Val.bool_of_fits {v : Val} (h : v.fits .bool = true) : ∃ b, v = .bool b := by
  cases v <;> simp_all [Val.fits]

theorem Val.sameSort_of_fits {v w : Val} {τ υ : Ty} (hv : v.fits τ = true) (hw : w.fits υ = true)
    (hc : τ.comparable υ = true) : Val.sameSort v w.ty = true := by
  cases v <;> cases w <;> cases τ <;> cases υ <;> simp_all [Val.fits, Ty.comparable, Val.sameSort, Val.ty]

theorem checked_ne_sort (τ : ATy) (a b r : Int) : checked τ a b r ≠ .error .sort := by
  unfold checked
  split
  · intro h; cases h
  · split
    · intro h; cases h
    · split <;> intro h <;> cases h

theorem AOp.apply_ne_sort (op : AOp) (τ : ATy) (a b : Int) : op.apply τ a b ≠ .error .sort := by
  cases op <;> simp only [AOp.apply]
  all_goals
    repeat' split
    all_goals first
      | exact checked_ne_sort _ _ _ _
      | (intro h; cases h)

theorem at?_ne_sort {β : Type} {l : List β} {i : Nat} (h : at? l i = .error .sort) : False := by
  unfold at? at h; split at h <;> cases h

theorem countIn_ne_sort {S : Sig} {snap : List MState} {name : String} :
    (g : List (Fin S.machines)) → countIn S snap name g ≠ .error .sort
  | [] => by simp [countIn]
  | m :: g => by
    simp only [countIn]
    cases h1 : at? snap m.val with
    | error e => intro h; injection h with h; subst h; exact at?_ne_sort h1
    | ok x =>
      simp only []
      cases h2 : at? (S.states m) x.ctrl with
      | error e => intro h; injection h with h; subst h; exact at?_ne_sort h2
      | ok nm =>
        simp only []
        cases h3 : countIn S snap name g with
        | error e => intro h; injection h with h; subst h; exact countIn_ne_sort g h3
        | ok k => intro h; cases h

theorem intsIn_ok {S : Sig} {snap : List MState} (hs : S.Shaped snap) :
    (g : List ((m : Fin S.machines) × Fin (S.vars m).length)) →
    g.all (fun p => ((S.vars p.1).get p.2).isInt) = true →
      ∃ ns, intsIn snap g = .ok ns ∧ ns.length = g.length
  | [], _ => ⟨[], rfl, rfl⟩
  | p :: g, hg => by
    simp only [List.all_cons, Bool.and_eq_true] at hg
    obtain ⟨x, hx, hxs⟩ := hs.get p.1
    have hl : p.1.val < snap.length := by rw [hs.1]; exact p.1.isLt
    have hxe : snap[p.1.val] = x := by
      rw [List.getElem?_eq_getElem hl] at hx; exact Option.some.inj hx
    have hv : p.2.val < x.vars.length := by rw [hxs.2.1]; exact p.2.isLt
    have hfit := hxs.2.2 p.2.val hv p.2.isLt
    rw [← List.get_eq_getElem (l := S.vars p.1) (i := p.2)] at hfit
    obtain ⟨n, hn⟩ := Val.int_of_fits hfit hg.1
    obtain ⟨ns, hns, hlen⟩ := intsIn_ok hs g hg.2
    refine ⟨n :: ns, ?_, by simp [hlen]⟩
    simp only [intsIn, at?_of_lt hl, hxe, at?_of_lt hv, hn, hns]

theorem Val.check_int_ne_sort (lo hi n : Int) : Val.check (.int lo hi) (.int n) ≠ .error .sort := by
  simp only [Val.check, Val.sameSort]; split <;> intro h <;> cases h

theorem Ref.eval_ne_sort {S : Sig} {me : Fin S.machines} {cx : Ctx} (hcx : cx.Typed S me) :
    (r : Ref S me) → {τ : Ty} → r.ty? = some τ → r.eval cx ≠ .error .sort
  | .count g name, _, _ => by
    simp only [Ref.eval]
    cases h : countIn S cx.snap name g with
    | ok k => intro h'; cases h'
    | error e => simp only []; intro h'; injection h' with h'; subst h'; exact countIn_ne_sort g h
  | .agg op g, _, hty => by
    simp only [Ref.ty?] at hty
    split at hty
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
        List.isEmpty_eq_false_iff] at hc
      obtain ⟨ns, hns, hlen⟩ := intsIn_ok hcx.1 g hc.1
      simp only [Ref.eval, hns]
      cases op <;> cases ns <;> simp only [AggOp.apply] <;>
        first
          | exact Val.check_int_ne_sort _ _ _
          | (exfalso; rcases hc.2 with h | h
             · cases h
             · apply h; exact List.length_eq_zero_iff.mp (by simpa using hlen.symm))
    · cases hty
  | .own v, _, _ => by
    simp only [Ref.eval, at?]; split <;> intro h <;> cases h
  | .other m v, _, _ => by
    simp only [Ref.eval]
    cases h1 : at? cx.snap m.val with
    | error e => intro h; injection h with h; subst h; exact at?_ne_sort h1
    | ok ms => simp only []; intro h; exact at?_ne_sort h
  | .state m, _, _ => by
    simp only [Ref.eval]
    cases h1 : at? cx.snap m.val with
    | error e => intro h; injection h with h; subst h; exact at?_ne_sort h1
    | ok ms =>
      simp only []
      cases h2 : at? (S.states m) ms.ctrl with
      | error e => intro h; injection h with h; subst h; exact at?_ne_sort h2
      | ok nm => intro h; cases h
  | .field f τ, _, _ => by
    simp only [Ref.eval]
    repeat' split
    all_goals intro h; cases h
  | .time, _, _ => by simp [Ref.eval]
  | .absent _, _, _ => by simp [Ref.eval]

theorem ne_sort_of {α β : Type} {x : Except Err α} {err : Err} (hx : x ≠ .error .sort)
    (h : x = .error err) : (Except.error err : Except Err β) ≠ .error .sort := by
  intro h'; injection h' with h'; subst h'; exact hx h

/-- **A well-typed expression does not fail with `sort`** in a typed context. -/
theorem Expr.eval_ne_sort {S : Sig} {me : Fin S.machines} {cx : Ctx} (hcx : cx.Typed S me) :
    (x : Expr S me) → {τ : Ty} → x.ty? = some τ → x.eval cx ≠ .error .sort
  | .val w, τ, hty => by simp [Expr.eval]
  | .ref r, τ, hty => by simp only [Expr.eval]; exact Ref.eval_ne_sort hcx r hty
  | .un (.neg σ) a, τ, hty => by
    simp only [Expr.ty?] at hty
    split at hty
    · rename_i υ hυ
      split at hty
      · rename_i hi
        simp only [Expr.eval]
        split
        · rename_i v hv
          obtain ⟨n, rfl⟩ := Val.int_of_fits (Expr.eval_fits hcx a hυ hv) hi
          exact checked_ne_sort _ _ _ _
        · rename_i err hr; exact ne_sort_of (Expr.eval_ne_sort hcx a hυ) hr
      · cases hty
    · cases hty
  | .un .not a, τ, hty => by
    simp only [Expr.ty?] at hty
    split at hty
    · rename_i hυ
      simp only [Expr.eval]
      split
      · rename_i v hv
        obtain ⟨b, rfl⟩ := Val.bool_of_fits (Expr.eval_fits hcx a hυ hv)
        intro h; cases h
      · rename_i err hr; exact ne_sort_of (Expr.eval_ne_sort hcx a hυ) hr
    · cases hty
  | .bin op a b, τ, hty => by
    simp only [Expr.ty?] at hty
    split at hty
    · rename_i τa τb ha hb
      have iha := Expr.eval_ne_sort hcx a ha
      have ihb := Expr.eval_ne_sort hcx b hb
      have fa := fun {v} (hv : a.eval cx = .ok v) => Expr.eval_fits hcx a ha hv
      have fb := fun {v} (hv : b.eval cx = .ok v) => Expr.eval_fits hcx b hb hv
      cases op <;> simp only [BOp.ty?] at hty <;> simp only [Expr.eval]
      -- arithmetic, comparisons: both operands integers, or of comparable sorts
      iterate 5
        (split at hty
         · rename_i hc
           split
           · rename_i x y hx hy
             first
               | (simp only [Bool.and_eq_true] at hc
                  obtain ⟨n, rfl⟩ := Val.int_of_fits (fa hx) hc.1
                  obtain ⟨m, rfl⟩ := Val.int_of_fits (fb hy) hc.2
                  simp only [BOp.apply]
                  first
                    | exact AOp.apply_ne_sort _ _ _ _
                    | (intro h; cases h))
               | (have hs := Val.sameSort_of_fits (fa hx) (fb hy) hc
                  simp only [BOp.apply, hs, ↓reduceIte]
                  intro h; cases h)
           all_goals (intro h; injection h with h; subst h; first | exact iha ‹_› | exact ihb ‹_›)
         · cases hty)
      case concat =>
        split at hty
        · rename_i hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          split
          · rename_i x y hx hy
            obtain ⟨s1, rfl⟩ := Val.str_of_fits (fa hx)
            obtain ⟨s2, rfl⟩ := Val.str_of_fits (fb hy)
            simp only [BOp.apply]; intro h; cases h
          all_goals (intro h; injection h with h; subst h; first | exact iha ‹_› | exact ihb ‹_›)
        · cases hty
      -- `and`, `or`, `imp`: both operands Booleans
      all_goals
        split at hty
        · rename_i hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          repeat' split
          all_goals first
            | (intro h; injection h with h; subst h; first | exact iha ‹_› | exact ihb ‹_›)
            | (intro h; cases h; rename_i hne hv; obtain ⟨q, rfl⟩ := Val.bool_of_fits (fb hv); exact hne q rfl)
            | (intro h; cases h; rename_i hf ht hv; obtain ⟨q, rfl⟩ := Val.bool_of_fits (fa hv); cases q <;> simp_all)
            | (intro h; cases h)
        · cases hty
    · cases hty


/-! #### Well-formed systems do not fail with `sort` -/

theorem Val.check_ne_sort {τ υ : Ty} {v : Val} (hv : v.fits υ = true) (hc : υ.comparable τ = true) :
    Val.check τ v ≠ .error .sort := by
  unfold Val.check
  split
  · intro h; cases h
  · split
    · intro h; cases h
    · rename_i hs
      exfalso; apply hs
      cases v <;> cases τ <;> cases υ <;> simp_all [Val.fits, Ty.comparable, Val.sameSort]

theorem evalPayload_ne_sort {S : Sig} {me : Fin S.machines} {cx : Ctx} (hcx : cx.Typed S me) :
    (pl : List (Nat × Expr S me)) → pl.all (fun p => p.2.ty?.isSome) = true →
    evalPayload cx pl ≠ .error .sort
  | [], _ => by simp [evalPayload]
  | (f, x) :: rest, h => by
    simp only [List.all_cons, Bool.and_eq_true, Option.isSome_iff_exists] at h
    obtain ⟨⟨τ, hτ⟩, hrest⟩ := h
    simp only [evalPayload]
    split
    · rename_i err hr; exact ne_sort_of (Expr.eval_ne_sort hcx x hτ) hr
    · split
      · rename_i err hr; exact ne_sort_of (evalPayload_ne_sort hcx rest hrest) hr
      · intro h; cases h

theorem maxSafe_of_lt {t : Nat} (h : t < timeLimit) : (t : Int) ≤ maxSafe := by
  simp only [timeLimit] at h; simp only [maxSafe]; omega

theorem runEffects_ne_sort {S : Sig} {me : Fin S.machines} {c : Cfg} {e : Entry}
    (hsnap : S.Shaped c.machines) (ht : (c.time : Int) ≤ maxSafe) :
    (effs : List (Effect S me)) → (∀ f ∈ effs, f.wt = true) → (own : MState) →
    VarsFit (S.vars me) own.vars → runEffects c e effs own ≠ .error .sort
  | [], _, own, _ => by simp [runEffects]
  | .set v rhs :: rest, hw, own, hf => by
    have hwt := hw _ List.mem_cons_self
    have hrest := fun f hf => hw f (List.mem_cons_of_mem _ hf)
    simp only [Effect.wt] at hwt
    split at hwt
    · rename_i υ hυ
      have hcx : (ctxOf c e own).Typed S me := ⟨hsnap, hf, ht⟩
      simp only [runEffects]
      split
      · rename_i err hr; exact ne_sort_of (Expr.eval_ne_sort hcx rhs hυ) hr
      · rename_i x hx
        split
        · rename_i err hr
          exact ne_sort_of (Val.check_ne_sort (Expr.eval_fits hcx rhs hυ hx) hwt) hr
        · rename_i x' hx'
          split
          · have hfx := Val.check_fits hx'
            rw [List.get_eq_getElem] at hfx
            exact runEffects_ne_sort hsnap ht rest hrest _ (hf.set v.isLt hfx)
          · intro h; cases h
    · cases hwt
  | .emit ev after pl :: rest, hw, own, hf => by
    have hwt := hw _ List.mem_cons_self
    have hrest := fun f hf => hw f (List.mem_cons_of_mem _ hf)
    simp only [Effect.wt] at hwt
    have hcx : (ctxOf c e own).Typed S me := ⟨hsnap, hf, ht⟩
    simp only [runEffects]
    split
    · intro h; cases h
    · split
      · rename_i err hr; exact ne_sort_of (evalPayload_ne_sort hcx pl hwt) hr
      · split
        · rename_i err hr; exact ne_sort_of (runEffects_ne_sort hsnap ht rest hrest own hf) hr
        · intro h; cases h
  | .timer n after ev pl :: rest, hw, own, hf => by
    have hwt := hw _ List.mem_cons_self
    have hrest := fun f hf => hw f (List.mem_cons_of_mem _ hf)
    simp only [Effect.wt] at hwt
    have hcx : (ctxOf c e own).Typed S me := ⟨hsnap, hf, ht⟩
    simp only [runEffects]
    split
    · intro h; cases h
    · split
      · rename_i err hr; exact ne_sort_of (evalPayload_ne_sort hcx pl hwt) hr
      · split
        · rename_i err hr; exact ne_sort_of (runEffects_ne_sort hsnap ht rest hrest own hf) hr
        · intro h; cases h
  | .cancel n :: rest, hw, own, hf => by
    have hrest := fun f hf => hw f (List.mem_cons_of_mem _ hf)
    simp only [runEffects]
    split
    · rename_i err hr; exact ne_sort_of (runEffects_ne_sort hsnap ht rest hrest own hf) hr
    · intro h; cases h
  | .reply ev after pl :: rest, hw, own, hf => by
    have hwt := hw _ List.mem_cons_self
    have hrest := fun f hf => hw f (List.mem_cons_of_mem _ hf)
    simp only [Effect.wt] at hwt
    have hcx : (ctxOf c e own).Typed S me := ⟨hsnap, hf, ht⟩
    simp only [runEffects]
    split
    · intro h; cases h
    · split
      · rename_i err hr; exact ne_sort_of (evalPayload_ne_sort hcx pl hwt) hr
      · split
        · intro h; cases h
        · split
          · rename_i err hr; exact ne_sort_of (runEffects_ne_sort hsnap ht rest hrest own hf) hr
          · intro h; cases h

/-- Every transition of the system is well-typed. -/
def Sys.TransWT (sys : Sys) : Prop := ∀ m, ∀ t ∈ sys.trans m, Trans.wt t = true

theorem phase2_ne_sort {sys : Sys} {c : Cfg} {e : Entry} (hwt : sys.TransWT)
    (hsnap : sys.sig.Shaped c.machines) (ht : (c.time : Int) ≤ maxSafe) :
    (ws : List (Winner sys)) → (ms : List MState) → sys.sig.Shaped ms →
    phase2 sys c e ws ms ≠ .error .sort
  | [], ms, _ => by simp [phase2]
  | w :: ws, ms, hs => by
    obtain ⟨own, ho, hown⟩ := hs.get w.mach
    have htw := hwt w.mach _ (List.get_mem _ w.idx)
    simp only [Trans.wt, Bool.and_eq_true, List.all_eq_true] at htw
    simp only [phase2, ho]
    split
    · rename_i err hr
      refine ne_sort_of ?_ hr
      simp only [fireOne]
      split
      · rename_i err' hr'; exact ne_sort_of (runEffects_ne_sort hsnap ht _ htw.2 own hown.2) hr'
      · intro h; cases h
    · rename_i st out hf
      split
      · rename_i err hr
        exact ne_sort_of (phase2_ne_sort hwt hsnap ht ws _ (hs.set (fireOne_shaped (r := (st, out)) hown hf))) hr
      · intro h; cases h

theorem scan_ne_sort {sys : Sys} {act : List (Nat × Fault)} {c : Cfg} {e : Entry}
    {m : Fin sys.sig.machines} {own : MState} (hwt : sys.TransWT)
    (hcx : (ctxOf c e own).Typed sys.sig m) :
    (is : List (Fin (sys.trans m).length)) → scan sys act c e m own is ≠ .error .sort
  | [] => by simp [scan]
  | i :: is => by
    have ih := scan_ne_sort (act := act) hwt hcx is
    have htw := hwt m _ (List.get_mem _ i)
    simp only [Trans.wt, Bool.and_eq_true, beq_iff_eq] at htw
    simp only [scan]
    split
    · split
      · exact ih
      · split
        · split
          · exact ih
          · intro h; cases h
        · exact ih
        · rename_i v hne₁ hne₂ hv
          exfalso
          obtain ⟨b, rfl⟩ := Val.bool_of_fits (Expr.eval_fits hcx _ htw.1 hv)
          cases b
          · exact hne₂ rfl
          · exact hne₁ rfl
        · rename_i err hr; exact ne_sort_of (Expr.eval_ne_sort hcx _ htw.1) hr
    · exact ih

theorem winnersOf_ne_sort {sys : Sys} {act : List (Nat × Fault)} {c : Cfg} {e : Entry}
    (hwt : sys.TransWT) (hsnap : sys.sig.Shaped c.machines) (ht : (c.time : Int) ≤ maxSafe) :
    (ms : List (Fin sys.sig.machines)) → winnersOf sys act c e ms ≠ .error .sort
  | [] => by simp [winnersOf]
  | m :: ms => by
    obtain ⟨own, ho, hown⟩ := hsnap.get m
    have hl : m.val < c.machines.length := by rw [hsnap.1]; exact m.isLt
    have hoe : c.machines[m.val] = own := by
      rw [List.getElem?_eq_getElem hl] at ho; exact Option.some.inj ho
    have hcx : (ctxOf c e own).Typed sys.sig m := ⟨hsnap, hown.2, ht⟩
    simp only [winnersOf, choose, at?_of_lt hl, hoe]
    split
    · rename_i err hr
      split at hr
      · rename_i err' hr'; cases hr; exact ne_sort_of (scan_ne_sort hwt hcx _) hr'
      · cases hr
      · cases hr
    · split
      · rename_i err hr; exact ne_sort_of (winnersOf_ne_sort hwt hsnap ht ms) hr
      · intro h; cases h

theorem WF.transWT {sys : Sys} (h : sys.WF) : sys.TransWT := fun m => WF.trans h m

/-- **No step of a well-formed system fails with `sort`** from a shaped configuration whose
times are in order and below `2^53`. -/
theorem deliver_ne_sort {sys : Sys} (hwf : sys.WF) {mask : List Bool} {c : Cfg} (hs : c.Shaped sys)
    (ht : c.TimeOK) (k : Nat) : deliverAt sys mask c k ≠ some (.error .sort) := by
  intro h
  obtain ⟨e, he, _, hf⟩ := deliver_error_form h
  have hel : e.time < timeLimit := (ht.2 e (List.mem_of_getElem? he)).2
  have hte : ((c.pop k e).time : Int) ≤ maxSafe := maxSafe_of_lt hel
  rcases hf with hf | ⟨act, hw⟩ | ⟨ws, hp⟩
  · cases hf
  · exact winnersOf_ne_sort (c := c.pop k e) (WF.transWT hwf) hs hte _ hw
  · exact phase2_ne_sort (c := c.pop k e) (WF.transWT hwf) hs hte ws c.machines hs hp

/-- **`sort` is unreachable in a well-formed system**: no step from a reachable configuration fails
with `sort`. -/
theorem sort_unreachable (sys : Sys) (hwf : sys.WF) {m : List Bool} {c : Cfg}
    (hr : (Sys.lts sys).Reach (.run m c)) (l : Label) : deliver sys m c l ≠ some (.error .sort) := by
  intro hd
  unfold deliver at hd
  split at hd
  · split at hd
    · cases hd
    · exact deliver_ne_sort (sys := sys.resolve l.draws) (resolve_wf hwf l.draws)
        (shaped_invariant sys (WF.shaped hwf) _ hr) (time_invariant sys (WF.timesOK hwf) _ hr) _ hd
  · cases hd

/-- **A well-formed system reaches no state of the wrong shape**, with no bound on runs. -/
theorem wf_shaped_invariant (sys : Sys) (hwf : sys.WF) :
    (Sys.lts sys).Invariant (fun s => s.Shaped sys) :=
  shaped_invariant sys (WF.shaped hwf)

theorem mapM_congr_opt {α β : Type} (f g : α → Option β) : ∀ l : List α, (∀ x ∈ l, f x = g x) → l.mapM f = l.mapM g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.mapM_cons]
    rw [h x List.mem_cons_self, mapM_congr_opt f g xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- The parallel reading of phase 2. -/
def parUpd (sys : Sys) (c : Cfg) (e : Entry) (ms : List MState) (w : Winner sys) : Option (Nat × MState) :=
  (ms[w.mach.val]?).bind fun o => ((fireOne sys c e w o).toOption).map (fun r => (w.mach.val, r.1))

theorem phase2_eq_par_from {sys : Sys} {c : Cfg} {e : Entry} :
    (ws : List (Winner sys)) → (ms : List MState) → (ws.map (·.mach)).Nodup →
    machinesAfter (phase2 sys c e ws ms) =
      (ws.mapM (parUpd sys c e ms)).map (fun upd => upd.foldl (fun ms p => ms.set p.1 p.2) ms)
  | [], ms, _ => by simp [phase2, machinesAfter, Except.toOption]
  | w :: ws, ms, hnd => by
    have hnd' := List.nodup_cons.mp hnd
    cases hms : ms[w.mach.val]? with
    | none => simp [phase2, machinesAfter, Except.toOption, parUpd, hms]
    | some own =>
      cases hf : fireOne sys c e w own with
      | error err => simp [phase2, machinesAfter, Except.toOption, parUpd, hms, hf]
      | ok r =>
        obtain ⟨st, out⟩ := r
        rw [machinesAfter_cons_ok hms hf, phase2_eq_par_from ws (ms.set w.mach.val st) hnd'.2]
        have hcongr : ws.mapM (parUpd sys c e (ms.set w.mach.val st)) = ws.mapM (parUpd sys c e ms) := by
          apply mapM_congr_opt
          intro x hx
          have hne : x.mach.val ≠ w.mach.val := by
            intro h
            apply hnd'.1
            exact List.mem_map.mpr ⟨x, hx, Fin.ext h⟩
          simp only [parUpd, List.getElem?_set_ne (Ne.symm hne)]
        rw [hcongr]
        simp only [List.mapM_cons, parUpd, hms, hf, Option.bind_some, Except.toOption, Option.map_some]
        cases ws.mapM (parUpd sys c e ms) <;> simp

/-- **Phase 2 is a parallel step** (review-M2.1, finding 5): when the winners are on distinct
machines, the machines after phase 2 are the starting machines with every winner's result written
at its machine, each winner having fired from the starting machine and the snapshot, in no
particular order. -/
theorem phase2_eq_par {sys : Sys} {c : Cfg} {e : Entry} {ws : List (Winner sys)}
    (h : (ws.map (·.mach)).Nodup) :
    machinesAfter (phase2 sys c e ws c.machines) =
      (ws.mapM (fun w => (c.machines[w.mach.val]?).bind fun o =>
          ((fireOne sys c e w o).toOption).map (fun r => (w.mach.val, r.1)))).map
        (fun upd => upd.foldl (fun ms p => ms.set p.1 p.2) c.machines) :=
  phase2_eq_par_from ws c.machines h

end Exegra.Core.Behav
