import Exegra.Format2
import Exegra.Core.BehavExec

/-
Elaboration of a format-2 input into the behaviour calculus (docs/assessment/2026-11-26/plan-M2.md,
increment M2.4; the task's criteria 13 and 17).

`Elab.elab : V2.Input → Except Refusal Core.Behav.Sys` turns a decoded version-2 input into a
calculus system, or refuses it:

* `outOfFragment what`: the input uses a construct the calculus does not cover (links, workloads,
  option types, a scenario step addressed to an instance of a keyed behaviour).
  A `sample` effect (a variable set from a draw) is covered: an integer literal at a draw site; so
  are resources, their `use`, `acquire` and `release` effects, the counts expressions read,
  resource faults, routes and keyed instances (WG-5683). Measured outputs are a function of the
  trace (`metrics`): an input that measures runs on the calculus like any other. An input
  outside the fragment runs on the legacy interpreter, flagged in its trace, and no
  theorem is about it.
* `illTyped msg`: the input is not well-typed: an unknown event or variable, a guard that is not
  Boolean, an operator applied to the wrong sorts, a repeated behaviour id, an id declared both as
  an event and as a behaviour, fault or scenario, a variable named `time` or `state` (the five
  behaviours of WG-4688, docs/simulation.md).
Numbers are exact rationals (owner decision 2026-11-27, WG-5683): a literal, an initial value or a
payload that is not an integer elaborates to the rational it is (`Core.Behav.Val.ofRat`), of the sort
of untyped numbers.

The layout: machines are the instances of the behaviours, behaviours in input order, the instances
of a counted behaviour in index order (the order format 2's phase 1 visits them,
Format2.lean:1290-1304); a keyed behaviour with at most `max` instances is `max` slot machines, not
live until a route creates them, in creation order. `Sys.routes` holds the routes in format 2's
decision order (`routeList`). A keyed behaviour's `b.x` and `b.state` are `Ref.one` (read when the
step runs: ambiguous with more than one instance, absent with none), its `instance` is
`Ref.key`, its `b.instances.count` the sum of `Ref.count` over its control states; a short-circuit
node whose right operand reads a behaviour that may have several instances as one is preceded by
`Ref.uniq`, since format 2 resolves every reference before evaluating (`guardUniq`). Guards and effect expressions are parsed once (`parseExpr`) and resolved
to `Fin`-scoped references: own variables, `b.x`, `b.state`, `b.instances.count` (a literal),
`b.count.s`, `b.sum.x`, `b.min.x`, `b.max.x`, `event.f`, `time`, `instance` (a literal). A
reference to nothing (an unknown name, a behaviour with several instances read as one, an
aggregate of a single behaviour) is `Ref.absent`: the step that evaluates it fails, as format 2's
does. A payload field and an absent reference take the sort their context needs (a comparison
with a string, an arithmetic operand, a Boolean operator, the variable a `set` writes). Event
names become their positions (`evIdx`), payload field names and timer names numbers (`strId`,
injective).

`elab_wf`: an accepted input elaborates to a well-formed system. `elab` checks `Sys.wf`, the
decidable well-formedness, last, and refuses as `illTyped` what fails it.
-/

namespace Exegra.V2.Elab

open Exegra

/-- Why an input is not elaborated. -/
inductive Refusal where
  | outOfFragment (what : String)
  | illTyped (msg : String)
  deriving Repr, Inhabited

def Refusal.kind : Refusal → String
  | .outOfFragment _ => "outOfFragment"
  | .illTyped _ => "illTyped"

def Refusal.detail : Refusal → String
  | .outOfFragment w => w
  | .illTyped m => m

/-- The message an input refused as ill-typed is reported with. -/
def Refusal.message : Refusal → String
  | .outOfFragment w => s!"The input uses {w}, which the behaviour calculus does not cover."
  | .illTyped m => s!"The input is ill-typed: {m}"

abbrev E := Except Refusal

/-- An injective numbering of strings (event names, payload fields, timer names). -/
def strId (s : String) : Nat := s.foldl (fun acc c => acc * 1114113 + c.toNat + 1) 0

/-- The number of an event: its position among the input's events (events index the attempt
counts, so they are numbered densely); an undeclared event gets the number after the last. -/
def evIdx (i : Input) (ev : String) : Nat := (i.events.idxOf? ev).getD i.events.length

/-- The range of an integer representation type. -/
def intRange : IntKind → Int × Int
  | .u8 => (0, 255) | .u16 => (0, 65535) | .u32 => (0, 4294967295)
  | .u64 => (0, 9007199254740991)
  | .i32 => (-2147483648, 2147483647)
  | .i64 => (-9007199254740991, 9007199254740991)

/-- An integer from a JSON number (an instance index). -/
def intOf (x : Rat) (path : String) : E Int :=
  match Num.safeInteger? x with
  | some n => .ok n
  | none => .error (.illTyped s!"the number at {path} is not an integer")

/-- A JSON constant with the members of every object sorted by key, so that structurally equal
constants (format 2's `==`, `Value.eqv`) have equal texts. -/
partial def canon : Value → Value
  | .obj n fs => .obj n ((fs.map fun (k, v) => (k, canon v)).mergeSort (fun a b => a.1 ≤ b.1))
  | .arr n xs => .arr n (xs.map canon)
  | v => v

/-- A JSON constant as a calculus value: an integer, a Boolean, a string, or an object, array or
`null` by its canonical text. -/
def valOf (v : Value) (path : String) : E Core.Behav.Val :=
  match v with
  | .num x => .ok (Core.Behav.Val.ofRat x)
  | .str s => .ok (.str s)
  | .bool b => .ok (.bool b)
  | .undef => .error (.illTyped s!"{path} has no value")
  | v => .ok (.lit (Json.write (canon v)) (Json.write v))

/-- A payload object as calculus fields. -/
def payloadOf (v : Value) (path : String) : E (List (Nat × Core.Behav.Val)) :=
  match v with
  | .obj _ fs => fs.mapM fun (k, x) => do pure (strId k, ← valOf x s!"{path}.{k}")
  | .null | .undef => .ok []
  | _ => .error (.illTyped s!"{path} is not an object")

def distOf : Dist → Core.Behav.Dist
  | .fixed v => .fixed v
  | .uniform lo hi => .uniform lo hi
  | .table pts => .table pts
  | .choice vs => .choice vs

/-! ### The layout -/

/-- The number of instances of a behaviour. -/
def instCount (b : BehaviorIn) : Nat :=
  match b.instances with
  | .count n => n
  | .keyed _ max => max
  | _ => 1

/-- A keyed behaviour: its instances are created by routes, up to its maximum; it is laid out as
that many slot machines, none live at the start. -/
def isKeyed (b : BehaviorIn) : Bool :=
  match b.instances with
  | .keyed .. => true
  | _ => false

/-- The machines: (behaviour index, instance index), behaviours in order; a keyed behaviour has one
slot per instance it may have. -/
def layout (bs : List BehaviorIn) : List (Nat × Nat) :=
  (List.range bs.length).flatMap fun j => (List.range (instCount (bs.getD j default))).map fun k => (j, k)

/-- The machine of instance `k` of behaviour `j`. -/
def machineOf (bs : List BehaviorIn) (j k : Nat) : Nat :=
  ((layout bs).findIdx? (· == (j, k))).getD (layout bs).length

/-- The control states of a behaviour: the initial state, then every source and target, first
occurrence first. -/
def statesOf (b : BehaviorIn) : List String :=
  (b.transitions.foldl (fun acc t => [t.source, t.target].foldl (fun acc s =>
    if acc.contains s then acc else acc ++ [s]) acc) [b.initial])

def stateIdx (b : BehaviorIn) (s : String) : Nat := ((statesOf b).idxOf? s).getD 0

/-- The sort of a variable: its declared integer type, or the sort of its initial value. -/
def varTy (b : BehaviorIn) (v : VariableIn) : E Core.Behav.Ty :=
  match tyLookup b.types [v.name], v.initial with
  | .option, _ => .error (.outOfFragment s!"option types (variable {b.id}.{v.name})")
  | .int k, .num _ => .ok (.int (intRange k).1 (intRange k).2)
  | .int _, _ => .error (.illTyped s!"variable {b.id}.{v.name} has an integer type and a non-numeric initial value")
  | .none, .num _ => .ok Core.Behav.Ty.num
  | .none, .str _ => .ok .str
  | .none, .bool _ => .ok .bool
  | .none, .undef => .error (.illTyped s!"variable {b.id}.{v.name} has no initial value")
  | .none, _ => .ok .lit

/-! ### Expressions -/

/-- What an expression elaborator needs to know about the machine and the input. -/
structure Ctx where
  input : Input
  behs : List BehaviorIn
  /-- The behaviour of the machine, its index and the instance index. -/
  b : BehaviorIn
  bi : Nat
  inst : Nat
  /-- The event of the transition being elaborated (its payload fields are `event.f`). -/
  ev : String := ""

/-- The sort of a JSON constant. -/
def sortOfValue : Value → Option Core.Behav.Ty
  | .num _ => some Core.Behav.Ty.num
  | .str _ => some .str
  | .bool _ => some .bool
  | .undef => none
  | _ => some .lit

/-- The sort a payload field `f` of event `ev` carries, as the input shows it: the value a scenario
step or an injected entry gives it, or what an emit of the event puts there (a constant, a string
expression, or a field passed on from the emitting transition's own event). -/
def payloadFieldTy (i : Input) : Nat → String → String → Option Core.Behav.Ty
  | 0, _, _ => none
  | fuel + 1, ev, f =>
    let ofPayload (v : Value) : Option Core.Behav.Ty := match v with
      | .obj _ fs => (objGet? fs f).bind sortOfValue
      | _ => none
    let fromSteps := i.scenario.steps.findSome? fun st => if st.event == ev then ofPayload st.payload else none
    let fromFaults := i.faults.findSome? fun fl => if fl.event == some ev then ofPayload fl.payload else none
    let fromEmits := i.behaviors.findSome? fun b => b.transitions.findSome? fun t =>
      t.effects.findSome? fun e =>
        let pl := match e with
          | .emit ev' _ pl _ | .timer _ _ ev' pl => if ev' == ev then pl else []
          | _ => []
        (pl.find? (·.1 == f)).bind fun (_, v) => match v with
          | .str src => match parseExpr src with
            | .ok (.ref ["event", g]) => payloadFieldTy i fuel t.on g
            | .ok (.lit v) => sortOfValue v
            | .ok (.bin .add _ _) | .ok (.bin .sub _ _) | .ok (.bin .mul _ _) | .ok (.bin .div _ _)
            | .ok (.bin .rem _ _) | .ok (.un .neg _) => none
            | .ok (.ref [x]) => (b.variables.find? (·.name == x)).bind fun var => sortOfValue var.initial
            | .ok (.ref [bn, x]) =>
              if x == "state" then some .str
              else (i.behaviors.find? (·.id == bn)).bind fun b' =>
                (b'.variables.find? (·.name == x)).bind fun var => sortOfValue var.initial
            | .ok (.bin _ _ _) | .ok (.un .not _) => some .bool
            | _ => none
          | v => sortOfValue v
    -- the answers of requests: `resource`, `class`, `reason` are strings, `waited` and `served`
    -- numbers, the request's own payload as an emit's (Format2.lean:1654-1665)
    let fromAnswers := i.behaviors.findSome? fun b => b.transitions.findSome? fun t =>
      t.effects.findSome? fun e => match e with
        | .request _ _ _ _ _ thenEv refused pl =>
          if thenEv == ev || refused == some ev then
            if f == "resource" || f == "class" || f == "reason" then some .str
            else if f == "waited" || f == "served" then some Core.Behav.Ty.num
            else (pl.find? (·.1 == f)).bind fun (_, v) => match v with
              | .str src => match parseExpr src with
                | .ok (.ref ["event", g]) => payloadFieldTy i fuel t.on g
                | .ok (.lit v) => sortOfValue v
                | .ok (.ref [x]) => (b.variables.find? (·.name == x)).bind fun var => sortOfValue var.initial
                | .ok (.bin .add _ _) | .ok (.bin .sub _ _) | .ok (.bin .mul _ _) | .ok (.bin .div _ _)
                | .ok (.bin .rem _ _) | .ok (.un .neg _) => none
                | .ok (.bin _ _ _) | .ok (.un .not _) => some .bool
                | _ => none
              | v => sortOfValue v
          else none
        | _ => none
    fromSteps <|> fromFaults <|> fromEmits <|> fromAnswers

def Ctx.fieldTy (cx : Ctx) (f : String) : Option Core.Behav.Ty :=
  match tyLookup cx.b.types ["event", f] with
  | .int k => some (.int (intRange k).1 (intRange k).2)
  | _ => payloadFieldTy cx.input 8 cx.ev f

def Ctx.tys (cx : Ctx) : TyEnv := tyLookup cx.b.types

/-- The sort of the keys of keyed behaviour `b`: the sort of the payload field its first key route
reads. -/
def keyTy (i : Input) (b : BehaviorIn) : Option Core.Behav.Ty :=
  i.routes.findSome? fun r =>
    if r.behavior == b.id && r.rby == "key" then r.field.bind fun f => payloadFieldTy i 8 r.event f
    else none

/-- The arithmetic sort of a node: the declared integer type of its first typed operand
(format 2's `staticTy`, Expr.lean:267-277), or untyped. -/
def Ctx.aty (cx : Ctx) (a : Ast) : Core.Behav.ATy :=
  match staticTy cx.tys a with
  | .int k => .int (intRange k).1 (intRange k).2
  | _ => .untyped

/-- The sort an expression has without context (none for a payload field or an absent reference,
whose sort comes from the context). -/
def Ctx.hint (cx : Ctx) : Ast → Option Core.Behav.Ty
  | .lit (.num _) => some Core.Behav.Ty.num
  | .lit (.str _) => some .str
  | .lit (.bool _) => some .bool
  | .lit _ => some .lit
  | .ref ["time"] => some Core.Behav.Ty.num
  | .ref ["instance"] => if isKeyed cx.b then keyTy cx.input cx.b else some Core.Behav.Ty.num
  | .ref [x] => (cx.b.variables.find? (·.name == x)).bind fun v => (varTy cx.b v).toOption
  | .ref ["event", f] => cx.fieldTy f
  | .ref [_, "inUse"] | .ref [_, "waiting"] => some Core.Behav.Ty.num
  | .ref [bn, x] =>
    if x == "state" then (cx.input.behaviors.find? (·.id == bn)).map fun _ => .str
    else (cx.input.behaviors.find? (·.id == bn)).bind fun b' =>
      (b'.variables.find? (·.name == x)).bind fun v => (varTy b' v).toOption
  | .ref [_, _, _] => some Core.Behav.Ty.num
  | .ref _ => none
  | .un .not _ => some .bool
  | .un .neg _ => some Core.Behav.Ty.num
  | .bin op a b => match op with
    | .add => if cx.hint a == some .str || cx.hint b == some .str then some .str else some Core.Behav.Ty.num
    | .sub | .mul | .div | .rem => some Core.Behav.Ty.num
    | _ => some .bool

section
variable {S : Core.Behav.Sig} (me : Fin S.machines)

/-- Variable `x` of machine `m`, if it has one. -/
def varIdx (cx : Ctx) (m : Fin S.machines) (b : BehaviorIn) (x : String) : Option (Fin (S.vars m).length) :=
  match b.variables.findIdx? (·.name == x) with
  | some i => if h : i < (S.vars m).length then some ⟨i, h⟩ else none
  | none => none

def finOf (n i : Nat) : Option (Fin n) := if h : i < n then some ⟨i, h⟩ else none

/-- A reference, resolved in machine `me`; `want` is the sort the context needs. -/
def resolveRef (cx : Ctx) (want : Core.Behav.Ty) (path : List String) : E (Core.Behav.Expr S me) :=
  let absent : E (Core.Behav.Expr S me) := .ok (.ref (.absent want))
  let behIdx (bn : String) : Option Nat := cx.behs.findIdx? (·.id == bn)
  match path with
  | ["time"] => .ok (.ref .time)
  | ["instance"] =>
    if isKeyed cx.b then .ok (.ref (.key ((keyTy cx.input cx.b).getD want)))
    else .ok (.val (.int cx.inst))
  | ["event", f] => .ok (.ref (.field (strId f) ((cx.fieldTy f).getD want)))
  | [x] => match varIdx cx me cx.b x with
    | some v => .ok (.ref (.own v))
    | none => absent
  -- resources first, as format 2 resolves them (Format2.lean:1177-1192)
  | [r, "inUse"] => match cx.input.resources.findIdx? (·.id == r) with
    | some ri => .ok (.ref (.res ri .inUse))
    | none => absent
  | [r, "waiting"] => match cx.input.resources.findIdx? (·.id == r) with
    | some ri => .ok (.ref (.res ri .waiting))
    | none => absent
  | [r, "inUse", c] | [r, "waiting", c] =>
    match cx.input.resources.findIdx? (·.id == r) with
    | some ri =>
      match (cx.input.resources.getD ri default).classes.findIdx? (·.id == c) with
      | some k => .ok (.ref (.res ri (if path[1]! == "inUse" then .inUseC k else .waitingC k)))
      | none => absent
    | none => absent
  | [bn, "instances", "count"] =>
    match behIdx bn with
    | some j =>
      let b' := cx.behs.getD j default
      match b'.instances with
      | .count n => .ok (.val (.int n))
      | .keyed _ max =>
        -- the live slots: the instances in each control state, summed
        let ms : List (Fin S.machines) :=
          (List.range max).filterMap fun k => finOf S.machines (machineOf cx.behs j k)
        let cs : List (Core.Behav.Expr S me) := (statesOf b').map fun st => .ref (.count ms st)
        .ok (cs.tail.foldl (fun acc x => .bin (.arith .add .untyped) acc x) (cs.headD (.val (.int 0))))
      | _ => absent
    | none => absent
  | [bn, agg, x] =>
    match behIdx bn with
    | none => absent
    | some j =>
      let b' := cx.behs.getD j default
      let count? : Option Nat := match b'.instances with
        | .count n => some n
        | .keyed _ max => some max
        | _ => none
      match count? with
      | some n =>
        let ms : List (Fin S.machines) :=
          (List.range n).filterMap fun k => finOf S.machines (machineOf cx.behs j k)
        if agg == "count" then .ok (.ref (.count ms x))
        else
          let op : Option Core.Behav.AggOp :=
            if agg == "sum" then some .sum else if agg == "min" then some .min
            else if agg == "max" then some .max else none
          match op with
          | none => absent
          | some op =>
            let g := ms.filterMap fun m => (varIdx cx m b' x).map fun v => (⟨m, v⟩ : (m : Fin S.machines) × Fin (S.vars m).length)
            if g.length = ms.length then .ok (.ref (.agg op g)) else absent
      | none => absent
  | [bn, x] =>
    match behIdx bn with
    | none => absent
    | some j =>
      let b' := cx.behs.getD j default
      if isKeyed b' then
        -- the one live instance, read when the step runs (Format2.lean `resolve`)
        let ms : List (Fin S.machines) :=
          (List.range (instCount b')).filterMap fun k => finOf S.machines (machineOf cx.behs j k)
        if x == "state" then
          .ok (.ref (.one (ms.map fun m => (⟨m, none⟩ : (m : Fin S.machines) × Option (Fin (S.vars m).length))) .str))
        else
          let g := ms.filterMap fun m => (varIdx cx m b' x).map fun v =>
            (⟨m, some v⟩ : (m : Fin S.machines) × Option (Fin (S.vars m).length))
          let τ : Core.Behav.Ty := match g.head? with
            | some ⟨m, some v⟩ => (S.vars m).get v
            | _ => want
          if g.length = ms.length then .ok (.ref (.one g τ)) else absent
      else if instCount b' ≠ 1 then absent
      else match finOf S.machines (machineOf cx.behs j 0) with
        | none => absent
        | some m =>
          if x == "state" then .ok (.ref (.state m))
          else match varIdx cx m b' x with
            | some v => .ok (.ref (.other m v))
            | none => absent
  | _ => absent

/-- The machines of each behaviour that a `b.x` or `b.state` reference of `a` reads and that may
have more than one instance (a keyed behaviour, or one of several counted instances). Format 2
resolves every reference of an expression before evaluating it, so such a reference fails the step
with more than one instance even where `&&`, `||` or `=>` does not evaluate it (`evalIn`). -/
def multiRefs (cx : Ctx) : Ast → List (List Nat)
  | .ref [bn, x] =>
    if bn == "event" || x == "inUse" || x == "waiting" then [] else
    match cx.behs.findIdx? (·.id == bn) with
    | some j =>
      let b' := cx.behs.getD j default
      if isKeyed b' || instCount b' > 1 then [(List.range (instCount b')).map (machineOf cx.behs j)] else []
    | none => []
  | .un _ a => multiRefs cx a
  | .bin _ a b => multiRefs cx a ++ multiRefs cx b
  | _ => []

/-- A short-circuit node `node` whose right operand is `b`, preceded by the check that each
behaviour `b` reads as one has at most one instance (`Ref.uniq`). -/
def guardUniq (cx : Ctx) (b : Ast) (node : Core.Behav.Expr S me) : Core.Behav.Expr S me :=
  (multiRefs cx b).foldl (fun acc g =>
    .bin .and (.ref (.uniq (g.filterMap fun m => (finOf S.machines m).map fun m' =>
      (⟨m', none⟩ : (m : Fin S.machines) × Option (Fin (S.vars m).length))))) acc) node

/-- An expression, elaborated in machine `me`; `want` is the sort its context needs, used for
payload fields and absent references only. -/
def elabExpr (cx : Ctx) : Core.Behav.Ty → Ast → E (Core.Behav.Expr S me)
  | _, .lit (.num x) => .ok (.val (Core.Behav.Val.ofRat x))
  | _, .lit (.str s) => .ok (.val (.str s))
  | _, .lit (.bool b) => .ok (.val (.bool b))
  | _, .lit v => (valOf v "an expression literal").map .val
  | want, .ref p => resolveRef me cx want p
  | _, .un .not a => do pure (.un .not (← elabExpr cx .bool a))
  | _, .un .neg a => do pure (.un (.neg (cx.aty (.un .neg a))) (← elabExpr cx Core.Behav.Ty.num a))
  | _, .bin op a b =>
    let num := Core.Behav.Ty.num
    match op with
    | .and => do pure (guardUniq me cx b (.bin .and (← elabExpr cx .bool a) (← elabExpr cx .bool b)))
    | .or => do pure (guardUniq me cx b (.bin .or (← elabExpr cx .bool a) (← elabExpr cx .bool b)))
    | .implies => do pure (guardUniq me cx b (.bin .imp (← elabExpr cx .bool a) (← elabExpr cx .bool b)))
    | .eq => do
      let wa := (cx.hint b).getD ((cx.hint a).getD num)
      let wb := (cx.hint a).getD wa
      pure (.bin .eq (← elabExpr cx wa a) (← elabExpr cx wb b))
    | .ne => do
      let wa := (cx.hint b).getD ((cx.hint a).getD num)
      let wb := (cx.hint a).getD wa
      pure (.bin .ne (← elabExpr cx wa a) (← elabExpr cx wb b))
    | .lt => do pure (.bin .lt (← elabExpr cx num a) (← elabExpr cx num b))
    | .le => do pure (.bin .le (← elabExpr cx num a) (← elabExpr cx num b))
    | .gt => do
      let ea ← elabExpr cx num a
      let eb ← elabExpr cx num b
      pure (.bin .lt eb ea)
    | .ge => do
      let ea ← elabExpr cx num a
      let eb ← elabExpr cx num b
      pure (.bin .le eb ea)
    | .add =>
      if cx.hint a == some .str || cx.hint b == some .str then do
        pure (.bin .concat (← elabExpr cx .str a) (← elabExpr cx .str b))
      else do pure (.bin (.arith .add (cx.aty (.bin op a b))) (← elabExpr cx num a) (← elabExpr cx num b))
    | .sub => do pure (.bin (.arith .sub (cx.aty (.bin op a b))) (← elabExpr cx num a) (← elabExpr cx num b))
    | .mul => do pure (.bin (.arith .mul (cx.aty (.bin op a b))) (← elabExpr cx num a) (← elabExpr cx num b))
    | .div => do pure (.bin (.arith .div (cx.aty (.bin op a b))) (← elabExpr cx num a) (← elabExpr cx num b))
    | .rem => do pure (.bin (.arith .mod (cx.aty (.bin op a b))) (← elabExpr cx num a) (← elabExpr cx num b))

/-- A source string parsed and elaborated. -/
def elabSrc (cx : Ctx) (want : Core.Behav.Ty) (src : String) (what : String) : E (Core.Behav.Expr S me) :=
  match parseExpr src with
  | .error e => .error (.illTyped s!"{what}: {e}")
  | .ok ast => elabExpr me cx want ast

/-- A payload or `set` value: a string is an expression, a number or Boolean a literal. -/
def elabValue (cx : Ctx) (want : Core.Behav.Ty) (v : Value) (what : String) : E (Core.Behav.Expr S me) :=
  match v with
  | .str src => elabSrc me cx want src what
  | v => (valOf v what).map .val

def elabPayload (cx : Ctx) (pl : List (String × Value)) (what : String) :
    E (List (Nat × Core.Behav.Expr S me)) :=
  pl.mapM fun (k, v) => do pure (strId k, ← elabValue me cx Core.Behav.Ty.num v s!"{what}.payload.{k}")

/-- The delay of an `emit` or `timer`: a fixed delay, or a sampled one (its draw site). -/
def afterOf (d : Dist) : Nat × Option Core.Behav.Dist :=
  match d with
  | .fixed v => (v, none)
  | d => (0, some (distOf d))

/-- An effect of machine `me` (effect `ei` of transition `ti`), with the sampled delay it
introduces, if any. -/
def elabEffect (cx : Ctx) (what : String) (ti ei : Nat) : Effect → E (Core.Behav.Effect S me × Option Core.Behav.Dist)
  | .set x to =>
    match varIdx cx me cx.b x with
    | none => .error (.illTyped s!"{what} sets {x}, which is not a variable of {cx.b.id}")
    | some v =>
      match to with
      | none => .error (.illTyped s!"{what} sets {x} with no value")
      | some val => do
        let rhs ← elabValue me cx ((S.vars me).get v) val s!"{what}.to"
        pure (.set v rhs, none)
  | .sample x d =>
    -- A variable set from a draw (WG-5683): an integer literal at a draw site, which the label's
    -- draw replaces (`Sys.resolve`, `Effect.withAfter`); a fixed distribution is its value.
    match varIdx cx me cx.b x with
    | none => .error (.illTyped s!"{what} samples into {x}, which is not a variable of {cx.b.id}")
    | some v => match d with
      | .fixed n => .ok (.set v (.val (.int n)), none)
      | d => .ok (.set v (.val (.int 0)), some (distOf d))
  | .emit ev after pl reply =>
    if !cx.input.isEvent ev then .error (.illTyped s!"{what} emits {ev}, which is not an event") else do
    let pl' ← elabPayload me cx pl what
    let (a, d) := afterOf after
    pure ((if reply then .reply (evIdx cx.input ev) a pl' else .emit (evIdx cx.input ev) a pl'), d)
  | .timer name after ev pl =>
    if !cx.input.isEvent ev then .error (.illTyped s!"{what} emits {ev}, which is not an event") else do
    let pl' ← elabPayload me cx pl what
    let (a, d) := afterOf after
    pure (.timer (strId name) a (evIdx cx.input ev) pl', d)
  | .cancel name => .ok (.cancel (strId name), none)
  | .request kind res cls units demand thenEv refused pl =>
    match cx.input.resources.findIdx? (·.id == res) with
    | none => .error (.illTyped s!"{what} uses {res}, which is not a resource")
    | some ri =>
      match classIndex (cx.input.resources.getD ri default) cls with
      | none => .error (.illTyped s!"{what} names no class of {res}")
      | some ci => do
        let pl' ← elabPayload me cx pl what
        pure (.request ri ci units kind (evIdx cx.input thenEv) (refused.map (evIdx cx.input)) (distOf demand)
          (ti, ei) pl', none)
  | .release res cls units =>
    match cx.input.resources.findIdx? (·.id == res) with
    | none => .error (.illTyped s!"{what} releases {res}, which is not a resource")
    | some ri =>
      match classIndex (cx.input.resources.getD ri default) cls with
      | none => .error (.illTyped s!"{what} names no class of {res}")
      | some ci => .ok (.release ri ci units, none)
  | .send .. => .error (.outOfFragment s!"links ({what})")
  | .malformed => .error (.illTyped s!"{what} is malformed")

end

/-! ### Transitions and the system -/

/-- The transitions of machine `me`, and its sampled delays (transition, effect, distribution). -/
def elabTrans (S : Core.Behav.Sig) (me : Fin S.machines) (cx : Ctx) :
    E (List (Core.Behav.Trans S me) × List (Nat × Nat × Core.Behav.Dist)) := do
  let sts := statesOf cx.b
  let mut ts : List (Core.Behav.Trans S me) := []
  let mut ds : List (Nat × Nat × Core.Behav.Dist) := []
  for (t, ti) in cx.b.transitions.zipIdx do
    let cx := { cx with ev := t.on }
    let what := s!"transition {cx.b.id}.{t.id}"
    if !cx.input.isEvent t.on then throw (.illTyped s!"{what} is on {t.on}, which is not an event")
    let some src := finOf (S.states me).length (stateIdx cx.b t.source) | throw (.illTyped s!"{what}: unknown state")
    let some dst := finOf (S.states me).length (stateIdx cx.b t.target) | throw (.illTyped s!"{what}: unknown state")
    let guard ← match t.guard with
      | none => pure (.val (.bool true))
      | some g => elabSrc me cx .bool g s!"the guard of {what}"
    let mut effs : List (Core.Behav.Effect S me) := []
    for (e, ei) in t.effects.zipIdx do
      let (eff, d) ← elabEffect me cx s!"effect {ei} of {what}" ti ei e
      effs := effs ++ [eff]
      if let some d := d then ds := ds ++ [(ti, ei, d)]
    let tr : Core.Behav.Trans S me := { src, dst, event := evIdx cx.input t.on, guard, effects := effs, faultOnly := t.faultOnly }
    if !(tr.guard.ty? == some .bool) then throw (.illTyped s!"the guard of {what} is not Boolean")
    for (e, ei) in tr.effects.zipIdx do
      if !e.wt then throw (.illTyped s!"effect {ei} of {what} is ill-typed")
    ts := ts ++ [tr]
  return (ts, ds)

/-- The fault kinds the calculus covers. -/
def faultKind? : Option String → Option Core.Behav.FKind
  | some "drop-event" => some .drop
  | some "lose-event" => some .lose
  | some "delay-event" => some .delay
  | some "retry-event" => some .retry
  | some "duplicate-event" => some .duplicate
  | some "enable-transition" => some .enable
  | some "disable-transition" => some .disable
  | some "inject-event" => some .inject
  | some "set-capacity" => some .setCapacity
  | some "set-class-limit" => some .setClassLimit
  | some "collapse-classes" => some .collapse
  | some "scale-demand" => some .scaleDemand
  | some "replace-demand" => some .replaceDemand
  | _ => none

def occOf : Occurrence → Core.Behav.Occ
  | .any => .any
  | .exactly x => match Num.safeInteger? x with
    | some n => if 0 ≤ n then .exactly n.toNat else .never
    | none => .never
  | .never => .never

/-- The checks that precede the layout: constructs outside the calculus, and the WG-4688
decisions on ids and variable names. -/
def preCheck (i : Input) : E Unit := do
  unless i.links.isEmpty do throw (.outOfFragment "links")
  unless i.workloads.isEmpty do throw (.outOfFragment "workloads")
  -- a scenario step addressed to an instance of a keyed behaviour names a key, not a slot
  for st in i.scenario.steps do
    if let some (bn, _) := st.target then
      if (i.behaviors.find? (·.id == bn)).any isKeyed then
        throw (.outOfFragment s!"a scenario step addressed to an instance of keyed behavior {bn}")
  -- WG-4688, decision 1: a repeated behaviour id is refused.
  let ids := i.behaviors.map (·.id)
  for (b, k) in i.behaviors.zipIdx do
    if (ids.take k).contains b.id then throw (.illTyped s!"the behavior id {b.id} is repeated")
  -- WG-4688, decision 2: an id declared as an event and as a behaviour, fault or scenario.
  for ev in i.events do
    if ids.contains ev || i.faults.any (·.id == ev) || i.scenario.id == ev then
      throw (.illTyped s!"the id {ev} is declared both as an event and as a behavior, fault or scenario")
  -- WG-4688, decision 5: a variable named `time` or `state` is refused.
  for b in i.behaviors do
    for v in b.variables do
      if v.name == "time" || v.name == "state" then
        throw (.illTyped s!"variable {b.id}.{v.name}: the names time and state are reserved")

/-- The JSON text of a calculus value, as format 2 writes the value (a key route hashes it). -/
def valJson : Core.Behav.Val → String
  | .int n => Json.write (.num (n : Rat))
  | .rat q => Json.write (.num q)
  | .bool b => Json.write (.bool b)
  | .str s => Json.write (.str s)
  | .lit _ json => json

/-- The routes, in format 2's decision order (`decideRoutes`): behaviour by behaviour in input
order, for each the first route of each event (`Input.route?`), with the behaviour's index. -/
def routeList (i : Input) : List (Nat × RouteIn) :=
  (List.range i.behaviors.length).flatMap fun j =>
    let b := i.behaviors.getD j default
    (i.routes.zipIdx.filter fun (r, k) => r.behavior == b.id &&
        !((i.routes.take k).any fun r' => r'.event == r.event && r'.behavior == r.behavior)).map
      fun (r, _) => (j, r)

/-- A route as a calculus route. -/
def routeOfIn (i : Input) (j : Nat) (r : RouteIn) : Core.Behav.Route :=
  let b := i.behaviors.getD j default
  let by_ : Core.Behav.RouteBy := match r.rby with
    | "key" =>
      let f := strId (r.field.getD "")
      if isKeyed b then .keyed f else .key f (fun v => (Random.fnv1a64 (valJson v)).toNat)
    | "round-robin" => .roundRobin
    | "least-busy" => .leastBusy (r.resource.bind fun x => i.resources.findIdx? (·.id == x))
    | _ => .random
  { event := evIdx i r.event, group := (List.range (instCount b)).map (machineOf i.behaviors j), by_ }

/-- The calculus system of an input, before the well-formedness check. -/
def build (i : Input) : E Core.Behav.Sys := do
  preCheck i
  let behs := i.behaviors
  let lay := layout behs
  let n := lay.length
  let behOf (m : Nat) : BehaviorIn := behs.getD (lay.getD m (0, 0)).1 default
  -- variable sorts and initial machines
  let vtys ← behs.mapM fun b => b.variables.mapM (varTy b)
  let vtysM : Nat → List Core.Behav.Ty := fun m => vtys.getD (lay.getD m (0, 0)).1 []
  let sig : Core.Behav.Sig :=
    { machines := n, vars := fun m => vtysM m.val, states := fun m => statesOf (behOf m.val) }
  let machines ← lay.mapM fun (j, _) => do
    let b := behs.getD j default
    let vs ← b.variables.mapM fun v => valOf v.initial s!"{b.id}.{v.name}"
    pure ({ ctrl := stateIdx b b.initial, vars := vs, live := !isKeyed b } : Core.Behav.MState)
  -- transitions and sampled delays, machine by machine
  let tsl ← (Core.Behav.finList n).mapM fun m => do
    let (j, k) := lay.getD m.val (0, 0)
    let cx : Ctx := { input := i, behs, b := behs.getD j default, bi := j, inst := k }
    let (ts, ds) ← elabTrans sig m cx
    pure ((⟨m, ts⟩ : (m : Fin sig.machines) × List (Core.Behav.Trans sig m)), ds)
  -- the transitions are elaborated once; `trans` looks them up
  let tarr : Array ((m : Fin sig.machines) × List (Core.Behav.Trans sig m)) := (tsl.map (·.1)).toArray
  let tr := tsl.map (·.2)
  let trans : (m : Fin sig.machines) → List (Core.Behav.Trans sig m) := fun m =>
    match tarr[m.val]? with
    | some p => if h : p.1 = m then h ▸ p.2 else []
    | none => []
  let samples := (List.range n).flatMap fun m =>
    (tr.getD m []).map fun (ti, ei, d) => (m, ti, ei, d)
  -- faults: the scenario's, in its order
  let mut faults : List Core.Behav.Fault := []
  for fid in dedup i.scenario.faults do
    let some f := i.fault? fid | continue
    let some kind := faultKind? f.kind | throw (.outOfFragment s!"the fault kind of {f.id}")
    -- a `replace-demand` names the transitions of one behaviour; other faults any behaviour's
    let ofBeh (m : Nat) : Bool := kind != .replaceDemand || f.behavior == some (behOf m).id
    let targets := match f.transition with
      | none => []
      | some tid => ((List.range n).filter ofBeh).flatMap fun m =>
          ((behOf m).transitions.zipIdx.filter (·.1.id == tid)).map fun (_, ti) => (m, ti)
    let payload ← payloadOf f.payload s!"fault {f.id}.payload"
    let ev := evIdx i (f.event.getD "")
    let ri := (f.resource.bind fun r => i.resources.findIdx? (·.id == r)).getD i.resources.length
    let cls := (f.cls.bind fun c => (i.resources.getD ri default).classes.findIdx? (·.id == c)).getD 0
    let fault : Core.Behav.Fault :=
      { kind, event := ev, targets, occ := occOf f.occurrence, by_ := f.delayBy, window := f.window,
        at_ := f.injectAt, payload, res := ri, cls, capacity := f.capacity, limit := f.limit,
        num := f.num, den := f.den, effect := f.effect, demand := distOf f.demand }
    faults := faults ++ [fault]
  -- the scenario's entries, inserted by time in step order
  let mut pending : List Core.Behav.Entry := []
  for (st, si) in i.scenario.steps.zipIdx do
    let payload ← payloadOf st.payload s!"scenario step {si}.payload"
    let target ← match st.target with
      | none => pure none
      | some (bn, v) =>
        match behs.findIdx? (·.id == bn), v with
        | some j, .num x => do
          let k ← intOf x s!"scenario step {si}.target.instance"
          pure (some (if k < 0 then n else machineOf behs j k.toNat))
        | _, _ => pure (some n)
    pending := Core.Behav.insertByTime pending { time := st.time, event := evIdx i st.event, payload := payload, target := target }
  -- attempts are told apart only up to the largest occurrence a fault names (`Cfg.attCap`)
  let attCap := faults.foldl (fun k f => match f.occ with | .exactly m => max k m | _ => k) 0
  -- the resources, each at its declared capacity (`Sys.initCfg` applies the untimed resource faults)
  let world : Core.Behav.World :=
    { res := i.resources.map fun d => { capacity := d.capacity, holds := [], waiting := [] }, nextReq := 0 }
  return { sig, trans, init := { time := 0, machines, pending, attCap := some attCap, world }, faults,
           stopAt := i.scenario.stopAt, samples, resources := i.resources,
           routes := (routeList i).map fun (j, r) => routeOfIn i j r }

/-- **Elaboration**: the calculus system of a format-2 input, or why there is none. The last check
is the decidable well-formedness of the calculus (`Sys.wf`). -/
def «elab» (i : Input) : Except Refusal Core.Behav.Sys := do
  let sys ← build i
  if sys.wf && decide (1 ≤ i.scenario.stepLimit) then pure sys
  else if sys.wf then throw (.illTyped "the step limit is 0")
  else throw (.illTyped "the elaborated system is not well-formed")

theorem elab_check {i : Input} {sys : Core.Behav.Sys} (h : «elab» i = .ok sys) :
    sys.WF ∧ 1 ≤ i.scenario.stepLimit := by
  unfold «elab» at h
  cases hb : build i with
  | error e => rw [hb] at h; cases h
  | ok s =>
    rw [hb] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · rename_i hw
      cases h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
      exact ⟨hw.1, hw.2⟩
    · split at h <;> cases h

/-- **An accepted input elaborates to a well-formed system.** -/
theorem elab_wf {i : Input} {sys : Core.Behav.Sys} (h : «elab» i = .ok sys) : sys.WF :=
  (elab_check h).1

/-- An accepted input has a step limit of at least 1 (format 2's decoding guarantees it too). -/
theorem elab_stepLimit {i : Input} {sys : Core.Behav.Sys} (h : «elab» i = .ok sys) : 1 ≤ i.scenario.stepLimit :=
  (elab_check h).2

/-! ### At the call boundary -/

/-- What `engine.elab` reports: an accepted input's machine, fault and draw-site counts, or the
refusal's kind, detail and message. -/
def summary (i : Input) : String :=
  match «elab» i with
  | .ok sys => Json.write (.obj 0 [("accepted", .bool true),
      ("machines", .num (↑sys.sig.machines : Rat)), ("faults", .num (↑sys.faults.length : Rat)),
      ("samples", .num (↑sys.samples.length : Rat))])
  | .error r => Json.write (.obj 0 [("accepted", .bool false), ("kind", .str r.kind),
      ("detail", .str r.detail), ("message", .str r.message)])

/-- `engine.elab`: a version-2 engine input to its elaboration summary. -/
def elabJson (v : Value) : Except String String :=
  match v with
  | .obj _ root =>
    match objGet? root "version" with
    | some (.num x) => if x == 2 then do pure (summary (← Decode.input root))
      else .error "engine.elab takes a version-2 engine input"
    | _ => .error "engine.elab takes a version-2 engine input"
  | _ => .error "an engine input must be a JSON object"

end Exegra.V2.Elab

namespace Exegra.V2

open Exegra.Core.Behav in
/-- The initial state of a format-2 run: every fault of the scenario active. -/
def initialB (sys : Core.Behav.Sys) : Core.Behav.State :=
  .run (List.replicate sys.faults.length true) (sys.initCfg (List.replicate sys.faults.length true))

/-- **Every state of a run of the proved scheduler is reachable** (the task's criterion 14, first
half): for an input the elaborator accepts, every configuration of the run of `Exec.step` from the
format-2 initial state, up to the scenario's step limit and with any stream positions, is a
reachable state of the calculus. -/
theorem runB_reach {i : Input} {sys : Core.Behav.Sys} (h : Elab.«elab» i = .ok sys) :
    ∀ b : Core.Behav.Book, ∀ s ∈ (Core.Behav.Exec.run sys i.scenario.stepLimit (initialB sys) b).states,
      (Core.Behav.Sys.lts sys).Reach s := by
  intro b
  exact Core.Behav.run_reach (Elab.elab_wf h) _ b
    (.init ⟨List.replicate sys.faults.length true, List.length_replicate, rfl⟩)

end Exegra.V2

/-- info: 'Exegra.V2.Elab.elab_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.V2.Elab.elab_wf

/-- info: 'Exegra.V2.runB_reach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.V2.runB_reach
