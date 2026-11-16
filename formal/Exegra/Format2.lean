import Exegra.Semantics
import Exegra.Random
import Exegra.Resource

/-
Format 2 of the engine input and trace, the WG-4664 part (`docs/simulation.md`, "Planned:
resources, workloads and performance"): integer time in a declared unit, instances (counted and
keyed, with routes), resources (`use`, `acquire`, `release`, class queues, bounds, overflow) and
seeded SplitMix64 streams. Version-1 inputs never reach this module (`Exegra.runAny`).

Not here yet (refused when present): links, workloads, timers, meters, request classes, prices,
windowed and resource faults, `crash-instance` (no instance is ever down, every incarnation is 0).

The step mirrors the format-1 step (`Exegra/Semantics.lean`): the head is taken, drop and delay
faults act, then phase 1 (choose, reading the configuration from before the step) and phase 2
(effects, writing the next configuration). New here:

* routes are decided when an entry is first taken as head, and kept by delayed copies;
* phase 1 visits behaviors in scenario order and each addressed instance in index (creation)
  order; a behavior addressed by no instance gets one `ignored` record with reason `no-instance`;
  a targeted entry addresses only its target behavior;
* resource effects are recorded in phase 2 and applied when the step settles, resource by
  resource in input order: releases, then enqueues (each request takes a sequence number, then its
  `wait-timeout` entry, if its class has `maxWait`, takes the next), then grants (each `service-done`
  or `then` entry takes a number), then bounds (each `refused` entry takes a number);
* every draw is recorded in the step's `draws`.

ORDER marks where an order decides an observable result.
-/

namespace Exegra.V2

open Exegra.Res (ResourceDecl ClassDecl Req Hold RState)

/-! ## Input -/

/-- An integer distribution. -/
inductive Dist where
  | fixed (v : Nat)
  | uniform (lo hi : Nat)
  | table (points : List (Nat × Nat))
  | choice (values : List Nat)
  deriving Inhabited

def Dist.draws : Dist → Bool
  | .fixed _ => false
  | .choice _ => false
  | _ => true

inductive Instances where
  | single
  | count (n : Nat)
  | keyed (field : String) (max : Nat)
  deriving Inhabited

inductive Effect where
  | set (varName : String) (to : Option Value)
  | sample (varName : String) (d : Dist)
  | emit (event : String) (after : Dist) (payload : List (String × Value)) (reply : Bool)
  | request (kind : Res.ReqKind) (res : String) (cls : Option String) (units : Nat) (demand : Dist)
      (thenEv : String) (refused : Option String) (payload : List (String × Value))
  | release (res : String) (cls : Option String) (units : Nat)
  | malformed
  deriving Inhabited

structure TransitionIn where
  id : String
  source : String
  target : String
  on : String
  guard : Option String
  effects : List Effect
  faultOnly : Bool
  deriving Inhabited

structure BehaviorIn where
  id : String
  subject : Option String
  initial : String
  variables : List VariableIn
  transitions : List TransitionIn
  instances : Instances
  deriving Inhabited

structure RouteIn where
  event : String
  behavior : String
  rby : String
  field : Option String
  resource : Option String
  deriving Inhabited

structure FaultIn where
  id : String
  kind : Option String
  event : Option String
  transition : Option String
  occurrence : Occurrence
  delayBy : Nat
  injectAt : Nat
  payload : Value
  deriving Inhabited

def FaultIn.isKind (f : FaultIn) (k : String) : Bool := f.kind == some k

structure StepIn where
  time : Nat
  event : String
  payload : Value
  target : Option (String × Value)
  deriving Inhabited

structure ScenarioIn where
  id : String
  steps : List StepIn
  faults : List String
  stepLimit : Nat
  seed : Option UInt64
  horizon : Option Nat
  warmup : Option Nat
  stopAt : Option Nat
  output : String
  deriving Inhabited

structure Input where
  unit : String
  perSecond : Option Nat
  scenario : ScenarioIn
  behaviors : List BehaviorIn
  events : List String
  faults : List FaultIn
  routes : List RouteIn
  resources : List ResourceDecl
  deriving Inhabited

/-! ## Decoding -/

namespace Decode

open Exegra.Decode (R field object string array arrayOrEmpty payloadOrEmpty mapIdx)

def two53 : Nat := 9007199254740992
def two32 : Nat := 4294967296

/-- An integer in `[lo, hi]`. -/
def intIn (v : Value) (path : String) (lo hi : Nat) : R Nat :=
  let err := s!"Field \"{path}\" must be an integer in [{lo}, {hi}]."
  match v with
  | .num x =>
    if x.floor == x && x ≥ lo.toFloat && x ≤ hi.toFloat then .ok x.toUInt64.toNat else .error err
  | _ => .error err

def optInt (o : List (String × Value)) (key path : String) (lo hi : Nat) : R (Option Nat) :=
  match field o key with
  | .undef | .null => .ok none
  | v => (intIn v path lo hi).map some

def intOr (o : List (String × Value)) (key path : String) (lo hi d : Nat) : R Nat :=
  (optInt o key path lo hi).map (·.getD d)

def optStr (o : List (String × Value)) (key what : String) : R (Option String) :=
  match field o key with
  | .undef | .null => .ok none
  | .str s => .ok (some s)
  | _ => .error s!"{what}: \"{key}\" must be a string."

def payloadObj (o : List (String × Value)) (what : String) : R (List (String × Value)) :=
  match field o "payload" with
  | .obj _ fs => .ok fs
  | x => if x.isNullish then .ok [] else .error s!"{what}: \"payload\" must be an object."

/-- A duration: an integer, or a distribution object. -/
def dist (v : Value) (path : String) : R Dist :=
  match v with
  | .num _ => (intIn v path 0 (two53 - 1)).map .fixed
  | .obj _ o =>
    match field o "kind" with
    | .str "fixed" => (intIn (field o "value") s!"{path}.value" 0 (two53 - 1)).map .fixed
    | .str "uniform" => do
      let lo ← intIn (field o "lo") s!"{path}.lo" 0 (two53 - 1)
      let hi ← intIn (field o "hi") s!"{path}.hi" lo (two53 - 1)
      pure (.uniform lo hi)
    | .str "table" => do
      let pts ← match field o "points" with
        | .arr _ xs => mapIdx (fun i p => match p with
            | .arr _ [u, x] => do
              let u ← intIn u s!"{path}.points[{i}][0]" 0 two32
              let x ← intIn x s!"{path}.points[{i}][1]" 0 (two53 - 1)
              pure (u, x)
            | _ => throw s!"Distribution \"{path}\" has a malformed table.") xs
        | _ => throw s!"Distribution \"{path}\" has a malformed table."
      -- `u` strictly increasing from 0 to 2^32, `x` non-decreasing.
      let us := pts.map (·.1)
      let xs := pts.map (·.2)
      let incr := (us.zip us.tail).all (fun (a, b) => a < b)
      let nondec := (xs.zip xs.tail).all (fun (a, b) => a ≤ b)
      if us.head? != some 0 || us.getLast? != some two32 || !incr || !nondec then
        throw s!"Distribution \"{path}\" has a malformed table."
      pure (.table pts)
    | .str "choice" => do
      let vs ← match field o "values" with
        | .arr _ xs => mapIdx (fun i x => intIn x s!"{path}.values[{i}]" 0 (two53 - 1)) xs
        | _ => throw s!"Distribution \"{path}\" must have \"values\"."
      if vs.isEmpty then throw s!"Distribution \"{path}\" must have \"values\"."
      pure (.choice vs)
    | _ => .error s!"Distribution \"{path}\" has an unknown kind."
  | _ => .error s!"Field \"{path}\" must be an integer or a distribution."

def effect (v : Value) (what : String) : R Effect :=
  match v with
  | .obj _ fx =>
    if objHas fx "set" then do
      let varName ← string fx "set" what
      match field fx "to" with
      | .obj _ o =>
        if objHas o "sample" then pure (.sample varName (← dist (field o "sample") s!"{what}.to.sample"))
        else pure (.set varName (some (field fx "to")))
      | .undef => pure (.set varName none)
      | other => pure (.set varName (some other))
    else if objHas fx "emit" then do
      let after ← match field fx "after" with
        | .undef | .null => pure (.fixed 0)
        | x => dist x s!"{what}.after"
      let payload ← payloadObj fx what
      let event ← string fx "emit" what
      let reply ← match field fx "target" with
        | .undef | .null => pure false
        | .str "reply" => pure true
        | _ => throw s!"{what}: \"target\" must be \"reply\"."
      pure (.emit event after payload reply)
    else if objHas fx "use" || objHas fx "acquire" then do
      let kind := if objHas fx "use" then Res.ReqKind.use else .acquire
      let res ← string fx (if kind == .use then "use" else "acquire") what
      let cls ← optStr fx "class" what
      let units ← intOr fx "units" s!"{what}.units" 1 (two32 - 1) 1
      let demand ← if kind == .use then dist (field fx "demand") s!"{what}.demand" else pure (.fixed 0)
      let thenEv ← string fx "then" what
      let refused ← optStr fx "refused" what
      let payload ← payloadObj fx what
      pure (.request kind res cls units demand thenEv refused payload)
    else if objHas fx "release" then do
      let res ← string fx "release" what
      let cls ← optStr fx "class" what
      let units ← intOr fx "units" s!"{what}.units" 1 (two32 - 1) 1
      pure (.release res cls units)
    else .ok .malformed
  | _ => .ok .malformed

def transition (v : Value) (what : String) : R TransitionIn := do
  let t ← object v what
  let effects ← mapIdx (fun k fx => effect fx s!"{what}.effects[{k}]") (arrayOrEmpty t "effects")
  let id ← string t "id" what
  let source ← string t "from" what
  let target ← string t "to" what
  let on ← string t "on" what
  let guard := match field t "guard" with
    | .str s => some s
    | _ => none
  let faultOnly := match field t "faultOnly" with
    | .bool true => true
    | _ => false
  pure { id, source, target, on, guard, effects, faultOnly }

def behavior (v : Value) (i : Nat) : R BehaviorIn := do
  let what := s!"behaviors[{i}]"
  let b ← object v what
  let id ← string b "id" what
  let variables ← mapIdx (fun j var => do
      let vw := s!"{what}.variables[{j}]"
      let o ← object var vw
      let name ← string o "name" vw
      pure { name, initial := field o "initial" : VariableIn })
    (arrayOrEmpty b "variables")
  let transitions ← mapIdx (fun j t => transition t s!"{what}.transitions[{j}]")
    (arrayOrEmpty b "transitions")
  let subject := (field b "subject").asString?
  let initial ← string b "initial" what
  let instances ← match field b "instances" with
    | .undef | .null => pure Instances.single
    | .obj _ o =>
      if objHas o "key" then do
        let key ← string o "key" s!"{what}.instances"
        let max ← intIn (field o "max") s!"{what}.instances.max" 0 (two32 - 1)
        pure (.keyed key max)
      else (intIn (field o "count") s!"{what}.instances.count" 0 (two32 - 1)).map .count
    | _ => throw s!"{what}: \"instances\" must be an object."
  pure { id, subject, initial, variables, transitions, instances }

def fault (v : Value) (i : Nat) : R FaultIn := do
  let what := s!"faults[{i}]"
  let f ← object v what
  let kind ← optStr f "kind" what
  if f.any (·.1 == "window") then throw s!"{what}: windowed faults are not implemented (WG-4664)."
  match kind with
  | some k =>
    if ["scale-demand", "set-capacity", "set-class-limit", "collapse-classes", "replace-demand",
        "crash-instance"].contains k then
      throw s!"{what}: fault kind \"{k}\" is not implemented (WG-4664)."
  | none => pure ()
  let occurrence := match field f "occurrence" with
    | .undef => Occurrence.any
    | .num n => .exactly n
    | _ => .never
  let delayBy ← if kind == some "delay-event" then intIn (field f "by") s!"{what}.by" 0 (two53 - 1) else pure 0
  let injectAt ← if kind == some "inject-event" then intIn (field f "at") s!"{what}.at" 0 (two53 - 1) else pure 0
  let id ← string f "id" what
  let event ← optStr f "event" what
  let transition ← optStr f "transition" what
  pure { id, kind, event, transition, occurrence, delayBy, injectAt,
         payload := payloadOrEmpty (field f "payload") }

def route (v : Value) (i : Nat) : R RouteIn := do
  let what := s!"routes[{i}]"
  let o ← object v what
  let event ← string o "event" what
  let behavior ← string o "behavior" what
  let by_ ← string o "by" what
  if !["key", "round-robin", "random", "any", "least-busy"].contains by_ then
    throw s!"{what}: \"by\" must be key, round-robin, random, any or least-busy."
  let field ← optStr o "field" what
  let resource ← optStr o "resource" what
  pure { event, behavior, rby := by_, field, resource }

def resource (v : Value) (i : Nat) : R ResourceDecl := do
  let what := s!"resources[{i}]"
  let o ← object v what
  let id ← string o "id" what
  let kind := ((field o "kind").asString?).getD "pool"
  let capacity ← intIn (field o "capacity") s!"{what}.capacity" 1 (two32 - 1)
  let byPriority ← match field o "discipline" with
    | .undef | .null | .str "fifo" => pure false
    | .str "priority" => pure true
    | _ => throw s!"{what}: \"discipline\" must be fifo or priority."
  let queueBound ← optInt o "queueBound" s!"{what}.queueBound" 0 (two32 - 1)
  let overflow ← match field o "overflow" with
    | .undef | .null | .str "refuse" => pure Res.Overflow.refuse
    | .str "drop" => pure .drop
    | .str "shed-oldest" => pure .shedOldest
    | _ => throw s!"{what}: \"overflow\" must be refuse, drop or shed-oldest."
  let demandFactor ← match field o "demandFactor" with
    | .undef | .null => pure Res.DemandFactor.none
    | .arr _ rows => do
      let rs ← mapIdx (fun j r => match r with
        | .arr _ [n, num, den] => do
          let p := s!"{what}.demandFactor[{j}]"
          pure (← intIn n s!"{p}[0]" 0 (two32 - 1), ← intIn num s!"{p}[1]" 0 (two32 - 1),
                ← intIn den s!"{p}[2]" 1 (two32 - 1))
        | _ => throw s!"{what}: malformed \"demandFactor\".") rows
      let ns := rs.map (·.1)
      if ns.head? != some 0 || !(ns.zip ns.tail).all (fun (a, b) => a < b) then
        throw s!"{what}: malformed \"demandFactor\"."
      pure (.table rs)
    | .obj _ u =>
      match field u "usl" with
      | .obj _ p =>
        let rat (k : String) : R (Nat × Nat) := match field p k with
          | .arr _ [a, b] => do
            pure (← intIn a s!"{what}.demandFactor.usl.{k}[0]" 0 (two32 - 1),
                  ← intIn b s!"{what}.demandFactor.usl.{k}[1]" 1 (two32 - 1))
          | _ => throw s!"{what}: malformed \"demandFactor\"."
        do
          let (an, ad) ← rat "alpha"
          let (bn, bd) ← rat "beta"
          pure (.usl an ad bn bd)
      | _ => throw s!"{what}: malformed \"demandFactor\"."
    | _ => throw s!"{what}: malformed \"demandFactor\"."
  let classes ← match field o "classes" with
    | .arr _ (c :: cs) => mapIdx (fun j c => do
        let cw := s!"{what}.classes[{j}]"
        let co ← object c cw
        let cid ← string co "id" cw
        let priority ← match field co "priority" with
          | .undef | .null => pure (0 : Int)
          | .num x =>
            if x.floor == x && x.abs < 4294967296 then
              pure (if x < 0 then -((-x).toUInt64.toNat : Int) else (x.toUInt64.toNat : Int))
            else throw s!"Field \"{cw}.priority\" must be an integer in [-4294967295, 4294967295]."
          | _ => throw s!"Field \"{cw}.priority\" must be an integer in [-4294967295, 4294967295]."
        let reserved ← intOr co "reserved" s!"{cw}.reserved" 0 (two32 - 1) 0
        let limit ← optInt co "limit" s!"{cw}.limit" 1 (two32 - 1)
        let qb ← optInt co "queueBound" s!"{cw}.queueBound" 0 (two32 - 1)
        let maxWait ← optInt co "maxWait" s!"{cw}.maxWait" 0 (two53 - 1)
        pure { id := cid, priority, reserved, limit, queueBound := qb, maxWait : ClassDecl }) (c :: cs)
    | _ => pure [{ id := "default", priority := 0, reserved := 0, limit := none, queueBound := none,
                   maxWait := none }]
  pure { id, kind, capacity, byPriority, queueBound, overflow, demandFactor, classes }

def units : List (String × Option Nat) :=
  [("tick", none), ("s", some 1), ("ms", some 1000), ("us", some 1000000), ("ns", some 1000000000)]

/-- A decimal seed: digits only, no leading zeros, below 2^64. -/
def seed (v : Value) : R (Option UInt64) :=
  let err := "Field \"scenario.seed\" must be a decimal string in [0, 18446744073709551615]."
  match v with
  | .undef | .null => .ok none
  | .str s =>
    let cs := s.toList
    if cs.isEmpty || !cs.all Char.isDigit || (cs.length > 1 && cs.head? == some '0') then .error err
    else
      let n := cs.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
      if n < 2 ^ 64 then .ok (some n.toUInt64) else .error err
  | _ => .error err

/-- Decode a parsed version-2 engine input (format and version already checked). -/
def input (root : List (String × Value)) : R Input := do
  let (unit, perSecond) ← match field root "time" with
    | .obj _ t =>
      match field t "unit" with
      | .str u => match units.find? (·.1 == u) with
        | some (_, ps) => pure (u, ps)
        | none => throw s!"Unknown time unit \"{u}\"."
      | _ => throw "Unknown time unit \"undefined\"."
    | _ => throw "Unknown time unit \"undefined\"."
  for k in ["links", "workloads", "requests", "meters", "prices"] do
    match field root k with
    | .arr _ (_ :: _) => throw s!"Input field \"{k}\" is not implemented by this engine (WG-4715)."
    | _ => pure ()
  let events ← mapIdx (fun i e => do
      let o ← object e s!"events[{i}]"
      string o "id" s!"events[{i}]")
    (← array root "events" "input")
  let behaviors ← mapIdx (fun i b => behavior b i) (← array root "behaviors" "input")
  let faults ← mapIdx (fun i f => fault f i) (← array root "faults" "input")
  let routes ← mapIdx (fun i r => route r i) (arrayOrEmpty root "routes")
  let resources ← mapIdx (fun i r => resource r i) (arrayOrEmpty root "resources")
  let sc ← object (field root "scenario") "scenario"
  let id ← string sc "id" "scenario"
  let steps ← mapIdx (fun i st => do
      let what := s!"scenario.steps[{i}]"
      let o ← object st what
      let time ← intIn (field o "at") s!"{what}.at" 0 (two53 - 1)
      let event ← string o "event" what
      let target ← match field o "target" with
        | .obj _ t => do
          let b ← string t "behavior" s!"{what}.target"
          pure (some (b, field t "instance"))
        | _ => pure none
      pure { time, event, payload := payloadOrEmpty (field o "payload"), target : StepIn })
    (← array sc "steps" "scenario")
  let faultIds ← match field sc "faults" with
    | .arr _ xs => xs.mapM fun
        | .str s => pure s
        | _ => throw "scenario.faults must hold strings."
    | x => if x.isNullish then pure [] else throw "scenario: \"faults\" must be an array."
  let stepLimit ← intOr sc "stepLimit" "scenario.stepLimit" 1 (two53 - 1) 1000
  let seed ← seed (field sc "seed")
  let horizon ← optInt sc "horizon" "scenario.horizon" 0 (two53 - 1)
  let warmup ← optInt sc "warmup" "scenario.warmup" 0 (two53 - 1)
  let stopAt ← optInt sc "stopAt" "scenario.stopAt" 0 (two53 - 1)
  let output := ((field sc "output").asString?).getD "trace"
  pure { unit, perSecond, behaviors, events, faults, routes, resources,
         scenario := { id, steps, faults := faultIds, stepLimit, seed, horizon, warmup, stopAt, output } }

end Decode

/-! ## Static environment -/

def Input.behavior? (i : Input) (id : String) : Option BehaviorIn :=
  if i.events.contains id && !(i.behaviors.any (·.id == id)) then none
  else i.behaviors.find? (·.id == id)

def Input.isEvent (i : Input) (id : String) : Bool :=
  i.events.contains id && !(i.behaviors.any (·.id == id)) && !(i.faults.any (·.id == id)) &&
    i.scenario.id != id

def Input.fault? (i : Input) (id : String) : Option FaultIn := i.faults.find? (·.id == id)

def Input.resource? (i : Input) (id : String) : Option ResourceDecl := i.resources.find? (·.id == id)

def Input.route? (i : Input) (ev b : String) : Option RouteIn :=
  i.routes.find? fun r => r.event == ev && r.behavior == b

/-- The class index of an effect's `class` (the only class when omitted). -/
def classIndex (d : ResourceDecl) : Option String → Option Nat
  | some c => d.classes.findIdx? (·.id == c)
  | none => if d.classes.length == 1 then some 0 else none

structure Env where
  input : Input
  behaviors : List BehaviorIn
  faultIds : List String
  faults : List FaultIn

def envOf (i : Input) : Env where
  input := i
  behaviors := i.behaviors
  faultIds := dedup i.scenario.faults
  faults := (dedup i.scenario.faults).filterMap i.fault?

/-! ## Configuration -/

/-- An instance address. -/
structure Addr where
  behavior : String
  inst : Value
  incarnation : Nat
  deriving Inhabited

inductive Src where
  | scenario (step : Nat)
  | fault (fault : String)
  | transition (transition behavior : String)
  | resource (res : String) (request : Nat) (outcome : String)
  deriving Inhabited

/-- What a request needs to be answered. -/
structure ReqInfo where
  requester : Addr
  requesterKey : String
  thenEv : String
  refused : Option String
  payload : List (String × Value)
  demand : Dist
  stream : String
  deriving Inhabited

inductive EntryKind where
  | event
  | serviceDone (res : String) (r : Req ReqInfo) (waited served : Nat)
  | waitTimeout (res : String) (request : Nat)
  deriving Inhabited

structure Entry where
  seq : Nat
  time : Nat
  scheduledAt : Nat
  event : String
  payload : Value
  source : Src
  kind : EntryKind
  target : Option Addr
  sender : Option Addr
  /-- The routed instances, decided when first taken as head. -/
  routes : Option (List (String × Value))
  deriving Inhabited

structure Conf where
  time : Nat
  machines : List (String × Machine)
  /-- Behavior id ↦ its instances, in index or creation order. -/
  insts : List (String × List Value)
  pending : List Entry
  resources : List (String × RState ReqInfo)
  routeCounters : List (String × Nat)
  streams : List (String × Nat)
  deriving Inhabited

instance : Inhabited (RState ReqInfo) := ⟨{ capacity := 0, holds := [], waiting := [] }⟩

def Conf.machine? (c : Conf) (k : String) : Option Machine := (c.machines.find? (·.1 == k)).map (·.2)

def Conf.setMachine (c : Conf) (k : String) (m : Machine) : Conf :=
  if c.machines.any (·.1 == k) then
    { c with machines := c.machines.map fun (k', x) => if k' == k then (k', m) else (k', x) }
  else { c with machines := c.machines ++ [(k, m)] }

def Conf.instsOf (c : Conf) (b : String) : List Value := ((c.insts.find? (·.1 == b)).map (·.2)).getD []

def Conf.resource? (c : Conf) (r : String) : Option (RState ReqInfo) :=
  (c.resources.find? (·.1 == r)).map (·.2)

def Conf.setResource (c : Conf) (r : String) (s : RState ReqInfo) : Conf :=
  { c with resources := c.resources.map fun (k, x) => if k == r then (k, s) else (k, x) }

def lookup (xs : List (String × Nat)) (k : String) : Nat := ((xs.find? (·.1 == k)).map (·.2)).getD 0

def bump (xs : List (String × Nat)) (k : String) : List (String × Nat) :=
  if xs.any (·.1 == k) then xs.map fun (k', n) => if k' == k then (k', n + 1) else (k', n)
  else xs ++ [(k, 1)]

/-- The machine key of an instance. -/
def machineKey (b : BehaviorIn) (inst : Value) : String :=
  match b.instances with
  | .single => b.id
  | _ => b.id ++ "#" ++ Json.write inst

def insertE (q : List Entry) (e : Entry) : List Entry :=
  let later := (q.reverse.takeWhile fun p => decide (p.time > e.time)).length
  let pos := q.length - later
  q.take pos ++ [e] ++ q.drop pos

def initialMachine (b : BehaviorIn) : Machine :=
  { state := b.initial, vars := b.variables.foldl (fun vs v => objInsert vs v.name v.initial) [] }

/-! ## Records -/

structure Draw where
  stream : String
  index : Nat
  value : UInt64
  deriving Inhabited

structure ResRecord where
  resource : String
  cls : String
  request : Option Nat
  action : String
  atTime : Nat
  waited : Option Nat
  served : Option Nat
  reason : Option String
  units : Option Nat
  deriving Inhabited

structure Fired2 where
  base : Fired
  inst : Value
  deriving Inhabited

structure Ignored2 where
  base : Ignored
  inst : Option Value
  deriving Inhabited

inductive Kind2 where
  | deliver | drop | delay | serviceDone | waitTimeout
  deriving Inhabited, DecidableEq

def Kind2.name : Kind2 → String
  | .deliver => "deliver" | .drop => "drop" | .delay => "delay"
  | .serviceDone => "service-done" | .waitTimeout => "wait-timeout"

structure Step2 where
  index : Nat
  time : Nat
  kind : Kind2
  head : Entry
  fired : List Fired2
  ignored : List Ignored2
  faults : List FaultRecord
  responsible : List String
  resources : List ResRecord
  draws : List Draw
  config : Conf
  error : Option String
  deriving Inhabited

/-! ## Draws -/

/-- Draw the next value of a stream (the seed is present: inputs that draw without one are
refused). Returns the value, the draw record and the next counters. -/
def drawNext (seed : UInt64) (streams : List (String × Nat)) (name : String) :
    UInt64 × Draw × List (String × Nat) :=
  let i := lookup streams name
  let r := Random.draw seed name i
  (r, { stream := name, index := i, value := r }, bump streams name)

/-- Sample a distribution from a stream. `choice` without a seed takes its first value. -/
def sample (seed : Option UInt64) (streams : List (String × Nat)) (name : String) (d : Dist) :
    Nat × List Draw × List (String × Nat) :=
  match d, seed with
  | .fixed v, _ => (v, [], streams)
  | .choice vs, none => (vs.headD 0, [], streams)
  | .choice vs, some s =>
    let (r, dr, st) := drawNext s streams name
    (vs.getD (Random.index r vs.length) 0, [dr], st)
  | .uniform lo hi, some s =>
    let (r, dr, st) := drawNext s streams name
    (Random.uniformInt r lo hi, [dr], st)
  | .table pts, some s =>
    let (r, dr, st) := drawNext s streams name
    (Random.sampleTable r pts, [dr], st)
  | _, none => (0, [], streams)

/-! ## Expressions -/

def refsOf : Ast → List (List String)
  | .lit _ => []
  | .ref p => [p]
  | .un _ a => refsOf a
  | .bin _ a b => refsOf a ++ refsOf b

def numsOf (path : String) (vs : List Value) : Except String (List Float) :=
  vs.mapM fun
    | .num x => .ok x
    | v => .error s!"Aggregate \"{path}\" needs numbers, got {v.typeName}."

/-- Resolve a reference in the scope of the instance with machine key `mk`. `view` gives
variables, states and aggregates; `start` the start-of-step configuration, from which resources
are read. -/
def resolve (env : Env) (view start : Conf) (mk : String) (inst : Value) (payload : Value)
    (time : Nat) (path : List String) : Except String Value :=
  let i := env.input
  let joined := ".".intercalate path
  let machinesOf (b : BehaviorIn) : List Machine :=
    (view.instsOf b.id).filterMap fun v => view.machine? (machineKey b v)
  match path with
  | ["time"] => .ok (.num time.toFloat)
  | ["instance"] => .ok inst
  | [name] => .ok (((view.machine? mk).bind fun m => objGet? m.vars name).getD .undef)
  | ["event", f] => .ok (match payload with
    | .obj _ fs => (objGet? fs f).getD .undef
    | _ => .undef)
  | [r, "inUse"] =>
    match start.resource? r with
    | some s => .ok (.num (Res.heldAll s.holds).toFloat)
    | none => .ok .undef
  | [r, "waiting"] =>
    match start.resource? r with
    | some s => .ok (.num s.waiting.length.toFloat)
    | none => .ok .undef
  | [r, "inUse", c] | [r, "waiting", c] =>
    match start.resource? r, i.resource? r with
    | some s, some d =>
      match d.classes.findIdx? (·.id == c) with
      | some k => .ok (.num (if path[1]! == "inUse" then Res.heldC s.holds k
                             else Res.waitingC s.waiting k).toFloat)
      | none => .ok .undef
    | _, _ => .ok .undef
  | [b, name] =>
    match i.behavior? b with
    | none => .ok .undef
    | some bd =>
      let ks := view.instsOf b
      if ks.length > 1 then .error s!"Reference \"{joined}\" is ambiguous: \"{b}\" has {ks.length} instances."
      else match ks.head? >>= fun v => view.machine? (machineKey bd v) with
        | none => .ok .undef
        | some m => .ok (if name == "state" then .str m.state else (objGet? m.vars name).getD .undef)
  | [b, "instances", "count"] =>
    match i.behavior? b with
    | some bd => match bd.instances with
      | .single => .ok .undef
      | _ => .ok (.num (view.instsOf b).length.toFloat)
    | none => .ok .undef
  | [b, agg, x] =>
    match i.behavior? b with
    | none => .ok .undef
    | some bd =>
      match bd.instances with
      | .single => .ok .undef
      | _ =>
        let ms := machinesOf bd
        if agg == "count" then .ok (.num (ms.filter (·.state == x)).length.toFloat)
        else if agg == "sum" || agg == "min" || agg == "max" then do
          let ns ← numsOf joined (ms.map fun m => (objGet? m.vars x).getD .undef)
          match agg, ns with
          | "sum", _ => pure (.num (ns.foldl (· + ·) 0))
          | _, [] => pure .null
          | "min", n :: rest => pure (.num (rest.foldl (fun a b => if b < a then b else a) n))
          | _, n :: rest => pure (.num (rest.foldl (fun a b => if b > a then b else a) n))
        else .ok .undef
  | _ => .ok .undef

/-- Evaluate an expression: references are resolved first, in the order they appear, so a failed
resolution (an ambiguous reference, an aggregate over non-numbers) ends the step before any
evaluation error. -/
def evalIn (env : Env) (src : String) (view start : Conf) (mk : String) (inst payload : Value)
    (time : Nat) : Except String Value := do
  let ast ← compile src
  for p in refsOf ast do
    let _ ← resolve env view start mk inst payload time p
  eval (fun p => match resolve env view start mk inst payload time p with
    | .ok v => v
    | .error _ => .undef) ast

def valueOf (env : Env) (x : Option Value) (view start : Conf) (mk : String) (inst payload : Value)
    (time : Nat) (nid : Nat) : Except String (Value × Nat) :=
  match x with
  | none => .error "Effect has no value."
  | some (.str src) => (evalIn env src view start mk inst payload time).map fun v => (v, nid)
  | some v => .ok (v.copy nid)

def guardHolds (env : Env) (t : TransitionIn) (view : Conf) (mk : String) (inst payload : Value)
    (time : Nat) : Except String Bool :=
  match t.guard with
  | none => .ok true
  | some g => match evalIn env g view view mk inst payload time with
    | .error e => .error e
    | .ok (.bool b) => .ok b
    | .ok _ => .error s!"Guard \"{g}\" of transition \"{t.id}\" did not evaluate to a boolean."

/-! ## Phase 1 -/

def targeting (faults : List FaultIn) (kind tid : String) : List FaultIn :=
  faults.filter fun f => f.isKind kind && f.transition == some tid

/-- Scan one instance's transitions (as `Exegra.scan`). -/
def scan (env : Env) (cur : Conf) (mk : String) (inst : Value) (state : Option String)
    (event : String) (payload : Value) (time : Nat) :
    List TransitionIn → List String → Bool → Bool → List FaultRecord →
    Except String (Option (TransitionIn × List FaultIn) × List String × Bool × Bool × List FaultRecord)
  | [], considered, dis, gf, recs => .ok (none, considered, dis, gf, recs)
  | t :: ts, considered, dis, gf, recs =>
    if some t.source != state || t.on != event then
      scan env cur mk inst state event payload time ts considered dis gf recs
    else
      let enablers := targeting env.faults "enable-transition" t.id
      if t.faultOnly && enablers.isEmpty then
        scan env cur mk inst state event payload time ts considered dis gf recs
      else
        let considered := considered ++ [t.id]
        let disablers := targeting env.faults "disable-transition" t.id
        match guardHolds env t cur mk inst payload time with
        | .error e => .error e
        | .ok false => scan env cur mk inst state event payload time ts considered dis true recs
        | .ok true =>
          if !disablers.isEmpty then
            scan env cur mk inst state event payload time ts considered true gf
              (recs ++ disablers.map fun d => { fault := d.id, effect := .disabled })
          else
            .ok (some (t, if t.faultOnly then enablers else []), considered, dis, gf, recs)

/-- A winner of phase 1: behavior, instance, machine key, transition. -/
structure Winner where
  b : BehaviorIn
  inst : Value
  key : String
  t : TransitionIn

def chooseInst (env : Env) (cur : Conf) (b : BehaviorIn) (inst : Value) (event : String)
    (payload : Value) (time : Nat) :
    Except String (Option Winner × Option Ignored2 × List FaultRecord) :=
  let mk := machineKey b inst
  let state := (cur.machine? mk).map (·.state)
  match scan env cur mk inst state event payload time b.transitions [] false false [] with
  | .error e => .error e
  | .ok (some (t, enablers), _, _, _, recs) =>
    .ok (some { b, inst, key := mk, t }, none, recs ++ enablers.map fun e => { fault := e.id, effect := .enabled })
  | .ok (none, considered, dis, gf, recs) =>
    let reason := if dis then IgnoredReason.disabled else if gf then .guardFalse else .noTransition
    .ok (none, some { base := { behavior := b.id, reason, considered }, inst := some inst }, recs)

/-- The instances of `b` an entry addresses. `none`: the behavior is not addressed at all. -/
def addressed (cur : Conf) (head : Entry) (b : BehaviorIn) : Option (List Value) :=
  match head.target with
  | some a => if a.behavior == b.id then
      some (if (cur.instsOf b.id).any (fun v => Json.write v == Json.write a.inst) then [a.inst] else []) else none
  | none =>
    match head.routes.bind fun rs => rs.find? (·.1 == b.id) with
    | some (_, v) => some [v]
    | none => some (cur.instsOf b.id)

def chooseAll (env : Env) (cur : Conf) (head : Entry) :
    List BehaviorIn → Except String (List Winner × List Ignored2 × List FaultRecord)
  | [] => .ok ([], [], [])
  | b :: bs => do
    let (ws, igs, recs) ← match addressed cur head b with
      | none => pure ([], [], [])
      | some [] => pure ([], [{ base := { behavior := b.id, reason := .noTransition, considered := [] },
                                inst := none }], [])
      | some insts => insts.foldlM (fun (ws, igs, recs) inst => do
          let (w, ig, r) ← chooseInst env cur b inst head.event head.payload head.time
          pure (ws ++ w.toList, igs ++ ig.toList, recs ++ r)) ([], [], [])
    let (ws', igs', recs') ← chooseAll env cur head bs
    pure (ws ++ ws', igs ++ igs', recs ++ recs')

/-! ## Phase 2 -/

/-- A resource operation recorded in phase 2. -/
inductive Op where
  | req (r : Req ReqInfo) (maxWait : Option Nat)
  | release (owner : String) (cls : Nat) (units : Nat)
  deriving Inhabited

structure FireState where
  next : Conf
  seq : Nat
  nid : Nat
  draws : List Draw
  ops : List (String × Op)

def two53 : Nat := 9007199254740992

def evalEntries (env : Env) (view start : Conf) (mk : String) (inst payload : Value) (time : Nat) :
    List (String × Value) → List (String × Value) → Nat → Except String (List (String × Value) × Nat)
  | [], acc, nid => .ok (acc, nid)
  | (k, v) :: rest, acc, nid =>
    match valueOf env (some v) view start mk inst payload time nid with
    | .error e => .error e
    | .ok (x, nid) => evalEntries env view start mk inst payload time rest (objInsert acc k x) nid

def runEffects (env : Env) (start : Conf) (head : Entry) (w : Winner) :
    Nat → List Effect → FireState → List SetRecord → List EmitRecord →
    Except String (FireState × List SetRecord × List EmitRecord)
  | _, [], s, sets, emits => .ok (s, sets, emits)
  | k, e :: rest, s, sets, emits =>
    let site := s!"{w.b.id}:{w.t.id}:{k}"
    let time := head.time
    match e with
    | .set varName to =>
      match s.next.machine? w.key with
      | none => .error s!"Effect sets \"{varName}\", which is not a variable of \"{w.b.id}\"."
      | some m =>
        if !objHas m.vars varName then
          .error s!"Effect sets \"{varName}\", which is not a variable of \"{w.b.id}\"."
        else
          match valueOf env to s.next start w.key w.inst head.payload time s.nid with
          | .error e => .error e
          | .ok (value, nid) =>
            let before := (objGet? m.vars varName).getD .undef
            let next := s.next.setMachine w.key { m with vars := objSet m.vars varName value }
            runEffects env start head w (k + 1) rest { s with next, nid }
              (sets ++ [{ varName, before, after := value }]) emits
    | .sample varName d =>
      match s.next.machine? w.key with
      | none => .error s!"Effect sets \"{varName}\", which is not a variable of \"{w.b.id}\"."
      | some m =>
        if !objHas m.vars varName then
          .error s!"Effect sets \"{varName}\", which is not a variable of \"{w.b.id}\"."
        else
          let (x, drs, streams) := sample env.input.scenario.seed s.next.streams s!"sample:{site}" d
          let value := Value.num x.toFloat
          let before := (objGet? m.vars varName).getD .undef
          let next := { s.next.setMachine w.key { m with vars := objSet m.vars varName value } with streams }
          runEffects env start head w (k + 1) rest { s with next, draws := s.draws ++ drs }
            (sets ++ [{ varName, before, after := value }]) emits
    | .emit event after entries reply =>
      if !env.input.isEvent event then .error s!"Effect emits \"{event}\", which is not an event."
      else
        let (delay, drs, streams) := sample env.input.scenario.seed s.next.streams s!"after:{site}" after
        let atTime := s.next.time + delay
        if atTime ≥ two53 then .error "Value time exceeds 2^53." else
        match evalEntries env s.next start w.key w.inst head.payload time entries [] s.nid with
        | .error e => .error e
        | .ok (fs, nid) =>
          match (if reply then
              match head.sender with
              | some a => .ok (some a)
              | none => .error s!"Effect replies to \"{head.event}\", which has no requester."
            else .ok none : Except String (Option Addr)) with
          | .error e => .error e
          | .ok target =>
          let pv : Value := .obj nid fs
          let entry : Entry :=
            { seq := s.seq, time := atTime, scheduledAt := atTime, event, payload := pv,
              source := .transition w.t.id w.b.id, kind := .event, target,
              sender := some { behavior := w.b.id, inst := w.inst, incarnation := 0 }, routes := none }
          let next := { s.next with pending := insertE s.next.pending entry, streams }
          runEffects env start head w (k + 1) rest
            { s with next, seq := s.seq + 1, nid := nid + 1, draws := s.draws ++ drs } sets
            (emits ++ [{ event, time := atTime.toFloat, seq := s.seq, payload := pv }])
    | .request kind res cls units demand thenEv refused entries =>
      match env.input.resource? res with
      | none => .error s!"Effect uses \"{res}\", which is not a resource."
      | some d =>
        match classIndex d cls with
        | none => .error s!"Effect names no class of \"{res}\"."
        | some ci =>
          match evalEntries env s.next start w.key w.inst head.payload time entries [] s.nid with
          | .error e => .error e
          | .ok (fs, nid) =>
            let info : ReqInfo :=
              { requester := { behavior := w.b.id, inst := w.inst, incarnation := 0 },
                requesterKey := w.key, thenEv, refused, payload := fs, demand,
                stream := s!"demand:{site}" }
            let r : Req ReqInfo :=
              { id := 0, owner := w.key, cls := ci, units, since := time, kind, info }
            runEffects env start head w (k + 1) rest
              { s with nid, ops := s.ops ++ [(res, .req r ((d.classAt? ci).bind (·.maxWait)))] } sets emits
    | .release res cls units =>
      match env.input.resource? res with
      | none => .error s!"Effect releases \"{res}\", which is not a resource."
      | some d =>
        match classIndex d cls with
        | none => .error s!"Effect names no class of \"{res}\"."
        | some ci =>
          runEffects env start head w (k + 1) rest
            { s with ops := s.ops ++ [(res, .release w.key ci units)] } sets emits
    | .malformed => .error s!"Malformed effect in transition \"{w.t.id}\"."

def fireOne (env : Env) (start : Conf) (head : Entry) (w : Winner) (s : FireState) :
    Except String (Fired2 × FireState) := do
  let (s, sets, emitted) ← runEffects env start head w 0 w.t.effects s [] []
  let next := match s.next.machine? w.key with
    | some m => s.next.setMachine w.key { m with state := w.t.target }
    | none => s.next
  pure ({ base := { behavior := w.b.id, transition := w.t.id, source := w.t.source,
                    target := w.t.target, guard := w.t.guard, sets, emitted },
          inst := w.inst }, { s with next })

def fireAll (env : Env) (start : Conf) (head : Entry) :
    List Winner → FireState → Except String (List Fired2 × FireState)
  | [], s => .ok ([], s)
  | w :: ws, s => do
    let (f, s) ← fireOne env start head w s
    let (fs, s) ← fireAll env start head ws s
    pure (f :: fs, s)

/-! ## Settling -/

structure Settle where
  conf : Conf
  seq : Nat
  nid : Nat
  draws : List Draw
  recs : List ResRecord

def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

def removeTimeout (res : String) (rid : Nat) (q : List Entry) : List Entry :=
  q.filter fun e => match e.kind with
    | .waitTimeout r i => !(r == res && i == rid)
    | _ => true

def classId (d : ResourceDecl) (c : Nat) : String := ((d.classAt? c).map (·.id)).getD "default"

/-- The `then` or `refused` entry answering a request, targeted at its requester. -/
def answer (st : Settle) (res : String) (d : ResourceDecl) (r : Req ReqInfo) (event : String)
    (outcome : String) (extra : List (String × Value)) : Settle :=
  -- ORDER: the effect's payload, then `resource`, `class` and the extra fields, each set as
  -- `o[k] = v` (a payload field of the same name is overwritten in place).
  let fs := ([("resource", Value.str res), ("class", .str (classId d r.cls))] ++ extra).foldl
    (fun acc (k, v) => objInsert acc k v) r.info.payload
  let (pv, nid) := (Value.obj st.nid fs, st.nid + 1)
  let e : Entry :=
    { seq := st.seq, time := st.conf.time, scheduledAt := st.conf.time, event, payload := pv,
      source := .resource res r.id outcome, kind := .event, target := some r.info.requester,
      sender := none, routes := none }
  { st with conf := { st.conf with pending := insertE st.conf.pending e }, seq := st.seq + 1, nid }

def resRec (res : String) (d : ResourceDecl) (r : Req ReqInfo) (action : String) (atTime : Nat) : ResRecord :=
  { resource := res, cls := classId d r.cls, request := some r.id, action, atTime, waited := none,
    served := none, reason := none, units := none }

/-- Grant outcomes become entries and records, in grant order. -/
def applyGrants (env : Env) (res : String) (d : ResourceDecl) :
    List (Res.Out ReqInfo) → Settle → Except String Settle
  | [], st => .ok st
  | .granted r occ :: rest, st =>
    let now := st.conf.time
    let waited := now - r.since
    let q := removeTimeout res r.id st.conf.pending
    let st := { st with conf := { st.conf with pending := q } }
    match r.kind with
    | .use =>
      let (dd, drs, streams) := sample env.input.scenario.seed st.conf.streams r.info.stream r.info.demand
      let (num, den) := d.demandFactor.at occ
      let served := ceilDiv (dd * num) den
      if served ≥ two53 then .error s!"Value service time of \"{res}\" exceeds 2^53." else
      if now + served ≥ two53 then .error "Value time exceeds 2^53." else
      let e : Entry :=
        { seq := st.seq, time := now + served, scheduledAt := now + served, event := "",
          payload := .null, source := .resource res r.id "service-done",
          kind := .serviceDone res r waited served, target := none, sender := none, routes := none }
      applyGrants env res d rest
        { st with conf := { st.conf with pending := insertE st.conf.pending e, streams }, seq := st.seq + 1, draws := st.draws ++ drs, recs := st.recs ++ [{ resRec res d r "granted" now with waited := some waited }] }
    | .acquire =>
      let st := answer st res d r r.info.thenEv "granted" [("waited", .num waited.toFloat)]
      applyGrants env res d rest
        { st with recs := st.recs ++ [{ resRec res d r "granted" now with waited := some waited }] }
  | _ :: rest, st => applyGrants env res d rest st

/-- Requests removed at a bound, in removal order. -/
def applyRemoved (res : String) (d : ResourceDecl) : List (Req ReqInfo) → Settle → Settle
  | [], st => st
  | r :: rest, st =>
    let now := st.conf.time
    let st := { st with conf := { st.conf with pending := removeTimeout res r.id st.conf.pending } }
    let waited := now - r.since
    let (action, reason) := match d.overflow with
      | .refuse => ("refused", some "bound")
      | .drop => ("dropped", none)
      | .shedOldest => ("shed", some "shed")
    let st := match reason, r.info.refused with
      | some why, some ev =>
        answer st res d r ev "refused" [("waited", .num waited.toFloat), ("reason", .str why)]
      | _, _ => st
    applyRemoved res d rest
      { st with recs := st.recs ++ [{ resRec res d r action now with waited := some waited, reason }] }

/-- Settle one resource: releases, enqueues, grants, bounds. -/
def settleOne (env : Env) (res : String) (ops : List Op) (st : Settle) : Except String Settle := do
  let some d := env.input.resource? res | .ok st
  let some s := st.conf.resource? res | .ok st
  let now := st.conf.time
  -- 1. releases, in effect order
  let mut s := s
  let mut st := st
  for op in ops do
    if let .release owner c n := op then
      let held := Res.heldBy s.holds owner c
      if held < n then
        throw s!"Instance \"{owner}\" releases {n} units of \"{res}\" class \"{classId d c}\" but holds {held}."
      s := { s with holds := Res.consume owner c n s.holds }
      st := { st with recs := st.recs ++ [{ resource := res, cls := classId d c, request := none, action := "released", atTime := now, waited := none, served := none, reason := none, units := some n }] }
  -- 2. enqueues, in creation order
  for op in ops do
    if let .req r maxWait := op then
      let r := { r with id := st.seq }
      st := { st with seq := st.seq + 1 }
      s := { s with waiting := s.waiting ++ [r] }
      if let some mw := maxWait then
        if now + mw ≥ two53 then throw "Value time exceeds 2^53."
        let e : Entry :=
          { seq := st.seq, time := now + mw, scheduledAt := now + mw, event := "", payload := .null,
            source := .resource res r.id "wait-timeout", kind := .waitTimeout res r.id,
            target := none, sender := none, routes := none }
        st := { st with conf := { st.conf with pending := insertE st.conf.pending e }, seq := st.seq + 1 }
      st := { st with recs := st.recs ++ [resRec res d r "enqueued" now] }
  -- 3. grants
  let (s2, outs) := Res.grantLoop d s.waiting.length s []
  st := { st with conf := st.conf.setResource res s2 }
  st ← applyGrants env res d outs st
  -- 4. bounds
  let (ws, removed) := Res.bounds d s2.waiting
  st := { st with conf := st.conf.setResource res { s2 with waiting := ws } }
  pure (applyRemoved res d removed st)

/-- Settle every resource the step touched, in input order. -/
def settle (env : Env) (ops : List (String × Op)) (touched : List String) (st : Settle) :
    Except String Settle :=
  env.input.resources.foldlM (fun st d =>
    if touched.contains d.id || ops.any (·.1 == d.id) then
      settleOne env d.id ((ops.filter (·.1 == d.id)).map (·.2)) st
    else .ok st) st

/-! ## Routes -/

/-- Decide the routed instances of an entry first taken as head, creating keyed instances. -/
def decideRoutes (env : Env) (c : Conf) (head : Entry) :
    Except String (List (String × Value) × Conf × List Draw) :=
  env.behaviors.foldlM (fun (acc, c, drs) b =>
    match env.input.route? head.event b.id with
    | none => .ok (acc, c, drs)
    | some r =>
      let insts := c.instsOf b.id
      let ckey := s!"{r.event}:{r.behavior}"
      let stream := s!"route:{r.event}:{r.behavior}"
      match r.rby with
      | "key" =>
        let f := r.field.getD ""
        let v := match head.payload with
          | .obj _ fs => (objGet? fs f).getD .undef
          | _ => .undef
        if v matches .undef then
          .error s!"Route of \"{head.event}\" to \"{b.id}\" needs payload field \"{f}\"."
        else match b.instances with
          | .keyed _ max =>
            let key := (v.copy 0).1
            if insts.any (fun k => Json.write k == Json.write v) then
              .ok (acc ++ [(b.id, (insts.find? (fun k => Json.write k == Json.write v)).getD key)], c, drs)
            else if insts.length ≥ max then
              .error s!"Behavior \"{b.id}\" would exceed {max} instances."
            else
              let c := { c with insts := c.insts.map fun (k, xs) => if k == b.id then (k, xs ++ [key]) else (k, xs) }
              let c := c.setMachine (machineKey b key) (initialMachine b)
              .ok (acc ++ [(b.id, key)], c, drs)
          | _ =>
            if insts.isEmpty then .ok (acc, c, drs) else
            let h := Random.fnv1a64 (Json.write v)
            .ok (acc ++ [(b.id, insts.getD (h.toNat % insts.length) .null)], c, drs)
      | "round-robin" =>
        if insts.isEmpty then .ok (acc, c, drs) else
        let n := lookup c.routeCounters ckey
        .ok (acc ++ [(b.id, insts.getD (n % insts.length) .null)],
             { c with routeCounters := bump c.routeCounters ckey }, drs)
      | "least-busy" =>
        if insts.isEmpty then .ok (acc, c, drs) else
        let load (v : Value) : Nat :=
          match r.resource.bind c.resource? with
          | some s =>
            let mk := machineKey b v
            Res.sumUnits (fun h => h.owner == mk) s.holds + (s.waiting.filter (·.owner == mk)).length
          | none => 0
        let best := insts.foldl (fun acc v => match acc with
          | none => some v
          | some u => if load v < load u then some v else some u) none
        .ok (acc ++ [(b.id, best.getD .null)], c, drs)
      | _ =>
        -- random, any: a draw from the route's stream; `any` without a seed takes instance 0
        if insts.isEmpty then .ok (acc, c, drs) else
        match env.input.scenario.seed with
        | none => .ok (acc ++ [(b.id, insts.getD 0 .null)], c, drs)
        | some seed =>
          let (x, dr, streams) := drawNext seed c.streams stream
          .ok (acc ++ [(b.id, insts.getD (Random.index x insts.length) .null)], { c with streams }, drs ++ [dr]))
    ([], c, [])

/-! ## The step -/

structure Config where
  conf : Conf
  seq : Nat
  nid : Nat
  attempts : List (String × Nat)
  delayedBy : List (Nat × List String)
  taken : Nat

inductive StepResult where
  | idle
  | stopped
  | committed (rec : Step2) (next : Config)
  | failed (rec : Step2)

def blank (index : Nat) (head : Entry) (kind : Kind2) (config : Conf) : Step2 :=
  { index, time := head.time, kind, head, fired := [], ignored := [], faults := [], responsible := [],
    resources := [], draws := [], config, error := none }

def responsibleOf (i : Input) (event : String) (fired : List Fired2) (faults : List FaultRecord) :
    List String :=
  let add (acc : List String) (x : String) := if acc.contains x then acc else acc ++ [x]
  let acc := fired.foldl (fun acc w =>
    let acc := add (add acc w.base.transition) w.base.behavior
    match (i.behavior? w.base.behavior).bind (·.subject) with
    | some subj => add acc subj
    | none => acc) (if event == "" then [] else [event])
  faults.foldl (fun acc f => add acc f.fault) acc

def copyMachines : List (String × Machine) → Nat → List (String × Machine) × Nat
  | [], n => ([], n)
  | (id, m) :: ms, n =>
    let (vars, n1) := Value.copyFields m.vars n
    let (rest, n2) := copyMachines ms n1
    ((id, { m with vars }) :: rest, n2)

def copyPending : List Entry → Nat → List Entry × Nat
  | [], n => ([], n)
  | p :: ps, n =>
    let (payload, n1) := p.payload.copy n
    let (rest, n2) := copyPending ps n1
    ({ p with payload } :: rest, n2)

/-- The deep copy of a configuration (machines, then pending payloads), as in format 1. -/
def Conf.copy (c : Conf) (n : Nat) : Conf × Nat :=
  let (machines, n1) := copyMachines c.machines n
  let (pending, n2) := copyPending c.pending n1
  ({ c with machines, pending }, n2)

def attemptOf (c : Config) (ev : String) : Nat := (lookupNat c.attempts ev).getD 0 + 1

def faultMatches (kind ev : String) (attempt : Nat) (f : FaultIn) : Bool :=
  f.isKind kind && f.event == some ev && f.occurrence.matches attempt

def injectedOf : Src → List FaultRecord
  | .fault f => [{ fault := f, effect := .injected }]
  | _ => []

/-- A step that ends with settling: the records and the next semantic configuration. -/
def finish (env : Env) (c : Config) (head : Entry) (kind : Kind2) (fired : List Fired2)
    (ignored : List Ignored2) (faults : List FaultRecord) (draws : List Draw) (ops : List (String × Op))
    (touched : List String) (st : Settle) (attempts : List (String × Nat)) (pre : List ResRecord) :
    StepResult :=
  match settle env ops touched st with
  | .error msg =>
    .failed { blank c.taken head kind c.conf with responsible := [head.event].filter (· != ""), error := some msg }
  | .ok st =>
    .committed
      { blank c.taken head kind st.conf with
        fired, ignored, faults, responsible := responsibleOf env.input head.event fired faults,
        resources := pre ++ st.recs, draws := draws ++ st.draws }
      { c with conf := st.conf, seq := st.seq, nid := st.nid, attempts, taken := c.taken + 1 }

def stepHead (env : Env) (c : Config) (next : Conf) (nid : Nat) (head : Entry) : StepResult :=
  match head.kind with
  | .serviceDone res r waited served =>
    match env.input.resource? res, next.resource? res with
    | some d, some s =>
      let next := next.setResource res { s with holds := Res.endService r.id s.holds }
      let st : Settle := { conf := next, seq := c.seq, nid, draws := [], recs := [] }
      let st := answer st res d r r.info.thenEv "completed"
        [("waited", .num waited.toFloat), ("served", .num served.toFloat)]
      finish env c head .serviceDone [] [] [] [] [] [res] st c.attempts
        [{ resRec res d r "completed" next.time with waited := some waited, served := some served }]
    | _, _ => .committed (blank c.taken head .serviceDone next) { c with conf := next, nid, taken := c.taken + 1 }
  | .waitTimeout res rid =>
    match env.input.resource? res, next.resource? res with
    | some d, some s =>
      match s.waiting.find? (·.id == rid) with
      | none => .committed (blank c.taken head .waitTimeout next) { c with conf := next, nid, taken := c.taken + 1 }
      | some r =>
        let next := next.setResource res { s with waiting := s.waiting.filter (·.id != rid) }
        let st : Settle := { conf := next, seq := c.seq, nid, draws := [], recs := [] }
        let waited := next.time - r.since
        let st := match r.info.refused with
          | some ev => answer st res d r ev "refused" [("waited", .num waited.toFloat), ("reason", .str "timeout")]
          | none => st
        finish env c head .waitTimeout [] [] [] [] [] [res] st c.attempts
          [{ resRec res d r "timed-out" next.time with waited := some waited, reason := some "timeout" }]
    | _, _ => .committed (blank c.taken head .waitTimeout next) { c with conf := next, nid, taken := c.taken + 1 }
  | .event =>
    let ev := head.event
    -- Routes are decided when the entry is first taken as head (ORDER: before drop and delay).
    let routed : Except String (Entry × Conf × Conf × List Draw) :=
      match head.routes, head.target with
      | none, none => do
        let (rs, next', drs) ← decideRoutes env next head
        -- the start-of-step view gains the keyed instances the routes created
        let cur := { c.conf with insts := next'.insts, machines := c.conf.machines ++ next'.machines.filter fun (k, _) =>
                                   !(c.conf.machines.any (·.1 == k)) }
        pure ({ head with routes := some rs }, next', cur, drs)
      | _, _ => pure (head, next, c.conf, [])
    match routed with
    | .error msg =>
      .failed { blank c.taken head .deliver c.conf with responsible := [ev], error := some msg }
    | .ok (head, next, cur, rdraws) =>
    let attempt := attemptOf c ev
    let attempts := (ev, attempt) :: c.attempts.filter (·.1 != ev)
    match env.faults.filter (faultMatches "drop-event" ev attempt) with
    | d :: ds =>
      let recs := (d :: ds).map fun f => { fault := f.id, effect := FaultEffect.dropped }
      .committed
        { blank c.taken head .drop next with faults := recs, draws := rdraws, responsible := responsibleOf env.input ev [] recs }
        { c with conf := next, nid, attempts, taken := c.taken + 1 }
    | [] =>
      let already := (lookupSeq c.delayedBy head.seq).getD []
      match env.faults.find? (fun f => faultMatches "delay-event" ev attempt f && !already.contains f.id) with
      | some d =>
        if head.time + d.delayBy ≥ two53 then
          .failed { blank c.taken head .delay c.conf with responsible := [ev], error := some "Value time exceeds 2^53." }
        else
        let (payload, nid') := head.payload.copy nid
        let copy : Entry := { head with seq := c.seq, time := head.time + d.delayBy, payload }
        let next := { next with pending := insertE next.pending copy }
        let recs := [{ fault := d.id, effect := FaultEffect.delayed }]
        .committed
          { blank c.taken head .delay next with faults := recs, draws := rdraws, responsible := responsibleOf env.input ev [] recs }
          { c with conf := next, seq := c.seq + 1, nid := nid', attempts, delayedBy := (c.seq, already ++ [d.id]) :: c.delayedBy, taken := c.taken + 1 }
      | none =>
        let r : Except String (List Fired2 × List Ignored2 × List FaultRecord × FireState) := do
          let (ws, igs, recs) ← chooseAll env cur head env.behaviors
          let (fired, s) ← fireAll env cur head ws { next, seq := c.seq, nid, draws := [], ops := [] }
          pure (fired, igs, recs, s)
        match r with
        | .error msg =>
          .failed { blank c.taken head .deliver c.conf with responsible := [ev], error := some msg }
        | .ok (fired, ignored, recs, s) =>
          finish env c head .deliver fired ignored (injectedOf head.source ++ recs) (rdraws ++ s.draws)
            s.ops [] { conf := s.next, seq := s.seq, nid := s.nid, draws := [], recs := [] } attempts []

def step (env : Env) (c : Config) : StepResult :=
  match c.conf.pending with
  | [] => .idle
  | h :: _ =>
    if (env.input.scenario.stopAt.map (fun x => decide (h.time > x))).getD false then .stopped else
    let (copy, nid) := c.conf.copy c.nid
    match copy.pending with
    | [] => .idle
    | head :: rest => stepHead env c { copy with pending := rest, time := head.time } nid head

/-! ## Runs -/

inductive Outcome2 where
  | running | quiescent | stepLimit | error | stopped
  deriving DecidableEq, Inhabited

def Outcome2.name : Outcome2 → String
  | .running => "running" | .quiescent => "quiescent" | .stepLimit => "step-limit"
  | .error => "error" | .stopped => "stopped"

structure Run where
  config : Config
  stepsRev : List Step2
  outcome : Outcome2

def advance (env : Env) (bound : Nat) (r : Run) : Run :=
  match step env r.config with
  | .idle => { r with outcome := .quiescent }
  | .stopped => { r with outcome := .stopped }
  | .committed rec next =>
    { config := next, stepsRev := rec :: r.stepsRev,
      outcome :=
        if next.conf.pending.isEmpty then .quiescent
        else if r.stepsRev.length + 1 ≥ bound then .stepLimit
        else .running }
  | .failed rec => { r with stepsRev := rec :: r.stepsRev, outcome := .error }

def loop (env : Env) (bound : Nat) : Nat → Run → Run
  | 0, r => r
  | fuel + 1, r => if r.outcome = .running then loop env bound fuel (advance env bound r) else r

/-- The initial configuration: instances, machines, resources, the scenario's steps then the
injected faults. -/
def initialConf (i : Input) (faults : List FaultIn) : Conf × Nat :=
  let insts := i.behaviors.map fun b => (b.id, match b.instances with
    | .single => [Value.num 0]
    | .count n => (List.range n).map fun k => Value.num k.toFloat
    | .keyed .. => [])
  let insts := insts.foldl (fun acc (k, v) => if acc.any (·.1 == k) then acc else acc ++ [(k, v)]) []
  let machines := insts.flatMap fun (bid, vs) =>
    match i.behavior? bid with
    | some b => vs.map fun v => (machineKey b v, initialMachine b)
    | none => []
  let mk (n : Nat) (time : Nat) (event : String) (payload : Value) (source : Src)
      (target : Option Addr) : Entry :=
    { seq := n, time, scheduledAt := time, event, payload, source, kind := .event, target,
      sender := none, routes := none }
  let (q, n) := i.scenario.steps.foldl (fun (q, n) st =>
    let target := st.target.map fun (b, v) => { behavior := b, inst := v, incarnation := 0 }
    (insertE q (mk n st.time st.event st.payload (.scenario n) target), n + 1)) ([], 0)
  let (q, n) := (faults.filter (·.isKind "inject-event")).foldl (fun (q, n) f =>
    (insertE q (mk n f.injectAt (f.event.getD "") f.payload (.fault f.id) none), n + 1)) (q, n)
  ({ time := 0, machines, insts, pending := q,
     resources := i.resources.map fun d => (d.id, { capacity := d.capacity, holds := [], waiting := [] }),
     routeCounters := [], streams := [] }, n)

structure Trace2 where
  input : Input
  faults : List String
  initial : Conf
  steps : List Step2
  outcome : Outcome2
  final : Conf

def traceOf (i : Input) : Trace2 :=
  let env := envOf i
  let (initial, seq) := initialConf i env.faults
  let (conf, nid) := initial.copy 1
  let c0 : Config := { conf, seq, nid, attempts := [], delayedBy := [], taken := 0 }
  let bound := i.scenario.stepLimit
  let r := loop env bound bound
    { config := c0, stepsRev := [], outcome := if conf.pending.isEmpty then .quiescent else .running }
  { input := i, faults := env.faultIds, initial, steps := r.stepsRev.reverse, outcome := r.outcome,
    final := r.config.conf }

/-! ## Refusals -/

def sampledSites (i : Input) : List String :=
  (i.behaviors.flatMap fun b => b.transitions.flatMap fun t =>
    (t.effects.zip (List.range t.effects.length)).filterMap fun (e, k) =>
      let site := s!"{b.id}:{t.id}:{k}"
      match e with
      | .emit _ d _ _ => if d.draws then some s!"after:{site}" else none
      | .sample _ d => if d.draws then some s!"sample:{site}" else none
      | .request _ _ _ _ d _ _ _ => if d.draws then some s!"demand:{site}" else none
      | _ => none) ++
  (i.routes.filter (·.rby == "random")).map fun r => s!"route:{r.event}:{r.behavior}"

def validate (i : Input) : Except String Unit := do
  let sid := i.scenario.id
  for b in i.behaviors do
    if (i.behavior? b.id).isNone then throw s!"Scenario \"{sid}\" lists \"{b.id}\", which is not a behavior."
  for id in dedup i.scenario.faults do
    if (i.fault? id).isNone then throw s!"\"{id}\" is not a fault in this model."
  let mut k := 0
  for st in i.scenario.steps do
    if !i.isEvent st.event then
      throw s!"Scenario \"{sid}\" step {k} delivers \"{st.event}\", which is not an event."
    k := k + 1
  for f in (envOf i).faults do
    if f.isKind "inject-event" then
      match f.event with
      | some e => if !i.isEvent e then throw s!"Fault \"{f.id}\" injects \"{e}\", which is not an event."
      | none => throw s!"Fault \"{f.id}\" injects \"undefined\", which is not an event."
  -- format 2: reserved names
  let ids := i.behaviors.map (·.id) ++ i.resources.map (·.id)
  for x in ids do
    if (ids.filter (· == x)).length > 1 then throw s!"Id \"{x}\" is reserved: it names more than one element."
  for b in i.behaviors do
    for v in b.variables do
      if v.name == "instance" then throw s!"Variable \"instance\" of \"{b.id}\" is reserved."
      match b.instances with
      | .single => pure ()
      | _ => if ["count", "sum", "min", "max", "instances"].contains v.name then
          throw s!"Variable \"{v.name}\" of \"{b.id}\" is reserved."
  -- unknown ids
  for r in i.routes do
    if !i.isEvent r.event then throw s!"Route names \"{r.event}\", which is not an event."
    match i.behavior? r.behavior with
    | none => throw s!"Route names \"{r.behavior}\", which is not a behavior."
    | some b =>
      match b.instances, r.rby with
      | .keyed .., "key" => pure ()
      | .keyed .., _ => throw s!"Route of \"{r.event}\" to keyed \"{b.id}\" must be by key."
      | _, _ => pure ()
    if r.rby == "key" && r.field.isNone then throw s!"Route of \"{r.event}\" to \"{r.behavior}\" needs a field."
    if r.rby == "least-busy" then
      match r.resource with
      | some x => if (i.resource? x).isNone then throw s!"Route names \"{x}\", which is not a resource."
      | none => throw s!"Route of \"{r.event}\" to \"{r.behavior}\" needs a resource."
  for b in i.behaviors do
    for t in b.transitions do
      for e in t.effects do
        match e with
        | .request _ res cls units _ thenEv refused _ =>
          match i.resource? res with
          | none => throw s!"Effect uses \"{res}\", which is not a resource."
          | some d =>
            match classIndex d cls with
            | none => throw s!"Effect names no class of \"{res}\"."
            | some c =>
              let others := ((List.range d.classes.length).filter (· != c)).foldl
                (fun acc k => acc + d.reservedOf k) 0
              let lim := (d.limitOf c).getD d.capacity
              if units > min lim (d.capacity - others) then
                throw s!"Class \"{classId d c}\" of \"{res}\" can never grant {units} units."
          if !i.isEvent thenEv then throw s!"Effect emits \"{thenEv}\", which is not an event."
          if let some ev := refused then
            if !i.isEvent ev then throw s!"Effect emits \"{ev}\", which is not an event."
        | .release res cls _ =>
          match i.resource? res with
          | none => throw s!"Effect releases \"{res}\", which is not a resource."
          | some d => if (classIndex d cls).isNone then throw s!"Effect names no class of \"{res}\"."
        | _ => pure ()
  for d in i.resources do
    let total := d.classes.foldl (fun acc c => acc + c.reserved) 0
    if total > d.capacity then throw s!"Resource \"{d.id}\" reserves more units than its capacity."
    for c in d.classes do
      if let some l := c.limit then
        if c.reserved > l then throw s!"Class \"{c.id}\" of \"{d.id}\" reserves more units than its limit."
  -- time
  if i.unit == "tick" && i.perSecond.isSome then throw "Unit tick has no rate."
  -- seed
  if i.scenario.seed.isNone then
    if let some s := (sampledSites i).head? then throw s!"Input samples \"{s}\" but declares no seed."
  match i.scenario.horizon, i.scenario.warmup, i.scenario.stopAt with
  | some h, some w, _ => if w ≥ h then throw "Scenario warmup must be below its horizon."
  | _, _, _ => pure ()
  match i.scenario.horizon, i.scenario.stopAt with
  | some h, some s => if s < h then throw "Scenario stopAt must be at least its horizon."
  | _, _ => pure ()

/-! ## Trace encoding -/

namespace Encode

open Exegra.Encode (o s nat a strings)

def n (k : Nat) : Value := .num k.toFloat

def addr (x : Addr) : Value :=
  o [("behavior", s x.behavior), ("instance", x.inst), ("incarnation", n x.incarnation)]

def source : Src → Value
  | .scenario step => o [("kind", s "scenario"), ("step", nat step)]
  | .fault f => o [("kind", s "fault"), ("fault", s f)]
  | .transition t b => o [("kind", s "transition"), ("transition", s t), ("behavior", s b)]
  | .resource r q out => o [("kind", s "resource"), ("resource", s r), ("request", n q), ("outcome", s out)]

def opt (k : String) : Option Value → List (String × Value)
  | some v => [(k, v)]
  | none => []

def entryFields (e : Entry) : List (String × Value) :=
  (match e.kind with
   | .event => []
   | .serviceDone r q _ _ => [("kind", s "service-done"), ("resource", s r), ("request", n q.id)]
   | .waitTimeout r q => [("kind", s "wait-timeout"), ("resource", s r), ("request", n q)]) ++
  opt "target" (e.target.map addr) ++ opt "from" (e.sender.map addr) ++
  (match e.routes with
   | some (r :: rs) => [("routes", o ((r :: rs).map fun (b, v) => (b, v)))]
   | _ => [])

def pending (e : Entry) : Value :=
  o ([("seq", n e.seq), ("time", n e.time), ("scheduledAt", n e.scheduledAt),
      ("event", if e.event == "" then .null else s e.event), ("payload", e.payload),
      ("source", source e.source)] ++ entryFields e)

def resource (c : Conf) (d : ResourceDecl) : Value :=
  match c.resource? d.id with
  | none => .null
  | some st =>
    o [("capacity", n st.capacity),
       ("held", a (st.holds.map fun h =>
          o ([("instance", s h.owner), ("class", s (classId d h.cls)), ("units", n h.units)] ++
             opt "request" (h.req.map n)))),
       ("waiting", a (st.waiting.map fun r =>
          o [("request", n r.id), ("requester", s r.owner), ("class", s (classId d r.cls)),
             ("units", n r.units), ("since", n r.since), ("seq", n r.id)]))]

def configuration (i : Input) (c : Conf) : Value :=
  o [("time", n c.time),
     ("machines", o (c.machines.map fun (id, m) =>
        (id, o [("state", s m.state), ("vars", .obj 0 m.vars)]))),
     ("pending", a (c.pending.map pending)),
     ("resources", o (i.resources.map fun d => (d.id, resource c d))),
     ("links", o []), ("timers", o []), ("workloads", o []), ("meters", o []),
     ("routeCounters", o (c.routeCounters.map fun (k, v) => (k, n v))),
     ("streams", o (c.streams.map fun (k, v) => (k, n v))),
     ("down", a []),
     ("incarnations", o (c.machines.map fun (k, _) => (k, n 0)))]

def draw (d : Draw) : Value :=
  o [("stream", s d.stream), ("index", n d.index), ("value", s (toString d.value.toNat))]

def resRecord (r : ResRecord) : Value :=
  o ([("resource", s r.resource), ("class", s r.cls),
      ("request", match r.request with | some q => n q | none => .null),
      ("action", s r.action), ("at", n r.atTime)] ++
     opt "waited" (r.waited.map n) ++ opt "served" (r.served.map n) ++
     opt "reason" (r.reason.map s) ++ opt "units" (r.units.map n))

def fired (f : Fired2) : Value :=
  match Exegra.Encode.fired f.base with
  | .obj k fs => .obj k (fs ++ [("instance", f.inst)])
  | v => v

def step (i : Input) (st : Step2) : Value :=
  let e := st.head
  o ([("index", n st.index), ("time", n st.time), ("kind", s st.kind.name),
      ("event", o ([("id", if e.event == "" then .null else s e.event), ("payload", e.payload),
                    ("seq", n e.seq), ("source", source e.source), ("scheduledAt", n e.scheduledAt)] ++
                   entryFields e)),
      ("fired", a (st.fired.map fired)),
      ("ignored", a (st.ignored.map fun ig =>
         o ([("behavior", s ig.base.behavior),
             ("reason", s (if ig.inst.isNone then "no-instance" else ig.base.reason.name)),
             ("considered", strings ig.base.considered)] ++ opt "instance" ig.inst))),
      ("faults", a (st.faults.map fun f => o [("fault", s f.fault), ("effect", s f.effect.name)])),
      ("responsible", strings st.responsible),
      ("resources", a (st.resources.map resRecord)),
      ("draws", a (st.draws.map draw)),
      ("config", configuration i st.config)] ++
     match st.error with
     | some m => [("error", o [("message", s m)])]
     | none => [])

def trace (t : Trace2) : Value :=
  let i := t.input
  let truncated := t.outcome == .stepLimit || t.outcome == .error
  o ([("version", n 2), ("timeUnit", s i.unit),
      ("seed", match i.scenario.seed with | some x => s (toString x.toNat) | none => .null),
      ("scenarioId", s i.scenario.id), ("faults", strings t.faults),
      ("initialDraws", a [])] ++
     (if i.scenario.output == "metrics" then [] else
       [("initial", configuration i t.initial), ("steps", a (t.steps.map (step i)))]) ++
     [("stepsTaken", n t.steps.length), ("outcome", s t.outcome.name),
      ("truncated", .bool truncated), ("final", configuration i t.final)])

end Encode

/-- Run a decoded version-2 input: a refusal, or the trace JSON text. -/
def runInput (i : Input) : Except String String := do
  validate i
  pure (Json.write (Encode.trace (traceOf i)))

end Exegra.V2

namespace Exegra

/-- The engine input of either version, as text to text. Version 1 is run by the format-1
semantics, unchanged (`runText`); version 2 by `V2.runInput`. -/
def runAny (text : String) : Except String String := do
  let v ← Json.parse text
  match v with
  | .obj _ root =>
    match objGet? root "version", objGet? root "format" with
    | some (.num x), some (.str "exegra-sim-input") =>
      if x == 2 then V2.runInput (← V2.Decode.input root) else runText text
    | _, _ => runText text
  | _ => runText text

end Exegra
