import Exegra.Semantics
import Exegra.Random
import Exegra.Resource
import Exegra.Workload

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

/-- The size of a message sent over a link: none (0), an expression, or a distribution. -/
inductive SizeIn where
  | none
  | expr (src : String)
  | dist (d : Dist)
  deriving Inhabited

inductive Effect where
  | set (varName : String) (to : Option Value)
  | sample (varName : String) (d : Dist)
  | emit (event : String) (after : Dist) (payload : List (String × Value)) (reply : Bool)
  | request (kind : Res.ReqKind) (res : String) (cls : Option String) (units : Nat) (demand : Dist)
      (thenEv : String) (refused : Option String) (payload : List (String × Value))
  | release (res : String) (cls : Option String) (units : Nat)
  /-- An emit sent over a link (`via`), with its size; `fanout` sends one message per receiver
  instance. -/
  | send (event : String) (size : SizeIn) (payload : List (String × Value)) (reply : Bool)
      (via : String) (fanout : Bool)
  /-- `{timer, after, emit, payload}`: (re)set a named timer of the firing instance. -/
  | timer (name : String) (after : Dist) (event : String) (payload : List (String × Value))
  | cancel (name : String)
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

/-- A link (WG-4729): transfer at `bandwidth` bytes per second through a FIFO queue, then a
propagation latency. -/
structure LinkIn where
  id : String
  source : String
  target : String
  latency : Dist
  bandwidth : Option Nat
  queueBound : Option Nat
  ordered : Bool
  fanout : Bool
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
  /-- `window {at, until?}`: the fault acts only on heads whose time is in `[at, until)`. -/
  window : Option (Nat × Option Nat) := none
  resource : Option String := none
  cls : Option String := none
  capacity : Nat := 0
  limit : Nat := 0
  num : Nat := 1
  den : Nat := 1
  /-- `replace-demand`: the behavior and effect index of the `use`, and the new demand. -/
  behavior : Option String := none
  effect : Nat := 0
  demand : Dist := .fixed 0
  deriving Inhabited

def FaultIn.isKind (f : FaultIn) (k : String) : Bool := f.kind == some k

/-- A format-1 fault kind with a window acts only on heads whose time lies in it. -/
def FaultIn.actsAt (f : FaultIn) (t : Nat) : Bool :=
  match f.window with
  | none => true
  | some (a, u) => decide (a ≤ t) && (u.all fun u => decide (t < u))

def resourceKinds : List String :=
  ["set-capacity", "set-class-limit", "collapse-classes", "scale-demand", "replace-demand"]

def FaultIn.isResourceKind (f : FaultIn) : Bool := (f.kind.map resourceKinds.contains).getD false

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

/-- A generated payload field of a workload. -/
inductive PField where
  | lit (v : Value)
  | sample (d : Dist)
  | choose (values : List Value) (weights : List Nat)
  | counter
  deriving Inhabited

structure ClientsIn where
  count : Nat
  roundRobin : Bool
  deriving Inhabited

inductive WKind where
  | open_ | closed | population
  deriving Inhabited, DecidableEq

/-- A workload (WG-4715): open, closed or a population. A population's `event` is its start event. -/
structure WorkloadIn where
  id : String
  event : String
  poisson : Bool
  phases : List Work.Phase
  period : Option Nat
  batch : Dist
  clients : Option ClientsIn
  legitimate : Bool
  maxArrivals : Option Nat
  payload : List (String × PField)
  requestField : String
  clientField : String
  addressField : String
  kind : WKind := .open_
  /-- Closed: the number of clients; population: the number of client instances. -/
  population : Nat := 0
  think : Dist := .fixed 0
  /-- Closed: the start offset of each client; population: `start.at`. -/
  start : Dist := .fixed 0
  reply : String := ""
  timeout : Option Nat := none
  /-- Population: the client behavior. -/
  behavior : String := ""
  /-- `clients.addresses.groupSize`: users grouped onto addresses. -/
  groupSize : Option Dist := none
  deriving Inhabited

/-- A request class: `{id, start: {event, workload?}, key, ends: [{event, outcome}]}`. -/
structure ReqClassIn where
  id : String
  startEvent : String
  startWorkload : Option String
  key : String
  ends : List (String × String)
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
  links : List LinkIn := []
  workloads : List WorkloadIn := []
  unitExp : List (Nat × Nat) := []
  /-- The quantiles of the measured outputs, as exact fractions; `none` when no metrics are asked. -/
  metrics : Option (List (String × Nat × Nat)) := none
  /-- `metrics.series.bucket`. -/
  series : Option Nat := none
  requests : List ReqClassIn := []
  deriving Inhabited

/-- Whether the run reports measured outputs. -/
def Input.measures (i : Input) : Bool :=
  i.metrics.isSome || i.scenario.output == "metrics" || !i.requests.isEmpty

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
    else if objHas fx "emit" && objHas fx "via" then do
      let event ← string fx "emit" what
      let via ← string fx "via" what
      if !(field fx "after").isNullish then throw s!"{what}: \"via\" cannot be combined with \"after\"."
      let size ← match field fx "size" with
        | .undef | .null => pure SizeIn.none
        | .str src => pure (.expr src)
        | x => (dist x s!"{what}.size").map .dist
      let payload ← payloadObj fx what
      let reply ← match field fx "target" with
        | .undef | .null => pure false
        | .str "reply" => pure true
        | _ => throw s!"{what}: \"target\" must be \"reply\"."
      let fanout := field fx "fanout" matches .bool true
      pure (.send event size payload reply via fanout)
    else if objHas fx "timer" then do
      let name ← string fx "timer" what
      let after ← dist (field fx "after") s!"{what}.after"
      let event ← string fx "emit" what
      let payload ← payloadObj fx what
      pure (.timer name after event payload)
    else if objHas fx "cancel" then do
      pure (.cancel (← string fx "cancel" what))
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
  if kind == some "crash-instance" then
    throw s!"{what}: fault kind \"crash-instance\" is not implemented (WG-4664)."
  let window ← match field f "window" with
    | .undef | .null => pure none
    | w => do
      let wo ← object w s!"{what}.window"
      let a ← intIn (field wo "at") s!"{what}.window.at" 0 (two53 - 1)
      let u ← optInt wo "until" s!"{what}.window.until" 0 (two53 - 1)
      pure (some (a, u))
  let occurrence := match field f "occurrence" with
    | .undef => Occurrence.any
    | .num n => .exactly n
    | _ => .never
  let delayBy ← if kind == some "delay-event" then intIn (field f "by") s!"{what}.by" 0 (two53 - 1) else pure 0
  let injectAt ← if kind == some "inject-event" then intIn (field f "at") s!"{what}.at" 0 (two53 - 1) else pure 0
  let resource ← optStr f "resource" what
  let cls ← optStr f "class" what
  let capacity ← if kind == some "set-capacity" then intIn (field f "capacity") s!"{what}.capacity" 1 (two32 - 1) else pure 0
  let limit ← if kind == some "set-class-limit" then intIn (field f "limit") s!"{what}.limit" 1 (two32 - 1) else pure 0
  let num ← if kind == some "scale-demand" then intIn (field f "num") s!"{what}.num" 0 (two32 - 1) else pure 1
  let den ← if kind == some "scale-demand" then intIn (field f "den") s!"{what}.den" 1 (two32 - 1) else pure 1
  let behavior ← optStr f "behavior" what
  let effect ← if kind == some "replace-demand" then intIn (field f "effect") s!"{what}.effect" 0 (two32 - 1) else pure 0
  let demand ← if kind == some "replace-demand" then dist (field f "demand") s!"{what}.demand" else pure (.fixed 0)
  let id ← string f "id" what
  let event ← optStr f "event" what
  let transition ← optStr f "transition" what
  pure { id, kind, event, transition, occurrence, delayBy, injectAt,
         payload := payloadOrEmpty (field f "payload"), window, resource, cls, capacity, limit, num, den,
         behavior, effect, demand }

def link (v : Value) (i : Nat) : R LinkIn := do
  let what := s!"links[{i}]"
  let o ← object v what
  let id ← string o "id" what
  let source := ((field o "from").asString?).getD ""
  let target := ((field o "to").asString?).getD ""
  let latency ← match field o "latency" with
    | .undef | .null => pure (Dist.fixed 0)
    | x => dist x s!"{what}.latency"
  let bandwidth ← optInt o "bandwidth" s!"{what}.bandwidth" 1 (2 ^ 40 - 1)
  let queueBound ← optInt o "queueBound" s!"{what}.queueBound" 0 (two32 - 1)
  let ordered := field o "ordered" matches .bool true
  let fanout := field o "fanout" matches .bool true
  pure { id, source, target, latency, bandwidth, queueBound, ordered, fanout }

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

/-- A natural number written as a JSON number or as a decimal string, in `[0, hi]`. -/
def bigNat (v : Value) (path : String) (hi : Nat) : R Nat :=
  let err := s!"Field \"{path}\" must be an integer in [0, {hi}]."
  match v with
  | .num _ => intIn v path 0 (min hi (two53 - 1))
  | .str s =>
    let cs := s.toList
    if cs.isEmpty || !cs.all Char.isDigit || (cs.length > 1 && cs.head? == some '0') then .error err
    else
      let n := cs.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
      if n ≤ hi then .ok n else .error err
  | _ => .error err

/-- The pinned unit-mean exponential table: `[[u, x]]`, `u` strictly increasing from 0 to 2^32,
`x` non-decreasing below 2^72, numbers or decimal strings. -/
def unitExp (v : Value) : R (List (Nat × Nat)) :=
  match v with
  | .undef | .null => .ok []
  | .arr _ xs => do
    let pts ← mapIdx (fun i p => match p with
        | .arr _ [u, x] => do
          let u ← bigNat u s!"unitExponential[{i}][0]" two32
          let x ← bigNat x s!"unitExponential[{i}][1]" (2 ^ 72 - 1)
          pure (u, x)
        | _ => throw "Distribution \"unitExponential\" has a malformed table.") xs
    let us := pts.map (·.1)
    let ys := pts.map (·.2)
    if us.head? != some 0 || us.getLast? != some two32 || !(us.zip us.tail).all (fun (a, b) => a < b)
        || !(ys.zip ys.tail).all (fun (a, b) => a ≤ b) then
      throw "Distribution \"unitExponential\" has a malformed table."
    pure pts
  | _ => .error "Distribution \"unitExponential\" has a malformed table."

def rateOf (v : Value) (path : String) : R (Nat × Nat) := do
  let o ← object v path
  let num ← intIn (field o "num") s!"{path}.num" 0 (two32 - 1)
  let den ← intIn (field o "den") s!"{path}.den" 1 (two32 - 1)
  pure (num, den)

def pfield (what : String) : String × Value → R (String × PField)
  | (k, x) =>
    let pw := s!"{what}.payload.{k}"
    match x with
    | .obj _ xo =>
      if objHas xo "sample" then do
        let d ← dist (field xo "sample") s!"{pw}.sample"
        pure (k, PField.sample d)
      else if objHas xo "choose" then do
        let vs ← array xo "choose" pw
        let ws ← mapIdx (fun j w => intIn w s!"{pw}.weights[{j}]" 0 (two32 - 1)) (← array xo "weights" pw)
        let total := ws.foldl (· + ·) 0
        if vs.length != ws.length || total == 0 || total ≥ two53 then
          throw s!"Field \"{pw}\" must have one weight per value, with a sum in [1, 2^53)."
        pure (k, PField.choose vs ws)
      else if field xo "counter" matches .bool true then pure (k, PField.counter)
      else pure (k, PField.lit x)
    | _ => pure (k, PField.lit x)

def clientsOf (o : List (String × Value)) (what : String) (count : Option Nat) :
    R (Option ClientsIn × Option Dist) :=
  match field o "clients" with
  | .undef | .null => pure (none, none)
  | c => do
    let co ← object c s!"{what}.clients"
    let count ← match count with
      | some n => pure n
      | none => intIn (field co "count") s!"{what}.clients.count" 1 (two32 - 1)
    let roundRobin ← match field co "pick" with
      | .undef | .null | .str "uniform" => pure false
      | .str "round-robin" => pure true
      | _ => throw s!"{what}.clients: \"pick\" must be uniform or round-robin."
    let groupSize ← match field co "addresses" with
      | .undef | .null => pure none
      | a => do
        let ao ← object a s!"{what}.clients.addresses"
        pure (some (← dist (field ao "groupSize") s!"{what}.clients.addresses.groupSize"))
    pure (some { count, roundRobin : ClientsIn }, groupSize)

def workload (v : Value) (i : Nat) : R WorkloadIn := do
  let what := s!"workloads[{i}]"
  let o ← object v what
  let id ← string o "id" what
  let kind ← string o "kind" what
  let legitimate := match field o "legitimate" with
    | .bool false => false
    | _ => true
  let payload ← match field o "payload" with
    | .obj _ fs => fs.mapM (pfield what)
    | x => if x.isNullish then pure [] else throw s!"{what}: \"payload\" must be an object."
  let fname (k d : String) : String := match field o k with
    | .str x => x
    | _ => d
  let base : WorkloadIn :=
    { id, event := "", poisson := false, phases := [], period := none, batch := .fixed 1, clients := none,
      legitimate, maxArrivals := none, payload,
      requestField := fname "requestField" "request", clientField := fname "clientField" "client",
      addressField := fname "addressField" "address" }
  if kind == "closed" then
    let event ← string o "event" what
    let population ← intIn (field o "population") s!"{what}.population" 0 (two32 - 1)
    let think ← match field o "think" with
      | .undef | .null => pure (Dist.fixed 0)
      | x => dist x s!"{what}.think"
    let start ← match field o "start" with
      | .undef | .null => pure (Dist.fixed 0)
      | x => dist x s!"{what}.start"
    let reply ← string o "reply" what
    let timeout ← optInt o "timeout" s!"{what}.timeout" 1 (two53 - 1)
    return { base with kind := .closed, event, population, think, start, reply, timeout,
                       clients := some { count := population, roundRobin := true } }
  if kind == "population" then
    let behavior ← string o "behavior" what
    let count ← intIn (field o "count") s!"{what}.count" 0 (two32 - 1)
    let so ← object (field o "start") s!"{what}.start"
    let event ← string so "event" s!"{what}.start"
    let start ← match field so "at" with
      | .undef | .null => pure (Dist.fixed 0)
      | x => dist x s!"{what}.start.at"
    let (_, groupSize) ← clientsOf o what (some count)
    return { base with kind := .population, event, population := count, start, behavior, groupSize,
                       clients := some { count, roundRobin := true } }
  if kind != "open" then throw s!"{what}: \"kind\" must be open, closed or population."
  let event ← string o "event" what
  let poisson ← match field o "process" with
    | .str "poisson" => pure true
    | .str "constant" => pure false
    | _ => throw s!"{what}: \"process\" must be poisson or constant."
  let phases ← mapIdx (fun k p => do
      let pw := s!"{what}.phases[{k}]"
      let po ← object p pw
      let start ← intIn (field po "from") s!"{pw}.from" 0 (two53 - 1)
      let stop ← intIn (field po "until") s!"{pw}.until" 0 (two53 - 1)
      let ro ← object (field po "rate") s!"{pw}.rate"
      let rate ← match field ro "from", field ro "to" with
        | .undef, .undef => do
          let (a, b) ← rateOf (field po "rate") s!"{pw}.rate"
          pure (Work.Rate.const a b)
        | f, t => do
          let (a0, b0) ← rateOf f s!"{pw}.rate.from"
          let (a1, b1) ← rateOf t s!"{pw}.rate.to"
          pure (Work.Rate.ramp a0 b0 a1 b1)
      pure { start, stop, rate : Work.Phase }) (← array o "phases" what)
  let period ← optInt o "repeat" s!"{what}.repeat" 1 (two53 - 1)
  let batch ← match field o "batch" with
    | .undef | .null => pure (Dist.fixed 1)
    | b => dist b s!"{what}.batch"
  let (clients, groupSize) ← clientsOf o what none
  let maxArrivals ← optInt o "maxArrivals" s!"{what}.maxArrivals" 0 (two32 - 1)
  pure { base with event, poisson, phases, period, batch, clients, maxArrivals, groupSize }

/-- An exact decimal in (0, 1]: `"1"` or `"0.<digits>"`, as `(num, den)`. -/
def quantile (v : Value) (path : String) : R (String × Nat × Nat) :=
  let err := s!"Field \"{path}\" must be an exact decimal in (0, 1]."
  match v with
  | .str "1" => .ok ("1", 1, 1)
  | .str q =>
    match q.toList with
    | '0' :: '.' :: ds =>
      if ds.isEmpty || !ds.all Char.isDigit then .error err else
      let n := ds.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
      if n == 0 then .error err else .ok (q, n, 10 ^ ds.length)
    | _ => .error err
  | _ => .error err

def metricsSpec (v : Value) : R (Option (List (String × Nat × Nat))) :=
  match v with
  | .undef | .null => .ok none
  | .obj _ o =>
    match field o "quantiles" with
    | .undef | .null => .ok (some [("0.5", 1, 2), ("0.9", 9, 10), ("0.99", 99, 100)])
    | .arr _ qs => (mapIdx (fun i q => quantile q s!"metrics.quantiles[{i}]") qs).map some
    | _ => .error "Field \"metrics.quantiles\" must be an array."
  | _ => .error "Field \"metrics\" must be an object."

def reqClass (v : Value) (i : Nat) : R ReqClassIn := do
  let what := s!"requests[{i}]"
  let o ← object v what
  let id ← string o "id" what
  let so ← object (field o "start") s!"{what}.start"
  let startEvent ← string so "event" s!"{what}.start"
  let startWorkload ← optStr so "workload" s!"{what}.start"
  let key ← string o "key" what
  let ends ← mapIdx (fun j e => do
      let ew := s!"{what}.ends[{j}]"
      let eo ← object e ew
      let ev ← string eo "event" ew
      let out ← string eo "outcome" ew
      if !["ok", "refused", "timeout", "error"].contains out then
        throw s!"Request class \"{id}\": outcome must be ok, refused, timeout or error."
      pure (ev, out)) (arrayOrEmpty o "ends")
  pure { id, startEvent, startWorkload, key, ends }

def seriesOf (v : Value) : R (Option Nat) :=
  match v with
  | .obj _ o => match field o "series" with
    | .undef | .null => .ok none
    | s => do
      let so ← object s "metrics.series"
      pure (some (← intIn (field so "bucket") "metrics.series.bucket" 1 (two53 - 1)))
  | _ => .ok none

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
  for k in ["meters", "prices"] do
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
  let links ← mapIdx (fun i l => link l i) (arrayOrEmpty root "links")
  let workloads ← mapIdx (fun i w => workload w i) (arrayOrEmpty root "workloads")
  let unitExp ← unitExp (field root "unitExponential")
  let metrics ← metricsSpec (field root "metrics")
  let series ← seriesOf (field root "metrics")
  let requests ← mapIdx (fun i r => reqClass r i) (arrayOrEmpty root "requests")
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
  pure { unit, perSecond, behaviors, events, faults, routes, resources, links, workloads, unitExp, metrics,
         series, requests,
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
  | arrival (workload : String) (n : Nat) (client : Option String)
  /-- A closed client's timeout for its request `n`. -/
  | clientTimeout (workload : String) (n : Nat) (client : String)
  | timer (behavior : String) (inst : Value) (timer : String)
  | link (link : String) (message : Nat)
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
  /-- A closed client gives up on its request `n`. -/
  | clientTimeout (workload : String) (client : Nat) (n : Nat)
  /-- The transfer of message `msg` on queue `key` of link `link` ends. -/
  | linkDone (link key : String) (msg : Nat)
  /-- A windowed fault starts (`on`) or ends acting. -/
  | faultEdge (fault : String) (on : Bool)
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
  /-- The instant number, on the original first entry of an arrival instant only. -/
  first : Option Nat := none
  /-- The timer id `<machine key>/<name>` of a timer firing (kept by delayed copies). -/
  timer : Option String := none
  /-- On a delayed copy: the sequence number of the original entry. -/
  copyOf : Option Nat := none
  deriving Inhabited

/-- A message on a link. -/
structure Msg where
  id : Nat
  event : String
  payload : Value
  size : Nat
  sentAt : Nat
  target : Option Addr
  sender : Option Addr
  deriving Inhabited

/-- A link's transfer queue (one per link, or per receiver with fan-out). -/
structure LQueue where
  inTransfer : Option Msg := none
  waiting : List Msg := []
  lastDelivery : Option Nat := none
  deriving Inhabited

/-- The state of an open workload: instants and arrival entries created so far, and where its
schedule is. -/
structure WState where
  instants : Nat
  arrivals : Nat
  cursor : Work.Cursor
  /-- Closed: per client, the number of its outstanding request (`none` while thinking or done). -/
  clients : List (Option Nat) := []
  /-- With `addresses`: the group size of each address, in address order. -/
  groups : List Nat := []
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
  workloads : List (String × WState) := []
  /-- Link queues by (link, queue key), in creation order; the key is `""`, or the receiver's
  machine key with fan-out. -/
  lqueues : List ((String × String) × LQueue) := []
  /-- The windowed faults acting now, in `faults` order. -/
  active : List String := []
  deriving Inhabited

def Conf.lqueue (c : Conf) (l k : String) : LQueue :=
  ((c.lqueues.find? (·.1 == (l, k))).map (·.2)).getD {}

def Conf.setLQueue (c : Conf) (l k : String) (q : LQueue) : Conf :=
  if c.lqueues.any (·.1 == (l, k)) then
    { c with lqueues := c.lqueues.map fun (lk, x) => if lk == (l, k) then (lk, q) else (lk, x) }
  else { c with lqueues := c.lqueues ++ [((l, k), q)] }

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

structure LinkRec where
  link : String
  queue : String
  message : Nat
  action : String
  atTime : Nat
  size : Nat
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
  | deliver | drop | delay | serviceDone | waitTimeout | clientTimeout | linkDone | faultEdge
  deriving Inhabited, DecidableEq

def Kind2.name : Kind2 → String
  | .deliver => "deliver" | .drop => "drop" | .delay => "delay"
  | .serviceDone => "service-done" | .waitTimeout => "wait-timeout"
  | .clientTimeout => "client-timeout" | .linkDone => "link-done" | .faultEdge => "fault-edge"

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
  links : List LinkRec := []
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

def targeting (faults : List FaultIn) (kind tid : String) (time : Nat) : List FaultIn :=
  faults.filter fun f => f.isKind kind && f.transition == some tid && f.actsAt time

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
      let enablers := targeting env.faults "enable-transition" t.id time
      if t.faultOnly && enablers.isEmpty then
        scan env cur mk inst state event payload time ts considered dis gf recs
      else
        let considered := considered ++ [t.id]
        let disablers := targeting env.faults "disable-transition" t.id time
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
  lrecs : List LinkRec := []

def two53 : Nat := 9007199254740992

def evalEntries (env : Env) (view start : Conf) (mk : String) (inst payload : Value) (time : Nat) :
    List (String × Value) → List (String × Value) → Nat → Except String (List (String × Value) × Nat)
  | [], acc, nid => .ok (acc, nid)
  | (k, v) :: rest, acc, nid =>
    match valueOf env (some v) view start mk inst payload time nid with
    | .error e => .error e
    | .ok (x, nid) => evalEntries env view start mk inst payload time rest (objInsert acc k x) nid

/-! ## Links and timers -/

/-- Remove every queued entry with timer id `tid`. -/
def dropTimer (q : List Entry) (tid : String) : List Entry := q.filter (·.timer != some tid)

def linkRec (l k : String) (m : Msg) (action : String) (now : Nat) : LinkRec :=
  { link := l, queue := k, message := m.id, action, atTime := now, size := m.size }

/-- Propagation of message `m` at `now`: a latency drawn from `latency:<link>`, and the delivery
entry at `now + latency` (on an ordered link, no earlier than the previous delivery of that
queue). -/
def propagate (i : Input) (l : LinkIn) (k : String) (m : Msg) (now : Nat) (s : FireState) :
    Except String FireState :=
  let (lat, drs, streams) := sample i.scenario.seed s.next.streams s!"latency:{l.id}" l.latency
  let q := s.next.lqueue l.id k
  let t := if l.ordered then max (now + lat) (q.lastDelivery.getD 0) else now + lat
  if t ≥ two53 then .error "Value time exceeds 2^53." else
  let e : Entry :=
    { seq := s.seq, time := t, scheduledAt := t, event := m.event, payload := m.payload,
      source := .link l.id m.id, kind := .event, target := m.target, sender := m.sender, routes := none }
  let next := { s.next with streams, pending := insertE s.next.pending e }
  let next := if l.ordered then next.setLQueue l.id k { q with lastDelivery := some t } else next
  .ok { s with next, seq := s.seq + 1, draws := s.draws ++ drs,
               lrecs := s.lrecs ++ [linkRec l.id k m "propagated" now] }

/-- Message `m` starts its transfer at `now`: its `link-done` entry at `now + ⌈size·perSecond/bandwidth⌉`. -/
def startTransfer (i : Input) (l : LinkIn) (k : String) (m : Msg) (now : Nat) (s : FireState) :
    Except String FireState :=
  let bw := l.bandwidth.getD 1
  let tt := (m.size * i.perSecond.getD 1 + bw - 1) / bw
  if now + tt ≥ two53 then .error "Value time exceeds 2^53." else
  let e : Entry :=
    { seq := s.seq, time := now + tt, scheduledAt := now + tt, event := "", payload := .null,
      source := .link l.id m.id, kind := .linkDone l.id k m.id, target := none, sender := none, routes := none }
  let q := s.next.lqueue l.id k
  let next := ({ s.next with pending := insertE s.next.pending e }).setLQueue l.id k { q with inTransfer := some m }
  .ok { s with next, seq := s.seq + 1, lrecs := s.lrecs ++ [linkRec l.id k m "started" now] }

/-- Send message `m` on queue `k` of link `l` at `now`. Without bandwidth, and for a message of
size 0 on a link that is not ordered, straight to propagation; otherwise it starts its transfer
when the queue is idle, or waits. Beyond `queueBound` the newest waiting message is lost, or
with fan-out the oldest. -/
def sendMsg (i : Input) (l : LinkIn) (fan : Bool) (k : String) (m : Msg) (now : Nat) (s : FireState) :
    Except String FireState :=
  if l.bandwidth.isNone || (!l.ordered && m.size == 0) then propagate i l k m now s else
  let q := s.next.lqueue l.id k
  if q.inTransfer.isNone then startTransfer i l k m now s else
  let ws := q.waiting ++ [m]
  let (ws, lost) : List Msg × Option Msg := match l.queueBound with
    | some b => if ws.length > b then (if fan then (ws.drop 1, ws.head?) else (ws.dropLast, ws.getLast?)) else (ws, none)
    | none => (ws, none)
  let recs := [linkRec l.id k m "queued" now] ++ (lost.map fun x => linkRec l.id k x "lost" now).toList
  .ok { s with next := s.next.setLQueue l.id k { q with waiting := ws }, lrecs := s.lrecs ++ recs }

/-- The receivers of a fan-out over link `l`: every instance of every behavior whose subject is
the link's `to`, in behavior order and index (creation) order. -/
def fanReceivers (i : Input) (c : Conf) (l : LinkIn) : List (String × Option Addr) :=
  i.behaviors.flatMap fun b =>
    if b.subject == some l.target then
      (c.instsOf b.id).map fun v => (machineKey b v, some { behavior := b.id, inst := v, incarnation := 0 })
    else []

/-- The size of a message: an integer in `[0, 2^40)`. -/
def sizeOf (event : String) (v : Value) : Except String Nat :=
  let err (x : String) := s!"Size of emit \"{event}\" must be an integer in [0, 2^40), got {x}."
  match v with
  | .num x =>
    if x.floor == x && x ≥ 0 && x < 1099511627776 then .ok x.toUInt64.toNat else .error (err (Json.write v))
  | _ => .error (err v.typeName)

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
    | .send event size entries reply via fan =>
      if !env.input.isEvent event then .error s!"Effect emits \"{event}\", which is not an event." else
      match env.input.links.find? (·.id == via) with
      | none => .error s!"Effect sends over \"{via}\", which is not a link."
      | some l =>
        let fan := fan || l.fanout
        let sized : Except String (Nat × List Draw × List (String × Nat)) := match size with
          | .none => .ok (0, [], s.next.streams)
          | .dist d => .ok (sample env.input.scenario.seed s.next.streams s!"size:{site}" d)
          | .expr src => do
            let v ← evalIn env src s.next start w.key w.inst head.payload time
            pure (← sizeOf event v, [], s.next.streams)
        match sized with
        | .error e => .error e
        | .ok (sz, drs, streams) =>
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
          let receivers := if fan then fanReceivers env.input s.next l else [("", target)]
          let sender := some { behavior := w.b.id, inst := w.inst, incarnation := 0 : Addr }
          let s := { s with next := { s.next with streams }, nid, draws := s.draws ++ drs }
          let r : Except String (FireState × List EmitRecord) := receivers.foldlM (fun (s, ems) (k, tg) =>
            let m : Msg := { id := s.seq, event, payload := .obj s.nid fs, size := sz, sentAt := time,
                             target := tg, sender }
            match sendMsg env.input l fan k m time { s with seq := s.seq + 1, nid := s.nid + 1 } with
            | .error e => .error e
            | .ok s => .ok (s, ems ++ [{ event, time := time.toFloat, seq := m.id, payload := m.payload }])) (s, [])
          match r with
          | .error e => .error e
          | .ok (s, ems) => runEffects env start head w (k + 1) rest s sets (emits ++ ems)
    | .timer name after event entries =>
      if !env.input.isEvent event then .error s!"Effect emits \"{event}\", which is not an event." else
      let (delay, drs, streams) := sample env.input.scenario.seed s.next.streams s!"after:{site}" after
      let atTime := s.next.time + delay
      if atTime ≥ two53 then .error "Value time exceeds 2^53." else
      match evalEntries env s.next start w.key w.inst head.payload time entries [] s.nid with
      | .error e => .error e
      | .ok (fs, nid) =>
        let tid := s!"{w.key}/{name}"
        let pv : Value := .obj nid fs
        let entry : Entry :=
          { seq := s.seq, time := atTime, scheduledAt := atTime, event, payload := pv,
            source := .timer w.b.id w.inst name, kind := .event,
            target := some { behavior := w.b.id, inst := w.inst, incarnation := 0 }, sender := none,
            routes := none, timer := some tid }
        let next := { s.next with pending := insertE (dropTimer s.next.pending tid) entry, streams }
        runEffects env start head w (k + 1) rest
          { s with next, seq := s.seq + 1, nid := nid + 1, draws := s.draws ++ drs } sets
          (emits ++ [{ event, time := atTime.toFloat, seq := s.seq, payload := pv }])
    | .cancel name =>
      let tid := s!"{w.key}/{name}"
      runEffects env start head w (k + 1) rest
        { s with next := { s.next with pending := dropTimer s.next.pending tid } } sets emits
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

/-! ## Resource faults

The value in effect is a function of the faults acting on the target: the untimed ones, and the
windowed ones whose edge has started them (`Conf.active`). For `set-capacity`, `set-class-limit`
(per class) and `replace-demand` the last acting fault in `faults` order decides; `scale-demand`
factors multiply; `collapse-classes` collapses while any acts. -/

def activeFaults (faults : List FaultIn) (active : List String) : List FaultIn :=
  faults.filter fun f => f.window.isNone || active.contains f.id

def effCapacity (faults : List FaultIn) (active : List String) (d : ResourceDecl) : Nat :=
  (((activeFaults faults active).filter fun f => f.isKind "set-capacity" && f.resource == some d.id).getLast?.map
    (·.capacity)).getD d.capacity

/-- The resource as the acting faults leave it: class limits set, or collapsed into one strict
FIFO queue with no reservation, class limit or class bound. -/
def effDecl (faults : List FaultIn) (active : List String) (d : ResourceDecl) : ResourceDecl :=
  let act := activeFaults faults active
  let classes := d.classes.map fun cl =>
    match (act.filter fun f => f.isKind "set-class-limit" && f.resource == some d.id && f.cls == some cl.id).getLast? with
    | some f => { cl with limit := some f.limit }
    | none => cl
  if act.any (fun f => f.isKind "collapse-classes" && f.resource == some d.id) then
    { d with byPriority := false, strict := true,
             classes := classes.map fun cl => { cl with reserved := 0, limit := none, queueBound := none } }
  else { d with classes }

/-- The combined `scale-demand` factor of a resource, in lowest terms. -/
def effScale (faults : List FaultIn) (active : List String) (res : String) : Except String (Nat × Nat) :=
  let (n, m) := (activeFaults faults active).foldl (fun (n, m) f =>
    if f.isKind "scale-demand" && f.resource == some res then (n * f.num, m * f.den) else (n, m)) (1, 1)
  let g := Nat.gcd n m
  let (n, m) := (n / g, m / g)
  if n ≥ 4294967296 || m ≥ 4294967296 then .error s!"Value demand scale of \"{res}\" exceeds 2^32."
  else .ok (n, m)

/-- The demand a `use` draws from: the last acting `replace-demand` of its site, else its own. -/
def effDemand (faults : List FaultIn) (active : List String) (stream : String) (d : Dist) : Dist :=
  (((activeFaults faults active).filter fun f =>
      f.isKind "replace-demand" &&
      s!"demand:{f.behavior.getD ""}:{f.transition.getD ""}:{f.effect}" == stream).getLast?.map (·.demand)).getD d

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
      match effScale env.faults st.conf.active res with
      | .error e => .error e
      | .ok (sn, sd) =>
      let demand := effDemand env.faults st.conf.active r.info.stream r.info.demand
      let (dd, drs, streams) := sample env.input.scenario.seed st.conf.streams r.info.stream demand
      let (num, den) := d.demandFactor.at occ
      let served := ceilDiv (dd * num * sn) (den * sd)
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
  -- 3. grants, under the acting faults
  let de := effDecl env.faults st.conf.active d
  let (s2, outs) := Res.grantLoop de s.waiting.length s []
  st := { st with conf := st.conf.setResource res s2 }
  st ← applyGrants env res d outs st
  -- 4. bounds
  let (ws, removed) := Res.bounds de s2.waiting
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

structure Config where
  conf : Conf
  seq : Nat
  nid : Nat
  attempts : List (String × Nat)
  delayedBy : List (Nat × List String)
  taken : Nat

/-! ## Arrivals -/

/-- The address index of user `k`: users fill address 0, then 1, and so on. -/
def groupOf : List Nat → Nat → Nat → Nat
  | [], _, a => a
  | g :: gs, k, a => if k < g then a else groupOf gs (k - g) (a + 1)

/-- The address of client `k` of a workload: `<w>@<a>` with address groups, else the client. -/
def addressOf (w : WorkloadIn) (st : WState) (k : Nat) : String :=
  match w.groupSize with
  | some _ => s!"{w.id}@{groupOf st.groups k 0}"
  | none => s!"{w.id}:{k}"

/-- The generated payload of entry `n` of a workload for `client`: the payload fields in
declaration order (`payload:<w>:<field>`), then the request id, client and address. -/
def genPayload (i : Input) (w : WorkloadIn) (st : WState) (n : Nat) (client : Option Nat)
    (streams : List (String × Nat)) (nid : Nat) :
    List (String × Value) × Nat × List Draw × List (String × Nat) :=
  let seed := i.scenario.seed.getD 0
  let (fs, nid, pdraws, streams) := w.payload.foldl (fun (fs, nid, pdraws, streams) (f, pf) =>
    let pname := s!"payload:{w.id}:{f}"
    match pf with
    | .lit v => let (v, nid) := v.copy nid; (objInsert fs f v, nid, pdraws, streams)
    | .counter => (objInsert fs f (.num n.toFloat), nid, pdraws, streams)
    | .sample d =>
      let (x, drs, streams) := sample i.scenario.seed streams pname d
      (objInsert fs f (.num x.toFloat), nid, pdraws ++ drs, streams)
    | .choose vs ws =>
      let (r, dr, streams) := drawNext seed streams pname
      let (v, nid) := (vs.getD (Random.categorical r ws) .null).copy nid
      (objInsert fs f v, nid, pdraws ++ [dr], streams)) ([], nid, [], streams)
  let fs := objInsert fs w.requestField (.str s!"{w.id}#{n}")
  let fs := match client with
    | some c => objInsert (objInsert fs w.clientField (.str s!"{w.id}:{c}")) w.addressField (.str (addressOf w st c))
    | none => fs
  (fs, nid, pdraws, streams)

/-- Create the next arrival instant of an open workload, if any: its time (Poisson draws from
`arrival:<w>`, spent ones included), its batch size (`batch:<w>`), then per entry its client
(`client:<w>`, uniform pick) and payload fields in declaration order (`payload:<w>:<field>`).
Returns the workload state, the stream counters, the next sequence number and object identity,
the queue and the draws, in order. -/
def makeInstant (i : Input) (w : WorkloadIn) (st : WState) (streams : List (String × Nat))
    (seq nid : Nat) (q : List Entry) :
    WState × List (String × Nat) × Nat × Nat × List Entry × List Draw :=
  let full := match w.maxArrivals with
    | some m => decide (st.arrivals ≥ m)
    | none => false
  if st.cursor.done || full then ({ st with cursor := { st.cursor with done := true } }, streams, seq, nid, q, [])
  else
  let seed := i.scenario.seed.getD 0
  let aname := s!"arrival:{w.id}"
  let base := lookup streams aname
  let ex (k : Nat) : Nat := Random.sampleTable (Random.draw seed aname (base + k)) i.unitExp
  let horizon := i.scenario.horizon.getD 0
  let (t?, cur, used) := Work.nextTime (i.perSecond.getD 1) horizon w.phases w.period w.poisson ex
    (Work.fuelFor horizon w.phases) st.cursor 0
  let adraws : List Draw := (List.range used).map fun k =>
    { stream := aname, index := base + k, value := Random.draw seed aname (base + k) }
  let streams := (List.range used).foldl (fun s _ => bump s aname) streams
  match t? with
  | none => ({ st with cursor := cur }, streams, seq, nid, q, adraws)
  | some t =>
    let (b, bdraws, streams) := sample i.scenario.seed streams s!"batch:{w.id}" w.batch
    let b := max b 1
    let b := match w.maxArrivals with
      | some m => min b (m - st.arrivals)
      | none => b
    let (q, streams, seq, nid, draws) := (List.range b).foldl (fun (q, streams, seq, nid, draws) k =>
      let n := st.arrivals + k
      let (client, cdraws, streams) : Option Nat × List Draw × List (String × Nat) :=
        match w.clients with
        | none => (none, [], streams)
        | some cl =>
          if cl.roundRobin then (some (n % cl.count), [], streams)
          else
            let (r, dr, streams) := drawNext seed streams s!"client:{w.id}"
            (some (Random.index r cl.count), [dr], streams)
      let (fs, nid, pdraws, streams) := genPayload i w st n client streams nid
      let cname := client.map fun c => s!"{w.id}:{c}"
      let e : Entry :=
        { seq, time := t, scheduledAt := t, event := w.event, payload := .obj nid fs,
          source := .arrival w.id n cname, kind := .event, target := none, sender := none,
          routes := none, first := if k = 0 then some st.instants else none }
      (insertE q e, streams, seq + 1, nid + 1, draws ++ cdraws ++ pdraws)) (q, streams, seq, nid, [])
    let arrivals := st.arrivals + b
    let capped := match w.maxArrivals with
      | some m => decide (arrivals ≥ m)
      | none => false
    ({ st with instants := st.instants + 1, arrivals, cursor := if capped then { cur with done := true } else cur },
     streams, seq, nid, q, adraws ++ bdraws ++ draws)

/-- Draw the address group sizes (stream `groups:<w>`, each at least 1) until `left` users have
an address. -/
def drawGroups (seed : Option UInt64) (name : String) (d : Dist) :
    Nat → Nat → List Nat → List (String × Nat) → List Draw → List Nat × List (String × Nat) × List Draw
  | 0, _, gs, st, ds => (gs, st, ds)
  | fuel + 1, left, gs, st, ds =>
    if left = 0 then (gs, st, ds) else
    let (g, drs, st) := sample seed st name d
    let g := max g 1
    drawGroups seed name d fuel (left - min g left) (gs ++ [g]) st (ds ++ drs)

/-- A closed client `c` issues its next request at `t`, unless `t` is at or after the horizon
(then it stops): the arrival entry, then its `client-timeout` entry when the workload has a
`timeout`. -/
def issue (i : Input) (w : WorkloadIn) (st : WState) (c t : Nat) (streams : List (String × Nat))
    (seq nid : Nat) (q : List Entry) :
    WState × List (String × Nat) × Nat × Nat × List Entry × List Draw :=
  if t ≥ i.scenario.horizon.getD 0 then
    ({ st with clients := st.clients.set c none }, streams, seq, nid, q, [])
  else
  let n := st.arrivals
  let (fs, nid, drs, streams) := genPayload i w st n (some c) streams nid
  let cname := s!"{w.id}:{c}"
  let e : Entry :=
    { seq, time := t, scheduledAt := t, event := w.event, payload := .obj nid fs,
      source := .arrival w.id n (some cname), kind := .event, target := none, sender := none,
      routes := none }
  let q := insertE q e
  let (q, seq) := match w.timeout with
    | some to =>
      (insertE q { seq := seq + 1, time := t + to, scheduledAt := t + to, event := "", payload := .null,
                   source := .clientTimeout w.id n cname, kind := .clientTimeout w.id c n,
                   target := none, sender := none, routes := none }, seq + 2)
    | none => (q, seq + 1)
  ({ st with arrivals := n + 1, clients := st.clients.set c (some n) }, streams, seq, nid + 1, q, drs)

/-- A closed client `c` got its reply or gave up at `now`: it thinks (a draw from `think:<w>`)
and issues again. -/
def rethink (i : Input) (w : WorkloadIn) (st : WState) (c now : Nat) (streams : List (String × Nat))
    (seq nid : Nat) (q : List Entry) :
    WState × List (String × Nat) × Nat × Nat × List Entry × List Draw :=
  let (d, drs, streams) := sample i.scenario.seed streams s!"think:{w.id}" w.think
  let (st, streams, seq, nid, q, drs2) :=
    issue i w { st with clients := st.clients.set c none } c (now + d) streams seq nid q
  (st, streams, seq, nid, q, drs ++ drs2)

/-- The initial entries of a workload, after its address groups (`groups:<w>`): an open
workload's first instant; a closed workload's first issue per client in client order, each after
its start offset (`start:<w>`); a population's client instances, then per client its `start`
entry at a time from `start:<w>`, targeted at its instance. -/
def initialWorkload (i : Input) (c : Conf) (w : WorkloadIn) (st : WState) (seq nid : Nat) :
    Conf × WState × Nat × Nat × List Draw :=
  let (st, streams, gdraws) := match w.groupSize with
    | some d =>
      let users := (w.clients.map (fun (cl : ClientsIn) => cl.count)).getD 0
      let (gs, streams, ds) := drawGroups i.scenario.seed s!"groups:{w.id}" d users users [] c.streams []
      ({ st with groups := gs }, streams, ds)
    | none => (st, c.streams, [])
  let c := { c with streams }
  match w.kind with
  | .open_ =>
    let (st, streams, seq, nid, pending, ds) := makeInstant i w st c.streams seq nid c.pending
    ({ c with streams, pending }, st, seq, nid, gdraws ++ ds)
  | .closed =>
    let st := { st with clients := List.replicate w.population none }
    let (c, st, seq, nid, ds) := (List.range w.population).foldl (fun ((c, st, seq, nid, ds) : Conf × WState × Nat × Nat × List Draw) k =>
      let (t, d1, streams) := sample i.scenario.seed c.streams s!"start:{w.id}" w.start
      let (st, streams, seq, nid, pending, d2) := issue i w st k t streams seq nid c.pending
      ({ c with streams, pending }, st, seq, nid, ds ++ d1 ++ d2)) (c, st, seq, nid, [])
    (c, st, seq, nid, gdraws ++ ds)
  | .population =>
    match i.behavior? w.behavior with
    | none => (c, st, seq, nid, gdraws)
    | some b =>
      let keys := (List.range w.population).map fun k => Value.str s!"{w.id}:{k}"
      let c := { c with insts := c.insts.map fun (k, xs) => if k == b.id then (k, xs ++ keys) else (k, xs) }
      let c := keys.foldl (fun (c : Conf) v => c.setMachine (machineKey b v) (initialMachine b)) c
      let (c, seq, nid, ds) := (List.range w.population).foldl (fun ((c, seq, nid, ds) : Conf × Nat × Nat × List Draw) k =>
        let (t, d1, streams) := sample i.scenario.seed c.streams s!"start:{w.id}" w.start
        let c := { c with streams }
        if t ≥ i.scenario.horizon.getD 0 then (c, seq, nid, ds ++ d1) else
        let cname := s!"{w.id}:{k}"
        let fs := objInsert (objInsert [] w.clientField (.str cname)) w.addressField (.str (addressOf w st k))
        let e : Entry :=
          { seq, time := t, scheduledAt := t, event := w.event, payload := .obj nid fs,
            source := .arrival w.id k (some cname), kind := .event,
            target := some { behavior := b.id, inst := .str cname, incarnation := 0 }, sender := none,
            routes := none }
        ({ c with pending := insertE c.pending e }, seq + 1, nid + 1, ds ++ d1)) (c, seq, nid, [])
      (c, st, seq, nid, gdraws ++ ds)

/-- Set a workload's state. -/
def setW (ws : List (String × WState)) (id : String) (st : WState) : List (String × WState) :=
  ws.map fun (k, x) => if k == id then (k, st) else (k, x)

/-- Every created instant of every workload has the arrivals it was created with, and no more
than `maxArrivals`. -/
theorem makeInstant_arrivals_le (i : Input) (w : WorkloadIn) (st : WState) (streams : List (String × Nat))
    (seq nid : Nat) (q : List Entry) (m : Nat) (hm : w.maxArrivals = some m) (hst : st.arrivals ≤ m) :
    (makeInstant i w st streams seq nid q).1.arrivals ≤ m := by
  unfold makeInstant
  simp only [hm]
  split
  · exact hst
  · split
    · exact hst
    · simp only
      omega

/-- When the original first entry of instant `k` is taken as head and the workload has created
exactly `k + 1` instants, the next instant is created before anything else happens in the step. -/
def arrive (env : Env) (c : Config) (next : Conf) (nid : Nat) (head : Entry) :
    Config × Conf × Nat × List Draw :=
  match head.first, head.source with
  | some k, .arrival wid _ _ =>
    match env.input.workloads.find? (·.id == wid), next.workloads.find? (·.1 == wid) with
    | some w, some (_, st) =>
      if st.instants == k + 1 then
        let (st, streams, seq, nid, pending, drs) := makeInstant env.input w st next.streams c.seq nid next.pending
        ({ c with seq }, { next with streams, pending, workloads := setW next.workloads wid st }, nid, drs)
      else (c, next, nid, [])
    | _, _ => (c, next, nid, [])
  | _, _ => (c, next, nid, [])

/-- The delivery of a closed workload's `reply` event: the client whose outstanding request id
equals the entry's request field gets its answer, its `client-timeout` entry is removed, and it
thinks and issues again. Workloads in input order. -/
def replies (env : Env) (head : Entry) (c : Conf) (seq nid : Nat) : Conf × Nat × Nat × List Draw :=
  let reqOf (w : WorkloadIn) : Option String := match head.payload with
    | .obj _ fs => match objGet? fs w.requestField with
      | some (.str x) => some x
      | _ => none
    | _ => none
  env.input.workloads.foldl (fun (c, seq, nid, drs) w =>
    if w.kind != .closed || w.reply != head.event then (c, seq, nid, drs) else
    match reqOf w, c.workloads.find? (·.1 == w.id) with
    | some r, some (_, st) =>
      match st.clients.findIdx? (fun o => match o with
          | some n => s!"{w.id}#{n}" == r
          | none => false) with
      | some k =>
        let n := (st.clients.getD k none).getD 0
        let q := c.pending.filter fun e => match e.kind with
          | .clientTimeout w' k' n' => !(w' == w.id && k' == k && n' == n)
          | _ => true
        let (st, streams, seq, nid, pending, ds) := rethink env.input w st k c.time c.streams seq nid q
        ({ c with streams, pending, workloads := setW c.workloads w.id st }, seq, nid, drs ++ ds)
      | none => (c, seq, nid, drs)
    | _, _ => (c, seq, nid, drs)) (c, seq, nid, [])

/-! ## The step -/


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

def faultMatches (kind ev : String) (attempt time : Nat) (f : FaultIn) : Bool :=
  f.isKind kind && f.event == some ev && f.occurrence.matches attempt && f.actsAt time

def injectedOf : Src → List FaultRecord
  | .fault f => [{ fault := f, effect := .injected }]
  | _ => []

/-- A step that ends with settling: the records and the next semantic configuration. -/
def finish (env : Env) (c : Config) (head : Entry) (kind : Kind2) (fired : List Fired2)
    (ignored : List Ignored2) (faults : List FaultRecord) (draws : List Draw) (ops : List (String × Op))
    (touched : List String) (st : Settle) (attempts : List (String × Nat)) (pre : List ResRecord)
    (lrecs : List LinkRec := []) :
    StepResult :=
  match settle env ops touched st with
  | .error msg =>
    .failed { blank c.taken head kind c.conf with responsible := [head.event].filter (· != ""), error := some msg }
  | .ok st =>
    .committed
      { blank c.taken head kind st.conf with
        fired, ignored, faults, responsible := responsibleOf env.input head.event fired faults,
        resources := pre ++ st.recs, draws := draws ++ st.draws, links := lrecs }
      { c with conf := st.conf, seq := st.seq, nid := st.nid, attempts, taken := c.taken + 1 }

/-- After a delivery that did not fail: closed clients receive their replies. -/
def afterDeliver (env : Env) (head : Entry) : StepResult → StepResult
  | .committed rec next =>
    let (conf, seq, nid, drs) := replies env head next.conf next.seq next.nid
    .committed { rec with config := conf, draws := rec.draws ++ drs } { next with conf, seq, nid }
  | r => r

def stepHead (env : Env) (c : Config) (next : Conf) (nid : Nat) (head : Entry) : StepResult :=
  match head.kind with
  | .faultEdge fid on =>
    let active := env.faults.filterMap fun f =>
      if f.window.isSome && ((f.id == fid && on) || (f.id != fid && next.active.contains f.id)) then some f.id
      else none
    let next := { next with active }
    match env.faults.find? (·.id == fid) with
    | none => .committed (blank c.taken head .faultEdge next) { c with conf := next, nid, taken := c.taken + 1 }
    | some f =>
      let name := match f.kind with
        | some "set-capacity" => "capacity"
        | some "set-class-limit" => "limit"
        | some "collapse-classes" => "collapsed"
        | some "scale-demand" => "scaled"
        | _ => "replaced"
      let recs : List FaultRecord := [{ fault := fid, effect := .other name }]
      match f.resource.bind env.input.resource? with
      | some d =>
        let next := match next.resource? d.id with
          | some s => next.setResource d.id { s with capacity := effCapacity env.faults active d }
          | none => next
        finish env c head .faultEdge [] [] recs [] [] [d.id]
          { conf := next, seq := c.seq, nid, draws := [], recs := [] } c.attempts []
      | none =>
        .committed { blank c.taken head .faultEdge next with faults := recs, responsible := [fid] }
          { c with conf := next, nid, taken := c.taken + 1 }
  | .linkDone lid k _ =>
    let skip := StepResult.committed (blank c.taken head .linkDone next) { c with conf := next, nid, taken := c.taken + 1 }
    match env.input.links.find? (·.id == lid) with
    | none => skip
    | some l =>
      let q := next.lqueue lid k
      match q.inTransfer with
      | none => skip
      | some m =>
        let now := next.time
        let s0 : FireState := { next := next.setLQueue lid k { q with inTransfer := none }, seq := c.seq, nid,
                                draws := [], ops := [], lrecs := [linkRec lid k m "transferred" now] }
        let r : Except String FireState := do
          let s ← propagate env.input l k m now s0
          let q := s.next.lqueue lid k
          match q.waiting with
          | m' :: rest => startTransfer env.input l k m' now { s with next := s.next.setLQueue lid k { q with waiting := rest } }
          | [] => pure s
        match r with
        | .error msg => .failed { blank c.taken head .linkDone c.conf with error := some msg }
        | .ok s =>
          .committed { blank c.taken head .linkDone s.next with draws := s.draws, links := s.lrecs }
            { c with conf := s.next, seq := s.seq, nid := s.nid, taken := c.taken + 1 }
  | .clientTimeout wid k n =>
    match env.input.workloads.find? (·.id == wid), next.workloads.find? (·.1 == wid) with
    | some w, some (_, st) =>
      if st.clients.getD k none == some n then
        let (st, streams, seq, nid, pending, drs) :=
          rethink env.input w st k next.time next.streams c.seq nid next.pending
        let next := { next with streams, pending, workloads := setW next.workloads wid st }
        .committed { blank c.taken head .clientTimeout next with draws := drs }
          { c with conf := next, seq, nid, taken := c.taken + 1 }
      else .committed (blank c.taken head .clientTimeout next) { c with conf := next, nid, taken := c.taken + 1 }
    | _, _ => .committed (blank c.taken head .clientTimeout next) { c with conf := next, nid, taken := c.taken + 1 }
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
    match env.faults.filter (faultMatches "drop-event" ev attempt head.time) with
    | d :: ds =>
      let recs := (d :: ds).map fun f => { fault := f.id, effect := FaultEffect.dropped }
      .committed
        { blank c.taken head .drop next with faults := recs, draws := rdraws, responsible := responsibleOf env.input ev [] recs }
        { c with conf := next, nid, attempts, taken := c.taken + 1 }
    | [] =>
      let already := (lookupSeq c.delayedBy head.seq).getD []
      match env.faults.find? (fun f => faultMatches "delay-event" ev attempt head.time f && !already.contains f.id) with
      | some d =>
        if head.time + d.delayBy ≥ two53 then
          .failed { blank c.taken head .delay c.conf with responsible := [ev], error := some "Value time exceeds 2^53." }
        else
        let (payload, nid') := head.payload.copy nid
        let copy : Entry := { head with seq := c.seq, time := head.time + d.delayBy, payload, first := none,
                                        copyOf := some (head.copyOf.getD head.seq) }
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
          afterDeliver env head <| finish env c head .deliver fired ignored (injectedOf head.source ++ recs) (rdraws ++ s.draws)
            s.ops [] { conf := s.next, seq := s.seq, nid := s.nid, draws := [], recs := [] } attempts [] s.lrecs

/-- Put the arrival draws of a step first among its draws. -/
def withDraws (ds : List Draw) : StepResult → StepResult
  | .committed r n => .committed { r with draws := ds ++ r.draws } n
  | .failed r => .failed { r with draws := ds ++ r.draws }
  | r => r

def step (env : Env) (c : Config) : StepResult :=
  match c.conf.pending with
  | [] => .idle
  | h :: _ =>
    if (env.input.scenario.stopAt.map (fun x => decide (h.time > x))).getD false then .stopped else
    let (copy, nid) := c.conf.copy c.nid
    match copy.pending with
    | [] => .idle
    | head :: rest =>
      let (c, next, nid, adraws) := arrive env c { copy with pending := rest, time := head.time } nid head
      withDraws adraws (stepHead env c next nid head)

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
def initialConf (i : Input) (faults : List FaultIn) : Conf × Nat × List Draw :=
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
  -- the edges of windowed resource faults, in `faults` order: `at`, then `until`
  let edge (n t : Nat) (f : FaultIn) (on : Bool) : Entry :=
    { seq := n, time := t, scheduledAt := t, event := "", payload := .null, source := .fault f.id,
      kind := .faultEdge f.id on, target := none, sender := none, routes := none }
  let (q, n) := (faults.filter (·.isResourceKind)).foldl (fun (q, n) f =>
    match f.window with
    | some (a, some u) => (insertE (insertE q (edge n a f true)) (edge (n + 1) u f false), n + 2)
    | some (a, none) => (insertE q (edge n a f true), n + 1)
    | none => (q, n)) (q, n)
  let c : Conf :=
    { time := 0, machines, insts, pending := q,
      resources := i.resources.map fun d => (d.id, { capacity := effCapacity faults [] d, holds := [], waiting := [] }),
      routeCounters := [], streams := [],
      workloads := i.workloads.map fun w => (w.id, { instants := 0, arrivals := 0, cursor := {} }) }
  -- each workload's initial entries, in input order
  let (c, n, _, drs) := i.workloads.foldl (fun (c, n, nid, drs) w =>
    match c.workloads.find? (·.1 == w.id) with
    | some (_, st) =>
      let (c, st, n, nid, ds) := initialWorkload i c w st n nid
      ({ c with workloads := setW c.workloads w.id st }, n, nid, drs ++ ds)
    | none => (c, n, nid, drs)) (c, n, 0, [])
  (c, n, drs)

structure Trace2 where
  input : Input
  initialDraws : List Draw
  faults : List String
  initial : Conf
  steps : List Step2
  outcome : Outcome2
  final : Conf

def traceOf (i : Input) : Trace2 :=
  let env := envOf i
  let (initial, seq, initialDraws) := initialConf i env.faults
  let (conf, nid) := initial.copy 1
  let c0 : Config := { conf, seq, nid, attempts := [], delayedBy := [], taken := 0 }
  let bound := i.scenario.stepLimit
  let r := loop env bound bound
    { config := c0, stepsRev := [], outcome := if conf.pending.isEmpty then .quiescent else .running }
  { input := i, initialDraws, faults := env.faultIds, initial, steps := r.stepsRev.reverse, outcome := r.outcome,
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
      | .send _ (.dist d) _ _ _ _ => if d.draws then some s!"size:{site}" else none
      | .timer _ d _ _ => if d.draws then some s!"after:{site}" else none
      | _ => none) ++
  (i.links.filter (·.latency.draws)).map (fun l => s!"latency:{l.id}") ++
  (i.routes.filter (·.rby == "random")).map (fun r => s!"route:{r.event}:{r.behavior}") ++
  i.workloads.flatMap fun w =>
    (match w.groupSize with
     | some d => if d.draws then [s!"groups:{w.id}"] else []
     | none => []) ++
    (if w.kind != .open_ && w.start.draws then [s!"start:{w.id}"] else []) ++
    (if w.kind == .closed && w.think.draws then [s!"think:{w.id}"] else []) ++
    (if w.poisson then [s!"arrival:{w.id}"] else []) ++
    (if w.batch.draws then [s!"batch:{w.id}"] else []) ++
    (match w.clients with
     | some cl => if cl.roundRobin || w.kind != .open_ then [] else [s!"client:{w.id}"]
     | none => []) ++
    w.payload.filterMap fun (f, pf) => match pf with
      | .sample d => if d.draws then some s!"payload:{w.id}:{f}" else none
      | .choose .. => some s!"payload:{w.id}:{f}"
      | _ => none

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
  let ids := i.behaviors.map (·.id) ++ i.resources.map (·.id) ++ i.workloads.map (·.id) ++ i.links.map (·.id)
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
        | .send _ _ _ _ via _ =>
          if !(i.links.any (·.id == via)) then throw s!"Effect sends over \"{via}\", which is not a link."
        | _ => pure ()
  for d in i.resources do
    let total := d.classes.foldl (fun acc c => acc + c.reserved) 0
    if total > d.capacity then throw s!"Resource \"{d.id}\" reserves more units than its capacity."
    for c in d.classes do
      if let some l := c.limit then
        if c.reserved > l then throw s!"Class \"{c.id}\" of \"{d.id}\" reserves more units than its limit."
  -- format-2 faults
  let sfaults := (envOf i).faults
  for f in sfaults do
    if f.isKind "inject-event" && f.window.isSome then throw s!"Fault \"{f.id}\": inject-event takes no window."
    if let some (a, some u) := f.window then
      if u ≤ a then throw s!"Fault \"{f.id}\" has an empty window."
    if f.isKind "replace-demand" then
      let ok := match f.behavior.bind i.behavior? with
        | some b => match (b.transitions.find? (some ·.id == f.transition)).bind (·.effects[f.effect]?) with
          | some (.request .use ..) => true
          | _ => false
        | none => false
      if !ok then throw s!"Fault \"{f.id}\" names no use effect."
    else if f.isResourceKind then
      match f.resource.bind i.resource? with
      | none => throw s!"Fault \"{f.id}\" names \"{f.resource.getD ""}\", which is not a resource."
      | some d =>
        if f.isKind "set-class-limit" && !(d.classes.any (some ·.id == f.cls)) then
          throw s!"Fault \"{f.id}\" names no class of \"{d.id}\"."
  -- validity after the fault mask (untimed faults)
  for d in i.resources do
    let cap := effCapacity sfaults [] d
    let total := d.classes.foldl (fun acc c => acc + c.reserved) 0
    if total > cap then
      let f := ((sfaults.filter fun f => f.window.isNone && f.isKind "set-capacity" && f.resource == some d.id).getLast?.map (·.id)).getD ""
      throw s!"Fault \"{f}\" leaves \"{d.id}\" with reserved units above capacity."
    let de := effDecl sfaults [] d
    for c in de.classes do
      if let some l := c.limit then
        if c.reserved > l then
          let f := ((sfaults.filter fun f => f.window.isNone && f.isKind "set-class-limit" && f.resource == some d.id && f.cls == some c.id).getLast?.map (·.id)).getD ""
          throw s!"Fault \"{f}\" leaves \"{d.id}\" with reserved units above a class limit."
  -- time
  if i.unit == "tick" && i.perSecond.isSome then throw "Unit tick has no rate."
  let mut li := 0
  for l in i.links do
    if i.perSecond.isNone && l.bandwidth.isSome then throw s!"Unit tick has no rate; \"links[{li}]\" needs one."
    li := li + 1
  -- workloads
  let mut wi := 0
  for w in i.workloads do
    if !i.isEvent w.event then throw s!"Workload \"{w.id}\" generates \"{w.event}\", which is not an event."
    if w.kind == .closed then
      if !i.isEvent w.reply then throw s!"Workload \"{w.id}\" waits for \"{w.reply}\", which is not an event."
      if let some to := w.timeout then
        if i.scenario.horizon.getD 0 + to ≥ two53 then
          throw s!"Workload \"{w.id}\" has a timeout that reaches 2^53 after the horizon."
    if w.kind == .population then
      match i.behavior? w.behavior with
      | some { instances := .keyed _ max, .. } =>
        let total := (i.workloads.filter fun x => x.kind == .population && x.behavior == w.behavior).foldl
          (fun acc x => acc + x.population) 0
        if total > max then throw s!"Population of \"{w.behavior}\" exceeds its max of {max} instances."
      | _ => throw s!"Workload \"{w.id}\" names \"{w.behavior}\", which is not a keyed behavior."
    if w.kind != .open_ then
      wi := wi + 1
      continue
    if i.perSecond.isNone then throw s!"Unit tick has no rate; \"workloads[{wi}]\" needs one."
    let ps := i.perSecond.getD 1
    let ok := (w.phases.all fun ph => decide (ph.start < ph.stop)) &&
      ((w.phases.zip w.phases.tail).all fun (a, b) => decide (a.stop ≤ b.start)) &&
      (match w.period with
       | some p => decide (p ≥ ((w.phases.getLast?).map (·.stop)).getD 0)
       | none => true) &&
      (w.poisson || w.phases.all fun ph => match ph.rate with
        | .ramp .. => false
        | _ => true)
    if !ok then throw s!"Workload \"{w.id}\" has malformed phases."
    let mut pi := 0
    for ph in w.phases do
      let ((a0, b0), (a1, b1)) := ph.rate.ends
      if ps * b0 < 100 * a0 || ps * b1 < 100 * a1 then
        throw s!"Phase {pi} of workload \"{w.id}\" has a mean interarrival below 100 base units; use a finer unit."
      pi := pi + 1
    if let .fixed 0 := w.batch then throw s!"Workload \"{w.id}\" has a batch below 1."
    if w.poisson && i.unitExp.isEmpty then
      throw "Input field \"unitExponential\" is required by a Poisson workload."
    wi := wi + 1
  -- seed
  if i.scenario.seed.isNone then
    if let some s := (sampledSites i).head? then throw s!"Input samples \"{s}\" but declares no seed."
  if !i.workloads.isEmpty && i.scenario.horizon.isNone then
    throw s!"Scenario \"{sid}\" has workloads but no horizon."
  for c in i.requests do
    if !i.isEvent c.startEvent then throw s!"Request class \"{c.id}\" starts on \"{c.startEvent}\", which is not an event."
    for (e, _) in c.ends do
      if !i.isEvent e then throw s!"Request class \"{c.id}\" ends on \"{e}\", which is not an event."
    if let some w := c.startWorkload then
      if !(i.workloads.any (·.id == w)) then throw s!"Request class \"{c.id}\" names \"{w}\", which is not a workload."
  if i.measures && i.scenario.horizon.isNone then
    throw s!"Scenario \"{sid}\" measures outputs but has no horizon."
  match i.scenario.horizon, i.scenario.warmup, i.scenario.stopAt with
  | some h, some w, _ => if w ≥ h then throw "Scenario warmup must be below its horizon."
  | _, _, _ => pure ()
  match i.scenario.horizon, i.scenario.stopAt with
  | some h, some s => if s < h then throw "Scenario stopAt must be at least its horizon."
  | _, _ => pure ()
  match i.series, i.scenario.horizon with
  | some b, some h =>
    if (h - i.scenario.warmup.getD 0) % b != 0 then throw "Metrics series bucket must divide the window."
  | _, _ => pure ()

/-! ## Measured outputs

Metrics are a pure function of the run (`docs/simulation.md`, "Measured outputs"), here of the
trace: the window is `W = [warmup, horizon)`; signals are piecewise constant between steps, the
initial configuration's value holding from 0 and the last value holding to the horizon; waiting
times are attributed by the request's `since`, one sample per enqueued request, `waited` for a
grant and +∞ (`none`) for a request removed without one or still waiting when the run ends. -/

structure ResSignals where
  busy : Nat := 0
  capTime : Nat := 0
  maxHeld : Nat := 0
  queueInt : Nat := 0
  maxWaiting : Nat := 0
  deriving Inhabited

/-- Units held, requests waiting and capacity of a resource in a configuration. -/
def signalsAt (d : ResourceDecl) (c : Conf) : Nat × Nat × Nat :=
  match c.resource? d.id with
  | some s => (Res.sumUnits (fun _ => true) s.holds, s.waiting.length, s.capacity)
  | none => (0, 0, 0)

/-- Add the segment `[a, b)` with the configuration's values, clipped to `[w, h)`. -/
def addSegment (d : ResourceDecl) (w h a b : Nat) (c : Conf) (acc : ResSignals) : ResSignals :=
  let len := min b h - max a w
  if len = 0 then acc else
  let (held, waiting, cap) := signalsAt d c
  { busy := acc.busy + held * len, capTime := acc.capTime + cap * len, maxHeld := max acc.maxHeld held,
    queueInt := acc.queueInt + waiting * len, maxWaiting := max acc.maxWaiting waiting }

/-- Integrate a resource's signals over `[w, h)` from the points `(time, configuration)`. -/
def integrate (d : ResourceDecl) (w h : Nat) : List (Nat × Conf) → ResSignals → ResSignals
  | [], acc => acc
  | [(t, c)], acc => addSegment d w h t (max t h) c acc
  | (t, c) :: (t', c') :: rest, acc => integrate d w h ((t', c') :: rest) (addSegment d w h t t' c acc)

/-- The waiting-time samples of a resource for requests enqueued in `[w, h)`, in enqueue order. -/
def waitSamples (r : String) (w h : Nat) (recs : List ResRecord) : List (Option Nat) :=
  let mine := recs.filter (·.resource == r)
  (mine.filter fun x => x.action == "enqueued" && decide (w ≤ x.atTime) && decide (x.atTime < h)).map fun x =>
    match mine.find? fun y => y.request == x.request &&
        ["granted", "refused", "shed", "dropped", "timed-out"].contains y.action with
    | some y => if y.action == "granted" then some (y.waited.getD 0) else none
    | none => none

/-- Nearest rank `max(1, ⌈a·n/b⌉)` over samples sorted ascending with +∞ last. -/
def nearestRank (samples : List (Option Nat)) (a b : Nat) : Option (Option Nat) :=
  let n := samples.length
  if n = 0 then none else
  let finite := (samples.filterMap id).mergeSort (· ≤ ·)
  let rank := max 1 ((a * n + b - 1) / b)
  some (finite[rank - 1]?)

def signalPoints (initial : Conf) (steps : List Step2) : List (Nat × Conf) :=
  (0, initial) :: steps.map fun st => (st.time, st.config)

/-! ## The request lifecycle

Requests of a class start when an original entry of its start event (from its workload, if one is
named) is first taken as head, whatever the step then does; their key is the entry's
`payload[key]` (as canonical JSON) and their start time its `scheduledAt`. A start entry that is
dropped, or delivered while no transition fires on it, ends its request at once with outcome
`error`; a delayed copy (`copyOf`) carries the decision to the step that takes it. A request ends
at the first delivery (a `deliver` step that does not fail) of an end event of its class carrying
its key, with that end's outcome, or with `timeout` at its closed client's `client-timeout` step.
A request not ended when the run ends is censored. -/

structure Rq where
  key : String
  start : Nat
  origSeq : Nat
  legit : Option Bool
  outcome : Option (String × Nat) := none
  deriving Inhabited

structure ClassAcc where
  reqs : List Rq := []
  unkeyed : Nat := 0
  duplicate : Nat := 0
  lateEnds : Nat := 0
  deriving Inhabited

def payloadKey (p : Value) (k : String) : Option String :=
  match p with
  | .obj _ fs => match objGet? fs k with
    | some .undef | none => none
    | some v => some (Json.write v)
  | _ => none

/-- Whether an entry belongs to a class's start: its event, and its workload when one is named. -/
def startsClass (c : ReqClassIn) (h : Entry) : Bool :=
  h.event == c.startEvent && (match h.kind with | .event => true | _ => false) &&
  (match c.startWorkload with
   | none => true
   | some w => match h.source with
     | .arrival w' _ _ => w' == w
     | _ => false)

/-- The legitimacy of a request, from the workload that started it: an arrival's workload, or the
population whose client instance emitted the start entry. -/
def legitOf (i : Input) (h : Entry) : Option Bool :=
  match h.source with
  | .arrival w _ _ => (i.workloads.find? (·.id == w)).map (·.legitimate)
  | .transition _ b =>
    match h.sender with
    | some { inst := .str s, .. } =>
      (i.workloads.find? fun w => w.kind == .population && w.behavior == b && s.startsWith (w.id ++ ":")).map
        (·.legitimate)
    | _ => none
  | _ => none

def endWhere (p : Rq → Bool) (o : String) (t : Nat) : List Rq → List Rq
  | [] => []
  | r :: rs => if r.outcome.isNone && p r then { r with outcome := some (o, t) } :: rs else r :: endWhere p o t rs

/-- One end per request: ending requests never changes a request that has already ended. -/
theorem endWhere_keeps_ended (p : Rq → Bool) (o : String) (t : Nat) :
    ∀ (rs : List Rq) (i : Nat) (r : Rq), rs[i]? = some r → r.outcome.isSome = true →
      (endWhere p o t rs)[i]? = some r := by
  intro rs
  induction rs with
  | nil => intro i r h; simp at h
  | cons x xs ih =>
    intro i r h hs
    unfold endWhere
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      have : (x.outcome.isNone && p x) = false := by
        cases ho : x.outcome <;> simp_all
      simp [this]
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      split <;> simp [ih k r h hs, h]

/-- Ending requests changes at most the outcome: every request keeps its key and start. -/
theorem endWhere_length (p : Rq → Bool) (o : String) (t : Nat) :
    ∀ rs : List Rq, (endWhere p o t rs).length = rs.length := by
  intro rs
  induction rs with
  | nil => rfl
  | cons x xs ih => unfold endWhere; split <;> simp [ih]

def lifeStep (i : Input) (c : ReqClassIn) (acc : ClassAcc) (st : Step2) : ClassAcc :=
  let h := st.head
  let failed := st.error.isSome
  let isStart := startsClass c h
  -- the start, on the original entry
  let acc := if isStart && h.copyOf.isNone then
      match payloadKey h.payload c.key with
      | none => { acc with unkeyed := acc.unkeyed + 1 }
      | some k =>
        if acc.reqs.any (fun r => r.key == k && r.outcome.isNone) then { acc with duplicate := acc.duplicate + 1 }
        else { acc with reqs := acc.reqs ++ [{ key := k, start := h.scheduledAt, origSeq := h.seq, legit := legitOf i h }] }
    else acc
  -- a start entry that is lost ends its request with `error`
  let acc := if isStart && !failed &&
      (st.kind == .drop || (st.kind == .deliver && st.fired.isEmpty)) then
      let orig := h.copyOf.getD h.seq
      { acc with reqs := endWhere (·.origSeq == orig) "error" st.time acc.reqs }
    else acc
  -- ends: deliveries of an end event carrying the key
  let acc := if st.kind == .deliver && !failed then
      match c.ends.find? (·.1 == h.event), payloadKey h.payload c.key with
      | some (_, o), some k =>
        if acc.reqs.any (fun r => r.key == k && r.outcome.isNone) then
          { acc with reqs := endWhere (·.key == k) o st.time acc.reqs }
        else if acc.reqs.any (·.key == k) then { acc with lateEnds := acc.lateEnds + 1 }
        else acc
      | _, _ => acc
    else acc
  -- a closed client's timeout
  match h.kind with
  | .clientTimeout w _ n =>
    match i.workloads.find? (·.id == w) with
    | some wl =>
      if wl.event == c.startEvent && (c.startWorkload.all (· == w)) then
        let k := Json.write (.str s!"{w}#{n}")
        { acc with reqs := endWhere (·.key == k) "timeout" st.time acc.reqs }
      else acc
    | none => acc
  | _ => acc

def lifecycle (i : Input) (c : ReqClassIn) (steps : List Step2) : ClassAcc :=
  steps.foldl (lifeStep i c) {}

/-- The sample of a request: its response time when it ended `ok`, else +∞ (`none`). -/
def Rq.sample (r : Rq) : Option Nat :=
  match r.outcome with
  | some ("ok", t) => some (t - r.start)
  | _ => none

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
  | .arrival w k cl => o [("kind", s "arrival"), ("workload", s w), ("n", n k),
                          ("client", match cl with | some c => s c | none => .null)]
  | .clientTimeout w k cl => o [("kind", s "client-timeout"), ("workload", s w), ("n", n k), ("client", s cl)]
  | .timer b v t => o [("kind", s "timer"), ("behavior", s b), ("instance", v), ("timer", s t)]
  | .link l m => o [("kind", s "link"), ("link", s l), ("message", n m)]

def opt (k : String) : Option Value → List (String × Value)
  | some v => [(k, v)]
  | none => []

def entryFields (e : Entry) : List (String × Value) :=
  (match e.kind with
   | .event => []
   | .serviceDone r q _ _ => [("kind", s "service-done"), ("resource", s r), ("request", n q.id)]
   | .waitTimeout r q => [("kind", s "wait-timeout"), ("resource", s r), ("request", n q)]
   | .clientTimeout w k q => [("kind", s "client-timeout"), ("workload", s w), ("client", n k), ("request", n q)]
   | .linkDone l k m => [("kind", s "link-done"), ("link", s l), ("queue", s k), ("message", n m)]
   | .faultEdge f on => [("kind", s "fault-edge"), ("fault", s f), ("edge", s (if on then "at" else "until"))]) ++
  opt "target" (e.target.map addr) ++ opt "from" (e.sender.map addr) ++
  (match e.routes with
   | some (r :: rs) => [("routes", o ((r :: rs).map fun (b, v) => (b, v)))]
   | _ => []) ++
  (if e.first.isSome then [("first", .bool true)] else []) ++
  opt "timer" (e.timer.map s) ++ opt "copyOf" (e.copyOf.map n)

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

def msg (m : Msg) : Value :=
  o ([("message", n m.id), ("event", s m.event), ("size", n m.size), ("sentAt", n m.sentAt),
      ("payload", m.payload)] ++ opt "target" (m.target.map addr) ++ opt "from" (m.sender.map addr))

def lqueue (q : LQueue) : Value :=
  o [("inTransfer", match q.inTransfer with | some m => msg m | none => .null),
     ("waiting", a (q.waiting.map msg)),
     ("lastDelivery", match q.lastDelivery with | some t => n t | none => .null)]

def linkRec (r : LinkRec) : Value :=
  o [("link", s r.link), ("queue", s r.queue), ("message", n r.message), ("action", s r.action),
     ("at", n r.atTime), ("size", n r.size)]

def configuration (i : Input) (c : Conf) : Value :=
  o [("time", n c.time),
     ("machines", o (c.machines.map fun (id, m) =>
        (id, o [("state", s m.state), ("vars", .obj 0 m.vars)]))),
     ("pending", a (c.pending.map pending)),
     ("resources", o (i.resources.map fun d => (d.id, resource c d))),
     ("links", o (i.links.map fun l =>
        (l.id, o ((c.lqueues.filter (·.1.1 == l.id)).map fun ((_, k), q) => (k, lqueue q))))),
     ("timers", o (c.pending.filterMap fun e => e.timer.map fun t => (t, n e.seq))),
     ("workloads", o (c.workloads.map fun (id, w) =>
        (id, o ([("instants", n w.instants), ("arrivals", n w.arrivals), ("repetition", n w.cursor.rep),
                ("phase", n w.cursor.phase), ("j", n w.cursor.j),
                ("last", match w.cursor.last with | some t => n t | none => .null),
                ("done", .bool w.cursor.done)] ++
                (match (i.workloads.find? (·.id == id)).map (·.kind) with
                 | some .closed => [("clients", a (w.clients.map fun x => match x with
                     | some k => n k
                     | none => .null))]
                 | _ => []) ++
                (if w.groups.isEmpty then [] else [("groups", a (w.groups.map n))]))))),
     ("meters", o []),
     ("routeCounters", o (c.routeCounters.map fun (k, v) => (k, n v))),
     ("streams", o (c.streams.map fun (k, v) => (k, n v))),
     ("down", a []),
     ("activeFaults", strings c.active),
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
      ("links", a (st.links.map linkRec)),
      ("draws", a (st.draws.map draw)),
      ("config", configuration i st.config)] ++
     match st.error with
     | some m => [("error", o [("message", s m)])]
     | none => [])

def quantileValue : Option (Option Nat) → Value
  | none => o [("value", .null), ("empty", .bool true)]
  | some none => o [("value", .null), ("infinite", .bool true)]
  | some (some v) => o [("value", n v)]

def samplesValue (samples : List (Option Nat)) (qs : List (String × Nat × Nat)) : Value :=
  let fin := samples.filterMap id
  o [("count", n samples.length), ("finite", n fin.length), ("infinite", n (samples.length - fin.length)),
     ("sum", n (fin.foldl (· + ·) 0)), ("max", match fin.max? with | some m => n m | none => .null),
     ("quantiles", o (qs.map fun (key, a, b) => (key, quantileValue (nearestRank samples a b))))]

/-- A class's requests measured in `[lo, hi)` (attributed by start time). -/
def classValue (qs : List (String × Nat × Nat)) (acc : ClassAcc) (lo hi : Nat) : Value :=
  let ms := acc.reqs.filter fun r => decide (lo ≤ r.start) && decide (r.start < hi)
  let cnt (rs : List Rq) (x : String) := (rs.filter fun r => (r.outcome.map (·.1)) == some x).length
  let leg := ms.filter (·.legit == some true)
  o [("measured", n ms.length),
     ("outcomes", o [("ok", n (cnt ms "ok")), ("refused", n (cnt ms "refused")), ("timeout", n (cnt ms "timeout")),
                     ("error", n (cnt ms "error")), ("censored", n (ms.filter (·.outcome.isNone)).length)]),
     ("responseTime", samplesValue (ms.map (·.sample)) qs),
     ("legitimate", o [("measured", n leg.length), ("refused", n (cnt leg "refused"))])]

/-- Firings of each transition (`<behavior>.<transition>`) in `[lo, hi)`. -/
def transitionsValue (i : Input) (steps : List Step2) (lo hi : Nat) : Value :=
  let fired := (steps.filter fun st => decide (lo ≤ st.time) && decide (st.time < hi)).flatMap (·.fired)
  o (i.behaviors.flatMap fun b => b.transitions.map fun tr =>
    (s!"{b.id}.{tr.id}", n (fired.filter fun f => f.base.behavior == b.id && f.base.transition == tr.id).length))

def metrics (t : Trace2) : Value :=
  let i := t.input
  let w := i.scenario.warmup.getD 0
  let h := i.scenario.horizon.getD 0
  let qs := i.metrics.getD [("0.5", 1, 2), ("0.9", 9, 10), ("0.99", 99, 100)]
  let pts := signalPoints t.initial t.steps
  let recs := t.steps.flatMap (·.resources)
  let accs := i.requests.map fun c => (c, lifecycle i c t.steps)
  o ([("window", o [("from", n w), ("until", n h)]),
     ("requests", o (accs.map fun (c, acc) =>
        (c.id, match classValue qs acc w h with
          | .obj k fs => .obj k (fs ++ [("unkeyed", n acc.unkeyed), ("duplicate", n acc.duplicate),
                                        ("lateEnds", n acc.lateEnds), ("window", n (h - w))])
          | v => v))),
     ("transitions", transitionsValue i t.steps w h),
     ("resources", o (i.resources.map fun d =>
        let sg := integrate d w h pts {}
        let ws := waitSamples d.id w h recs
        let fin := ws.filterMap id
        (d.id, o [
          ("utilisation", o [("busy", n sg.busy), ("capacityTime", n sg.capTime), ("max", n sg.maxHeld)]),
          ("queueLength", o [("integral", n sg.queueInt), ("window", n (h - w)), ("max", n sg.maxWaiting)]),
          ("waitingTime", o [("count", n ws.length), ("finite", n fin.length),
                             ("infinite", n (ws.length - fin.length)), ("sum", n (fin.foldl (· + ·) 0)),
                             ("max", match fin.max? with | some m => n m | none => .null),
                             ("quantiles", o (qs.map fun (key, a, b) => (key, quantileValue (nearestRank ws a b))))])])))] ++
     match i.series with
     | some b =>
       [("series", o [("bucket", n b), ("buckets", a ((List.range ((h - w) / b)).map fun k =>
          let lo := w + k * b
          o [("from", n lo), ("until", n (lo + b)),
             ("requests", o (accs.map fun (c, acc) => (c.id, classValue qs acc lo (lo + b)))),
             ("transitions", transitionsValue i t.steps lo (lo + b))]))])]
     | none => [])

def trace (t : Trace2) : Value :=
  let i := t.input
  let truncated := t.outcome == .stepLimit || t.outcome == .error
  o ([("version", n 2), ("timeUnit", s i.unit),
      ("seed", match i.scenario.seed with | some x => s (toString x.toNat) | none => .null),
      ("scenarioId", s i.scenario.id), ("faults", strings t.faults),
      ("initialDraws", a (t.initialDraws.map draw))] ++
     (if i.scenario.output == "metrics" then [] else
       [("initial", configuration i t.initial), ("steps", a (t.steps.map (step i)))]) ++
     [("stepsTaken", n t.steps.length), ("outcome", s t.outcome.name),
      ("truncated", .bool truncated), ("final", configuration i t.final)] ++
     (if i.measures then [("metrics", metrics t)] else []))

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
