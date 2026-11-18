import Exegra.Expr
import Exegra.Input
import Exegra.Trace

/-
The step semantics of the behavior language: the definition the Rust engine
(`engine/exegra-engine/src/engine.rs`) is checked against.

* `Env` is the static part of a run, derived from the engine input: the behaviors in scenario
  order with their transitions, the active faults, and the entity table.
* `Config` is the dynamic part: the observable `Configuration` (time, machines, pending queue)
  plus the run's bookkeeping (next sequence number, next object identity, delivery attempts per
  event, the delay faults each queue entry has already suffered, steps taken).
* `step : Env → Config → StepResult` is one event delivery. It is a total function, so it is
  deterministic by construction (`Exegra/Properties.lean`).
* `runEnv` repeats `step` until the queue is empty, the step limit is reached or a step fails.
  Its recursion is on fuel equal to the step bound, and `Properties.lean` proves that the fuel
  never runs out before the run stops.

Every place where the Rust engine's order of evaluation or of checks decides an observable
result is marked ORDER, and every place where the engine's behavior looks accidental rather
than designed, and is mirrored on purpose, is marked MIRRORED.
-/

namespace Exegra

/-! ## Static environment -/

/-- What an id names in the input. -/
inductive Entity where
  | event
  | behavior (b : BehaviorIn)
  | fault (f : FaultIn)
  | scenario

/-- The entity an id names. A later declaration with the same id replaces an earlier one, in the
order events, behaviors, faults, scenario (`EngineSource::new`).
MIRRORED: so an id declared both as an event and as a behavior is not an event. -/
def entityOf (i : SimInput) (id : String) : Option Entity :=
  if i.scenario.id == id then some .scenario
  else match i.faults.reverse.find? (·.id == id) with
    | some f => some (.fault f)
    | none => match i.behaviors.reverse.find? (·.id == id) with
      | some b => some (.behavior b)
      | none => if i.events.contains id then some .event else none

def isEvent (i : SimInput) (id : String) : Bool :=
  match entityOf i id with
  | some .event => true
  | _ => false

def behaviorOf? (i : SimInput) (id : String) : Option BehaviorIn :=
  match entityOf i id with
  | some (.behavior b) => some b
  | _ => none

def faultOf? (i : SimInput) (id : String) : Option FaultIn :=
  match entityOf i id with
  | some (.fault f) => some f
  | _ => none

/-- Transitions owned by a behavior id, in declaration order (all behaviors with that id). -/
def transitionsOf (i : SimInput) (bid : String) : List TransitionIn :=
  (i.behaviors.filter (·.id == bid)).flatMap (·.transitions)

/-- Remove repeats, keeping first occurrences. -/
def dedup (xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

structure Env where
  input : SimInput
  /-- One entry per input behavior, in scenario order, with its transitions.
  MIRRORED: a repeated behavior id gives two entries, so that behavior is scanned twice in a
  step (a validated model has unique ids). -/
  behaviors : List (String × List TransitionIn)
  /-- The active fault ids, in order, without repeats. -/
  faultIds : List String
  /-- The active faults, in `faultIds` order. -/
  faults : List FaultIn

def envOf (i : SimInput) : Env where
  input := i
  behaviors := i.behaviors.map fun b => (b.id, transitionsOf i b.id)
  faultIds := dedup i.scenario.faults
  faults := (dedup i.scenario.faults).filterMap (faultOf? i)

/-- The step bound: the least number of steps `k ≥ 1` with `k ≥ stepLimit`.
The engine stops when `steps.len() as f64 >= stepLimit` after a committed step that leaves
events pending; for a finite limit and fewer than 2^53 steps that is exactly `k ≥ stepBound`.
A limit of 1 or less still allows one step (`docs/simulation.md`). JSON cannot carry a
non-finite limit. -/
def stepBound (limit : Float) : Nat :=
  max 1 (if limit ≤ 1 then 1 else limit.ceil.toUInt64.toNat)

/-! ## Queue and configuration helpers -/

/-- Insert keeping the queue ordered by `(time, seq)`: walking back from the end over the entries
with a later time, so a new entry goes after every entry with an equal or earlier time
(`insert_pending`). -/
def insertPending (q : List Pending) (e : Pending) : List Pending :=
  let later := (q.reverse.takeWhile fun p => decide (p.time > e.time)).length
  let pos := q.length - later
  q.take pos ++ [e] ++ q.drop pos

def copyMachines : List (String × Machine) → Nat → List (String × Machine) × Nat
  | [], n => ([], n)
  | (id, m) :: ms, n =>
    let (vars, n1) := Value.copyFields m.vars n
    let (rest, n2) := copyMachines ms n1
    ((id, { m with vars }) :: rest, n2)

def copyPending : List Pending → Nat → List Pending × Nat
  | [], n => ([], n)
  | p :: ps, n =>
    let (payload, n1) := p.payload.copy n
    let (rest, n2) := copyPending ps n1
    ({ p with payload } :: rest, n2)

/-- The reference engine's `deepCopy` of a configuration: every array and object inside gets a
fresh identity. -/
def Configuration.copy (c : Configuration) (n : Nat) : Configuration × Nat :=
  let (machines, n1) := copyMachines c.machines n
  let (pending, n2) := copyPending c.pending n1
  ({ c with machines, pending }, n2)

def lookupNat (xs : List (String × Nat)) (k : String) : Option Nat :=
  (xs.find? (·.1 == k)).map (·.2)

def lookupSeq (xs : List (Nat × List String)) (k : Nat) : Option (List String) :=
  (xs.find? (·.1 == k)).map (·.2)

/-! ## Initial configuration -/

/-- The machines of a run: one per distinct behavior id, at the position of its first
occurrence, with the data of the behavior that id names (`behaviors` map of the engine). -/
def initialMachines (i : SimInput) : List (String × Machine) :=
  (dedup (i.behaviors.map (·.id))).filterMap fun bid =>
    (behaviorOf? i bid).map fun b =>
      (bid, { state := b.initial,
              vars := b.variables.foldl (fun vs v => objInsert vs v.name v.initial) [] })

/-- The initial queue: the scenario's steps in array order with `seq` 0, 1, ..., then the active
`inject-event` faults in fault order. Returns the queue and the next sequence number. -/
def initialPending (i : SimInput) (faults : List FaultIn) : List Pending × Nat :=
  let (q, n) := i.scenario.steps.foldl (fun (q, n) st =>
    (insertPending q { seq := n, time := st.time, event := st.event, payload := st.payload,
                       source := .scenario n }, n + 1)) ([], 0)
  (faults.filter (·.isKind "inject-event")).foldl (fun (q, n) f =>
    (insertPending q { seq := n, time := f.injectAt, event := f.event.getD "",
                       payload := f.payload, source := .fault f.id }, n + 1)) (q, n)

/-- The configuration before the first step (identities not yet assigned). -/
def initialConfiguration (i : SimInput) : Configuration × Nat :=
  let (pending, seq) := initialPending i (envOf i).faults
  ({ time := 0, machines := initialMachines i, pending }, seq)

/-- The creation refusals (`Simulation::new`), in the engine's order. -/
def validate (i : SimInput) : Except String Unit := do
  let sid := i.scenario.id
  -- ORDER: behaviors, then active faults, then step events, then injected events.
  for bid in i.behaviors.map (·.id) do
    if (behaviorOf? i bid).isNone then
      throw s!"Scenario \"{sid}\" lists \"{bid}\", which is not a behavior."
  for id in dedup i.scenario.faults do
    if (faultOf? i id).isNone then throw s!"\"{id}\" is not a fault in this model."
  let mut k := 0
  for st in i.scenario.steps do
    if !isEvent i st.event then
      throw s!"Scenario \"{sid}\" step {k} delivers \"{st.event}\", which is not an event."
    k := k + 1
  for f in (envOf i).faults do
    if f.isKind "inject-event" then
      match f.event with
      | some e => if !isEvent i e then throw s!"Fault \"{f.id}\" injects \"{e}\", which is not an event."
      | none => throw s!"Fault \"{f.id}\" injects \"undefined\", which is not an event."

/-! ## Expressions in a behavior's scope -/

/-- Reference resolution in one behavior's scope (`resolve`): `time`; a bare name is a variable
of the behavior; `event.<field>` a payload field; `<behavior>.state` and `<behavior>.<name>`.
ORDER: `time` wins over a variable named `time`, `event.` over a behavior named `event`, and
`.state` over a variable named `state`. -/
def resolve (view : Configuration) (bid : String) (payload : Value) (time : Float) :
    List String → Value
  | ["time"] => .num time
  | [name] => match view.machine? bid with
    | some m => (objGet? m.vars name).getD .undef
    | none => .undef
  | ["event", f] => match payload with
    | .obj _ fs => (objGet? fs f).getD .undef
    | _ => .undef
  | [b, name] => match view.machine? b with
    | none => .undef
    | some m => if name == "state" then .str m.state else (objGet? m.vars name).getD .undef
  | _ => .undef

/-- Parse an expression; a parse error is reported with its source. -/
def compile (src : String) : Except String Ast :=
  match parseExpr src with
  | .ok a => .ok a
  | .error e => .error s!"Expression \"{src}\": {e}"

def evalIn (src : String) (view : Configuration) (bid : String) (payload : Value) (time : Float) :
    Except String Value :=
  match compile src with
  | .error e => .error e
  | .ok ast => eval (resolve view bid payload time) ast

/-- The value of an effect `to` or payload entry: a string is an expression, anything else a
literal, copied (fresh identities from `nid`). -/
def valueOf (x : Option Value) (view : Configuration) (bid : String) (payload : Value)
    (time : Float) (nid : Nat) : Except String (Value × Nat) :=
  match x with
  | none => .error "Effect has no value."
  | some (.str src) => (evalIn src view bid payload time).map fun v => (v, nid)
  | some v => .ok (v.copy nid)

def guardHolds (t : TransitionIn) (view : Configuration) (bid : String) (payload : Value)
    (time : Float) : Except String Bool :=
  match t.guard with
  | none => .ok true
  | some g => match evalIn g view bid payload time with
    | .error e => .error e
    | .ok (.bool b) => .ok b
    | .ok _ => .error s!"Guard \"{g}\" of transition \"{t.id}\" did not evaluate to a boolean."

/-! ## Phase 1: choosing a transition per behavior -/

/-- Active faults of a kind that target a transition. -/
def targeting (faults : List FaultIn) (kind tid : String) : List FaultIn :=
  faults.filter fun f => f.isKind kind && f.transition == some tid

/-- What one behavior's scan found. -/
inductive Choice where
  | win (t : TransitionIn)
  | ignore (i : Ignored)

/-- Scan a behavior's transitions in declaration order (`deliver`, phase 1). `considered`,
`disabledWouldFire`, `guardFalse` and `recs` (the `disabled` records, in order) accumulate.
ORDER: the `faultOnly` test comes before the transition is considered, the guard is evaluated
before the disable faults are looked at (so a disabled transition with a false guard records
nothing), and a guard error ends the whole step. -/
def scan (faults : List FaultIn) (cur : Configuration) (bid : String) (state : Option String)
    (event : String) (payload : Value) (time : Float) :
    List TransitionIn → List String → Bool → Bool → List FaultRecord →
    Except String (Option (TransitionIn × List FaultIn) × List String × Bool × Bool × List FaultRecord)
  | [], considered, dis, gf, recs => .ok (none, considered, dis, gf, recs)
  | t :: ts, considered, dis, gf, recs =>
    if some t.source != state || t.on != event then
      scan faults cur bid state event payload time ts considered dis gf recs
    else
      let enablers := targeting faults "enable-transition" t.id
      if t.faultOnly && enablers.isEmpty then
        scan faults cur bid state event payload time ts considered dis gf recs
      else
        let considered := considered ++ [t.id]
        let disablers := targeting faults "disable-transition" t.id
        match guardHolds t cur bid payload time with
        | .error e => .error e
        | .ok false => scan faults cur bid state event payload time ts considered dis true recs
        | .ok true =>
          if !disablers.isEmpty then
            scan faults cur bid state event payload time ts considered true gf
              (recs ++ disablers.map fun d => { fault := d.id, effect := .disabled })
          else
            .ok (some (t, if t.faultOnly then enablers else []), considered, dis, gf, recs)

/-- One behavior's choice and the fault records it adds (its `disabled` records, then the
`enabled` records of a winning `faultOnly` transition). -/
def chooseOne (faults : List FaultIn) (cur : Configuration) (bid : String) (ts : List TransitionIn)
    (event : String) (payload : Value) (time : Float) : Except String (Choice × List FaultRecord) :=
  let state := (cur.machine? bid).map (·.state)
  match scan faults cur bid state event payload time ts [] false false [] with
  | .error e => .error e
  | .ok (some (t, enablers), _, _, _, recs) =>
    .ok (.win t, recs ++ enablers.map fun e => { fault := e.id, effect := .enabled })
  | .ok (none, considered, dis, gf, recs) =>
    let reason := if dis then IgnoredReason.disabled
      else if gf then .guardFalse else .noTransition
    .ok (.ignore { behavior := bid, reason, considered }, recs)

/-- Phase 1 over all behaviors in scenario order, reading the configuration from before the
step. Returns the winners, the ignored behaviors and the fault records, in order. -/
def choose (faults : List FaultIn) (cur : Configuration) (event : String) (payload : Value)
    (time : Float) :
    List (String × List TransitionIn) →
    Except String (List (String × TransitionIn) × List Ignored × List FaultRecord)
  | [] => .ok ([], [], [])
  | (bid, ts) :: rest =>
    match chooseOne faults cur bid ts event payload time with
    | .error e => .error e
    | .ok (c, recs) =>
      match choose faults cur event payload time rest with
      | .error e => .error e
      | .ok (ws, igs, fs) =>
        match c with
        | .win t => .ok ((bid, t) :: ws, igs, recs ++ fs)
        | .ignore i => .ok (ws, i :: igs, recs ++ fs)

/-! ## Phase 2: effects -/

/-- The state phase 2 writes: the next configuration and the counters. -/
structure FireState where
  next : Configuration
  seq : Nat
  nid : Nat

/-- Evaluate an emit payload's entries in property order, building the payload object.
ORDER: entries are evaluated in JavaScript property order, so the first failing entry in that
order gives the error. -/
def evalEntries (view : Configuration) (bid : String) (payload : Value) (time : Float) :
    List (String × Value) → List (String × Value) → Nat → Except String (List (String × Value) × Nat)
  | [], acc, nid => .ok (acc, nid)
  | (k, v) :: rest, acc, nid =>
    match valueOf (some v) view bid payload time nid with
    | .error e => .error e
    | .ok (x, nid) => evalEntries view bid payload time rest (objInsert acc k x) nid

/-- Run one transition's effects in order on the next configuration.
ORDER: a `set` checks the variable before evaluating the value; an `emit` checks the event,
then evaluates the payload, then takes its sequence number. Expressions read the next
configuration as it is at that moment, so a later effect sees an earlier `set`. -/
def runEffects (input : SimInput) (bid : String) (t : TransitionIn) (payload : Value) (time : Float) :
    List Effect → FireState → List SetRecord → List EmitRecord →
    Except String (FireState × List SetRecord × List EmitRecord)
  | [], s, sets, emits => .ok (s, sets, emits)
  | .set varName to :: rest, s, sets, emits =>
    match s.next.machine? bid with
    | none => .error s!"Effect sets \"{varName}\", which is not a variable of \"{bid}\"."
    | some m =>
      if !objHas m.vars varName then
        .error s!"Effect sets \"{varName}\", which is not a variable of \"{bid}\"."
      else
        match valueOf to s.next bid payload time s.nid with
        | .error e => .error e
        | .ok (value, nid) =>
          let before := (objGet? m.vars varName).getD .undef
          let next := s.next.setMachine bid { m with vars := objSet m.vars varName value }
          runEffects input bid t payload time rest { s with next, nid }
            (sets ++ [{ varName, before, after := value }]) emits
  | .emit event after entries :: rest, s, sets, emits =>
    if !isEvent input event then .error s!"Effect emits \"{event}\", which is not an event."
    else
      let atTime := s.next.time + after
      match evalEntries s.next bid payload time entries [] s.nid with
      | .error e => .error e
      | .ok (fs, nid) =>
        let pv : Value := .obj nid fs
        let entry : Pending :=
          { seq := s.seq, time := atTime, event, payload := pv, source := .transition t.id bid }
        let next := { s.next with pending := insertPending s.next.pending entry }
        runEffects input bid t payload time rest { next, seq := s.seq + 1, nid := nid + 1 } sets
          (emits ++ [{ event, time := atTime, seq := s.seq, payload := pv }])
  | .malformed :: _, _, _, _ => .error s!"Malformed effect in transition \"{t.id}\"."

/-- Fire one winner: its effects, then its machine moves to the target state (the state is
written after the behavior's own effects, so a later behavior sees it). -/
def fireOne (input : SimInput) (bid : String) (t : TransitionIn) (payload : Value) (time : Float)
    (s : FireState) : Except String (Fired × FireState) :=
  match runEffects input bid t payload time t.effects s [] [] with
  | .error e => .error e
  | .ok (s, sets, emitted) =>
    let next := match s.next.machine? bid with
      | some m => s.next.setMachine bid { m with state := t.target }
      | none => s.next
    .ok ({ behavior := bid, transition := t.id, source := t.source, target := t.target,
           guard := t.guard, sets, emitted }, { s with next })

/-- Phase 2: the winners' effects, behavior by behavior, in scenario order. -/
def fireAll (input : SimInput) (payload : Value) (time : Float) :
    List (String × TransitionIn) → FireState → Except String (List Fired × FireState)
  | [], s => .ok ([], s)
  | (bid, t) :: ws, s =>
    match fireOne input bid t payload time s with
    | .error e => .error e
    | .ok (f, s) =>
      match fireAll input payload time ws s with
      | .error e => .error e
      | .ok (fs, s) => .ok (f :: fs, s)

/-- Both phases of a delivery. -/
def deliver (env : Env) (cur : Configuration) (head : Pending) (s : FireState) :
    Except String (List Fired × List Ignored × List FaultRecord × FireState) :=
  match choose env.faults cur head.event head.payload head.time env.behaviors with
  | .error e => .error e
  | .ok (ws, igs, recs) =>
    match fireAll env.input head.payload head.time ws s with
    | .error e => .error e
    | .ok (fired, s) => .ok (fired, igs, recs, s)

/-- Ids that explain a step, without repeats: the event, each fired transition with its behavior
and that behavior's subject, then the faults. -/
def responsibleOf (i : SimInput) (event : String) (fired : List Fired) (faults : List FaultRecord) :
    List String :=
  let add (acc : List String) (x : String) := if acc.contains x then acc else acc ++ [x]
  let acc := fired.foldl (fun acc w =>
    let acc := add (add acc w.transition) w.behavior
    match (behaviorOf? i w.behavior).bind (·.subject) with
    | some subj => add acc subj
    | none => acc) [event]
  faults.foldl (fun acc f => add acc f.fault) acc

/-! ## The step function -/

/-- The semantic configuration: the observable configuration and the run's bookkeeping. -/
structure Config where
  conf : Configuration
  /-- The next sequence number. -/
  seq : Nat
  /-- The next free object identity. -/
  nid : Nat
  /-- Event id ↦ delivery attempts so far. -/
  attempts : List (String × Nat)
  /-- Queue entry seq ↦ the delay faults that already delayed it or the entries it was copied
  from. -/
  delayedBy : List (Nat × List String)
  /-- Steps taken so far (the next step's index). -/
  taken : Nat

inductive StepResult where
  /-- Nothing is pending. -/
  | idle
  /-- A step that changed the configuration. -/
  | committed (rec : Step) (next : Config)
  /-- A failed step: nothing of it is kept. -/
  | failed (rec : Step)

/-- A step record with nothing fired, ignored or recorded yet. -/
def blankStep (index : Nat) (head : Pending) (kind : StepKind) (config : Configuration) : Step :=
  { index, time := head.time, kind,
    event := { id := head.event, payload := head.payload, seq := head.seq, source := head.source },
    fired := [], ignored := [], faults := [], responsible := [], config, error := none }

/-- The `injected` record of a head that an `inject-event` fault queued. -/
def injectedOf : Source → List FaultRecord
  | .fault f => [{ fault := f, effect := .injected }]
  | _ => []

/-- The attempt number of the head's event: deliveries of that event taken so far, plus this one. -/
def attemptOf (c : Config) (ev : String) : Nat := (lookupNat c.attempts ev).getD 0 + 1

/-- Does an active fault of `kind` match a delivery of `ev` at attempt `attempt`? -/
def faultMatches (kind ev : String) (attempt : Nat) (f : FaultIn) : Bool :=
  f.isKind kind && f.event == some ev && f.occurrence.matches attempt

/-- The drop faults that act on the head, in fault order. -/
def dropsOf (env : Env) (c : Config) (head : Pending) : List FaultIn :=
  env.faults.filter (faultMatches "drop-event" head.event (attemptOf c head.event))

/-- The delay faults that already delayed the head or an entry it was copied from. -/
def alreadyDelayed (c : Config) (head : Pending) : List String :=
  (lookupSeq c.delayedBy head.seq).getD []

/-- The first matching delay fault that has not delayed the head yet. -/
def delayOf? (env : Env) (c : Config) (head : Pending) : Option FaultIn :=
  env.faults.find? fun f =>
    faultMatches "delay-event" head.event (attemptOf c head.event) f &&
      !(alreadyDelayed c head).contains f.id

/-- Handle the head of the queue. `cur` is the configuration before the step; `next` is its copy
with the head removed and the time set to the head's time; `nid` the next free identity after
the copy.
ORDER: the attempt is counted first (also for a step that fails); drop faults act before delay
faults, delay faults before delivery; every matching drop fault is recorded, but only the first
matching delay fault that has not delayed this entry yet acts; an injected event's `injected`
record comes before the records of phase 1. -/
def stepHead (env : Env) (c : Config) (next : Configuration) (nid : Nat) (head : Pending) : StepResult :=
  let ev := head.event
  let attempts := (ev, attemptOf c ev) :: c.attempts.filter (·.1 != ev)
  match dropsOf env c head with
  | d :: ds =>
    let recs := (d :: ds).map fun f => { fault := f.id, effect := FaultEffect.dropped }
    .committed
      { blankStep c.taken head .drop next with
        faults := recs, responsible := responsibleOf env.input ev [] recs }
      { c with conf := next, nid, attempts, taken := c.taken + 1 }
  | [] =>
    match delayOf? env c head with
    | some d =>
      let copy : Pending :=
        { seq := c.seq, time := head.time + d.delayBy, event := ev,
          payload := (head.payload.copy nid).1, source := head.source }
      let next := { next with pending := insertPending next.pending copy }
      let recs := [{ fault := d.id, effect := FaultEffect.delayed }]
      .committed
        { blankStep c.taken head .delay next with
          faults := recs, responsible := responsibleOf env.input ev [] recs }
        { c with conf := next, seq := c.seq + 1, nid := (head.payload.copy nid).2, attempts,
                 delayedBy := (c.seq, alreadyDelayed c head ++ [d.id]) :: c.delayedBy, taken := c.taken + 1 }
    | none =>
      match deliver env c.conf head { next, seq := c.seq, nid } with
      | .ok (fired, ignored, recs, s) =>
        let faults := injectedOf head.source ++ recs
        .committed
          { blankStep c.taken head .deliver s.next with
            fired, ignored, faults, responsible := responsibleOf env.input ev fired faults }
          { c with conf := s.next, seq := s.seq, nid := s.nid, attempts, taken := c.taken + 1 }
      | .error msg =>
        -- The failing step is not committed: its configuration is the one before it.
        .failed { blankStep c.taken head .deliver c.conf with
                  responsible := [ev], error := some msg }

/-- One event delivery. Guards read `c.conf` (the configuration at the start of the step);
effects write a deep copy of it, so identities in the next configuration are fresh.
MIRRORED: a `set a` to an expression naming the object or array `b` makes `a` and `b` the same
reference; the committed configuration keeps that sharing, so the next step's guards see
`a == b` true while that step's effects, reading the fresh copy, see it false. -/
def step (env : Env) (c : Config) : StepResult :=
  match c.conf.pending with
  | [] => .idle
  | _ :: _ =>
    match (c.conf.copy c.nid).1.pending with
    | [] => .idle
    | head :: rest =>
      stepHead env c { (c.conf.copy c.nid).1 with pending := rest, time := head.time }
        (c.conf.copy c.nid).2 head

/-! ## Runs -/

structure Run where
  config : Config
  /-- The steps taken, latest first. -/
  stepsRev : List Step
  outcome : Outcome

/-- Take one step of a running run and decide the outcome: `quiescent` when the queue is empty,
else `step-limit` when the step count has reached the bound, else still `running`; `error`
after a failed step (whatever the limit). -/
def advance (env : Env) (bound : Nat) (r : Run) : Run :=
  match step env r.config with
  | .idle => { r with outcome := .quiescent }
  | .committed rec next =>
    { config := next, stepsRev := rec :: r.stepsRev,
      outcome :=
        if next.conf.pending.isEmpty then .quiescent
        else if r.stepsRev.length + 1 ≥ bound then .stepLimit
        else .running }
  | .failed rec => { r with stepsRev := rec :: r.stepsRev, outcome := .error }

/-- Step while running, at most `fuel` times. -/
def loop (env : Env) (bound : Nat) : Nat → Run → Run
  | 0, r => r
  | fuel + 1, r => if r.outcome = .running then loop env bound fuel (advance env bound r) else r

def startRun (c0 : Config) : Run :=
  { config := c0, stepsRev := [],
    outcome := if c0.conf.pending.isEmpty then .quiescent else .running }

/-- A run to completion, with fuel equal to the bound (enough: `Properties.run_stops`). -/
def runEnv (env : Env) (bound : Nat) (c0 : Config) : Run :=
  loop env bound bound (startRun c0)

/-- The first semantic configuration: the initial configuration with fresh identities. -/
def initialConfig (i : SimInput) : Configuration × Config :=
  let (initial, seq) := initialConfiguration i
  let (conf, nid) := initial.copy 1
  (initial, { conf, seq, nid, attempts := [], delayedBy := [], taken := 0 })

/-- The trace of a valid input. -/
def traceOf (i : SimInput) : Trace :=
  let r := runEnv (envOf i) (stepBound i.scenario.stepLimit) (initialConfig i).2
  { scenarioId := i.scenario.id, faults := (envOf i).faultIds, initial := (initialConfig i).1,
    steps := r.stepsRev.reverse, outcome := r.outcome, final := r.config.conf }

/-- Run an engine input: a refusal, or its trace. -/
def runInput (i : SimInput) : Except String Trace :=
  match validate i with
  | .error e => .error e
  | .ok () => .ok (traceOf i)

/-- The semantics on a parsed engine input: trace JSON, or the refusal message. -/
def runValue (v : Value) : Except String String := do
  let i ← Decode.input v
  let t ← runInput i
  pure t.toJson

/-- The whole semantics as a text-to-text function: engine input JSON to trace JSON, or the
refusal message. -/
def runText (text : String) : Except String String := do
  let v ← Json.parse text
  runValue v

end Exegra
