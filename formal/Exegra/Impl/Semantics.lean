import Exegra.Format2
import Exegra.Impl.Expr
import Exegra.Impl.Json

/-!
# The format-1 engine as the application runs it

`Exegra/Semantics.lean` is the **definition** of the behavior language: the simple step
function the theorems of `Exegra/Properties.lean` are about. It parses an expression from its
text every time it evaluates it, and counts the steps of a run by measuring the list of steps
after every step. Both are fine for a definition and too slow for the application: an
expression of 8192 terms took about 63 ms per step.

This file is the **implementation** the application runs (`Exegra.Impl.runAnyValue`, registered
as `engine.run`). It differs from the definition in exactly these ways:

* every expression of a transition (its guard, the `to` of a `set`, the entries of an `emit`
  payload) is parsed at most once per run: `compileEnv` wraps its parse in a `Thunk`, which the
  runtime evaluates the first time the expression is evaluated and keeps. Logically
  `(Thunk.mk f).get = f ()` (`Thunk.get` is defined as that; the runtime's memoization is
  Lean's own primitive, not an `implemented_by` of ours), so the proofs see the parse itself;
  an expression the run never reaches is never parsed, as in the definition;
* expressions are evaluated by `evalFast`: arithmetic on numbers runs on unboxed floats, and a
  behavior's machine is looked up once per evaluation (`Exegra/Impl/Expr.lean`);
* whether an emitted event id names an event is decided once per effect, when the run starts,
  instead of every time the effect runs;
* the copy of the configuration a step makes is computed once per step;
* a run carries the number of steps it has taken, instead of measuring the list of steps;
* the trace is written as JSON by the fast writer `JsonOut.write'` (`Exegra/Impl/Json.lean`),
  for format 1 and format 2.

Format 2 otherwise runs the definition (`V2.traceOf`) unchanged.

Everything else is the definition's own code, called as is. `Exegra/Impl/Refinement.lean` proves
that the two agree on every input (`Impl.runAnyValue_eq`, `Impl.runAny_eq`), so the theorems
about the definition hold of what the application runs.
-/

namespace Exegra.Impl

/-! ## Expressions compiled once -/

/-- An expression's parse, or the definition's parse error for it (`compile`). -/
abbrev Compiled := Except String Ast

/-- `evalIn`, on an expression already parsed, with the fast evaluator
(`Exegra/Impl/Expr.lean`). -/
def evalC (c : Compiled) (view : Configuration) (bid : String) (payload : Value) (time : Float) :
    Except String Value :=
  match c with
  | .error e => .error e
  | .ok ast => evalFast (resolveFast (view.machine? bid) view bid payload time) ast

/-- The value of an effect `to` or a payload entry, with its expression parsed. -/
inductive CVal where
  /-- No value (`valueOf none`). -/
  | none
  /-- An expression: its source and its parse, computed when first needed and then kept. -/
  | expr (src : String) (c : Thunk Compiled)
  /-- A literal, copied when it is used. -/
  | lit (v : Value)

/-- Parse the expression of an effect value once. -/
def CVal.ofOpt : Option Value → CVal
  | Option.none => .none
  | some (.str src) => .expr src (Thunk.mk fun _ => compile src)
  | some v => .lit v

/-- `valueOf`, on a compiled value. -/
def valueOfC (x : CVal) (view : Configuration) (bid : String) (payload : Value) (time : Float)
    (nid : Nat) : Except String (Value × Nat) :=
  match x with
  | .none => .error "Effect has no value."
  | .expr _ c => (evalC c.get view bid payload time).map fun v => (v, nid)
  | .lit v => .ok (v.copy nid)

/-- An effect with its expressions parsed. An `emit` also carries whether its event id names an
event of the input (`isEvent`), decided once. -/
inductive CEffect where
  | set (varName : String) (to : CVal)
  | emit (event : String) (known : Bool) (after : Float) (entries : List (String × CVal))
  | malformed

def compileEffect (i : SimInput) : Effect → CEffect
  | .set v to => .set v (CVal.ofOpt to)
  | .emit ev after entries =>
    .emit ev (isEvent i ev) after (entries.map fun e => (e.1, CVal.ofOpt (some e.2)))
  | .malformed => .malformed

/-- A transition with its guard and effects compiled; `t` is the transition itself. -/
structure CTransition where
  t : TransitionIn
  guard : Option (String × Thunk Compiled)
  effects : List CEffect

def compileTransition (i : SimInput) (t : TransitionIn) : CTransition :=
  { t, guard := t.guard.map fun g => (g, Thunk.mk fun _ => compile g), effects := t.effects.map (compileEffect i) }

/-- The static environment of a run with every transition compiled. -/
structure CEnv where
  env : Env
  behaviors : List (String × List CTransition)

def compileEnv (env : Env) : CEnv :=
  { env, behaviors := env.behaviors.map fun b => (b.1, b.2.map (compileTransition env.input)) }

/-! ## Phase 1 -/

def guardHoldsC (t : CTransition) (view : Configuration) (bid : String) (payload : Value)
    (time : Float) : Except String Bool :=
  match t.guard with
  | Option.none => .ok true
  | some (g, c) => match evalC c.get view bid payload time with
    | .error e => .error e
    | .ok (.bool b) => .ok b
    | .ok _ => .error s!"Guard \"{g}\" of transition \"{t.t.id}\" did not evaluate to a boolean."

/-- `scan`, over compiled transitions. -/
def scanC (faults : List FaultIn) (cur : Configuration) (bid : String) (state : Option String)
    (event : String) (payload : Value) (time : Float) :
    List CTransition → List String → Bool → Bool → List FaultRecord →
    Except String (Option (CTransition × List FaultIn) × List String × Bool × Bool × List FaultRecord)
  | [], considered, dis, gf, recs => .ok (Option.none, considered, dis, gf, recs)
  | ct :: ts, considered, dis, gf, recs =>
    if some ct.t.source != state || ct.t.on != event then
      scanC faults cur bid state event payload time ts considered dis gf recs
    else
      let enablers := targeting faults "enable-transition" ct.t.id
      if ct.t.faultOnly && enablers.isEmpty then
        scanC faults cur bid state event payload time ts considered dis gf recs
      else
        let considered := considered ++ [ct.t.id]
        let disablers := targeting faults "disable-transition" ct.t.id
        match guardHoldsC ct cur bid payload time with
        | .error e => .error e
        | .ok false => scanC faults cur bid state event payload time ts considered dis true recs
        | .ok true =>
          if !disablers.isEmpty then
            scanC faults cur bid state event payload time ts considered true gf
              (recs ++ disablers.map fun d => { fault := d.id, effect := .disabled })
          else
            .ok (some (ct, if ct.t.faultOnly then enablers else []), considered, dis, gf, recs)

inductive CChoice where
  | win (t : CTransition)
  | ignore (i : Ignored)

def chooseOneC (faults : List FaultIn) (cur : Configuration) (bid : String)
    (ts : List CTransition) (event : String) (payload : Value) (time : Float) :
    Except String (CChoice × List FaultRecord) :=
  let state := (cur.machine? bid).map (·.state)
  match scanC faults cur bid state event payload time ts [] false false [] with
  | .error e => .error e
  | .ok (some (t, enablers), _, _, _, recs) =>
    .ok (.win t, recs ++ enablers.map fun e => { fault := e.id, effect := .enabled })
  | .ok (Option.none, considered, dis, gf, recs) =>
    let reason := if dis then IgnoredReason.disabled
      else if gf then .guardFalse else .noTransition
    .ok (.ignore { behavior := bid, reason, considered }, recs)

def chooseC (faults : List FaultIn) (cur : Configuration) (event : String) (payload : Value)
    (time : Float) :
    List (String × List CTransition) →
    Except String (List (String × CTransition) × List Ignored × List FaultRecord)
  | [] => .ok ([], [], [])
  | (bid, ts) :: rest =>
    match chooseOneC faults cur bid ts event payload time with
    | .error e => .error e
    | .ok (c, recs) =>
      match chooseC faults cur event payload time rest with
      | .error e => .error e
      | .ok (ws, igs, fs) =>
        match c with
        | .win t => .ok ((bid, t) :: ws, igs, recs ++ fs)
        | .ignore i => .ok (ws, i :: igs, recs ++ fs)

/-! ## Phase 2 -/

def evalEntriesC (view : Configuration) (bid : String) (payload : Value) (time : Float) :
    List (String × CVal) → List (String × Value) → Nat →
    Except String (List (String × Value) × Nat)
  | [], acc, nid => .ok (acc, nid)
  | (k, v) :: rest, acc, nid =>
    match valueOfC v view bid payload time nid with
    | .error e => .error e
    | .ok (x, nid) => evalEntriesC view bid payload time rest (objInsert acc k x) nid

def runEffectsC (bid : String) (t : TransitionIn) (payload : Value) (time : Float) :
    List CEffect → FireState → List SetRecord → List EmitRecord →
    Except String (FireState × List SetRecord × List EmitRecord)
  | [], s, sets, emits => .ok (s, sets, emits)
  | .set varName to :: rest, s, sets, emits =>
    match s.next.machine? bid with
    | Option.none => .error s!"Effect sets \"{varName}\", which is not a variable of \"{bid}\"."
    | some m =>
      if !objHas m.vars varName then
        .error s!"Effect sets \"{varName}\", which is not a variable of \"{bid}\"."
      else
        match valueOfC to s.next bid payload time s.nid with
        | .error e => .error e
        | .ok (value, nid) =>
          let before := (objGet? m.vars varName).getD .undef
          let next := s.next.setMachine bid { m with vars := objSet m.vars varName value }
          runEffectsC bid t payload time rest { s with next, nid }
            (sets ++ [{ varName, before, after := value }]) emits
  | .emit event known after entries :: rest, s, sets, emits =>
    if !known then .error s!"Effect emits \"{event}\", which is not an event."
    else
      let atTime := s.next.time + after
      match evalEntriesC s.next bid payload time entries [] s.nid with
      | .error e => .error e
      | .ok (fs, nid) =>
        let pv : Value := .obj nid fs
        let entry : Pending :=
          { seq := s.seq, time := atTime, event, payload := pv, source := .transition t.id bid }
        let next := { s.next with pending := insertPending s.next.pending entry }
        runEffectsC bid t payload time rest { next, seq := s.seq + 1, nid := nid + 1 } sets
          (emits ++ [{ event, time := atTime, seq := s.seq, payload := pv }])
  | .malformed :: _, _, _, _ => .error s!"Malformed effect in transition \"{t.id}\"."

def fireOneC (bid : String) (ct : CTransition) (payload : Value) (time : Float) (s : FireState) :
    Except String (Fired × FireState) :=
  match runEffectsC bid ct.t payload time ct.effects s [] [] with
  | .error e => .error e
  | .ok (s, sets, emitted) =>
    let next := match s.next.machine? bid with
      | some m => s.next.setMachine bid { m with state := ct.t.target }
      | Option.none => s.next
    .ok ({ behavior := bid, transition := ct.t.id, source := ct.t.source, target := ct.t.target,
           guard := ct.t.guard, sets, emitted }, { s with next })

def fireAllC (payload : Value) (time : Float) :
    List (String × CTransition) → FireState → Except String (List Fired × FireState)
  | [], s => .ok ([], s)
  | (bid, t) :: ws, s =>
    match fireOneC bid t payload time s with
    | .error e => .error e
    | .ok (f, s) =>
      match fireAllC payload time ws s with
      | .error e => .error e
      | .ok (fs, s) => .ok (f :: fs, s)

def deliverC (E : CEnv) (cur : Configuration) (head : Pending) (s : FireState) :
    Except String (List Fired × List Ignored × List FaultRecord × FireState) :=
  match chooseC E.env.faults cur head.event head.payload head.time E.behaviors with
  | .error e => .error e
  | .ok (ws, igs, recs) =>
    match fireAllC head.payload head.time ws s with
    | .error e => .error e
    | .ok (fired, s) => .ok (fired, igs, recs, s)

/-! ## The step function -/

/-- `stepHead`, delivering through the compiled transitions. -/
def stepHeadC (E : CEnv) (c : Config) (next : Configuration) (nid : Nat) (head : Pending) :
    StepResult :=
  let env := E.env
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
    | Option.none =>
      match deliverC E c.conf head { next, seq := c.seq, nid } with
      | .ok (fired, ignored, recs, s) =>
        let faults := injectedOf head.source ++ recs
        .committed
          { blankStep c.taken head .deliver s.next with
            fired, ignored, faults, responsible := responsibleOf env.input ev fired faults }
          { c with conf := s.next, seq := s.seq, nid := s.nid, attempts, taken := c.taken + 1 }
      | .error msg =>
        .failed { blankStep c.taken head .deliver c.conf with
                  responsible := [ev], error := some msg }

/-- `step`, with the configuration copied once. -/
def stepC (E : CEnv) (c : Config) : StepResult :=
  match c.conf.pending with
  | [] => .idle
  | _ :: _ =>
    let copied := c.conf.copy c.nid
    match copied.1.pending with
    | [] => .idle
    | head :: rest => stepHeadC E c { copied.1 with pending := rest, time := head.time } copied.2 head

/-! ## Runs -/

/-- `advance`, given the number of steps the run has taken; returns the new number. -/
def advanceC (E : CEnv) (bound : Nat) (r : Run) (len : Nat) : Run × Nat :=
  match stepC E r.config with
  | .idle => ({ r with outcome := .quiescent }, len)
  | .committed rec next =>
    ({ config := next, stepsRev := rec :: r.stepsRev,
       outcome :=
         if next.conf.pending.isEmpty then .quiescent
         else if len + 1 ≥ bound then .stepLimit
         else .running }, len + 1)
  | .failed rec => ({ r with stepsRev := rec :: r.stepsRev, outcome := .error }, len + 1)

/-- `loop`, carrying the number of steps taken. -/
def loopC (E : CEnv) (bound : Nat) : Nat → Run → Nat → Run
  | 0, r, _ => r
  | fuel + 1, r, len =>
    if r.outcome = .running then
      let (r, len) := advanceC E bound r len
      loopC E bound fuel r len
    else r

def runEnvC (E : CEnv) (bound : Nat) (c0 : Config) : Run :=
  loopC E bound bound (startRun c0) 0

/-- `traceOf`, computing the environment, the bound and the initial configuration once. -/
def traceOfC (i : SimInput) : Trace :=
  let env := envOf i
  let ic := initialConfig i
  let r := runEnvC (compileEnv env) (stepBound i.scenario.stepLimit) ic.2
  { scenarioId := i.scenario.id, faults := env.faultIds, initial := ic.1,
    steps := r.stepsRev.reverse, outcome := r.outcome, final := r.config.conf }

def runInputC (i : SimInput) : Except String Trace :=
  match validate i with
  | .error e => .error e
  | .ok () => .ok (traceOfC i)

/-- `runValue`: a parsed format-1 engine input to its trace JSON, or the refusal. -/
def runValue (v : Value) : Except String String := do
  let i ← Decode.input v
  let t ← runInputC i
  pure (JsonOut.write' (Encode.trace t))

/-- `V2.runInput`, writing the trace with the fast writer. The format-2 semantics itself is the
definition's (`V2.traceOf`). -/
def runInputV2 (i : V2.Input) : Except String String := do
  V2.validate i
  pure (JsonOut.write' (V2.Encode.trace (V2.traceOf i)))

/-- `Exegra.runAnyValue` with the format-1 implementation. Format 2 runs the definition's
semantics (`V2.traceOf`) and the fast writer. -/
def runAnyValue (v : Value) : Except String String :=
  match v with
  | .obj _ root =>
    match objGet? root "version", objGet? root "format" with
    | some (.num x), some (.str "exegra-sim-input") =>
      if x == 2 then do runInputV2 (← V2.Decode.input root) else runValue v
    | _, _ => runValue v
  | _ => runValue v

/-- `runAnyValue` on JSON text: what `exegra-lean` runs. -/
def runAny (text : String) : Except String String := do
  let v ← Json.parse text
  runAnyValue v

end Exegra.Impl
