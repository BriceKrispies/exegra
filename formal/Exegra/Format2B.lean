import Exegra.Elab

/-
Format 2 on the proved scheduler (docs/assessment/2026-11-26/plan-M2.md, increment M2.5; the task's
criteria 14 and 15).

`V2.runInput` dispatches every decoded version-2 input:

* an input `Elab.elab` accepts runs `traceOfB`: the fold of the calculus scheduler `Exec.step`
  (`Core/BehavExec.lean`, proved a scheduler of `Sys.lts`), encoded as a format-2 trace;
* an input outside the fragment (`outOfFragment`) runs the legacy interpreter `traceOf`, and its
  trace says `"semantics": "legacy"`;
* an ill-typed input, or one with a number that is not an integer, is refused with the refusal's
  message.

**What is proved and what is encoding.** The states of a `traceOfB` run are the states `Exec.step`
computes (`runB_reach`: all reachable in the calculus), and the run ends as `runB_terminates` says.
Everything else in the trace is bookkeeping that no theorem is about, kept beside the calculus
state as format 2 keeps it: sequence numbers, sources, senders and targets as addresses, timer ids,
`scheduledAt`, delayed copies' `copyOf`, the streams' draw counts, the records of a step (fired
transitions with the values each `set` replaced, emitted entries, ignored behaviours with the
transitions they considered, fault records, draws, responsibility). The records are computed by
`stepRec`, which repeats the step with the calculus's own functions (winners, guard and effect
evaluation, the commit) and records as it goes; every committed step checks that the configuration
`stepRec` arrives at is the one `Exec.step` committed, and fails the run with an internal error
otherwise. The text of an error is format 2's: the failing guard or effect is the one the calculus
fails on, and its message is what the format-2 expression evaluator reports for that expression,
evaluated against the calculus configuration (encoding only: whether the step fails is decided by
the calculus).
-/

namespace Exegra.V2.B

open Exegra
abbrev Book := Core.Behav.Book

abbrev CEntry := Core.Behav.Entry

/-- The format-2 bookkeeping of a pending entry, kept beside the calculus entry. -/
structure PMeta where
  seq : Nat
  sched : Nat
  src : Src
  target : Option Addr := none
  sender : Option Addr := none
  timer : Option String := none
  copyOf : Option Nat := none
  deriving Inhabited

/-- What the encoding needs from the input: the behaviours, the machine layout, and the names the
calculus numbers. -/
structure Info where
  input : Input
  env : Env
  behs : List BehaviorIn
  lay : List (Nat × Nat)
  fields : List String
  timers : List String

def payloadKeys (v : Value) : List String :=
  match v with
  | .obj _ fs => fs.map (·.1)
  | _ => []

def mkInfo (i : Input) : Info :=
  let effs := i.behaviors.flatMap fun b => b.transitions.flatMap (·.effects)
  let fields := (i.scenario.steps.flatMap fun st => payloadKeys st.payload) ++
    (i.faults.flatMap fun f => payloadKeys f.payload) ++
    effs.flatMap (fun e => match e with
      | .emit _ _ pl _ | .timer _ _ _ pl => pl.map (·.1)
      | _ => [])
  let timers := effs.flatMap fun e => match e with
    | .timer n .. | .cancel n => [n]
    | _ => []
  { input := i, env := envOf i, behs := i.behaviors, lay := Elab.layout i.behaviors, fields, timers }

namespace Info
variable (I : Info)

def beh (m : Nat) : BehaviorIn := I.behs.getD (I.lay.getD m (0, 0)).1 default
def inst (m : Nat) : Value := .num (I.lay.getD m (0, 0)).2.toFloat
def key (m : Nat) : String := machineKey (I.beh m) (I.inst m)
def addr (m : Nat) : Addr := { behavior := (I.beh m).id, inst := I.inst m, incarnation := 0 }
def event (id : Nat) : String := I.input.events.getD id ""
def field (id : Nat) : String := (I.fields.find? (Elab.strId · == id)).getD ""
def timerName (id : Nat) : String := (I.timers.find? (Elab.strId · == id)).getD ""

end Info

/-- A calculus value as a format-2 value. -/
def toValue : Core.Behav.Val → Value
  | .int n => .num (Float.ofInt n)
  | .bool b => .bool b
  | .str s => .str s
  | .lit _ json => (Json.parse json).toOption.getD .null

def payloadValue (I : Info) (pl : List (Nat × Core.Behav.Val)) : Value :=
  .obj 0 (pl.map fun (f, v) => (I.field f, toValue v))

def toEntry (I : Info) (e : CEntry) (mt : PMeta) : Entry :=
  { seq := mt.seq, time := e.time, scheduledAt := mt.sched, event := I.event e.event,
    payload := payloadValue I e.payload, source := mt.src, kind := .event, target := mt.target,
    sender := mt.sender, routes := none, timer := mt.timer, copyOf := mt.copyOf }

/-- A machine state as a format-2 machine. -/
def toMachine (I : Info) (m : Nat) (ms : Core.Behav.MState) : Machine :=
  let b := I.beh m
  { state := (Elab.statesOf b).getD ms.ctrl "",
    vars := (b.variables.zip ms.vars).foldl (fun vs (v, x) => objInsert vs v.name (toValue x)) [],
    types := b.types }

def insts (I : Info) : List (String × List Value) :=
  I.behs.map fun b => (b.id, (List.range (Elab.instCount b)).map fun k => Value.num k.toFloat)

/-- A calculus configuration with its bookkeeping, as a format-2 configuration. -/
def toConf (I : Info) (c : Core.Behav.Cfg) (metas : List PMeta) (b : Book) : Conf :=
  { time := c.time,
    machines := (c.machines.zipIdx).map fun (ms, m) => (I.key m, toMachine I m ms),
    insts := insts I,
    pending := (c.pending.zip metas).map fun (e, mt) => toEntry I e mt,
    resources := [], routeCounters := [], streams := b.counts }

/-! ### The queue with its bookkeeping -/

/-- `insertByTime` on entries with their bookkeeping. -/
def insertP (q : List (CEntry × PMeta)) (x : CEntry × PMeta) : List (CEntry × PMeta) :=
  match q with
  | [] => [x]
  | y :: ys => if x.1.time < y.1.time then x :: y :: ys else y :: insertP ys x

/-! ### Messages -/

def errText : Core.Behav.Err → String
  | .divZero => "Division by zero"
  | .timeBound => "Value time exceeds 2^53."
  | .inexact => "Division with a remainder: an untyped / must be exact"
  | .overflow => "Integer overflow: an untyped result is outside -9007199254740991..9007199254740991"
  | .operand => "An untyped operand is outside -9007199254740991..9007199254740991"
  | .absentField _ => "Unknown reference"
  | .unknownRef => "Unknown reference"
  | .fieldSort _ => "Payload field of another sort"
  | .sort => "Sort error"
  | .shape => "Shape error"
  | .noRequester => "Effect has no requester."

/-- Format 2's message for the first of `srcs` its evaluator fails on, or `fallback`. -/
def msgOf (I : Info) (view : Conf) (mk : String) (inst payload : Value) (time : Nat)
    (srcs : List String) (fallback : String) : String :=
  match srcs.findSome? (fun src => match evalIn I.env src view view mk inst payload time with
      | .error m => some m
      | .ok _ => none) with
  | some m => m
  | none => fallback

/-- The expression sources of a format-2 effect, in evaluation order. -/
def effSrcs : Effect → List String
  | .set _ (some (.str src)) => [src]
  | .emit _ _ pl _ | .timer _ _ _ pl => pl.filterMap fun (_, v) => match v with
    | .str src => some src
    | _ => none
  | _ => []

/-! ### One step, recorded -/

/-- What a committed step records, and the queue after it with its bookkeeping. -/
structure Out where
  kind : Kind2
  fired : List Fired2 := []
  ignored : List Ignored2 := []
  faults : List FaultRecord := []
  responsible : List String := []
  draws : List Draw := []
  pairs : List (CEntry × PMeta)
  seq : Nat
  book : Book

inductive SR where
  | ok (o : Out)
  | fail (kind : Kind2) (msg : String)

/-- The state of the recording of one winner's effects. -/
structure ESt where
  own : Core.Behav.MState
  sets : List SetRecord := []
  emits : List EmitRecord := []
  outs : List (CEntry × PMeta) := []
  seq : Nat
  book : Book
  draws : List Draw := []

/-- The draw slot of effect `j` of transition `ti` of machine `m`, if it is sampled. -/
def slotOf (sys : Core.Behav.Sys) (m ti j : Nat) : Option Nat :=
  sys.samples.findIdx? fun s => s.1 == m && s.2.1 == ti && s.2.2.1 == j

/-- Record the draw of a sampled effect (format 2's `drawNext`). -/
def drawRec (sys : Core.Behav.Sys) (b0 : Book) (m ti j : Nat) (st : ESt) : ESt :=
  match slotOf sys m ti j, b0.seed with
  | some k, some seed =>
    let name := b0.names.getD k ""
    let idx := st.book.count name
    { st with book := st.book.bump name,
              draws := st.draws ++ [{ stream := name, index := idx, value := Random.draw seed name idx }] }
  | _, _ => st

/-- The effects of one winner, recorded: the calculus's `runEffects`, repeated with the records
format 2 keeps. `.error (j, err)`: effect `j` fails with `err`.

`fin` is the machine's variables in the configuration `Exec.step` committed, when it committed:
the value of the last `set` of a variable is then read from there instead of being evaluated a
second time (the scheduler has already evaluated it, and no other machine writes this machine's
variables in a step). `commitRec` still checks the recorded queue against the committed one. -/
def effRec (I : Info) (sys : Core.Behav.Sys) {S : Core.Behav.Sig} {me : Fin S.machines} (b0 : Book)
    (c0 : Core.Behav.Cfg) (e : CEntry) (mt0 : PMeta) (b : BehaviorIn) (t : TransitionIn) (ti : Nat)
    (fin : Option (List Core.Behav.Val)) :
    Nat → List (Core.Behav.Effect S me) → List Effect → ESt → Except (Nat × Core.Behav.Err) ESt
  | _, [], _, st => .ok st
  | j, eff :: rest, leff :: lrest, st =>
    let m := me.val
    let cx := Core.Behav.ctxOf c0 e st.own
    let time := c0.time
    let next (st : ESt) := effRec I sys b0 c0 e mt0 b t ti fin (j + 1) rest lrest st
    match eff, leff with
    | .set v rhs, .set name _ =>
      let setLater := rest.any fun x => match x with
        | .set w _ => w.val == v.val
        | _ => false
      let committed : Option Core.Behav.Val := if setLater then none else fin.bind (·[v.val]?)
      let val : Except Core.Behav.Err Core.Behav.Val := match committed with
        | some x => .ok x
        | none => match rhs.eval cx with
          | .error err => .error err
          | .ok x => Core.Behav.Val.check ((S.vars me).get v) x
      match val with
      | .error err => .error (j, err)
      | .ok x =>
          if v.val < st.own.vars.length then
            let before := (st.own.vars[v.val]?.map toValue).getD .undef
            next { st with own := { st.own with vars := st.own.vars.set v.val x },
                           sets := st.sets ++ [{ varName := name, before, after := toValue x }] }
          else .error (j, .shape)
    | .emit ev after pl, _ | .reply ev after pl, _ =>
      let st := drawRec sys b0 m ti j st
      if Core.Behav.timeLimit ≤ time + after then .error (j, .timeBound) else
      match Core.Behav.evalPayload cx pl with
      | .error err => .error (j, err)
      | .ok vs =>
        let isReply := match eff with | .reply .. => true | _ => false
        if isReply && e.sender.isNone then .error (j, Core.Behav.Err.noRequester) else
        let ent : CEntry :=
          if isReply then { time := time + after, event := ev, payload := vs, target := e.sender, sender := some m }
          else { time := time + after, event := ev, payload := vs, sender := some m }
        let mt : PMeta := { seq := st.seq, sched := time + after, src := .transition t.id b.id,
                            target := if isReply then mt0.sender else none, sender := some (I.addr m) }
        let er : EmitRecord := { event := I.event ev, time := (time + after).toFloat, seq := st.seq, payload := payloadValue I vs }
        next { st with outs := st.outs ++ [(ent, mt)], seq := st.seq + 1, emits := st.emits ++ [er] }
    | .timer n after ev pl, _ =>
      let st := drawRec sys b0 m ti j st
      if Core.Behav.timeLimit ≤ time + after then .error (j, .timeBound) else
      match Core.Behav.evalPayload cx pl with
      | .error err => .error (j, err)
      | .ok vs =>
        let ent : CEntry := { time := time + after, event := ev, payload := vs, target := some m, timer := some n }
        let name := I.timerName n
        let mt : PMeta := { seq := st.seq, sched := time + after, src := .timer b.id (I.inst m) name,
                            target := some (I.addr m), timer := some s!"{I.key m}/{name}" }
        let er : EmitRecord := { event := I.event ev, time := (time + after).toFloat, seq := st.seq, payload := payloadValue I vs }
        next { st with outs := st.outs.filter (fun p => p.1.timer != some n) ++ [(ent, mt)], seq := st.seq + 1,
                       emits := st.emits ++ [er] }
    | .cancel n, _ => next { st with outs := st.outs.filter (fun p => p.1.timer != some n) }
    | _, _ => .error (j, .shape)
  | j, _ :: _, [], _ => .error (j, .shape)

/-- Phase 1 for one machine, recorded as format 2's `scan` records it: the winning transition (with
the `enabled` records of a fault-only one), the transitions considered, whether a true guard was
disabled, whether a guard was false, and the `disabled` records. `.error (ti, err)`: the guard of
transition `ti` fails. -/
def scanRec (I : Info) (sys : Core.Behav.Sys) (m : Fin sys.sig.machines) (c0 : Core.Behav.Cfg) (e : CEntry)
    (own : Core.Behav.MState) (state : String) (ev : String) (time : Nat) :
    List (TransitionIn × Nat) → List String → Bool → Bool → List FaultRecord →
    Except (Nat × Core.Behav.Err) (Option (Nat × List FaultRecord) × List String × Bool × Bool × List FaultRecord)
  | [], considered, dis, gf, recs => .ok (none, considered, dis, gf, recs)
  | (t, ti) :: ts, considered, dis, gf, recs =>
    if t.source != state || t.on != ev then scanRec I sys m c0 e own state ev time ts considered dis gf recs
    else
      let enablers := targeting I.env.faults "enable-transition" t.id time
      if t.faultOnly && enablers.isEmpty then scanRec I sys m c0 e own state ev time ts considered dis gf recs
      else
        let considered := considered ++ [t.id]
        let disablers := targeting I.env.faults "disable-transition" t.id time
        match (sys.trans m)[ti]? with
        | none => .error (ti, .shape)
        | some tr =>
          match tr.guard.eval (Core.Behav.ctxOf c0 e own) with
          | .error err => .error (ti, err)
          | .ok (.bool false) => scanRec I sys m c0 e own state ev time ts considered dis true recs
          | .ok (.bool true) =>
            if !disablers.isEmpty then
              scanRec I sys m c0 e own state ev time ts considered true gf
                (recs ++ disablers.map fun d => { fault := d.id, effect := .disabled })
            else .ok (some (ti, if t.faultOnly then enablers.map (fun d => { fault := d.id, effect := .enabled }) else []),
                      considered, dis, gf, recs)
          | .ok _ => .error (ti, .sort)

/-- The machines a delivered entry addresses in behaviour `b` (format 2's `addressed`): `none`
when it addresses another behaviour. -/
def addressedM (I : Info) (mt0 : PMeta) (j : Nat) (b : BehaviorIn) : Option (List Nat) :=
  let ms := (List.range (Elab.instCount b)).map (Elab.machineOf I.behs j)
  match mt0.target with
  | some a =>
    if a.behavior == b.id then
      some (ms.filter fun m => Json.write (I.inst m) == Json.write a.inst)
    else none
  | none => some ms

/-- **One step, recorded.** From configuration `c` (sorted, its head `e` with bookkeeping `mt0`),
under `mask`, with book `b`: the records of the step and the queue after it, or the kind and the
format-2 message of the failure. -/
def stepRecWith (I : Info) (sys : Core.Behav.Sys) (mask : List Bool) (c : Core.Behav.Cfg) (metas : List PMeta)
    (seq taken : Nat) (b : Book) (dsOv : Option (List Nat)) (next : Option Core.Behav.Cfg := none) : SR :=
  match c.pending, metas with
  | e :: _, mt0 :: mrest =>
    let ev := I.event e.event
    let time := e.time
    let act := sys.active mask
    let att := c.attemptsOf e.event + 1
    let tail := (c.pending.tail.zip mrest)
    let headE := toEntry I e mt0
    let payloadV := headE.payload
    let already := e.done.filterMap fun k => (I.env.faults[k]?).map (·.id)
    let drops := I.env.faults.filter (dropMatches ev att time)
    if act.any (fun p => p.2.hits [.drop, .lose] e.event att e.time) then
      let recs := drops.map fun f => { fault := f.id, effect := dropEffect f }
      .ok { kind := .drop, faults := recs, responsible := responsibleOf I.input ev [] recs, pairs := tail,
            seq, book := b }
    else
    match Core.Behav.delayFault act e att with
    | some (k, f) =>
      let fid := (I.env.faults[k]?.map (·.id)).getD ""
      let eff := (I.env.faults[k]?.map delayEffect).getD .delayed
      match Core.Behav.later e k f.by_ with
      | .error _ => .fail .delay "Value time exceeds 2^53."
      | .ok cp =>
        let mt : PMeta := { mt0 with seq, copyOf := some (mt0.copyOf.getD mt0.seq) }
        let recs := [{ fault := fid, effect := eff }]
        .ok { kind := .delay, faults := recs, responsible := responsibleOf I.input ev [] recs,
              pairs := insertP tail (cp, mt), seq := seq + 1, book := b }
    | none =>
      let ds := dsOv.getD (Core.Behav.Exec.drawsOf sys mask c e b).1
      let R := sys.resolve ds
      let c0 := c.popE e
      -- phase 1, behaviour by behaviour in input order, instance by instance
      let ph1 : Except String (List (Nat × Nat × List FaultRecord) × List Ignored2 × List FaultRecord) :=
        I.behs.zipIdx.foldlM (fun (ws, igs, recs) (bh, j) =>
          match addressedM I mt0 j bh with
          | none => .ok (ws, igs, recs)
          | some [] => .ok (ws, igs ++ [{ base := { behavior := bh.id, reason := .noTransition, considered := [] },
                                          inst := none }], recs)
          | some ms => ms.foldlM (fun (ws, igs, recs) m =>
              if h : m < R.sig.machines then
                let own := c0.machines.getD m ⟨0, []⟩
                let state := (Elab.statesOf bh).getD own.ctrl ""
                match scanRec I R ⟨m, h⟩ c0 e own state ev time bh.transitions.zipIdx [] false false [] with
                | .error (ti, err) =>
                  let src := ((bh.transitions[ti]?).bind (·.guard)).toList
                  .error (msgOf I (toConf I c metas b) (I.key m) (I.inst m) payloadV time src (errText err))
                | .ok (some (ti, en), _, _, _, rs) => .ok (ws ++ [(m, ti, en)], igs, recs ++ rs ++ en)
                | .ok (none, considered, dis, gf, rs) =>
                  let reason := if dis then IgnoredReason.disabled else if gf then .guardFalse else .noTransition
                  .ok (ws, igs ++ [{ base := { behavior := bh.id, reason, considered }, inst := some (I.inst m) }], recs ++ rs)
              else .ok (ws, igs, recs)) (ws, igs, recs)) ([], [], [])
      match ph1 with
      | .error msg => .fail .deliver msg
      | .ok (ws, ignored, recs) =>
        -- phase 2, winners in machine order, each from the start-of-step machine
        let ph2 : Except String (List Fired2 × List (Nat × Core.Behav.MState) × List (CEntry × PMeta) ×
            Nat × Book × List Draw) :=
          ws.foldlM (fun (fired, mss, outs, seq, bk, drs) (m, ti, _) =>
            if h : m < R.sig.machines then
              let bh := I.beh m
              match (R.trans ⟨m, h⟩)[ti]?, bh.transitions[ti]? with
              | some tr, some t =>
                let own := c0.machines.getD m ⟨0, []⟩
                let fin := next.bind fun c' => (c'.machines[m]?).map (·.vars)
                match effRec I sys (me := ⟨m, h⟩) b c0 e mt0 bh t ti fin 0 tr.effects t.effects
                    { own, seq, book := bk } with
                | .error (j, err) =>
                  let view := toConf I { c with machines := c.machines.set m own } metas b
                  .error (msgOf I view (I.key m) (I.inst m) payloadV time ((t.effects[j]?).map effSrcs |>.getD [])
                    (if err == .noRequester then s!"Effect replies to \"{ev}\", which has no requester." else errText err))
                | .ok st =>
                  let f : Fired2 := { base := { behavior := bh.id, transition := t.id, source := t.source,
                                                target := t.target, guard := t.guard, sets := st.sets, emitted := st.emits },
                                      inst := I.inst m }
                  .ok (fired ++ [f], mss ++ [(m, { st.own with ctrl := tr.dst.val })], outs ++ st.outs,
                       st.seq, st.book, drs ++ st.draws)
              | _, _ => .error "internal: a winner without its transition"
            else .error "internal: a winner out of range") ([], [], [], seq, b, [])
        match ph2 with
        | .error msg => .fail .deliver msg
        | .ok (fired, _, outs, seq', b', drs) =>
          -- the commit: the pending entries of the timers the winners touched removed, then the
          -- emitted entries inserted by time in machine order
          let touched : List (Nat × Nat) := ws.flatMap fun (m, ti, _) =>
            if h : m < R.sig.machines then
              match (R.trans ⟨m, h⟩)[ti]? with
              | some tr => tr.effects.filterMap fun eff => match eff with
                | Core.Behav.Effect.timer n .. | Core.Behav.Effect.cancel n => some (m, n)
                | _ => none
              | none => []
            else []
          let kept := tail.filter fun p => !Core.Behav.isTimerOf touched p.1
          let pairs := outs.foldl insertP kept
          let faults := injectedOf mt0.src ++ recs
          let base : Out := { kind := .deliver, fired, ignored, faults, responsible := responsibleOf I.input ev fired faults,
                              draws := drs, pairs, seq := seq', book := b' }
          -- a duplicate after a committed delivery
          match Core.Behav.dupFault act e att with
          | none => .ok base
          | some (k, f) =>
            match Core.Behav.later e k f.by_ with
            | .error _ => .fail .deliver "Value time exceeds 2^53."
            | .ok cp =>
              let fid := (I.env.faults[k]?.map (·.id)).getD ""
              let mt : PMeta := { mt0 with seq := seq', copyOf := some (mt0.copyOf.getD mt0.seq) }
              .ok { base with pairs := insertP pairs (cp, mt), seq := seq' + 1,
                              faults := faults ++ [{ fault := fid, effect := .other "duplicated" }],
                              responsible := if base.responsible.contains fid then base.responsible
                                             else base.responsible ++ [fid] }
  | _, _ => .fail .deliver "internal: no head"

/-- One step recorded with the draws the scheduler makes. -/
def stepRec (I : Info) (sys : Core.Behav.Sys) (mask : List Bool) (c : Core.Behav.Cfg) (metas : List PMeta)
    (seq taken : Nat) (b : Book) (next : Option Core.Behav.Cfg := none) : SR :=
  stepRecWith I sys mask c metas seq taken b none next

/-! ### The run -/

/-- The bookkeeping of the initial queue: the scenario's steps, then the active `inject` faults,
each inserted by time, as `initialConf` (Format2.lean:2358-2376) and `Sys.initCfg` insert them. -/
def initPairs (I : Info) (sys : Core.Behav.Sys) (mask : List Bool) : List (CEntry × PMeta) × Nat :=
  let i := I.input
  let steps := (sys.init.pending.length, ())
  let _ := steps
  let stepPairs := (i.scenario.steps.zipIdx).filterMap fun (st, k) =>
    match (Elab.payloadOf st.payload "").toOption with
    | none => none
    | some pl =>
      let target := st.target.map fun (bn, v) => ({ behavior := bn, inst := v, incarnation := 0 } : Addr)
      let tgt : Option Nat := st.target.map fun (bn, v) =>
        match I.behs.findIdx? (·.id == bn), v with
        | some j, .num x => match Num.safeInteger? x with
          | some n => if n < 0 then I.lay.length else Elab.machineOf I.behs j n.toNat
          | none => I.lay.length
        | _, _ => I.lay.length
      some (({ time := st.time, event := Elab.evIdx i st.event, payload := pl, target := tgt } : CEntry),
            ({ seq := k, sched := st.time, src := .scenario k, target } : PMeta))
  let q := stepPairs.foldl insertP []
  let n0 := i.scenario.steps.length
  let act := sys.active mask
  let (q, n) := act.foldl (fun (q, n) (p : Nat × Core.Behav.Fault) =>
    if p.2.kind = .inject then
      let fid := (I.env.faults[p.1]?.map (·.id)).getD ""
      (insertP q ({ time := p.2.at_, event := p.2.event, payload := p.2.payload },
                  { seq := n, sched := p.2.at_, src := .fault fid }), n + 1)
    else (q, n)) (q, n0)
  (q, n)

structure RunB where
  state : Core.Behav.State
  book : Book
  metas : List PMeta
  seq : Nat
  stepsRev : List Step2
  outcome : Outcome2

def blankB (I : Info) (index : Nat) (head : Entry) (kind : Kind2) (config : Conf) : Step2 :=
  { index, time := head.time, kind, head, fired := [], ignored := [], faults := [], responsible := [],
    resources := [], draws := [], config, error := none }

/-- The head of a configuration with its bookkeeping, as a format-2 entry. -/
def headOf (I : Info) (c : Core.Behav.Cfg) (metas : List PMeta) : Entry :=
  match c.pending, metas with
  | e :: _, mt :: _ => toEntry I e mt
  | _, _ => default

/-- The record of a failed step. -/
def failRec (I : Info) (sys : Core.Behav.Sys) (mask : List Bool) (c : Core.Behav.Cfg) (r : RunB) : Step2 :=
  let taken := r.stepsRev.length
  let head := headOf I c r.metas
  let (kind, msg) := match stepRec I sys mask c r.metas r.seq taken r.book with
    | .fail k msg => (k, msg)
    | .ok _ => (.deliver, "internal: the calculus step failed where its record did not")
  { blankB I taken head kind (toConf I c r.metas r.book) with responsible := [head.event], error := some msg }

/-- The record of a committed step and the run's bookkeeping after it, or the record of an internal
error when the recorded step does not arrive at the configuration `Exec.step` committed. -/
def commitRec (I : Info) (sys : Core.Behav.Sys) (mask : List Bool) (c : Core.Behav.Cfg) (r : RunB)
    (s' : Core.Behav.State) : Except Step2 (Step2 × Book × List PMeta × Nat) :=
  let taken := r.stepsRev.length
  let head := headOf I c r.metas
  let internal (msg : String) : Step2 :=
    { blankB I taken head .deliver (toConf I c r.metas r.book) with error := some msg }
  match stepRec I sys mask c r.metas r.seq taken r.book s'.cfg, s' with
  | .ok o, .run _ c' =>
    if o.pairs.map (·.1) != c'.pending then .error (internal "internal: the recorded queue differs from the calculus step")
    else
      let metas := o.pairs.map (·.2)
      .ok ({ blankB I taken head o.kind (toConf I c' metas o.book) with
              fired := o.fired, ignored := o.ignored, faults := o.faults, responsible := o.responsible,
              draws := o.draws }, o.book, metas, o.seq)
  | _, _ => .error (internal "internal: the calculus step committed where its record failed")

/-- One step of the run: `Exec.step` decides the next state; `stepRec` records it. -/
def advanceB (I : Info) (sys : Core.Behav.Sys) (bound : Nat) (r : RunB) : RunB :=
  match r.state with
  | .err _ _ => { r with outcome := .error }
  | .run mask c =>
    match Core.Behav.Exec.step sys r.state r.book with
    | .idle => { r with outcome := .quiescent }
    | .stopped => { r with outcome := .stopped }
    | .failed _ => { r with stepsRev := failRec I sys mask c r :: r.stepsRev, outcome := .error }
    | .committed _ s' _ =>
      match commitRec I sys mask c r s' with
      | .ok (rec_, book, metas, seq) =>
        { state := s', book, metas, seq, stepsRev := rec_ :: r.stepsRev,
          outcome := if s'.cfg.pending.isEmpty then .quiescent
            else if r.stepsRev.length + 1 ≥ bound then .stepLimit else .running }
      | .error rec_ => { r with stepsRev := rec_ :: r.stepsRev, outcome := .error }

def loopB (I : Info) (sys : Core.Behav.Sys) (bound : Nat) : Nat → RunB → RunB
  | 0, r => r
  | fuel + 1, r => if r.outcome = .running then loopB I sys bound fuel (advanceB I sys bound r) else r

/-- One advance either adds no step and stops, or adds one step, and runs on only below the bound. -/
theorem advanceB_len (I : Info) (sys : Core.Behav.Sys) (bound : Nat) (r : RunB) :
    ((advanceB I sys bound r).stepsRev.length = r.stepsRev.length ∧ (advanceB I sys bound r).outcome ≠ .running) ∨
    ((advanceB I sys bound r).stepsRev.length = r.stepsRev.length + 1 ∧
      ((advanceB I sys bound r).outcome = .running → r.stepsRev.length + 1 < bound)) := by
  unfold advanceB
  split
  · left; simp
  · split
    · left; simp
    · left; simp
    · right; simp
    · split
      · right
        simp only [List.length_cons, true_and]
        intro h
        split at h
        · cases h
        · split at h
          · cases h
          · omega
      · right; simp

/-- **The run stops within the bound**: from a run whose steps are below the bound while it runs,
`loopB` with `fuel` advances ends with an outcome other than `running` and at most `bound` steps,
when `fuel` advances suffice to reach the bound. -/
theorem loopB_stops (I : Info) (sys : Core.Behav.Sys) (bound : Nat) : (fuel : Nat) → (r : RunB) →
    r.stepsRev.length ≤ bound → (r.outcome = .running → r.stepsRev.length < bound) →
    (r.outcome = .running → bound ≤ r.stepsRev.length + fuel) →
    (loopB I sys bound fuel r).outcome ≠ .running ∧ (loopB I sys bound fuel r).stepsRev.length ≤ bound
  | 0, r, hl, hrun, hfuel => by
    simp only [loopB]
    refine ⟨fun h => ?_, hl⟩
    have := hrun h; have := hfuel h; omega
  | fuel + 1, r, hl, hrun, hfuel => by
    simp only [loopB]
    split
    · rename_i hr
      have hlt := hrun hr
      apply loopB_stops I sys bound fuel
      · rcases advanceB_len I sys bound r with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
      · intro h'
        rcases advanceB_len I sys bound r with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact absurd h' h2
        · have := h2 h'; omega
      · intro h'
        rcases advanceB_len I sys bound r with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact absurd h' h2
        · have := hfuel hr; omega
    · rename_i hr
      exact ⟨hr, hl⟩

/-- The stream names of the draw slots (format 2's `after:{behavior}:{transition}:{effect}`). -/
def slotNames (I : Info) (sys : Core.Behav.Sys) : List String :=
  sys.samples.map fun s =>
    let b := I.beh s.1
    let tid := ((b.transitions[s.2.1]?).map (·.id)).getD ""
    s!"after:{b.id}:{tid}:{s.2.2.1}"

/-- The initial book of a format-2 run. -/
def bookOf (I : Info) (sys : Core.Behav.Sys) : Book :=
  { seed := I.input.scenario.seed, names := slotNames I sys, counts := [] }

end Exegra.V2.B

namespace Exegra.V2

open Exegra.V2.B

/-- **The trace of an elaborated input**: the fold of `Exec.step` from the format-2 initial state
(every scenario fault active), up to the scenario's step limit, encoded as a format-2 trace. -/
def traceOfB (i : Input) (sys : Core.Behav.Sys) : Trace2 :=
  let I := mkInfo i
  let mask := List.replicate sys.faults.length true
  let (pairs, seq) := initPairs I sys mask
  let s0 := initialB sys
  let b0 := bookOf I sys
  let metas := pairs.map (·.2)
  let initial := toConf I s0.cfg metas b0
  let bound := i.scenario.stepLimit
  let r := loopB I sys bound bound
    { state := s0, book := b0, metas, seq, stepsRev := [],
      outcome := if s0.cfg.pending.isEmpty then .quiescent else .running }
  { input := i, initialDraws := [], faults := (envOf i).faultIds, initial,
    steps := r.stepsRev.reverse, outcome := r.outcome, final := toConf I r.state.cfg r.metas r.book }

/-- The run of `traceOfB` stops within the step limit. -/
theorem traceOfB_stops {i : Input} {sys : Core.Behav.Sys} (h1 : 1 ≤ i.scenario.stepLimit) :
    (traceOfB i sys).outcome ≠ .running ∧ (traceOfB i sys).steps.length ≤ i.scenario.stepLimit := by
  unfold traceOfB
  simp only [List.length_reverse]
  exact loopB_stops _ sys _ _ _ (by simp) (fun _ => by simp; omega) (fun _ => by simp)

/-- The legacy trace of an input outside the calculus, marked as such. -/
def legacyTrace (t : Value) : Value :=
  match t with
  | .obj k fs => .obj k (fs ++ [("semantics", .str "legacy")])
  | v => v

/-- **Format 2, dispatched**, with the trace written by `write`: an input `Elab.elab` accepts runs on
the calculus scheduler (`traceOfB`); an input outside the fragment runs the legacy interpreter and
its trace says `"semantics": "legacy"`; an ill-typed or non-integer input is refused. -/
def runInputWith (write : Value → String) (i : Input) : Except String String := do
  validate i
  match Elab.«elab» i with
  | .ok sys => pure (write (Encode.trace (traceOfB i sys)))
  | .error (.outOfFragment _) => pure (write (legacyTrace (Encode.trace (traceOf i))))
  | .error r => throw r.message

/-- Run a decoded version-2 input: a refusal, or the trace JSON text. -/
def runInput (i : Input) : Except String String := runInputWith Json.write i

/-- **A run of an elaborated input terminates** (the task's criterion 14, second half; the format-2
counterpart of `runInput_terminates`). For an input the elaborator accepts, whatever `runInput`
returns is the trace of `traceOfB`, the fold of the calculus scheduler, and that run ends with an
outcome other than `running` after at most `stepLimit` steps. -/
theorem runB_terminates {i : Input} {sys : Core.Behav.Sys} {out : String} (h : Elab.«elab» i = .ok sys)
    (hr : runInput i = .ok out) :
    out = Json.write (Encode.trace (traceOfB i sys)) ∧
      (traceOfB i sys).outcome ≠ .running ∧ (traceOfB i sys).steps.length ≤ i.scenario.stepLimit := by
  refine ⟨?_, traceOfB_stops (Elab.elab_stepLimit h)⟩
  unfold runInput runInputWith at hr
  cases hv : validate i with
  | error e => rw [hv] at hr; cases hr
  | ok u =>
    rw [hv, h] at hr
    simp only [bind, Except.bind, pure, Except.pure] at hr
    cases hr; rfl

end Exegra.V2

namespace Exegra

/-- The refusal of a version-1 engine input. -/
def formatOneGone : String :=
  "Version 1 engine inputs are no longer run: format 1 was removed (WG-5681); derive a version-2 input."

/-- The refusal of JSON that is not an engine input. -/
def notAnInput : String := "Not an engine input: \"format\" must be \"exegra-sim-input\" and \"version\" 2."

/-- An engine input, parsed: version 2 runs `V2.runInput`; any other input is refused. -/
def runAnyValue (v : Value) : Except String String :=
  match v with
  | .obj _ root =>
    match objGet? root "version", objGet? root "format" with
    | some (.num x), some (.str "exegra-sim-input") =>
      if x == 2 then do V2.runInput (← V2.Decode.input root) else .error formatOneGone
    | _, _ => .error notAnInput
  | _ => .error notAnInput

/-- `runAnyValue` on JSON text: what `exegra-lean` runs. -/
def runAny (text : String) : Except String String := do
  let v ← Json.parse text
  runAnyValue v

/-- The legacy interpreter on a version-2 input (`V2.traceOf` whatever the elaborator says):
`exegra-lean --legacy`, for the differential check of the calculus path against it. -/
def runAnyLegacy (text : String) : Except String String := do
  let v ← Json.parse text
  match v with
  | .obj _ root =>
    match objGet? root "version", objGet? root "format" with
    | some (.num x), some (.str "exegra-sim-input") =>
      if x == 2 then do V2.runInputLegacy (← V2.Decode.input root) else .error formatOneGone
    | _, _ => .error notAnInput
  | _ => .error notAnInput

end Exegra
/-- info: 'Exegra.V2.runB_terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.V2.runB_terminates
