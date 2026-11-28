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
`scheduledAt`, delayed copies' `copyOf`, the streams' draw counts, the routes an entry carries
by behaviour id and instance, format 2's round-robin counters (the calculus keeps them modulo the
instance count), the creation order of keyed instances, the records of a step (fired
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
  /-- Format 2's kind of the entry (an event, or an entry of a resource). -/
  kind : EntryKind := .event
  /-- The routes decided for the entry: behaviour id and instance (format 2's `Entry.routes`). -/
  routes : Option (List (String × Value)) := none
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
  /-- The routes in `Sys.routes` order, with their behaviours' indices. -/
  routes : List (Nat × RouteIn) := []
  /-- The key of each machine in the configuration at hand (a keyed instance's). -/
  keys : List (Option Core.Behav.Val) := []

/-- A calculus value as a format-2 value. -/
def toValue : Core.Behav.Val → Value
  | .int n => .num (n : Rat)
  | .rat q => .num q
  | .bool b => .bool b
  | .str s => .str s
  | .lit _ json => (Json.parse json).toOption.getD .null

def payloadKeys (v : Value) : List String :=
  match v with
  | .obj _ fs => fs.map (·.1)
  | _ => []

def mkInfo (i : Input) : Info :=
  let effs := i.behaviors.flatMap fun b => b.transitions.flatMap (·.effects)
  let fields := (i.scenario.steps.flatMap fun st => payloadKeys st.payload) ++
    (i.faults.flatMap fun f => payloadKeys f.payload) ++
    effs.flatMap (fun e => match e with
      | .emit _ _ pl _ | .timer _ _ _ pl | .request _ _ _ _ _ _ _ pl | .send _ _ pl _ _ _ => pl.map (·.1)
      | _ => []) ++ ["resource", "class", "waited", "served", "reason"]
  let timers := effs.flatMap fun e => match e with
    | .timer n .. | .cancel n => [n]
    | _ => []
  { input := i, env := envOf i, behs := i.behaviors, lay := Elab.layout i.behaviors, fields, timers,
    routes := Elab.routeList i }

namespace Info
variable (I : Info)

def beh (m : Nat) : BehaviorIn := I.behs.getD (I.lay.getD m (0, 0)).1 default
/-- The instance of machine `m`: its index, or for a slot of a keyed behaviour its key. -/
def inst (m : Nat) : Value :=
  if Elab.isKeyed (I.beh m) then ((I.keys.getD m none).map toValue).getD .null
  else .num (↑(I.lay.getD m (0, 0)).2 : Rat)
def key (m : Nat) : String := machineKey (I.beh m) (I.inst m)
def addr (m : Nat) : Addr := { behavior := (I.beh m).id, inst := I.inst m, incarnation := 0 }
def event (id : Nat) : String := I.input.events.getD id ""
def field (id : Nat) : String := (I.fields.find? (Elab.strId · == id)).getD ""
def timerName (id : Nat) : String := (I.timers.find? (Elab.strId · == id)).getD ""

/-- The information with the keys of machine states `ms`. -/
def withKeys (ms : List Core.Behav.MState) : Info := { I with keys := ms.map (·.key) }

end Info

def payloadValue (I : Info) (pl : List (Nat × Core.Behav.Val)) : Value :=
  .obj 0 (pl.map fun (f, v) => (I.field f, toValue v))

def toEntry (I : Info) (e : CEntry) (mt : PMeta) : Entry :=
  { seq := mt.seq, time := e.time, scheduledAt := mt.sched,
    event := (match mt.kind with | .event => I.event e.event | _ => ""),
    payload := (match mt.kind with | .event => payloadValue I e.payload | _ => .null),
    source := mt.src, kind := mt.kind, target := mt.target,
    sender := mt.sender, routes := mt.routes, timer := mt.timer, copyOf := mt.copyOf }

/-- A machine state as a format-2 machine. -/
def toMachine (I : Info) (m : Nat) (ms : Core.Behav.MState) : Machine :=
  let b := I.beh m
  { state := (Elab.statesOf b).getD ms.ctrl "",
    vars := (b.variables.zip ms.vars).foldl (fun vs (v, x) => objInsert vs v.name (toValue x)) [],
    types := b.types }

/-- The instances of each behaviour in machine states `ms`: a keyed behaviour's live slots, in
creation order (slot order), by key. -/
def insts (I : Info) (ms : List Core.Behav.MState) : List (String × List Value) :=
  let I := I.withKeys ms
  I.behs.zipIdx.map fun (b, j) =>
    (b.id, if Elab.isKeyed b then
        (((List.range (Elab.instCount b)).map (Elab.machineOf I.behs j)).filter
          (fun m => (ms[m]?.map (·.live)).getD false)).map I.inst
      else (List.range (Elab.instCount b)).map fun (k : Nat) => Value.num (k : Rat))

/-! ### The queue with its bookkeeping -/

/-- `insertByTime` on entries with their bookkeeping. -/
def insertP (q : List (CEntry × PMeta)) (x : CEntry × PMeta) : List (CEntry × PMeta) :=
  match q with
  | [] => [x]
  | y :: ys => if x.1.time < y.1.time then x :: y :: ys else y :: insertP ys x

/-- Format 2's id and sending time of each message on each link queue (WG-5683): the message in
transfer and those waiting, by (link, queue key). The calculus keeps the messages without them. -/
abbrev LQIds := List ((Nat × Option Nat) × (Option (Nat × Nat) × List (Nat × Nat)))

def LQIds.get (q : LQIds) (l : Nat) (k : Option Nat) : Option (Nat × Nat) × List (Nat × Nat) :=
  ((q.find? (·.1 == (l, k))).map (·.2)).getD (none, [])

def LQIds.set (q : LQIds) (l : Nat) (k : Option Nat) (x : Option (Nat × Nat) × List (Nat × Nat)) : LQIds :=
  if q.any (·.1 == (l, k)) then q.map fun p => if p.1 == (l, k) then ((l, k), x) else p
  else q ++ [((l, k), x)]

/-- A send's outcome on its queue, as settling decides it: propagated, started, queued, or a
failure (the transfer would end at or beyond `2^53`). -/
inductive LOut where
  | p | s | q | f
  deriving Inhabited, DecidableEq

/-- The outcomes of the sends of a delivery, in order, from its settling actions. -/
def planOf : List Core.Behav.Act → List LOut
  | [] => []
  | .prop .. :: as => .p :: planOf as
  | .put e :: as => (match e.kind with | .linkDone .. => [LOut.s] | _ => []) ++ planOf as
  | .note (.lqueued ..) :: as => .q :: planOf as
  | .fail _ :: _ => [.f]
  | _ :: as => planOf as

/-- A message sent in phase 2: its id (format 2's sequence number), the sequence number of the entry
its send created (propagated or started), and its drawn latency (propagated). -/
structure SMeta where
  mid : Nat
  eseq : Nat
  lat : Nat
  deriving Inhabited

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
  | .release _ _ _ _ _ => "A release of more units than held."
  | .serviceBound _ => "Value service time exceeds 2^53."
  | .scaleBound _ => "Value demand scale exceeds 2^32."
  | .routeField _ => "Route needs a payload field."
  | .routeFull _ => "Behavior would exceed its instances."
  | .ambiguous => "Ambiguous reference"
  | .keySort => "Instance key of another sort"
  | .size _ _ => "Size of emit must be an integer in [0, 2^40)."

/-- The message of a failed route decision (format 2's `decideRoutes`): `ev` is the entry's
event. -/
def routeErrText (I : Info) (ev : String) : Core.Behav.Err → String
  | .routeField i =>
    let (j, r) := I.routes.getD i (0, default)
    s!"Route of \"{ev}\" to \"{(I.behs.getD j default).id}\" needs payload field \"{r.field.getD ""}\"."
  | .routeFull i =>
    let b := I.behs.getD (I.routes.getD i (0, default)).1 default
    s!"Behavior \"{b.id}\" would exceed {Elab.instCount b} instances."
  | err => errText err

/-! ### Settling, recorded -/

/-- The sequence number of a calculus request id: the sequence number format 2 gave the request
when it was enqueued (its id there). -/
def seqOf (rs : List (Nat × Nat)) (rid : Nat) : Nat := ((rs.find? (·.1 == rid)).map (·.2)).getD rid

/-- A calculus request as format 2's request. -/
def reqOf (I : Info) (rs : List (Nat × Nat)) (r : Core.Behav.RReq) : Res.Req String ReqInfo :=
  { id := seqOf rs r.id, owner := I.key r.owner, cls := r.cls, units := r.units, since := r.since,
    kind := r.kind,
    info := { requester := I.addr r.owner, requesterKey := I.key r.owner, thenEv := I.event r.info.thenEv,
              refused := r.info.refused.map I.event,
              payload := r.info.payload.map fun (f, v) => (I.field f, toValue v),
              demand := .fixed 0, stream := "" } }

/-- The calculus world as format 2's resources. -/
def resourcesOf (I : Info) (w : Core.Behav.World) (rs : List (Nat × Nat)) : List (String × Res.RState String ReqInfo) :=
  I.input.resources.zipIdx.map fun (d, ri) =>
    (d.id, match w.res[ri]? with
      | some s =>
        { capacity := s.capacity,
          holds := s.holds.map fun h => { owner := I.key h.owner, cls := h.cls, units := h.units,
                                          req := h.req.map (seqOf rs) },
          waiting := s.waiting.map (reqOf I rs) }
      | none => { capacity := d.capacity, holds := [], waiting := [] })

/-- What the recording of settling keeps. -/
structure WSt where
  pairs : List (CEntry × PMeta)
  seq : Nat
  book : Book
  draws : List Draw := []
  recs : List ResRecord := []
  rs : List (Nat × Nat)
  /-- The entries phase 2 emitted, with their bookkeeping, in order (inserted at their `put`). -/
  emitted : List (CEntry × PMeta) := []
  /-- The messages phase 2 sent, in order. -/
  sends : List SMeta := []
  /-- The world as filling sees it (the last delivery of each ordered link queue). -/
  lw : Core.Behav.World := {}
  lq : LQIds := []
  /-- The message the last link action named. -/
  cur : Nat := 0
  links : List LinkRec := []

/-- A world draw from book `b`, with the record format 2's `sample` keeps (`Exec.drawW`). -/
def drawWB (h : (Nat × Nat × Nat) × Core.Behav.Dist) (b : Book) : Nat × Book × List Draw :=
  let (v, b') := Core.Behav.Exec.drawW h b
  let name := b.siteName h.1
  let drew := match h.2 with
    | .fixed _ => false
    | d => d.wf && b.seed.isSome
  match drew, b.seed with
  | true, some seed =>
    (v, b', [{ stream := name, index := b.count name, value := Random.draw seed name (b.count name) }])
  | _, _ => (v, b', [])

/-- A world draw, recorded. -/
def drawWRec (h : (Nat × Nat × Nat) × Core.Behav.Dist) (st : WSt) : Nat × WSt :=
  let (v, b', ds) := drawWB h st.book
  (v, { st with book := b', draws := st.draws ++ ds })

/-- A link queue key as format 2 names it: `""`, or the receiver's machine key. -/
def keyStr (I : Info) : Option Nat → String
  | none => ""
  | some r => I.key r

/-- A link record. -/
def lrec (I : Info) (l : Nat) (k : Option Nat) (mid : Nat) (action : String) (now size : Nat) : LinkRec :=
  { link := (I.input.links.getD l default).id, queue := keyStr I k, message := mid, action, atTime := now, size }

/-- The message of a failure of settling. -/
def settleErrText (I : Info) (sys : Core.Behav.Sys) : Core.Behav.Err → String
  | .release ri m c n held =>
    let d := sys.resources.getD ri default
    s!"Instance \"{I.key m}\" releases {n} units of \"{d.id}\" class \"{Core.Behav.classId d c}\" but holds {held}."
  | .serviceBound ri => s!"Value service time of \"{(sys.resources.getD ri default).id}\" exceeds 2^53."
  | .scaleBound ri => s!"Value demand scale of \"{(sys.resources.getD ri default).id}\" exceeds 2^32."
  | err => errText err

/-- Settling at `now`, recorded: the actions of `settle` (or `worldStep`) performed on the queue
with its bookkeeping, as format 2's `settleOne`, `applyGrants` and `applyRemoved` perform them
(Format2.lean:1654-1766): sequence numbers in order, the resource records, and the draws. -/
def actsRec (I : Info) (sys : Core.Behav.Sys) (now : Nat) : List Core.Behav.Act → WSt → Except String WSt
  | [], st => .ok st
  | a :: as, st =>
    let dOf (ri : Nat) : Res.ResourceDecl := sys.resources.getD ri default
    let rec_ (ri : Nat) (r : Core.Behav.RReq) (rs : List (Nat × Nat)) (action : String) : ResRecord :=
      resRec (dOf ri).id (dOf ri) (reqOf I rs r) action now
    match a with
    | .note (.released ri c n) =>
      let rr : ResRecord :=
        { resource := (dOf ri).id, cls := Core.Behav.classId (dOf ri) c, request := none,
          action := "released", atTime := now, waited := none, served := none, reason := none,
          units := some n }
      actsRec I sys now as { st with recs := st.recs ++ [rr] }
    | .note (.enqueued ri r) =>
      let rs := (r.id, st.seq) :: st.rs
      actsRec I sys now as { st with rs, seq := st.seq + 1, recs := st.recs ++ [rec_ ri r rs "enqueued"] }
    | .note (.granted ri r waited) =>
      actsRec I sys now as { st with recs := st.recs ++ [{ rec_ ri r st.rs "granted" with waited := some waited }] }
    | .note (.removed ri r waited) =>
      let (action, reason) : String × Option String := match (dOf ri).overflow with
        | .refuse => ("refused", some "bound")
        | .drop => ("dropped", none)
        | .shedOldest => ("shed", some "shed")
      actsRec I sys now as { st with recs := st.recs ++ [{ rec_ ri r st.rs action with waited := some waited, reason }] }
    | .note (.completed ri r waited served) =>
      let rr : ResRecord := { rec_ ri r st.rs "completed" with waited := some waited, served := some served }
      actsRec I sys now as { st with recs := st.recs ++ [rr] }
    | .note (.timedOut ri r waited) =>
      let rr : ResRecord := { rec_ ri r st.rs "timed-out" with waited := some waited, reason := some "timeout" }
      actsRec I sys now as { st with recs := st.recs ++ [rr] }
    | .ins ri rid outcome e =>
      let kind : EntryKind := match e.kind with
        | .waitTimeout _ _ => .waitTimeout (dOf ri).id (seqOf st.rs rid)
        | _ => .event
      let mt : PMeta := { seq := st.seq, sched := e.time, src := .resource (dOf ri).id (seqOf st.rs rid) outcome,
                          target := e.target.map I.addr, kind }
      actsRec I sys now as { st with pairs := insertP st.pairs (e, mt), seq := st.seq + 1 }
    | .hole ri r dm waited num den =>
      let (v, st) := drawWRec ((r.owner, r.info.site.1, r.info.site.2), dm) st
      let served := Core.Behav.ceilDiv (v * num) den
      if Core.Behav.timeLimit ≤ served then .error s!"Value service time of \"{(dOf ri).id}\" exceeds 2^53."
      else if Core.Behav.timeLimit ≤ now + served then .error "Value time exceeds 2^53."
      else
        let e : CEntry := { time := now + served, event := 0, payload := [], kind := .serviceDone ri r waited served }
        let mt : PMeta := { seq := st.seq, sched := now + served,
                            src := .resource (dOf ri).id (seqOf st.rs r.id) "service-done",
                            kind := .serviceDone (dOf ri).id (reqOf I st.rs r) waited served }
        actsRec I sys now as { st with pairs := insertP st.pairs (e, mt), seq := st.seq + 1 }
    | .rm ri rid =>
      actsRec I sys now as { st with pairs := st.pairs.filter (fun p => p.1.kind != .waitTimeout ri rid) }
    | .fail err => .error (settleErrText I sys err)
    | .put e =>
      match e.kind with
      | .linkDone l k =>
        let lid := (I.input.links.getD l default).id
        -- a send's transfer (its message and entry numbered in phase 2), or the next waiting
        -- message of a queue whose transfer ended (numbered now)
        let (mid, sent, eseq, sends, seq, lq) : Nat × Nat × Nat × List SMeta × Nat × LQIds := match st.sends with
          | x :: rest => (x.mid, now, x.eseq, rest, st.seq, st.lq)
          | [] =>
            let (it, ws) := st.lq.get l k
            let w := ws.headD (0, 0)
            (w.1, w.2, st.seq, [], st.seq + 1, st.lq.set l k (it, ws.drop 1))
        let lq := lq.set l k (some (mid, sent), (lq.get l k).2)
        let mt : PMeta := { seq := eseq, sched := e.time, src := .link lid mid, kind := .linkDone lid (keyStr I k) mid }
        actsRec I sys now as { st with pairs := insertP st.pairs (e, mt), sends, seq, lq, cur := mid }
      | _ =>
        match st.emitted with
        | p :: rest => actsRec I sys now as { st with pairs := insertP st.pairs p, emitted := rest }
        | [] => .error "internal: an emitted entry without its record"
    | .note (.lstarted l k m) =>
      actsRec I sys now as { st with links := st.links ++ [lrec I l k st.cur "started" now m.size] }
    | .note (.lqueued l k m) =>
      match st.sends with
      | x :: rest =>
        let (it, ws) := st.lq.get l k
        actsRec I sys now as { st with sends := rest, lq := st.lq.set l k (it, ws ++ [(x.mid, now)]), cur := x.mid,
                                       links := st.links ++ [lrec I l k x.mid "queued" now m.size] }
      | [] => .error "internal: a queued message without its record"
    | .note (.llost l k m oldest) =>
      let (it, ws) := st.lq.get l k
      let (lost, ws') := if oldest then (ws.headD (0, 0), ws.drop 1) else (ws.getLastD (0, 0), ws.dropLast)
      actsRec I sys now as { st with lq := st.lq.set l k (it, ws'), links := st.links ++ [lrec I l k lost.1 "lost" now m.size] }
    | .note (.ltransferred l k m) =>
      let (it, ws) := st.lq.get l k
      let mid := (it.map (·.1)).getD 0
      actsRec I sys now as { st with lq := st.lq.set l k (none, ws), cur := mid,
                                     links := st.links ++ [lrec I l k mid "transferred" now m.size] }
    | .prop l k ord lat m =>
      let L := I.input.links.getD l default
      -- a message sent in phase 2 (numbered and drawn there), or the message whose transfer ended
      let (mid, eseq, v, st) : Nat × Nat × Nat × WSt := match st.sends with
        | x :: rest => (x.mid, x.eseq, x.lat, { st with sends := rest })
        | [] =>
          let (v, st) := drawWRec (Core.Behav.linkSite l, lat) st
          (st.cur, st.seq, v, { st with seq := st.seq + 1 })
      let t := if ord then max (now + v) ((st.lw.lq l k).last.getD 0) else now + v
      if Core.Behav.timeLimit ≤ t then .error "Value time exceeds 2^53." else
      let lw := if ord then st.lw.setLq l k { st.lw.lq l k with last := some t } else st.lw
      let mt : PMeta := { seq := eseq, sched := t, src := .link L.id mid, target := m.target.map I.addr,
                          sender := m.sender.map I.addr }
      actsRec I sys now as { st with pairs := insertP st.pairs (Core.Behav.propEntry t m, mt), lw,
                                     links := st.links ++ [lrec I l k mid "propagated" now m.size] }

/-- A calculus configuration with its bookkeeping, as a format-2 configuration (`rs` maps the
calculus's request ids to format 2's). -/
def toConf (I : Info) (c : Core.Behav.Cfg) (metas : List PMeta) (b : Book) (rs : List (Nat × Nat) := [])
    (created : List Nat := []) (rcs : List (String × Nat) := []) (lq : LQIds := []) : Conf :=
  let I := I.withKeys c.machines
  let msgOf (m : Core.Behav.Msg) (idt : Nat × Nat) : Msg :=
    { id := idt.1, event := I.event m.event, payload := payloadValue I m.payload, size := m.size, sentAt := idt.2,
      target := m.target.map I.addr, sender := m.sender.map I.addr }
  { time := c.time,
    -- format 2's machines: the instances laid out at the start, then the keyed instances in
    -- creation order
    machines := ((c.machines.zipIdx).filterMap fun (ms, m) =>
        if Elab.isKeyed (I.beh m) then none else some (I.key m, toMachine I m ms)) ++
      created.filterMap fun m => (c.machines[m]?).map fun ms => (I.key m, toMachine I m ms),
    insts := insts I c.machines,
    pending := (c.pending.zip metas).map fun (e, mt) => toEntry I e mt,
    resources := resourcesOf I c.world rs, routeCounters := rcs, streams := b.counts,
    -- the link queues, in creation order, with format 2's message ids and sending times
    lqueues := c.world.links.map fun ((l, k), q) =>
      let (it, ws) := lq.get l k
      (((I.input.links.getD l default).id, keyStr I k),
        { inTransfer := q.inTransfer.map fun m => msgOf m (it.getD (0, 0)),
          waiting := (q.waiting.zipIdx).map fun (m, j) => msgOf m (ws.getD j (0, 0)),
          lastDelivery := q.last }),
    -- format 2's `active`: the windowed resource faults acting, in fault order
    active := (I.env.faults.zipIdx).filterMap fun (f, k) =>
      if f.window.isSome && c.world.active.contains k then some f.id else none }

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
  | .emit _ _ pl _ | .timer _ _ _ pl | .request _ _ _ _ _ _ _ pl => pl.filterMap fun (_, v) => match v with
    | .str src => some src
    | _ => none
  | .send _ size pl _ _ _ => (match size with | .expr src => [src] | _ => []) ++ pl.filterMap fun (_, v) =>
    match v with
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
  resources : List ResRecord := []
  rs : List (Nat × Nat) := []
  /-- The keyed instances created so far, in creation order, and format 2's route counters. -/
  created : List Nat := []
  rcs : List (String × Nat) := []
  /-- The head as the step's record shows it (with its routes, when the step decided them). -/
  head : Option Entry := none
  /-- The step's link records, and the message ids of the link queues after it. -/
  links : List LinkRec := []
  lq : LQIds

inductive SR where
  | ok (o : Out)
  /-- A failed step: its kind, its message, and the head as its record shows it (`none`: as
  queued). -/
  | fail (kind : Kind2) (msg : String) (head : Option Entry := none)

/-- The state of the recording of one winner's effects. -/
structure ESt where
  own : Core.Behav.MState
  sets : List SetRecord := []
  emits : List EmitRecord := []
  outs : List (CEntry × PMeta) := []
  seq : Nat
  book : Book
  draws : List Draw := []
  ops : List (Nat × Core.Behav.WOp) := []
  /-- The outcomes of the sends still to record, and the messages sent so far. -/
  plan : List LOut := []
  sends : List SMeta := []

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

/-- The messages of one send, one per receiver, recorded (WG-5683): format 2 numbers each message
(`m.id = seq`), then the entry its send creates (propagated or started); a propagated message draws
its latency (`latency:{link}`) here, in effect order. `none`: the send fails. -/
def sendsRec (I : Info) (L : Core.Behav.Link) (l : Nat) (msg : Core.Behav.Msg) (time : Nat) :
    List (Option Nat × Option Nat) → ESt → Option ESt
  | [], st => some st
  | _ :: rest, st =>
    match st.plan with
    | [] => none
    | .f :: _ => none
    | o :: plan =>
      let mid := st.seq
      let er : EmitRecord :=
        { event := I.event msg.event, time := (↑time : Rat), seq := mid, payload := payloadValue I msg.payload }
      let st := { st with plan, emits := st.emits ++ [er] }
      match o with
      | .q => sendsRec I L l msg time rest { st with seq := mid + 1, sends := st.sends ++ [({ mid := mid, eseq := 0, lat := 0 } : SMeta)] }
      | .s => sendsRec I L l msg time rest { st with seq := mid + 2, sends := st.sends ++ [({ mid := mid, eseq := mid + 1, lat := 0 } : SMeta)] }
      | _ =>
        let (v, book, drs) := drawWB (Core.Behav.linkSite l, L.latency) st.book
        sendsRec I L l msg time rest
          { st with seq := mid + 2, book := book, draws := st.draws ++ drs,
                    sends := st.sends ++ [({ mid := mid, eseq := mid + 1, lat := v } : SMeta)] }

/-- Format 2's message for a size that is not an integer in `[0, 2^40)` (`sizeOf`). -/
def sizeText (I : Info) (ev : Nat) (v : Core.Behav.Val) : String :=
  let got := match toValue v with
    | .num x => Json.write (.num x)
    | w => w.typeName
  s!"Size of emit \"{I.event ev}\" must be an integer in [0, 2^40), got {got}."

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
    let sampled := leff matches .sample ..
    let st := if sampled then drawRec sys b0 m ti j st else st
    match eff, (match leff with | .sample name _ => Effect.set name none | l => l) with
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
        let er : EmitRecord := { event := I.event ev, time := (↑(time + after) : Rat), seq := st.seq, payload := payloadValue I vs }
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
        let er : EmitRecord := { event := I.event ev, time := (↑(time + after) : Rat), seq := st.seq, payload := payloadValue I vs }
        next { st with outs := st.outs.filter (fun p => p.1.timer != some n) ++ [(ent, mt)], seq := st.seq + 1,
                       emits := st.emits ++ [er] }
    | .cancel n, _ => next { st with outs := st.outs.filter (fun p => p.1.timer != some n) }
    | .request ri ci units kind thenEv refused demand site pl, _ =>
      match Core.Behav.evalPayload cx pl with
      | .error err => .error (j, err)
      | .ok vs => next { st with ops := st.ops ++ [(m, .req ri ci units kind { thenEv, refused, payload := vs, demand, site })] }
    | .release ri ci units, _ => next { st with ops := st.ops ++ [(m, .release ri ci units)] }
    | .send ev l fan rp sz chk pl, _ =>
      -- a send over a link (Format2.lean:1513-1549): its size (a draw at a draw site), its
      -- payload, its target, then one message per receiver
      let st := drawRec sys b0 m ti j st
      match Core.Behav.sizeOfE cx ev chk sz with
      | .error err => .error (j, err)
      | .ok size =>
        match Core.Behav.evalPayload cx pl with
        | .error err => .error (j, err)
        | .ok vs =>
          match Core.Behav.replyTo rp e with
          | .error err => .error (j, err)
          | .ok tg =>
            match sys.links[l]? with
            | none => next st
            | some L =>
              let msg : Core.Behav.Msg := { event := ev, payload := vs, size, target := tg, sender := some m }
              match sendsRec I L l msg time (Core.Behav.receiversOf L (fan || L.fanout) c0.machines msg) st with
              | none => .error (j, .timeBound)
              | some st => next st
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
when it addresses another behaviour. The instances are the live machines of `b` in `ms0`; a route
decided for the entry picks one of them. -/
def addressedM (I : Info) (ms0 : List Core.Behav.MState) (mt0 : PMeta) (e : CEntry) (j : Nat)
    (b : BehaviorIn) : Option (List Nat) :=
  let all := (List.range (Elab.instCount b)).map (Elab.machineOf I.behs j)
  let ms := all.filter fun m => (ms0[m]?.map (·.live)).getD false
  match mt0.target with
  | some a =>
    if a.behavior == b.id then
      some (ms.filter fun m => Json.write (I.inst m) == Json.write a.inst)
    else none
  | none =>
    match (e.routes.getD []).find? (fun r => all.contains r.2) with
    | some r => some [r.2]
    | none => some ms

/-- The route draws of delivering `e` from `c` (`Exec.drawsW` of `routeHoles`), with format 2's
records of them (`drawNext` from `route:{event}:{behavior}`). -/
def routeDrawsRec (sys : Core.Behav.Sys) (c : Core.Behav.Cfg) (e : CEntry) (b : Book) :
    List Nat × Book × List Draw :=
  (Core.Behav.routeHoles sys c e).foldl (fun (vs, bk, drs) h =>
    let (v, bk') := Core.Behav.Exec.drawW h bk
    let name := bk.siteName h.1
    let drew := match h.2 with
      | .fixed _ => false
      | d => d.wf
    let drs := match bk.seed with
      | some seed => if drew then drs ++ [{ stream := name, index := bk.count name,
                                            value := Random.draw seed name (bk.count name) }] else drs
      | none => drs
    (vs ++ [v], bk', drs)) ([], b, [])

/-- Format 2's route counters after the routes of an entry of event `ev` are decided from machine
states `ms`: each round-robin route whose behaviour has an instance counts one more. -/
def bumpCounters (I : Info) (sys : Core.Behav.Sys) (ms : List Core.Behav.MState) (ev : Nat)
    (rcs : List (String × Nat)) : List (String × Nat) :=
  (sys.routesOf ev).foldl (fun rcs (i, r) =>
    match r.by_ with
    | .roundRobin =>
      if (Core.Behav.instsOf ms r.group).isEmpty then rcs
      else
        let rin := (I.routes.getD i (0, default)).2
        bump rcs s!"{rin.event}:{rin.behavior}"
    | _ => rcs) rcs

/-- **One step, recorded.** From configuration `c` (sorted, its head `e` with bookkeeping `mt0`),
under `mask`, with book `b`: the records of the step and the queue after it, or the kind and the
format-2 message of the failure. -/
def stepRecWith (I : Info) (sys : Core.Behav.Sys) (mask : List Bool) (c : Core.Behav.Cfg) (metas : List PMeta)
    (seq taken : Nat) (b : Book) (dsOv : Option (List Nat)) (next : Option Core.Behav.Cfg := none)
    (rs : List (Nat × Nat) := []) (created : List Nat := []) (rcs : List (String × Nat) := [])
    (rvOv : Option (List Nat) := none) (lq : LQIds := []) : SR :=
  let I := I.withKeys c.machines
  match c.pending, metas with
  | e :: _, mt0 :: mrest =>
    if e.kind != .event then
      -- an entry of the world: its step, then settling (Format2.lean:2253-2280)
      let kind2 : Kind2 := match e.kind with
        | .serviceDone .. => .serviceDone
        | .faultEdge .. => .faultEdge
        | .linkDone .. => .linkDone
        | _ => .waitTimeout
      -- a fault edge records the fault and what it changes (Format2.lean:2204-2210)
      let frecs : List FaultRecord := match e.kind with
        | .faultEdge fi _ =>
          let name := match (sys.faults[fi]?).map (·.kind) with
            | some .setCapacity => "capacity"
            | some .setClassLimit => "limit"
            | some .collapse => "collapsed"
            | some .scaleDemand => "scaled"
            | _ => "replaced"
          [{ fault := ((I.env.faults[fi]?).map (·.id)).getD "", effect := .other name }]
        | _ => []
      let p := Core.Behav.worldStep sys (c.popW e) e
      match actsRec I sys e.time p.2 { pairs := c.pending.tail.zip mrest, seq, book := b, rs, lw := p.1, lq } with
      | .error msg => .fail kind2 msg
      | .ok ws => .ok { kind := kind2, pairs := ws.pairs, seq := ws.seq, book := ws.book, draws := ws.draws,
                        resources := ws.recs, rs := ws.rs, faults := frecs,
                        responsible := responsibleOf I.input "" [] frecs, created, rcs,
                        links := ws.links, lq := ws.lq }
    else
    let ev := I.event e.event
    let time := e.time
    let act := sys.active mask
    -- the routes, decided when the entry is first taken as head (Format2.lean:2283-2296)
    let (rv, b, rdraws) := routeDrawsRec sys c e b
    -- an exploration replays a label's own route draws
    let rv := rvOv.getD rv
    match Core.Behav.routeOf sys c e rv with
    | none => .fail .deliver "internal: the route draws do not fit"
    | some (.error (err, _)) => .fail .deliver (routeErrText I ev err)
    | some (.ok (c1, e1, _)) =>
    let I := I.withKeys c1.machines
    let created := created ++ (List.range c1.machines.length).filter fun m =>
      (c1.machines[m]?.map (·.live)).getD false && !((c.machines[m]?.map (·.live)).getD false)
    let rcs := if sys.toRoute e then bumpCounters I sys c.machines e.event rcs else rcs
    let mt0 : PMeta := if sys.toRoute e then
        { mt0 with routes := some ((e1.routes.getD []).map fun r => ((I.beh r.2).id, I.inst r.2)) }
      else mt0
    let att := c1.attemptsOf e.event + 1
    let tail := (c.pending.tail.zip mrest)
    let headE := toEntry I e mt0
    let payloadV := headE.payload
    let already := e.done.filterMap fun k => (I.env.faults[k]?).map (·.id)
    let drops := I.env.faults.filter (dropMatches ev att time)
    if act.any (fun p => p.2.hits [.drop, .lose] e.event att e.time) then
      let recs := drops.map fun f => { fault := f.id, effect := dropEffect f }
      .ok { kind := .drop, faults := recs, responsible := responsibleOf I.input ev [] recs, pairs := tail,
            seq, book := b, rs, draws := rdraws, created, rcs, head := some headE, lq }
    else
    match Core.Behav.delayFault act e1 att with
    | some (k, f) =>
      let fid := (I.env.faults[k]?.map (·.id)).getD ""
      let eff := (I.env.faults[k]?.map delayEffect).getD .delayed
      match Core.Behav.later e1 k f.by_ with
      | .error _ => .fail .delay "Value time exceeds 2^53." (some headE)
      | .ok cp =>
        let mt : PMeta := { mt0 with seq, copyOf := some (mt0.copyOf.getD mt0.seq) }
        let recs := [{ fault := fid, effect := eff }]
        .ok { kind := .delay, faults := recs, responsible := responsibleOf I.input ev [] recs,
              pairs := insertP tail (cp, mt), seq := seq + 1, book := b, rs, draws := rdraws, created, rcs,
              head := some headE, lq }
    | none =>
      let ds := dsOv.getD (Core.Behav.Exec.drawsOf sys mask c e rv b).1
      let R := sys.resolve ds
      let c0 := c1.popE e
      -- phase 1, behaviour by behaviour in input order, instance by instance
      let ph1 : Except String (List (Nat × Nat × List FaultRecord) × List Ignored2 × List FaultRecord) :=
        I.behs.zipIdx.foldlM (fun (ws, igs, recs) (bh, j) =>
          match addressedM I c1.machines mt0 e1 j bh with
          | none => .ok (ws, igs, recs)
          | some [] => .ok (ws, igs ++ [{ base := { behavior := bh.id, reason := .noTransition, considered := [] },
                                          inst := none }], recs)
          | some ms => ms.foldlM (fun (ws, igs, recs) m =>
              if h : m < R.sig.machines then
                let own := c0.machines.getD m { ctrl := 0, vars := [] }
                let state := (Elab.statesOf bh).getD own.ctrl ""
                match scanRec I R ⟨m, h⟩ c0 e own state ev time bh.transitions.zipIdx [] false false [] with
                | .error (ti, err) =>
                  let src := ((bh.transitions[ti]?).bind (·.guard)).toList
                  .error (msgOf I (toConf I c1 metas b rs created rcs lq) (I.key m) (I.inst m) payloadV time src (errText err))
                | .ok (some (ti, en), _, _, _, rs) => .ok (ws ++ [(m, ti, en)], igs, recs ++ rs ++ en)
                | .ok (none, considered, dis, gf, rs) =>
                  let reason := if dis then IgnoredReason.disabled else if gf then .guardFalse else .noTransition
                  .ok (ws, igs ++ [{ base := { behavior := bh.id, reason, considered }, inst := some (I.inst m) }], recs ++ rs)
              else .ok (ws, igs, recs)) (ws, igs, recs)) ([], [], [])
      match ph1 with
      | .error msg => .fail .deliver msg (some headE)
      | .ok (ws, ignored, recs) =>
        -- the calculus's settling of the step (its emits and sends in order, then the resources),
        -- whose sends' outcomes phase 2 records in effect order
        let calcR : Option (List Core.Behav.MState × Core.Behav.Emitted) :=
          match Core.Behav.winners R act c0 e1 with
          | .ok cws => (Core.Behav.phase2 R c0 e1 cws c1.machines).toOption
          | .error _ => none
        let (wacts, lw0) : List Core.Behav.Act × Core.Behav.World := match calcR with
          | some (cms, cbs) =>
            let r := Core.Behav.settleOut sys time cms (Core.Behav.inMachineOrder sys.sig.machines cbs) c0.world
            (r.2, r.1)
          | none => ([], c0.world)
        -- phase 2, winners in machine order, each from the start-of-step machine
        let ph2 : Except String (List Fired2 × List (Nat × Core.Behav.MState) × List (CEntry × PMeta) ×
            Nat × Book × List Draw × List (Nat × Core.Behav.WOp) × List LOut × List SMeta) :=
          ws.foldlM (fun (fired, mss, outs, seq, bk, drs, ops, pln, sds) (m, ti, _) =>
            if h : m < R.sig.machines then
              let bh := I.beh m
              match (R.trans ⟨m, h⟩)[ti]?, bh.transitions[ti]? with
              | some tr, some t =>
                let own := c0.machines.getD m { ctrl := 0, vars := [] }
                let fin := next.bind fun c' => (c'.machines[m]?).map (·.vars)
                match effRec I sys (me := ⟨m, h⟩) b c0 e mt0 bh t ti fin 0 tr.effects t.effects
                    { own, seq, book := bk, plan := pln, sends := sds } with
                | .error (j, err) =>
                  let view := toConf I { c1 with machines := c1.machines.set m own } metas b rs created rcs lq
                  .error (msgOf I view (I.key m) (I.inst m) payloadV time ((t.effects[j]?).map effSrcs |>.getD [])
                    (match err with
                     | .noRequester => s!"Effect replies to \"{ev}\", which has no requester."
                     | .size sev v => sizeText I sev v
                     | err => errText err))
                | .ok st =>
                  let f : Fired2 := { base := { behavior := bh.id, transition := t.id, source := t.source,
                                                target := t.target, guard := t.guard, sets := st.sets, emitted := st.emits },
                                      inst := I.inst m }
                  .ok (fired ++ [f], mss ++ [(m, { st.own with ctrl := tr.dst.val })], outs ++ st.outs,
                       st.seq, st.book, drs ++ st.draws, ops ++ st.ops, st.plan, st.sends)
              | _, _ => .error "internal: a winner without its transition"
            else .error "internal: a winner out of range") ([], [], [], seq, b, [], [], planOf wacts, [])
        match ph2 with
        | .error msg => .fail .deliver msg (some headE)
        | .ok (fired, _, outs, seq0, b0, drs0, _, _, sends) =>
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
          let faults := injectedOf mt0.src ++ recs
          -- settling the step's operations (Format2.lean:2173-2187)
          match actsRec I sys time wacts
              { pairs := kept, seq := seq0, book := b0, rs, emitted := outs, sends, lw := lw0, lq } with
          | .error msg => .fail .deliver msg (some headE)
          | .ok wst =>
          let pairs := wst.pairs
          let seq' := wst.seq
          let base : Out := { kind := .deliver, fired, ignored, faults, responsible := responsibleOf I.input ev fired faults,
                              draws := rdraws ++ drs0 ++ wst.draws, pairs, seq := seq', book := wst.book,
                              resources := wst.recs, rs := wst.rs, created, rcs, head := some headE,
                              links := wst.links, lq := wst.lq }
          -- a duplicate after a committed delivery
          match Core.Behav.dupFault act e1 att with
          | none => .ok base
          | some (k, f) =>
            match Core.Behav.later e1 k f.by_ with
            | .error _ => .fail .deliver "Value time exceeds 2^53." (some headE)
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
    (seq taken : Nat) (b : Book) (next : Option Core.Behav.Cfg := none) (rs : List (Nat × Nat) := [])
    (created : List Nat := []) (rcs : List (String × Nat) := []) (lq : LQIds := []) : SR :=
  stepRecWith I sys mask c metas seq taken b none next rs created rcs (lq := lq)

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
  -- the edges of the windowed resource faults, in fault order: the start, then the end
  let (q, n) := act.foldl (fun (q, n) (p : Nat × Core.Behav.Fault) =>
    let fid := (I.env.faults[p.1]?.map (·.id)).getD ""
    let edge (k t : Nat) (on : Bool) : CEntry × PMeta :=
      (Core.Behav.edgeEntry p.1 t on, { seq := k, sched := t, src := .fault fid, kind := .faultEdge fid on })
    if sys.edgeOk p.2 then
      match p.2.window with
      | some (a, some u) => (insertP (insertP q (edge n a true)) (edge (n + 1) u false), n + 2)
      | some (a, none) => (insertP q (edge n a true), n + 1)
      | none => (q, n)
    else (q, n)) (q, n)
  (q, n)

structure RunB where
  state : Core.Behav.State
  book : Book
  metas : List PMeta
  seq : Nat
  stepsRev : List Step2
  outcome : Outcome2
  /-- Format 2's id (sequence number) of each calculus request. -/
  rs : List (Nat × Nat) := []
  /-- The keyed instances created, in creation order, and format 2's route counters. -/
  created : List Nat := []
  rcs : List (String × Nat) := []
  /-- The message ids on the link queues. -/
  lq : LQIds := []

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
  let (kind, msg, h) := match stepRec I sys mask c r.metas r.seq taken r.book none r.rs r.created r.rcs r.lq with
    | .fail k msg h => (k, msg, h)
    | .ok _ => (.deliver, "internal: the calculus step failed where its record did not", none)
  let head := h.getD (headOf I c r.metas)
  { blankB I taken head kind (toConf I c r.metas r.book r.rs r.created r.rcs r.lq) with
      responsible := [head.event].filter (· != ""), error := some msg }

/-- The record of a committed step and the run's bookkeeping after it, or the record of an internal
error when the recorded step does not arrive at the configuration `Exec.step` committed. -/
def commitRec (I : Info) (sys : Core.Behav.Sys) (mask : List Bool) (c : Core.Behav.Cfg) (r : RunB)
    (s' : Core.Behav.State) :
    Except Step2 (Step2 × Book × List PMeta × Nat × List (Nat × Nat) × List Nat × List (String × Nat) × LQIds) :=
  let taken := r.stepsRev.length
  let head := headOf I c r.metas
  let internal (msg : String) : Step2 :=
    { blankB I taken head .deliver (toConf I c r.metas r.book r.rs r.created r.rcs r.lq) with error := some msg }
  match stepRec I sys mask c r.metas r.seq taken r.book s'.cfg r.rs r.created r.rcs r.lq, s' with
  | .ok o, .run _ c' =>
    if o.pairs.map (·.1) != c'.pending then .error (internal "internal: the recorded queue differs from the calculus step")
    else
      let metas := o.pairs.map (·.2)
      .ok ({ blankB I taken (o.head.getD head) o.kind (toConf I c' metas o.book o.rs o.created o.rcs o.lq) with
              fired := o.fired, ignored := o.ignored, faults := o.faults, responsible := o.responsible,
              draws := o.draws, resources := o.resources, links := o.links }, o.book, metas, o.seq, o.rs, o.created,
              o.rcs, o.lq)
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
      | .ok (rec_, book, metas, seq, rs, created, rcs, lq) =>
        { state := s', book, metas, seq, rs, created, rcs, lq, stepsRev := rec_ :: r.stepsRev,
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
    let kind := match (b.transitions[s.2.1]?).bind (·.effects[s.2.2.1]?) with
      | some (.sample ..) => "sample"
      | some (.send ..) => "size"
      | _ => "after"
    s!"{kind}:{b.id}:{tid}:{s.2.2.1}"

/-- The initial book of a format-2 run. -/
def bookOf (I : Info) (sys : Core.Behav.Sys) : Book :=
  { seed := I.input.scenario.seed, names := slotNames I sys, counts := [],
    sites := ((List.range sys.sig.machines).flatMap fun m =>
      let b := I.beh m
      b.transitions.zipIdx.flatMap fun (t, ti) =>
        (t.effects.zipIdx.filterMap fun (e, ei) => match e with
          | .request .use .. => some ((m, ti, ei), s!"demand:{b.id}:{t.id}:{ei}")
          | _ => none)) ++
      -- the random routes' streams (format 2's `route:{event}:{behavior}`)
      (I.routes.zipIdx.map fun ((_, r), i) => (Core.Behav.routeSite i, s!"route:{r.event}:{r.behavior}")) ++
      -- the links' latency streams (format 2's `latency:{link}`)
      I.input.links.zipIdx.map fun (l, i) => (Core.Behav.linkSite i, s!"latency:{l.id}") }

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
    steps := r.stepsRev.reverse, outcome := r.outcome,
    final := toConf I r.state.cfg r.metas r.book r.rs r.created r.rcs r.lq }

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
