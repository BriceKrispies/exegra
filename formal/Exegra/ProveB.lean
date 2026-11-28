import Exegra.Format2B
import Exegra.Core.BehavCheck

/-
`exegra prove` on the behaviour calculus (plan-M2, M2.6; the task's criteria 18, 24 and 25).

The explore and temporal protocols (`exegra-lean explore`, `exegra-lean temporal`, `engine.explore`,
`engine.temporal`) read a version-2 engine input, elaborate it (`Elab.elab`) and search the
calculus's transition system `Sys.lts` through its complete and sound enumeration `Exec.gen`:

* **What is varied**: the delivery order among the entries of minimal time, the fault mask (every
  subset of the scenario's faults, chosen once per run) and the outcome of every draw, up to a cap
  on the size of a support (`drawCap`). A system with a support above the cap is reported
  `incomplete`, never `holds`.
* **What is counted**: the states the search visits are calculus states, which hold no sequence
  numbers, identities or stream counters.
* An input the elaborator refuses is not explored: one outside the fragment is reported `not
  covered by the calculus`, an ill-typed or non-integer one with the refusal's message.

**State invariants** (`claimInvB`): a claim expression over `time`, `<behavior>.state` and
`<behavior>.<variable>` (a behaviour with one instance), evaluated as `checkTrace` evaluates it on
a configuration. `exploreB sys P` searches for `s.ok ∧ P s`: `explore_holds_invariant` makes a
`holds` (returned only on an empty frontier) an invariant of `Sys.lts` with no bound,
`explore_cex_real` makes a counterexample a real run, replayed through the successor function to a
state where the property fails (an error state violates every invariant).

**Temporal claims** (`tcheckB`): `never m`, `precedes a b` and `eventually occurs expr`, with
matchers `event e` (a step that delivers `e`: neither dropped nor delayed, committed or failed) and
`transition t` (a committed step in which `t` fires). The search runs over pairs of a calculus
state and a monitor; `holds` is returned only on an empty frontier, and a run cut off by the bound
leaves the frontier non-empty, so it is `incomplete`, never judged on its last state.
-/

namespace Exegra.V2.ProveB

open Exegra
open Exegra.V2.B

abbrev State := Core.Behav.State

/-- The largest support whose every value the explorer tries. -/
def drawCap : Nat := 1000

/-- The size of a support, without building it. -/
def supportSize : Core.Behav.Dist → Nat
  | .fixed _ => 1
  | .choice vs => vs.length
  | .uniform lo hi => hi + 1 - lo
  | .table pts => match pts.map Prod.snd with
    | [] => 0
    | x :: xs => xs.foldl max x + 1 - xs.foldl min x

/-! ### State invariants of claims -/

/-- Reference resolution of a claim expression in a calculus configuration (`configResolver` of
`src/core/claims.js`): `time`, `<behavior>.state`, `<behavior>.<variable>`. -/
def claimResolveB (I : Info) (c : Core.Behav.Cfg) : List String → Value
  | ["time"] => .num (↑c.time : Rat)
  | [b, name] =>
    match I.behs.findIdx? (·.id == b) with
    | none => .undef
    | some j =>
      let bh := I.behs.getD j default
      if Elab.instCount bh ≠ 1 then .undef
      else match c.machines[Elab.machineOf I.behs j 0]? with
        | none => .undef
        | some ms =>
          if name == "state" then .str ((Elab.statesOf bh).getD ms.ctrl "")
          else match bh.variables.findIdx? (·.name == name) with
            | some k => (ms.vars[k]?.map toValue).getD .undef
            | none => .undef
  | _ => .undef

/-- **The evaluator of claim expressions** (the one `exegra prove` and the live view share): the
expression evaluated as a behaviour's expressions are (`Exegra.eval`, untyped), with references
resolved by `resolve`. `true` or `false`, or why it is neither: a parse failure, an evaluation error
(a division by zero, an unknown reference), or a value that is not a Boolean. A claim treats each of
these as a violation. -/
def claimTruthAst (resolve : List String → Value) (ast : Ast) : Except String Bool :=
  match eval resolve TyEnv.untyped ast with
  | .ok (.bool b) => .ok b
  | .ok v => .error s!"The expression evaluates to {match v with
      | .num _ => "number" | .str _ => "string" | .null => "null" | .undef => "undefined"
      | .arr _ _ => "object" | .obj _ _ => "object" | .bool _ => "boolean"}, not a boolean."
  | .error e => .error e

def claimTruth (resolve : List String → Value) (src : String) : Except String Bool :=
  match parseExpr src with
  | .ok ast => claimTruthAst resolve ast
  | .error e => .error s!"The expression does not parse: {e}"

/-- A claim's state invariant as a predicate on calculus states: the expression evaluates to
`true` in the state's configuration (`claimTruth`); anything else (false, not a Boolean, an error, a
parse failure) is a violation. -/
def claimInvB (I : Info) (src : String) : State → Bool :=
  match parseExpr src with
  | .ok ast => fun s => match claimTruthAst (claimResolveB I s.cfg) ast with
    | .ok true => true
    | _ => false
  | .error _ => fun _ => false

/-- Is the expression `true`, `false`, or neither in a configuration? -/
def evalB (I : Info) (src : String) (c : Core.Behav.Cfg) : Option Bool :=
  (claimTruth (claimResolveB I c) src).toOption

/-- Reference resolution in a configuration of a trace (`config` of a step: `time`, and per machine
key its `state` and `vars`), as `configResolver` of `src/core/claims.js` reads it. -/
def fieldOf? (v : Value) (k : String) : Option Value :=
  match v with
  | .obj _ fs => objGet? fs k
  | _ => none

def configResolve (cfg : Value) : List String → Value
  | ["time"] => (fieldOf? cfg "time").getD .undef
  | [b, x] =>
    match fieldOf? cfg "machines" >>= (fieldOf? · b) with
    | none => .undef
    | some m =>
      if x == "state" then (fieldOf? m "state").getD .undef
      else ((fieldOf? m "vars").bind (fieldOf? · x)).getD .undef
  | _ => .undef

/-! ### Elaborated inputs -/

/-- A decoded, validated and elaborated input, or why it is not explored. -/
def prepare (v : Value) : Except String (Input × Core.Behav.Sys × Info) := do
  let root ← match v with
    | .obj _ fs => pure fs
    | _ => throw "an engine input must be an object"
  match objGet? root "version" with
  | some (.num x) => if x == 2 then pure () else throw "exegra prove takes a version-2 engine input"
  | _ => throw "exegra prove takes a version-2 engine input"
  let i ← Decode.input root
  validate i
  match Elab.«elab» i with
  | .ok sys => pure (i, sys, mkInfo i)
  | .error (.outOfFragment what) =>
    throw s!"not covered by the calculus: the scenario uses {what}, which the behaviour calculus does not cover, so nothing is claimed about it"
  | .error r => throw r.message

/-- Whether a support is above the cap, so that the explorer would not try every draw. -/
def capped (sys : Core.Behav.Sys) : Bool := sys.dists.any fun d => drawCap < supportSize d

/-- The explorer's result for one invariant. -/
def exploreClaim (sys : Core.Behav.Sys) (I : Info) (src : String) (bound cap : Nat) : Gen.Result State :=
  if capped sys then .incomplete .cap 0
  else Core.Behav.exploreB sys (claimInvB I src) bound cap

/-! ### Replaying a path with the format-2 records -/

/-- The bookkeeping of the entries of `pend`, taken from `pairs` (each entry matched once). -/
def alignMetas (pend : List CEntry) (pairs : List (CEntry × PMeta)) : List PMeta :=
  (pend.foldl (fun (acc : List PMeta × List (CEntry × PMeta)) e =>
    match acc.2.findIdx? (·.1 == e) with
    | some k => (acc.1 ++ [(acc.2.getD k (e, default)).2], acc.2.eraseIdx k)
    | none => (acc.1 ++ [default], acc.2)) ([], pairs)).1

/-- The replay of a search path: each pick is a successor of `Exec.successors`; its step is
recorded by `stepRec` with the delivered entry moved to the front and the path's draws. -/
def replay (I : Info) (sys : Core.Behav.Sys) (created : List Nat := []) (rcs : List (String × Nat) := []) :
    Nat → State → List PMeta → Nat → List Nat → List Step2 × List Nat
  | _, _, _, _, [] => ([], [])
  | idx, s, metas, seq, k :: ks =>
    match s, (Core.Behav.Exec.successors sys s)[k]? with
    | .run mask c, some (l, t) =>
      match c.pending.idxOf? l.entry with
      | none => ([], [])
      | some pos =>
        let pairs := c.pending.zip metas
        let front := (pairs.getD pos (l.entry, default)) :: pairs.eraseIdx pos
        let c' := { c with pending := front.map (·.1) }
        let metas' := front.map (·.2)
        let head := headOf I c' metas'
        match stepRecWith I sys mask c' metas' seq idx {} (some l.draws) (created := created) (rcs := rcs)
            (rvOv := some (l.wdraws.take (sys.nR c' l.entry))), t with
        | .ok o, .run _ ct =>
          let ms := alignMetas ct.pending o.pairs
          let r : Step2 := { blankB I idx (o.head.getD head) o.kind (toConf I ct ms {} (created := o.created) (rcs := o.rcs)) with
            fired := o.fired, ignored := o.ignored, faults := o.faults, responsible := o.responsible }
          let (rest, ps) := replay I sys o.created o.rcs (idx + 1) t ms o.seq ks
          (r :: rest, pos :: ps)
        | .fail kind msg h, _ =>
          let head := h.getD head
          ([{ blankB I idx head kind (toConf I c metas {} (created := created) (rcs := rcs)) with
               responsible := [head.event], error := some msg }], [pos])
        | _, _ => ([], [])
    | _, _ => ([], [])

/-! ### Temporal claims -/

inductive Matcher where
  | event (id : String)
  | transition (id : String)
  deriving DecidableEq, Repr

inductive Form where
  | never (m : Matcher)
  | precedes (first thn : Matcher)
  | eventually (occurs : Option Matcher) (expr : Option String)
  deriving DecidableEq, Repr

/-- What a step of the calculus shows to a matcher: the event it delivers (a delivery that is
neither dropped nor delayed, committed or failed) and the transitions that fire in it (committed). -/
structure Occ where
  delivered : Option String
  fired : List String

/-- The occurrences of the step labelled `l` from configuration `c` to state `t`. -/
def occOf (I : Info) (sys : Core.Behav.Sys) (mask : List Bool) (c : Core.Behav.Cfg) (l : Core.Behav.Label)
    (t : State) : Occ :=
  let e := l.entry
  let act := sys.active mask
  let att := c.attemptsOf e.event + 1
  if act.any (fun p => p.2.hits [.drop, .lose] e.event att e.time) then { delivered := none, fired := [] }
  else match Core.Behav.delayFault act e att with
    | some _ => { delivered := none, fired := [] }
    | none =>
      let fired := match t with
        | .run _ _ =>
          match Core.Behav.winners (sys.resolve l.draws) act (c.popE e) e with
          | .ok ws => ws.map fun w => (((I.beh w.mach.val).transitions[w.idx.val]?).map (·.id)).getD ""
          | .error _ => []
        | .err _ _ => []
      { delivered := some (I.event e.event), fired }

def Matcher.hit : Matcher → Occ → Bool
  | .event e, o => o.delivered == some e
  | .transition tr, o => o.fired.contains tr

/-- The monitor of a run: whether the watched occurrence (`first` of `precedes`, `occurs` of
`eventually`) has been seen, and whether the run already violates the form. -/
structure Mon where
  seen : Bool := false
  viol : Bool := false
  deriving DecidableEq, Hashable, Repr

def Form.step : Form → Mon → Occ → Mon
  | .never m, mo, o => { mo with viol := mo.viol || m.hit o }
  | .precedes a b, mo, o =>
    let sameOk := match a, b with
      | .event _, .transition _ => true
      | _, _ => false
    let seenNow := mo.seen || (sameOk && a.hit o)
    { seen := mo.seen || a.hit o, viol := mo.viol || (b.hit o && !seenNow) }
  | .eventually occ _, mo, o => { mo with seen := mo.seen || (occ.map (·.hit o)).getD false }

/-- The product of the calculus with a monitor. -/
abbrev TNode := State × Mon

def tsucc (I : Info) (sys : Core.Behav.Sys) (f : Form) (n : TNode) : List TNode :=
  match n.1 with
  | .run mask c => (Core.Behav.Exec.successors sys n.1).map fun (l, t) => (t, f.step n.2 (occOf I sys mask c l t))
  | .err _ _ => []

def tsysB (I : Info) (sys : Core.Behav.Sys) (f : Form) : Gen.Sys TNode where
  init := (Core.Behav.Exec.inits sys).map fun s => (s, {})
  width n := (tsucc I sys f n).length
  next n k := (tsucc I sys f n)[k]?
  lt := by
    intro n k t h
    exact (List.getElem?_eq_some_iff.mp h).1

/-- A product node that violates the form: a violation of `never` or `precedes`; for `eventually`,
a state with no successor (the run ends) where the occurrence was not seen or the expression is
not true in the final configuration. -/
def bad (I : Info) (sys : Core.Behav.Sys) (f : Form) (n : TNode) : Bool :=
  match f with
  | .never _ | .precedes _ _ => n.2.viol
  | .eventually occ expr =>
    (tsucc I sys f n).isEmpty &&
      ((occ.isSome && !n.2.seen) || (expr.map (fun x => evalB I x n.1.cfg != some true)).getD false)

/-- The temporal check: the search of the product for a violating node. -/
def tcheckB (I : Info) (sys : Core.Behav.Sys) (f : Form) (bound cap : Nat) : Gen.Result TNode :=
  if capped sys then .incomplete .cap 0
  else Gen.search (tsysB I sys f) (fun n => !bad I sys f n) bound cap

/-- **A `holds` of the temporal check covers every reachable product node**, at any depth: no run
of the calculus reaches a node that violates the form (for `eventually`, no complete run ends
without the occurrence or with the expression not true). -/
theorem tcheckB_holds {I : Info} {sys : Core.Behav.Sys} {f : Form} {bound cap n : Nat}
    (h : tcheckB I sys f bound cap = .holds n) :
    ∀ d nd, Gen.Reach (tsysB I sys f) d nd → bad I sys f nd = false := by
  unfold tcheckB at h
  split at h
  · cases h
  · intro d nd hr
    have := Gen.search_sound h d nd hr
    simpa using this

/-- **A counterexample of the temporal check is real**: a path of the product from an initial
node that replays to a violating node. -/
theorem tcheckB_cex {I : Info} {sys : Core.Behav.Sys} {f : Form} {bound cap : Nat} {p : Gen.Path TNode}
    (h : tcheckB I sys f bound cap = .counterexample p) :
    p.root ∈ (tsysB I sys f).init ∧ ∃ t, Gen.greplay (tsysB I sys f) p.root p.picks = some t ∧
      bad I sys f t = true := by
  unfold tcheckB at h
  split at h
  · cases h
  · obtain ⟨hr, -, t, ht, hb⟩ := Gen.search_counterexample_real h
    exact ⟨hr, t, ht, by simpa using hb⟩

/-! ### The protocols -/

def fieldOr (o : List (String × Value)) (k : String) : Value := (objGet? o k).getD .undef

def activeIds (I : Info) (mask : List Bool) : List String :=
  ((I.env.faults.zip mask).filter (·.2)).map (·.1.id)

open Encode in
/-- A counterexample as `exegra prove` shows it: the fault mask, the search picks, the positions
of the delivered entries in their queues, the active faults, the initial configuration and the
replayed steps. -/
def cexJson (I : Info) (sys : Core.Behav.Sys) (id : String) (root : State) (picks : List Nat) : Value :=
  let mask := root.mask
  let (pairs, seq) := initPairs I sys mask
  let metas := alignMetas root.cfg.pending pairs
  let (steps, positions) := replay I sys [] [] 0 root metas seq picks
  o [("id", s id), ("verdict", s "counterexample"),
     ("mask", a (mask.map Value.bool)), ("picks", a (picks.map nat)), ("positions", a (positions.map nat)),
     ("faults", strings (activeIds I mask)),
     ("initial", configuration I.input (toConf I root.cfg metas {})),
     ("steps", a (steps.map (Encode.step I.input)))]

open Encode in
def verdictJson (I : Info) (sys : Core.Behav.Sys) (id : String) (r : Gen.Result State) : Value :=
  match r with
  | .holds k => o [("id", s id), ("verdict", s "holds"), ("states", nat k)]
  | .incomplete why k => o [("id", s id), ("verdict", s "incomplete"), ("reason", s why.name), ("states", nat k)]
  | .counterexample p => cexJson I sys id p.root p.picks

open Encode in
def tverdictJson (I : Info) (sys : Core.Behav.Sys) (id : String) (r : Gen.Result TNode) : Value :=
  match r with
  | .holds k => o [("id", s id), ("verdict", s "holds"), ("states", nat k)]
  | .incomplete why k => o [("id", s id), ("verdict", s "incomplete"), ("reason", s why.name), ("states", nat k)]
  | .counterexample p => cexJson I sys id p.root.1 p.picks

def natField (root : List (String × Value)) (k what : String) : Except String Nat :=
  match fieldOr root k with
  | .num x => pure x.floor.toNat
  | _ => throw s!"{what}: \"{k}\" must be a number"

/-- `{input, claims: [{id, expr}], bound, maxStates}`: the explorer's result per claim. -/
def exploreValue (req : Value) : Except String String := do
  let root ← match req with
    | .obj _ fs => pure fs
    | _ => throw "explore: the request must be an object"
  let (_, sys, I) ← prepare (fieldOr root "input")
  let bound ← natField root "bound" "explore"
  let cap ← natField root "maxStates" "explore"
  let claims ← match fieldOr root "claims" with
    | .arr _ xs => xs.mapM fun c => match c with
      | .obj _ fs => match fieldOr fs "id", fieldOr fs "expr" with
        | .str id, .str e => pure (id, e)
        | _, _ => throw "explore: a claim needs \"id\" and \"expr\" strings"
      | _ => throw "explore: a claim must be an object"
    | _ => throw "explore: \"claims\" must be an array"
  let results := claims.map fun (id, e) => verdictJson I sys id (exploreClaim sys I e bound cap)
  pure (Json.write (Encode.o [("faults", Encode.strings (I.env.faults.map (·.id))), ("results", Encode.a results)]))

def decodeMatcher (v : Value) : Except String Matcher :=
  match v with
  | .obj _ fs =>
    match fieldOr fs "event", fieldOr fs "transition" with
    | .str e, _ => pure (.event e)
    | _, .str t => pure (.transition t)
    | _, _ => throw "temporal: a matcher needs an \"event\" or a \"transition\" string"
  | _ => throw "temporal: a matcher must be an object"

def decodeForm (v : Value) : Except String Form :=
  match v with
  | .obj _ fs =>
    match fieldOr fs "method" with
    | .str "never" => do pure (.never (← decodeMatcher (fieldOr fs "occurs")))
    | .str "precedes" => do pure (.precedes (← decodeMatcher (fieldOr fs "first")) (← decodeMatcher (fieldOr fs "then")))
    | .str "eventually" => do
      let o ← match fieldOr fs "occurs" with
        | .undef => pure none
        | m => do pure (some (← decodeMatcher m))
      let e ← match fieldOr fs "expr" with
        | .undef => pure none
        | .str x => pure (some x)
        | _ => throw "temporal: \"expr\" must be a string"
      pure (.eventually o e)
    | _ => throw "temporal: \"method\" must be never, precedes or eventually"
  | _ => throw "temporal: a claim form must be an object"

/-- `{input, claims: [{id, evaluate}], bound, maxStates}`: the temporal check's result per claim. -/
def temporalValue (req : Value) : Except String String := do
  let root ← match req with
    | .obj _ fs => pure fs
    | _ => throw "temporal: the request must be an object"
  let (_, sys, I) ← prepare (fieldOr root "input")
  let bound ← natField root "bound" "temporal"
  let cap ← natField root "maxStates" "temporal"
  let claims ← match fieldOr root "claims" with
    | .arr _ xs => xs.mapM fun c => match c with
      | .obj _ fs => match fieldOr fs "id" with
        | .str id => do pure (id, ← decodeForm (fieldOr fs "evaluate"))
        | _ => throw "temporal: a claim needs an \"id\" string"
      | _ => throw "temporal: a claim must be an object"
    | _ => throw "temporal: \"claims\" must be an array"
  let results := claims.map fun (id, f) => tverdictJson I sys id (tcheckB I sys f bound cap)
  pure (Json.write (Encode.o [("faults", Encode.strings (I.env.faults.map (·.id))), ("results", Encode.a results)]))

def runExplore (text : String) : Except String String := do exploreValue (← Json.parse text)
def runTemporal (text : String) : Except String String := do temporalValue (← Json.parse text)

/-! ### The live view's claim checks, by the same evaluator -/

/-- What a step of a trace shows to a matcher (`occurrences` of `src/core/claims.js`): the event it
delivers when its kind is `deliver`, and the transitions that fired in it. -/
def occOfStep (step : Value) : Occ :=
  let delivered := match fieldOf? step "kind", fieldOf? step "event" >>= (fieldOf? · "id") with
    | some (.str "deliver"), some (.str e) => some e
    | _, _ => none
  let fired := match fieldOf? step "fired" with
    | some (.arr _ fs) => fs.filterMap fun f => match fieldOf? f "transition" with
      | some (.str t) => some t
      | _ => none
    | _ => []
  { delivered, fired }

open Encode in
/-- `{expr, configs: [config]}`: per configuration `{value: b}` or `{error: message}` (`claimTruth`). -/
def exprOnConfigsValue (args : Value) : Except String String := do
  let src ← match fieldOf? args "expr" with
    | some (.str x) => pure x
    | _ => throw "claims.exprOnConfigs: \"expr\" must be a string"
  let cfgs ← match fieldOf? args "configs" with
    | some (.arr _ xs) => pure xs
    | _ => throw "claims.exprOnConfigs: \"configs\" must be an array"
  let out := match parseExpr src with
    | .error e => cfgs.map fun _ => o [("error", s s!"The expression does not parse: {e}")]
    | .ok ast => cfgs.map fun c => match claimTruthAst (configResolve c) ast with
      | .ok b => o [("value", .bool b)]
      | .error e => o [("error", s e)]
  pure (Json.write (a out))

/-- `{matcher, steps: [step]}`: whether each step has the occurrence (`Matcher.hit`). -/
def matcherHitsValue (args : Value) : Except String String := do
  let m ← decodeMatcher ((fieldOf? args "matcher").getD .undef)
  let steps ← match fieldOf? args "steps" with
    | some (.arr _ xs) => pure xs
    | _ => throw "claims.matcherHits: \"steps\" must be an array"
  pure (Json.write (Encode.a (steps.map fun st => .bool (m.hit (occOfStep st)))))

/-- `{form, steps: [step]}`: the monitor of a temporal form (`Form.step`) over the steps: the index of
the first step after which the run violates the form (or `null`), and whether the watched occurrence
was seen. -/
def formViolationValue (args : Value) : Except String String := do
  let f ← decodeForm ((fieldOf? args "form").getD .undef)
  let steps ← match fieldOf? args "steps" with
    | some (.arr _ xs) => pure xs
    | _ => throw "claims.formViolation: \"steps\" must be an array"
  let (mo, at_) := steps.zipIdx.foldl (fun (acc : Mon × Option Nat) (st, i) =>
    let mo' := f.step acc.1 (occOfStep st)
    (mo', match acc.2 with | some k => some k | none => if mo'.viol then some i else none)) ({}, none)
  pure (Json.write (Encode.o [("violatedAt", match at_ with | some k => Encode.nat k | none => .null), ("seen", .bool mo.seen)]))

/-! ### What a generated proof file states -/

/-- The elaborated system and the names of an engine input text, if it elaborates. -/
def prepareText (text : String) : Option (Core.Behav.Sys × Info) :=
  match Json.parse text >>= prepare with
  | .ok (_, sys, I) => some (sys, I)
  | .error _ => none

/-- The verdict of an invariant claim on an engine input text, as a generated proof file states
it: `("holds", n)`, `("incomplete:bound", n)`, `("incomplete:cap", n)` or `("counterexample", picks)`. -/
def verdictOf (text src : String) (bound cap : Nat) : String × List Nat :=
  match prepareText text with
  | none => ("refused", [])
  | some (sys, I) => match exploreClaim sys I src bound cap with
    | .holds n => ("holds", [n])
    | .incomplete why n => ("incomplete:" ++ why.name, [n])
    | .counterexample p => ("counterexample", p.picks)

/-- **A `holds` verdict of a generated proof file proves the invariant** of the calculus system of
the input text, with no bound. -/
theorem verdictOf_holds {text src : String} {bound cap : Nat} {ns : List Nat}
    (h : verdictOf text src bound cap = ("holds", ns)) :
    ∃ sys I, prepareText text = some (sys, I) ∧
      (Core.Behav.Sys.lts sys).Invariant (fun s => s.ok = true ∧ claimInvB I src s = true) := by
  unfold verdictOf at h
  cases hp : prepareText text with
  | none => simp [hp] at h
  | some v =>
    obtain ⟨sys, I⟩ := v
    refine ⟨sys, I, rfl, ?_⟩
    cases hr : exploreClaim sys I src bound cap with
    | holds k =>
      unfold exploreClaim at hr
      split at hr
      · cases hr
      · exact Core.Behav.explore_holds_invariant hr
    | incomplete why k => cases why <;> simp [hp, hr, Gen.Reason.name] at h
    | counterexample q => simp [hp, hr] at h

/-- The verdict of a temporal claim, as a generated proof file states it. -/
def tverdictOf (text : String) (f : Form) (bound cap : Nat) : String × List Nat :=
  match prepareText text with
  | none => ("refused", [])
  | some (sys, I) => match tcheckB I sys f bound cap with
    | .holds n => ("holds", [n])
    | .incomplete why n => ("incomplete:" ++ why.name, [n])
    | .counterexample p => ("counterexample", p.picks)

end Exegra.V2.ProveB

/-- info: 'Exegra.V2.ProveB.verdictOf_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.V2.ProveB.verdictOf_holds

/-- info: 'Exegra.V2.ProveB.tcheckB_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Exegra.V2.ProveB.tcheckB_holds
