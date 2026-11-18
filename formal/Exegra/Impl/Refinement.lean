import Exegra.Impl.Semantics

/-!
# The implementation refines the definition

For every input, the format-1 engine the application runs (`Exegra.Impl`, see
`Exegra/Impl/Semantics.lean`) returns exactly what the definition (`Exegra/Semantics.lean`)
returns. The theorems go up the structure of a run, one function at a time: a compiled
expression evaluates as its text does, a compiled transition is scanned and fired as the
transition is, so a step, a run, a trace and finally the whole entry point agree.

The top-level statements are `Impl.runAnyValue_eq` and `Impl.runAny_eq`. Each depends only on
Lean's standard axioms (checked at the end of this file), and the implementation uses no
`implemented_by`, `extern` or `csimp` of its own, so the code the compiler emits is the code
these theorems are about.
-/

namespace Exegra.Impl

/-! ## Expressions -/

theorem evalC_compile (src : String) (view : Configuration) (bid : String) (payload : Value)
    (time : Float) : evalC (compile src) view bid payload time = evalIn src view bid payload time := by
  unfold evalC evalIn
  cases compile src <;> simp [resolveFast_eq, evalFast_eq]

theorem valueOfC_ofOpt (x : Option Value) (view : Configuration) (bid : String) (payload : Value)
    (time : Float) (nid : Nat) :
    valueOfC (CVal.ofOpt x) view bid payload time nid = valueOf x view bid payload time nid := by
  rcases x with _ | ⟨_ | _ | _ | _ | src | _ | _⟩ <;> try rfl
  simp only [CVal.ofOpt, valueOfC, valueOf, Thunk.get, evalC_compile]

theorem guardHoldsC_compile (i : SimInput) (t : TransitionIn) (view : Configuration) (bid : String)
    (payload : Value) (time : Float) :
    guardHoldsC (compileTransition i t) view bid payload time = guardHolds t view bid payload time := by
  unfold guardHoldsC guardHolds compileTransition
  cases t.guard with
  | none => rfl
  | some g =>
    simp only [Option.map, Thunk.get, evalC_compile]
    rfl

/-! ## Phase 1 -/

/-- The compiled form of a scan result. -/
def liftScan (i : SimInput)
    (r : Option (TransitionIn × List FaultIn) × List String × Bool × Bool × List FaultRecord) :
    Option (CTransition × List FaultIn) × List String × Bool × Bool × List FaultRecord :=
  (r.1.map fun p => (compileTransition i p.1, p.2), r.2)

theorem scanC_compile (i : SimInput) (faults : List FaultIn) (cur : Configuration) (bid : String)
    (state : Option String) (event : String) (payload : Value) (time : Float)
    (ts : List TransitionIn) (considered : List String) (dis gf : Bool) (recs : List FaultRecord) :
    scanC faults cur bid state event payload time (ts.map (compileTransition i)) considered dis gf recs =
      (scan faults cur bid state event payload time ts considered dis gf recs).map (liftScan i) := by
  induction ts generalizing considered dis gf recs with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, scanC, scan, guardHoldsC_compile]
    have ht : (compileTransition i t).t = t := rfl
    simp only [ht]
    split
    · exact ih ..
    · split
      · exact ih ..
      · cases guardHolds t cur bid payload time with
        | error e => rfl
        | ok b =>
          cases b with
          | false => exact ih ..
          | true =>
            simp only
            split
            · exact ih ..
            · rfl

/-- The compiled form of a choice. -/
def liftChoice (i : SimInput) : Choice → CChoice
  | .win t => .win (compileTransition i t)
  | .ignore x => .ignore x

theorem chooseOneC_compile (i : SimInput) (faults : List FaultIn) (cur : Configuration)
    (bid : String) (ts : List TransitionIn) (event : String) (payload : Value) (time : Float) :
    chooseOneC faults cur bid (ts.map (compileTransition i)) event payload time =
      (chooseOne faults cur bid ts event payload time).map fun r => (liftChoice i r.1, r.2) := by
  simp only [chooseOneC, chooseOne, scanC_compile]
  generalize scan faults cur bid _ event payload time ts [] false false [] = q
  cases q with
  | error e => rfl
  | ok r =>
    obtain ⟨o, considered, dis, gf, recs⟩ := r
    cases o with
    | none => rfl
    | some p => rfl

/-- The compiled form of the winners of phase 1. -/
def liftWinners (i : SimInput) (ws : List (String × TransitionIn)) : List (String × CTransition) :=
  ws.map fun w => (w.1, compileTransition i w.2)

theorem chooseC_compile (i : SimInput) (faults : List FaultIn) (cur : Configuration)
    (event : String) (payload : Value) (time : Float) (bs : List (String × List TransitionIn)) :
    chooseC faults cur event payload time (bs.map fun b => (b.1, b.2.map (compileTransition i))) =
      (choose faults cur event payload time bs).map fun r => (liftWinners i r.1, r.2) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨bid, ts⟩ := b
    simp only [List.map_cons, chooseC, choose, chooseOneC_compile, ih]
    cases chooseOne faults cur bid ts event payload time with
    | error e => rfl
    | ok r =>
      obtain ⟨c, recs⟩ := r
      cases choose faults cur event payload time bs with
      | error e => rfl
      | ok q =>
        obtain ⟨ws, igs, fs⟩ := q
        cases c <;> rfl

/-! ## Phase 2 -/

theorem evalEntriesC_compile (view : Configuration) (bid : String) (payload : Value) (time : Float)
    (es acc : List (String × Value)) (nid : Nat) :
    evalEntriesC view bid payload time (es.map fun e => (e.1, CVal.ofOpt (some e.2))) acc nid =
      evalEntries view bid payload time es acc nid := by
  induction es generalizing acc nid with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨k, v⟩ := e
    simp only [List.map_cons, evalEntriesC, evalEntries, valueOfC_ofOpt]
    cases valueOf (some v) view bid payload time nid with
    | error _ => rfl
    | ok r => exact ih ..

theorem runEffectsC_compile (input : SimInput) (bid : String) (t : TransitionIn) (payload : Value)
    (time : Float) (effs : List Effect) (s : FireState) (sets : List SetRecord)
    (emits : List EmitRecord) :
    runEffectsC bid t payload time (effs.map (compileEffect input)) s sets emits =
      runEffects input bid t payload time effs s sets emits := by
  induction effs generalizing s sets emits with
  | nil => rfl
  | cons e effs ih =>
    cases e with
    | set varName to =>
      simp only [List.map_cons, compileEffect, runEffectsC, runEffects, valueOfC_ofOpt]
      cases s.next.machine? bid with
      | none => rfl
      | some m =>
        simp only
        cases objHas m.vars varName with
        | false =>
          rfl
        | true =>
          simp only [Bool.not_true]
          cases valueOf to s.next bid payload time s.nid with
          | error _ => rfl
          | ok r => exact ih ..
    | emit event after entries =>
      simp only [List.map_cons, compileEffect, runEffectsC, runEffects, evalEntriesC_compile]
      split
      · rfl
      · cases evalEntries s.next bid payload time entries [] s.nid with
        | error _ => rfl
        | ok r => exact ih ..
    | malformed => rfl

theorem fireOneC_compile (input : SimInput) (bid : String) (t : TransitionIn) (payload : Value)
    (time : Float) (s : FireState) :
    fireOneC bid (compileTransition input t) payload time s = fireOne input bid t payload time s := by
  unfold fireOneC fireOne
  simp only [compileTransition, runEffectsC_compile]
  rfl

theorem fireAllC_compile (input : SimInput) (payload : Value) (time : Float)
    (ws : List (String × TransitionIn)) (s : FireState) :
    fireAllC payload time (liftWinners input ws) s = fireAll input payload time ws s := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    obtain ⟨bid, t⟩ := w
    simp only [liftWinners, List.map_cons, fireAllC, fireAll, fireOneC_compile] at ih ⊢
    cases fireOne input bid t payload time s with
    | error _ => rfl
    | ok r =>
      simp only [ih]
      rfl

theorem deliverC_compile (env : Env) (cur : Configuration) (head : Pending) (s : FireState) :
    deliverC (compileEnv env) cur head s = deliver env cur head s := by
  unfold deliverC deliver compileEnv
  simp only [chooseC_compile]
  cases choose env.faults cur head.event head.payload head.time env.behaviors with
  | error _ => rfl
  | ok r =>
    obtain ⟨ws, igs, recs⟩ := r
    simp only [Except.map, fireAllC_compile]
    rfl

/-! ## Steps and runs -/

theorem stepHeadC_compile (env : Env) (c : Config) (next : Configuration) (nid : Nat)
    (head : Pending) : stepHeadC (compileEnv env) c next nid head = stepHead env c next nid head := by
  unfold stepHeadC stepHead
  have he : (compileEnv env).env = env := rfl
  simp only [deliverC_compile, he]
  cases dropsOf env c head with
  | cons d ds => rfl
  | nil =>
    simp only
    cases delayOf? env c head with
    | some d => rfl
    | none =>
      simp only
      cases deliver env c.conf head { next, seq := c.seq, nid } with
      | error _ => rfl
      | ok _ => rfl

/-- **One step of the implementation is one step of the definition.** -/
theorem stepC_compile (env : Env) (c : Config) : stepC (compileEnv env) c = step env c := by
  unfold stepC step
  cases c.conf.pending with
  | nil => rfl
  | cons _ _ =>
    simp only
    cases (c.conf.copy c.nid).1.pending with
    | nil => rfl
    | cons head rest => exact stepHeadC_compile ..

theorem advanceC_compile (env : Env) (bound : Nat) (r : Run) :
    advanceC (compileEnv env) bound r r.stepsRev.length =
      (advance env bound r, (advance env bound r).stepsRev.length) := by
  unfold advanceC advance
  rw [stepC_compile]
  cases step env r.config <;> simp

theorem loopC_compile (env : Env) (bound fuel : Nat) (r : Run) :
    loopC (compileEnv env) bound fuel r r.stepsRev.length = loop env bound fuel r := by
  induction fuel generalizing r with
  | zero => rfl
  | succ fuel ih =>
    simp only [loopC, loop, advanceC_compile]
    split
    · exact ih _
    · rfl

theorem runEnvC_compile (env : Env) (bound : Nat) (c0 : Config) :
    runEnvC (compileEnv env) bound c0 = runEnv env bound c0 :=
  loopC_compile env bound bound (startRun c0)

theorem traceOfC_eq (i : SimInput) : traceOfC i = traceOf i := by
  unfold traceOfC traceOf
  simp only [runEnvC_compile]

theorem runInputC_eq (i : SimInput) : runInputC i = runInput i := by
  unfold runInputC runInput
  simp only [traceOfC_eq]
  rfl

/-! ## The entry points -/

/-- **The format-1 implementation equals the definition** on every parsed input. -/
theorem runValue_eq (v : Value) : Impl.runValue v = Exegra.runValue v := by
  unfold Impl.runValue Exegra.runValue
  simp only [runInputC_eq, JsonOut.write'_eq]
  rfl

theorem runInputV2_eq (i : V2.Input) : runInputV2 i = V2.runInput i := by
  unfold runInputV2 V2.runInput
  simp only [JsonOut.write'_eq]

/-- **The engine the application runs equals the definition** on every parsed input, format 1
and format 2. -/
theorem runAnyValue_eq (v : Value) : Impl.runAnyValue v = Exegra.runAnyValue v := by
  unfold Impl.runAnyValue Exegra.runAnyValue
  simp only [runValue_eq, runInputV2_eq]
  rfl

/-- **The engine the application runs equals the definition** on every input text. -/
theorem runAny_eq (text : String) : Impl.runAny text = Exegra.runAny text := by
  unfold Impl.runAny Exegra.runAny
  simp only [runAnyValue_eq]

/-! ## Axiom check -/

/-- info: 'Exegra.Impl.runAnyValue_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runAnyValue_eq

/-- info: 'Exegra.Impl.runAny_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runAny_eq

/-- info: 'Exegra.Impl.stepC_compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stepC_compile

end Exegra.Impl
