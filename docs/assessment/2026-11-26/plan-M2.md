# M2 implementation plan: the typed behaviour calculus, `step_sound`, `successors_complete`

Reasoned from source (no Lean installed). File:line citations are to the tree as of 2026-11-27. The
golden analysis in section 3 was executed (Python over `tests/conformance/goldens`); the script is at
`scratchpad/assessment/scripts/snapshot_diff.py`.

## 0. Summary of the decisions

1. **The executable carrier must change; a well-formedness filter on today's step is not enough.**
   Every number a format-2 machine holds, every payload value and every expression result is a
   `Float` (`Value.num`, Value.lean:21; `Expr.eval`, Expr.lean:310-367). Lean's `Float` operations
   are opaque, so no theorem can relate `V2.step`'s guard `n < L` to `Int.lt`, even on inputs whose
   numbers are all integers. `step_sound` against an `Int` relation is therefore unprovable for
   `V2.step` as written, with or without a fragment hypothesis (review-M1 finding 10 says the same).
2. **Plan: elaborate, then run a proved scheduler.** A typed core calculus
   `Exegra.Core.Behav` (sorts `int` with a range, `bool`, `str`, `lit`; `Fin`-scoped references;
   explicit error state), its relation `Sys.lts`, an executable `Exec.step` and `Exec.successors`
   in the core, both proved against the relation. Format 2 then runs as
   `encode ∘ Exec.run ∘ elab`: an elaborator turns a `V2.Input` into a `Behav.Sys` (parsing guard
   strings once, type-checking, resolving names to indices, refusing non-integers). For inputs the
   elaborator accepts, the code the application runs *is* the proved scheduler, so `step_sound`
   is about that code, not about a copy beside it.
3. **Numbers: `Int`, no rationals and no fixed point in M2.** Only one of the 88 goldens uses a
   non-integer (`fixture/expression-showcase`: `0.1 + 0.2` and the untyped `7 / 2 = 3.5`), and no
   specification under `specs/` uses `/`, `%` or a decimal literal. Untyped `/` becomes
   exact-or-error (`inexact`), untyped results are bounded by `|x| ≤ 2^53 - 1` (error `overflow`),
   declared integer types keep their ranges and truncating division (docs/semantics.md:22-26).
   Rationals wait until a specification needs them (M8 already uses `Nat` pairs).
4. **Snapshot reads change none of the 88 goldens** (section 3): 18 phase-2 cross reads exist in
   12 goldens, but in no step does the read machine fire in the same step as the reader.
5. **Delete format 1 in M2; do not prove `lift_agrees`.** `lift_agrees` (Lift.lean:128-136) is a
   byte-level equality of two JSON traces from a `Float`-time interpreter and a `Nat`-time one; it
   needs facts such as `toNat (x + after) = toNat x + toNat after` on `Float`, which cannot be
   proved in Lean core. It is not "smaller", it is out of reach. Deletion is mechanical once the
   explorer and the temporal monitors run on the calculus; `tools/differential.js --lift`
   (differential.js:238-260) already supplies the migration evidence.
6. **Scope boundary, stated honestly.** M2's list (machines, events, guards, effects, timers,
   faults) is the fragment. Resources, links, workloads, keyed instances and routes are not in
   it; inputs using them keep running on the legacy `V2.step`, flagged in the trace and covered by
   no theorem, until a follow-up milestone (called M2b below) moves them into the calculus and
   deletes `Float` from `Value`. This must be written in `docs/foundations.md` section 5 and as an
   `unknown` of the new component.

## 1. Value and number domain of format 2 (question 1)

### 1.1 Where format 2 still uses `Float`

| Use | Where | Role |
|---|---|---|
| `Value.num (x : Float)` | Value.lean:21 | every machine variable, payload value, literal, expression result |
| Expression evaluation on doubles | Expr.lean:261-263 (`numOf`), 289-299 (`intResult`), 301-304 (`divIn`), 345-366; `Num.fmod` Number.lean:69 | guard and effect arithmetic, including the typed-integer path, which checks integer ranges *on a double* (`IntKind.holds`, Expr.lean:283-284) |
| Number tokens `Tok.num : Float` | Expr.lean (`primary`, `.num x`) | literals in guards and effects |
| `Decode.intIn` compares `Float`s | Format2.lean:267-272 | JSON boundary (times, durations, counts) |
| `resolve` converts `Nat → Float` | Format2.lean:1145 (`time`), 1153-1164 (resource signals), 1180, 1190 (counts) | values read by expressions |
| Aggregates `sum/min/max` on `Float` | Format2.lean:1130-1133, 1191-1196 | instance aggregates |
| `sample` effect stores `.num x.toFloat` | Format2.lean:1430 | random variable values |
| Emit records `time := atTime.toFloat` | Format2.lean:1459, 1520, 1542; `EmitRecord.time : Float` Trace.lean:87 | trace records |
| Resource answer payloads | Format2.lean:1672, 1690, 2236, 2250 | `waited`, `served` numbers |
| Workload payload counters/samples | Format2.lean:1835, 1838 | generated payloads |
| Instance identities `Value.num k.toFloat` | Format2.lean:2361; machine keys `Json.write inst` Format2.lean:1017-1020 | instance addressing |
| `Occurrence.exactly (n : Float)`, `n == k.toFloat` | Input.lean:65, 72; used by format 2 at Format2.lean:442-445, 2100 | fault occurrence |
| `Encode.n : Nat → Value := .num k.toFloat` | Format2.lean:2826 | output |
| `Json.parse` yields `Float` | Json.lean | input boundary |

Already exact: time and durations (`Nat`), distributions (`Dist`, Format2.lean:40-45), streams
(`UInt64`, Random.lean), resources (`Resource.lean`, `Nat`), workload rates (`Nat` pairs),
quantiles (`(num, den)`).

So the *semantic* uses of `Float` are machine variables, payloads and expression evaluation; the
rest is the JSON boundary or record encoding.

### 1.2 What replacing them with `Int` breaks

* **Goldens.** All 88 golden inputs are format 1 (`"version": 1`, verified), so a change to format 2
  alone breaks none of them until format 1 is deleted. Non-integer numbers occur in no golden input
  number and in one golden trace, `fixture/expression-showcase.trace.json` (`quo = 3.5`,
  `inexact = 0.30000000000000004`); its guard `inexact > 0.3` decides whether `ops-again` fires. Static
  typing additionally refuses `mixed := 1 == '1'` (same golden) and the whole `calc-machine`
  input shared by seven goldens, because it contains `text - 1` (calc-type) and the guard
  `total + 1` (calc-guard): `error-type`, `error-guard-not-boolean`, `error-unknown-reference-guard`,
  `error-unknown-reference-effect`, `error-division-by-zero`, `error-modulo-by-zero`,
  `payload-field-present`. Section 6 lists the fixture edits that keep five of them as traces.
* **Rust oracle.** `engine/exegra-engine/src/value.rs`, `expr.rs`, `v2.rs` use `f64`. Because every
  admitted value is an integer with `|x| ≤ 2^53 - 1`, `f64` computes `+ - *` exactly there, so the
  oracle keeps `f64` and adds three rules: refuse non-integer numbers in a version-2 input, report
  `inexact` for an untyped division with a remainder, report `overflow` for an untyped result
  outside `±(2^53 - 1)`. Static typing is not mirrored in Rust: the differential harness compares
  only inputs the Lean elaborator accepts and counts refusals separately.
* **`src/core/sim-input.js`.** No lowering change for integer specifications (it copies numbers,
  sim-input.js:385-490). Readiness should flag a non-integer number in a simulated behaviour
  (extend the existing `ready.number-bound` rule, docs/semantics.md:23) so the user sees it at
  `validate`, not only as an engine refusal.
* **Generators.** `tools/gen-engine-inputs.js` deliberately generates `0.5`, `2.25`, `1e21`,
  `9007199254740993` (lines 57, 59, 90, 242, 277, 335-353, 377). It needs an integer-only mode for
  agreement runs, and the fractional cases move to refusal tests.
* **Docs.** docs/semantics.md:20-26 ("Without a declared type a number is an IEEE double"),
  docs/simulation.md:35 and :146 (phase 2 reads the next configuration), the expression docs.

### 1.3 A smaller first step, and whether it is honest

*Keeping `V2.step` and adding a fragment well-formedness that rejects `Float` values* does not make
`step_sound` provable: `V2.step` still evaluates `n < L` with `Float.decLt` on opaque doubles. The
only way to prove something about today's step is to make the relation compute with the same
`Expr.eval` on `Value`; that is provable, but it is a theorem about scheduling modulo an
uninterpreted expression semantics, it gives `omega` nothing to work with, and calling it "the
format-2 step is a scheduler of the Int calculus" would be false.

The honest smaller step is the one adopted: an **integer fragment of format 2 that runs on the
proved executable**. It is honest under five conditions, each enforced in the plan:

1. every theorem carries the hypothesis `Elab.elab i = .ok sys` explicitly;
2. the application runs the proved executable for exactly those inputs (dispatch in
   `V2.runInput`), so there is no parallel copy;
3. errors are inside the fragment, as the explicit error state; the fragment is never defined by
   excluding runs that fail;
4. refusals are visible: an ill-typed or non-integer input is refused with a message; an input
   outside the fragment (resources, links, workloads) runs on the legacy path and its trace says
   so (`"semantics": "legacy"`), and no claim may cite an M2 theorem for it;
5. the remainder is listed in the specification (`unknowns`) and in docs/foundations.md section 5.

## 2. Step structure of format 2 and the relation (question 2)

### 2.1 What `V2.step` does, in order

`V2.step` (Format2.lean:2313-2323):

1. empty queue: `.idle`; head time after `stopAt`: `.stopped`;
2. deep copy of the configuration (fresh identities, `Conf.copy`, Format2.lean:2092), pop the head
   (the first entry; the queue is ordered by time with insertion order among equal times,
   `insertE` Format2.lean:1022-1025), set `time := head.time`;
3. `arrive` (workload instant creation, Format2.lean:2015-2026; out of fragment);
4. `stepHead` by entry kind (Format2.lean:2169-2305); for `.event`:
   1. routes decided when first taken as head (draws `route:` streams; out of fragment);
   2. `attempt := attempts[ev] + 1`;
   3. **drop**: if any active `drop-event`/`lose-event` matches (event, occurrence, window), the entry
      is dropped and every matching drop fault is recorded (2272-2277);
   4. **delay**: else the first matching `delay-event`/`retry-event` not yet applied to this entry
      (`delayedBy`, keyed by `seq`) re-queues a copy at `time + by` (2279-2290); time `≥ 2^53` fails;
   5. **phase 1** `chooseAll env cur head env.behaviors` (2296; 1290-1304): behaviours in input
      order, which is scenario order (sim-input.js:132); for each addressed instance in index
      order, the first transition in declaration order with matching state and event whose guard is
      true (`scan`, 1235-1258), reading `cur`, the start-of-step configuration (guards use
      `guardHolds env t cur …`, 1220-1228, 1251); `enable-transition`/`disable-transition` faults
      act here;
   6. **phase 2** `fireAll` (1559-1565): winners in phase-1 order; each winner's effects in order
      (`runEffects`, 1400-1547). Expressions are evaluated against `s.next`, the configuration being
      written (1415, 1441, 1467, 1497, 1502, 1529), so `resolve` (1138-1199) reads *other*
      machines' variables and states (`[b, name]`, 1167-1176) and instance aggregates (1182-1196)
      as earlier winners left them; resources are read from `start` (1150-1166). Emitted and timer
      entries are inserted into `s.next.pending` immediately; the machine moves to `to` after its
      effects (`fireOne`, 1549-1557);
   7. `finish`: resource settling, resource by resource in input order (1735-1742; out of fragment);
   8. `afterDeliver`: closed-client replies (2163-2167; out of fragment);
   9. `duplicateAfter`: a matching `duplicate-event` not yet applied queues a copy `by` later
      (2122-2140);
   10. any error in 5-7 returns `.failed rec` carrying the pre-step configuration (2299-2300).
5. Draw order in a step: arrival draws first (`withDraws`, 2308-2311), route draws, then effect draws
   in effect order, then settling draws.

Faults: `V2.Env.faults` is the scenario's fault set (Format2.lean:868-872); there is no format-2
explorer (WG-4741; Explore.lean imports only `Exegra.Semantics`).

### 2.2 What the relation must allow so that this step is one scheduler of it

* **Delivery**: any pending entry whose time is minimal (the step takes index 0 of a time-sorted
  queue). The relation has no step limit (truncation belongs to the scheduler); `stopAt` is kept:
  no step when the minimal time exceeds it.
* **Faults, all-or-nothing** (modelchecking F6): a mask over the system's faults, chosen in the
  initial state and constant; the scenario's run is the all-true mask. Per-occurrence choice is a
  documented generalisation for later (it would need the explorer to enumerate it too).
* **Random draws**: any value in the support of the distribution (`fixed v`: `{v}`; `choice vs`:
  `vs`; `uniform lo hi`: `[lo, hi]`; `table pts`: `[first x, last x]`, an over-approximation, sound
  for safety). The SplitMix value is one of them (`uniformInt_ge/le`, Random.lean:74-82). Stream
  counters, `seq`, `nid` and `taken` are scheduler bookkeeping, erased by the abstraction.
* **Phase 2 order**: with snapshot reads (a winner reads its own machine as its earlier effects
  left it, every other machine and every aggregate from the start of the step) and writes confined
  to the winner's own machine and own timers, phase 2's machine result is independent of the order
  of winners (`phase2_perm`, M2.1). The relation therefore need not quantify over orders; it fixes
  the queue order of entries emitted in one step by machine index (= scenario order, = what the
  executable does). Because any minimal-time entry may be delivered, queue order among equal times
  adds no behaviour (optional theorem `pending_perm_bisim`, M2.3).
* **Errors**: a failing step goes to an explicit error state (review-M1 finding 6), never to "no
  successor". The error state has no successors; a safety claim is `Invariant (fun s => s.ok ∧ P s)`,
  so reaching it is a counterexample.

### 2.3 Lean signatures (the target after M2.3)

```lean
namespace Exegra.Core.Behav

inductive Ty where
  | int (lo hi : Int)    -- untyped numbers: ±(2^53 - 1); u8..i64 their declared ranges
  | bool | str | lit
  deriving DecidableEq, Repr

inductive Lit where      -- JSON constants without expressions (payload literals, `set` of an object)
  | null | int (v : Int) | bool (b : Bool) | str (s : String)
  | arr (xs : List Lit) | obj (fs : List (String × Lit))
inductive Val where | int (v : Int) | bool (b : Bool) | str (s : String) | lit (l : Lit)
inductive Err where
  | divZero | inexact | overflow | absentField (f : Nat) | fieldSort (f : Nat) | shape | timeBound
  deriving DecidableEq, Repr

structure MState where
  ctrl : Nat                 -- control state index (names in `Sig.states`)
  vars : List Val
  deriving DecidableEq

inductive Src where | scenario (k : Nat) | fault (f : Nat) | transition (m t : Nat) | timer (m name : Nat)
  deriving DecidableEq

structure Entry where
  time : Nat
  event : Nat
  payload : List (Nat × Val)
  src : Src
  target : Option Nat         -- machine index
  timer : Option (Nat × Nat)  -- (machine, timer name)
  delayed : List Nat          -- faults that already delayed this entry (replaces seq-keyed delayedBy)
  duplicated : List Nat
  deriving DecidableEq

structure Cfg where
  time : Nat
  machines : List MState
  pending : List Entry
  attempts : List Nat         -- per event index
  deriving DecidableEq

inductive State where
  | run (mask : List Bool) (c : Cfg)
  | err (mask : List Bool) (c : Cfg)   -- the configuration before the failed step
  deriving DecidableEq

def State.ok : State → Bool | .run .. => true | .err .. => false

/-- What identifies a transition: which minimal-time entry is delivered, and the outcomes of the
step's random draws in the order the step makes them. Fault choices are in the state (the mask). -/
structure Label where
  pick : Nat
  draws : List Nat
  deriving DecidableEq, Repr

structure Sys where
  sig : Sig
  trans : (m : Fin sig.machines) → List (Trans sig m)
  faults : List Fault
  init : List Bool → Cfg      -- initial configuration under a mask (injected entries of active faults)
  stopAt : Option Nat

/-- One delivery, declaratively: drop, delay, deliver (committed or failed), duplicate. -/
inductive Step (sys : Sys) (mask : List Bool) (c : Cfg) : Label → State → Prop
  -- constructors: drop, delay, delayTimeErr, deliverOk, deliverErr (each states the pick is a
  -- minimal-time index not after stopAt, and the draws are in their supports)

def Sys.lts (sys : Sys) : LTS State Label where
  init s := ∃ mask, mask.length = sys.faults.length ∧ s = .run mask (sys.init mask)
  step s l t := match s with
    | .run mask c => Step sys mask c l t
    | .err .. => False
```

The executable and the two theorems:

```lean
structure Book where          -- scheduler bookkeeping, erased by the relation
  seq : Nat
  seqs : List Nat             -- sequence number of each pending entry, positionally
  streams : List (String × Nat)
  taken : Nat

inductive XResult where
  | idle | stopped
  | committed (r : Rec) (s : State) (b : Book)
  | failed (r : Rec)

def Exec.step (sys : Sys) (s : State) (b : Book) : XResult      -- pick 0, mask fixed, SplitMix draws
def Exec.label (r : Rec) : Label := ⟨0, r.draws⟩
def State.Sorted (s : State) : Prop := s.cfg.pending.Pairwise (fun a b => a.time ≤ b.time)

theorem Exec.step_sound {sys : Sys} (hwf : sys.WF) {s s' : State} {b b' : Book} {r : Rec}
    (hs : s.Sorted) (h : Exec.step sys s b = .committed r s' b') :
    (Sys.lts sys).step s (Exec.label r) s'

theorem Exec.step_failed {sys : Sys} (hwf : sys.WF) {s : State} {b : Book} {r : Rec}
    (hs : s.Sorted) (h : Exec.step sys s b = .failed r) :
    (Sys.lts sys).step s (Exec.label r) (.err s.mask s.cfg)

theorem Exec.idle_deadlocked {sys : Sys} {s : State} {b : Book} (h : Exec.step sys s b = .idle) :
    (Sys.lts sys).Deadlocked s
theorem Exec.stopped_deadlocked {sys : Sys} {s : State} {b : Book} (h : Exec.step sys s b = .stopped) :
    (Sys.lts sys).Deadlocked s
theorem sorted_invariant (sys : Sys) (hwf : sys.WF) : (Sys.lts sys).Invariant State.Sorted

def Exec.successors (sys : Sys) (s : State) : List (Label × State)

theorem successors_complete {sys : Sys} {s t : State} {l : Label} :
    (Sys.lts sys).step s l t → (l, t) ∈ Exec.successors sys s
theorem successors_sound {sys : Sys} {s t : State} {l : Label} :
    (l, t) ∈ Exec.successors sys s → (Sys.lts sys).step s l t
```

Failed steps: `V2`'s `.failed rec` (pre-step configuration, Format2.lean:2299-2300) maps to
`.err mask c` with `c` the abstraction of that pre-step configuration; `.idle` and `.stopped` map to
deadlocked `.run` states (quiescent), distinguishable from `.err`; the step limit is not in the
relation (a truncated run is a prefix of a relation run). The abstraction `abs` drops `seq`, `nid`,
identities, streams and `taken`, so the calculus state is canonical by construction
(modelchecking C1: `attempts` and `delayed` are kept; `delayed` moves from a `seq`-keyed table into
the entry).

## 3. Snapshot reads against the goldens (question 3)

Method (`scripts/snapshot_diff.py`, run over all 88 goldens, 866 steps): for every step of every
trace, for every fired transition whose `set` right-hand sides or `emit` payload expressions read
`A.x` or `A.state` with `A` another behaviour, check whether an *earlier* entry of the same step's
`fired` list is `A` and changed `x` (a `sets` record with `before ≠ after`) or changed state
(`from ≠ to`). Only then does a start-of-step read give a different value. Guards already read the
start of the step (phase 1), so they cannot change.

Result:

* static phase-2 cross reads: 18, in 12 goldens, all in `exegra/`:
  `edit-with-disk-conflict(--none)`, `rejected-edit(--none)`, `source-edit-flow`, `visual-edit-flow`
  (`session-flow` reads `transaction-flow.revision`); `export-after-save`, `import-bundle`,
  `import-unparseable-bundle`, `live-session` (`toolbar-exchange-flow` reads
  `project-session-flow.projectName`); `generate-from-panel`, `live-session`
  (`realisation-generate-flow` reads `project-session-flow.textHash`, `.projectName`);
* steps where the reader and the read machine fire in the same step: **0** (checked in either
  order);
* **golden traces whose behaviour changes under snapshot reads: none.**

Format-2 inputs are not goldens. For them the definitive check is the M2.5 differential run of the
legacy `V2.step` against the new path on every version-2 input (generated, fixtures, lifted goldens),
which reports every divergence. The script generalises by adding instance identity (`fired[].instance`)
and aggregate references (`b.count.s`, `b.sum.x`, …, which also read `s.next` today,
Format2.lean:1182-1196).

## 4. Format 1: what depends on it, delete or prove `lift_agrees` (question 4)

Dependants:

* **Lean.** `Semantics.lean` (the definition); `Input.lean` (version-1 decoding; also defines
  `VariableIn`, `Occurrence`, shared by format 2); `Trace.lean` (`Machine`, `machineTys`, records,
  shared); `Properties.lean` (every run theorem is format 1; `runInput_terminates` is cited by
  `engine-run-terminates-proved`, spec.jsonc:17721); `Explore.lean` (format-1 only, imports
  `Exegra.Semantics`); `Prove.lean` (explore protocol, decodes version 1, Prove.lean:171-203);
  `Temporal.lean` (monitors over format-1 `Step`); `Lift.lean`; `Impl/Expr.lean`, `Impl/Semantics.lean`
  (the optimised format-1 engine), `Impl/Refinement.lean` (`runAnyValue_eq`, cited spec.jsonc:17987);
  `Api/Engine.lean` (`engine.explore`, `engine.temporal`); `Main.lean` (`explore`, `temporal`);
  `Format2.lean` imports `Exegra.Semantics` (line 1) for `Machine`, records, `compile`, `dedup`,
  `lookupNat`; `runAnyValue` dispatches by version (Format2.lean:3043-3050).
* **JavaScript.** `src/core/sim-input.js` (version 1 by default, `needsFormat2` 320-331, dispatch 194);
  `src/core/fault-model.js`:3, 192; `src/core/claims.js`:511; `src/core/replay.js`:67 (consumes the
  version-1 input shape); `tools/prove.js`, `src/core/proof-export.js`; `tools/differential.js`
  (`--lift`, version-1 generator), `tools/gen-engine-inputs.js`, `tools/record-goldens.js`,
  `tools/conformance.js`.
* **Rust.** `engine/exegra-engine/src/engine.rs`, `input.rs`, `trace.rs` (version 1).
* **Tests.** all 88 goldens; `tests/core/formal-semantics.test.js`, `conformance.test.js`,
  `formal-explore.test.js`.

`lift_agrees` is not the smaller option. Format 1 adds times in `Float` (`s.next.time + after`,
Semantics.lean:345; `head.time + d.delayBy`, :482), matches occurrences by `Float` equality
(Input.lean:72) and computes the step bound with `Float.ceil` (Semantics.lean:92). Any proof of
`lift_agrees` must equate these with `Nat` operations, which needs laws `Float` does not have in
Lean. It would additionally be a byte-level JSON equality over two interpreters of 584 and 3057
lines. Recommendation: **delete format 1** (M2.9) after the explorer and temporal monitors run on the
calculus (M2.6), using the `--lift` differential (already in CI) as the evidence that every
liftable golden keeps its content; keep `lift_agrees` pinned as `sorry` until its file is deleted.

## 5. Increments

Each increment compiles on Lean 4.35 core (no Mathlib), pins axioms of its theorems with
`#guard_msgs` (as a subset check of `propext, Classical.choice, Quot.sound`, review-M1 finding 11),
goes into `specs/exegra/spec.jsonc` through `node cli/exegra.js apply --project exegra --file ops.json`
(component `behaviour-calculus`, parent `semantic-core`, `implementation.modules` listing the new
files; `lean-theorem` claims with non-empty `about`), and is checked by `lake build` in
`.github/workflows/check.yml` plus `node cli/exegra.js validate` and `traceability`.

### M2.1: the instantaneous behaviour calculus and the snapshot theorem (Lean only)

**Files.** `formal/Exegra/Core/Behav.lean` (new), `formal/Exegra/Core/BehavExamples.lean` (new),
`formal/Exegra.lean` (two imports), `specs/exegra/spec.jsonc` (component + 2 claims).

**Definitions.** The M2.1 subset of section 2.3: `Ty`, `Lit`, `Val`, `Err`; a signature
```lean
structure Sig where
  machines : Nat
  vars : Fin machines → List Ty
  states : Fin machines → List String
```
`Fin`-scoped references and expressions
```lean
inductive Ref (S : Sig) (me : Fin S.machines) where
  | own (v : Fin (S.vars me).length)
  | other (m : Fin S.machines) (v : Fin (S.vars m).length)
  | state (m : Fin S.machines)
  | field (f : Nat) (τ : Ty)          -- payload field read at sort τ; absent or wrong sort: Err
  | time
inductive Expr (S : Sig) (me : Fin S.machines) where
  | val (v : Val) | ref (r : Ref S me) | un (op : UOp) (a : Expr S me) | bin (op : BOp) (a b : Expr S me)
```
`Expr.ty?` (static typing), `Expr.eval : Ctx → Expr S me → Except Err Val` (snapshot `c` for other
machines and time, `own` for the machine's own variables, short-circuit `&&`, `||`, `=>`; division by
zero, `inexact`, range overflow are `Err`, never a default value, review-M1 finding 10; a read past a
list's end is `Err.shape`, never `0`, review-M1 finding 2); `Effect` (`set`, `emit` with a fixed
`after`), `Trans` (`src dst on guard effects`), `Sys` (`sig`, `trans`, `init : Cfg`), `Entry`
(`time event payload`), `Cfg` (`time machines pending`), `State` (`run`/`err`), `Winner`, `choose`
(first enabled transition in declaration order, guards on the snapshot), `winners` (machines in index
order), `fireOne`, and
```lean
def phase2 (sys : Sys) (c : Cfg) (e : Entry) :
    List (Winner sys) → List MState → Except Err (List MState × List Entry)
  | [], ms => .ok (ms, [])
  | w :: ws, ms => do
    let own ← match ms[w.mach.val]? with | some o => pure o | none => throw .shape
    let (st, out) ← fireOne sys c e w own       -- reads `own` and the snapshot `c` only
    let (ms', outs) ← phase2 sys c e ws (ms.set w.mach.val st)
    pure (ms', out ++ outs)
def deliver (sys : Sys) (c : Cfg) (k : Nat) : Option (Except Err Cfg)   -- none: k not a minimal-time index
def Sys.lts (sys : Sys) : LTS State Nat where
  init s := s = .run sys.init
  step s k t := match s with
    | .run c => ∃ r, deliver sys c k = some r ∧ t = (match r with | .ok c' => .run c' | .error _ => .err c)
    | .err _ => False
```
For contrast, `phase2Next`: the same fold but evaluating other machines against `ms` (today's
format-1/format-2 rule).

**Main theorem (exact statement).**
```lean
theorem Exegra.Core.Behav.phase2_perm {sys : Sys} {c : Cfg} {e : Entry}
    {ws ws' : List (Winner sys)} (hp : ws.Perm ws') (hnd : (ws.map (·.mach)).Nodup) :
    (phase2 sys c e ws c.machines).toOption.map Prod.fst =
      (phase2 sys c e ws' c.machines).toOption.map Prod.fst
```
with the companion `phase2_perm_emitted` (the emitted lists are permutations when both succeed) and
the lemma it rests on, `phase2_eq_par`: for `Nodup` machines and `ms` agreeing with `c.machines` on
the winners, `phase2 sys c e ws ms` succeeds iff every `fireOne sys c e w (c.machines[w.mach])`
succeeds, and then sets each winner's machine to that result (proof: induction on `ws`, using
`List.getElem?_set_ne` and `List.set_comm` for distinct indices).

**Examples** (`BehavExamples.lean`): `f4AB`, `f4BA` (machines `a: x := 1` and `b: y := a.x` on
event `e` at time 0, listed in both orders);
```lean
theorem f4_ab_safe : (Sys.lts f4AB).Invariant (fun s => yAB s = some (.int 0))
theorem f4_ba_safe : (Sys.lts f4BA).Invariant (fun s => yBA s = some (.int 0))
theorem f4_next_reads_differ :
    yAfterNext f4AB = some (.int 1) ∧ yAfterNext f4BA = some (.int 0)
```
(`y…` is `none` on `.err`, so the invariants also exclude failure; the first two by
`safe_of_inductive` with the two reachable states, `deliver` evaluated by `decide`; the third by
`decide`, showing that today's next-configuration rule gives two verdicts.)

**Forced changes.** None outside Lean and the specification.

**Completion check.** `lake build` green with the pins for `phase2_perm`, `f4_ab_safe`, `f4_ba_safe`;
`validate` and `traceability` clean; the two claims read `proved`. If CI rounds are tight, land the
definitions and the three examples first (M2.1a), then `phase2_eq_par`/`phase2_perm` (M2.1b).

### M2.2: time, timers, faults, the full relation (Lean only)

**Files.** `Core/Behav.lean` (extended, or split into `Core/Behav/Syntax.lean`, `Eval.lean`,
`Step.lean`), `Core/BehavExamples.lean`, spec.

**Definitions.** Section 2.3 in full except draws: `Fault` (`FaultKind` drop, lose, delay, retry,
duplicate, enable, disable, inject; `Occ := any | exactly (n : Nat) | never`; windows), `Entry` with
`src target timer delayed duplicated`, `Cfg.attempts`, `State` with the mask, `Label` (with `draws`,
required to be `[]` until M2.8), effects `timer` and `cancel` (own machine only), `Trans.faultOnly`,
`Step` as an inductive with constructors `drop`, `delay`, `delayTimeErr`, `deliverOk`,
`deliverErr`, the `2^53` time bound as `Err.timeBound`, `Sys.WF` (decidable: well-typed guards and
right-hand sides, `init` shapes match `sig`, fault indices in range).

**Theorems.**
```lean
theorem lts_nonVacuous (sys : Sys) : (Sys.lts sys).NonVacuous
theorem err_deadlocked (sys : Sys) (m : List Bool) (c : Cfg) : (Sys.lts sys).Deadlocked (.err m c)
theorem mask_const {sys : Sys} {m : List Bool} {c : Cfg} {l : Label} {t : State}
    (h : (Sys.lts sys).step (.run m c) l t) : t.mask = m
theorem fits_invariant (sys : Sys) (hwf : sys.WF) : (Sys.lts sys).Invariant (Fits sys.sig)
theorem time_le_pending (sys : Sys) (hwf : sys.WF) :
    (Sys.lts sys).Invariant (fun s => ∀ e ∈ s.cfg.pending, s.cfg.time ≤ e.time)
theorem phase2_perm   -- restated for timers: machines equal, pending equal up to `List.Perm`
```
**Forced changes.** None outside Lean.

**Completion check.** `lake build` with pins; a timer example (`set` then `cancel` leaves no entry)
and a fault example (`drop` with `occurrence 2` drops exactly the second delivery) proved by
`decide`.

### M2.3: the executable scheduler, `step_sound`, `successors_complete` (Lean only)

**Files.** `Core/Behav/Exec.lean` (new), `Core/Search.lean` (add `Enum.toSys_sound` from a
soundness hypothesis), examples, spec.

**Definitions.** `Book`, `Rec` (fired, ignored with reasons and considered transitions, fault
records, sets with before/after, emitted, draws; what `V2.Step2` records, in calculus terms),
`XResult`, `Exec.step`, `Exec.inits` (one state per mask), `Exec.successors`, `Exec.enum : LTS.Enum
(Sys.lts sys)`, `Exec.gen := (Exec.enum sys).toSys`, a `Hashable State` instance (hand-written if
deriving fails on the nested `Lit`).

**Theorems.** `Exec.step_sound`, `Exec.step_failed`, `Exec.idle_deadlocked`,
`Exec.stopped_deadlocked`, `sorted_invariant`, `successors_complete`, `successors_sound` exactly as
in section 2.3, and
```lean
theorem Exec.covers (sys : Sys) : LTS.Covers (Exec.gen sys) (Sys.lts sys)
theorem Exec.sound (sys : Sys) : LTS.Sound (Exec.gen sys) (Sys.lts sys)
theorem Exec.holds_invariant {sys : Sys} {ok : State → Bool} {bound cap n : Nat}
    (h : Gen.search (Exec.gen sys) ok bound cap = .holds n) :
    (Sys.lts sys).Invariant (fun s => ok s = true)
theorem pending_perm_bisim   -- optional: Perm-related queues are bisimilar
```
Example: `ctr_le` in the behaviour calculus (counter with guard `n < L`, effect `n := n + 1`, emits
its own event), `∀ L ≥ 0`, by `safe_of_inductive` and `omega`.

**Forced changes.** None outside Lean.

**Completion check.** `lake build` with pins; `#guard` evaluations showing `Exec.step` on the F4
system commits with the same machines for both listings; `Exec.holds_invariant` instantiated on
`f4AB` by `decide` over `Gen.search`.

### M2.4: elaboration of format-2 input into the calculus (Lean; tests)

**Files.** `formal/Exegra/Elab.lean` (new; imports `Exegra.Format2` and `Exegra.Core.Behav.Exec`),
`formal/Exegra/Api/Engine.lean` (register `engine.elab`, returning the refusal or a summary),
`tests/core/formal-elab.test.js` (new), spec.

**Definitions.**
```lean
namespace Exegra.V2.Elab
inductive Refusal where
  | outOfFragment (what : String)   -- resources, links, workloads, keyed instances, routes,
                                     -- counted instances until M2.7, draws until M2.8
  | illTyped (msg : String)
  | notInteger (path : String)
def elab (i : V2.Input) : Except Refusal Core.Behav.Sys
def toConf (i : V2.Input) (sys : Core.Behav.Sys) (s : Core.Behav.State) (b : Core.Behav.Book) : V2.Conf
def toStep (i : V2.Input) (sys : Core.Behav.Sys) (r : Core.Behav.Rec) (b : Core.Behav.Book) : V2.Step2
```
Rules: guard and effect strings parsed once with `parseExpr` (Expr.lean); references resolved to
`Fin` indices (own variable, `b.x`, `b.state`, `event.f`, `time`); variable sorts from the initial
value (all 1221 golden variables have a number, string or boolean initial value and none changes sort
in any trace) or from `types`; `m.state == 'name'` compares the control-state name; integers taken
from JSON numbers with `Num.safeInteger?` (Number.lean:83) at the boundary; `Occurrence.exactly n`
with non-integer `n` becomes `Occ.never` (the legacy meaning); duplicate behaviour ids refused
(removes the MIRRORED double scan); `Float` survives only in JSON decoding and in `toConf`/`toStep`
encoding, which no theorem is about.

**Theorem.** `theorem elab_wf {i : V2.Input} {sys : Core.Behav.Sys} (h : elab i = .ok sys) : sys.WF`.

**Forced changes.** `tools/gen-engine-inputs.js` gains an integer-only version-2 mode.

**Completion check.** `formal-elab.test.js` runs `engine.elab` on every golden lifted with
`liftInput` (differential.js:210) and on the version-2 fixtures: all accepted except the expected
list (section 6), each with its expected refusal kind; the test prints the fragment coverage.

### M2.5: format 2 runs on the proved scheduler (Lean, Rust, JS, goldens)

**Files.** `formal/Exegra/Format2.lean` (`runInput` dispatch; legacy `traceOf` kept, flagged),
`formal/Exegra/Elab.lean` (`traceOfB`), `formal/Exegra/Impl/Semantics.lean` and
`Impl/Refinement.lean` (`runInputV2` follows the dispatch; `runAnyValue_eq` re-proved),
`formal/Main.lean` (`--legacy` flag for the differential), `engine/exegra-engine/src/v2.rs`,
`value.rs`, `expr.rs`, `tools/differential.js`, `tests/conformance/fixture/spec.jsonc` (edits of
section 6), re-recorded goldens of the edited fixture scenarios, `docs/semantics.md`,
`docs/simulation.md`, spec.

**Definitions and theorems.**
```lean
def V2.traceOfB (i : V2.Input) (sys : Core.Behav.Sys) : V2.Trace2   -- fold of Exec.step, encoded
def V2.runInput (i : V2.Input) : Except String String :=
  -- validate; elab: ok ⇒ traceOfB; outOfFragment ⇒ legacy traceOf with "semantics": "legacy";
  -- illTyped / notInteger ⇒ refusal
theorem V2.runB_reach {i : V2.Input} {sys : Core.Behav.Sys} (h : Elab.elab i = .ok sys) :
    ∀ s ∈ (Core.Behav.Exec.run sys i.scenario.stepLimit).states, (Core.Behav.Sys.lts sys).Reach s
theorem V2.runB_terminates   -- the format-2 counterpart of runInput_terminates
```
`V2.runB_reach` is the end-to-end statement: every configuration of the run the application
performs is a reachable state of the calculus; with `Exec.step_sound` it is "the format-2 step is
one scheduler of the relation" for every elaborated input.

**Rust.** Phase-2 reads of other machines and of aggregates from the start-of-step configuration;
the three numeric rules of section 1.2. **Differential.** Lean new path against Lean legacy path and
against Rust, on lifted goldens, fixtures and integer-only generated inputs; inputs Lean refuses as
ill-typed are counted, not compared.

**Completion check.** `node tools/differential.js --lift` and the legacy-versus-new run report zero
mismatches outside the expected list of section 6; `formal-semantics.test.js` green; claims
`behav-step-sound` and `format2-runs-proved-scheduler` read `proved`.

### M2.6: the explorer and temporal monitors on the calculus; the product-level F4 verdict

**Files.** `formal/Exegra/Prove.lean` (explore protocol over `Exec.gen`, claim expressions
elaborated against the `Sig`), `formal/Exegra/Temporal.lean` (monitors over `Rec`; the generic
monitor lemmas carry over), `Api/Engine.lean`, `tools/prove.js`, `src/core/proof-export.js`,
`tests/core/formal-explore.test.js`, `tests/fixtures/behaviour-order/spec.jsonc` (new), spec.

**Theorems.** `explore_holds_invariant` (a `holds` only on an empty frontier proves
`(Sys.lts sys).Invariant` with no bound, via `Exec.covers` and `invariant_of_search`),
`explore_cex_real` (via `Exec.sound` and `not_invariant_of_search`). Failed steps are `.err` states,
so `holds` of `s.ok ∧ P s` excludes them (closes modelchecking F7 / foundations F6 for this path); a
bound hit reports `incomplete` (closes F2 for this path).

**Forced changes.** The `prove` output text: "for every reachable configuration" only on an empty
frontier. Until M2.9, the JS side lifts version-1 inputs with `liftInput` before exploring.

**Completion check.** The fixture's two scenarios (`[a, b]` and `[b, a]`) give the same `prove`
verdict for `b.y == 0` (a test); the blinker of modelchecking F4 reports `incomplete`, not `holds`;
the `1/0 > 0` model of foundations F6 reports a counterexample ending in the error state.

### M2.7: counted instances, targets and replies

**Files.** `Core/Behav/*` (machines as instances of behaviour templates; `Entry.target`, sender for
`reply`; aggregates `count/sum/min/max` over the snapshot), `Elab.lean`, `v2.rs`, tests.
**Theorems.** All M2.2/M2.3 theorems re-checked; `phase2_perm` now over instances (aggregates read
the snapshot, so it still holds). **Completion check.** The version-2 fixtures with `instances.count`
elaborate and agree under the differential.

### M2.8: random draws as labels

**Files.** `Core/Behav/*` (`sample` effect, distributions on `after`, `Label.draws` constrained by
`support`), `Exec.lean` (SplitMix draws through `Random.lean`), `Elab.lean`, tests.
**Theorems.** `sample_mem_support` (from `uniformInt_ge/le`, Random.lean:74-82, and a new lemma for
`sampleTable`); `step_sound`, `successors_complete` re-proved with draws; the explorer enumerates
supports with a cap and answers `incomplete` beyond it (`successorsUpTo_eq` when not truncated).
**Completion check.** The seeded version-2 fixtures elaborate and agree; a two-outcome `choice`
example proved safe over both outcomes by `decide`.

### M2.9: delete format 1

**Files deleted.** `Semantics.lean`, `Properties.lean`, `Explore.lean` (old), `Lift.lean`,
`Impl/Expr.lean` and the format-1 half of `Impl/Semantics.lean`; version-1 decoding in `Input.lean`
(shared definitions such as `VariableIn`, `Machine`, records and `compile` move first into
`Format2.lean` or a `Shared.lean`, as a no-behaviour-change step); `engine.rs`, `input.rs`, `trace.rs`
version-1 paths in Rust; version-1 paths in `sim-input.js` (always version 2; scenarios with no
`timeUnit` use unit `tick`, which is `liftInput`'s choice and keeps every number), `needsFormat2`,
`fault-model.js`:192, `claims.js`:511 (test "declares workloads, seed or horizon" directly),
`replay.js` (read the version-2 input shape), the version-1 generator.
**Goldens.** `node tools/record-goldens.js --force`; all 88 become version-2 traces (a change of
shape only, justified by the `--lift` check of M2.5, which compares `strip(v2) = v1` on each).
**Spec.** `engine-run-terminates-proved` re-pointed to `V2.runB_terminates`; `runAnyValue_eq`
re-proved for the remaining dispatch; `call_engine_run_spec`'s docstring corrected (foundations
overclaim 1).
**Completion check.** `grep -r "Exegra.Semantics\|SimInput\|version 1" formal src engine` empty;
`lake build`, `npm test`, `npm run verify` green with only the expected violations.

### After M2 (M2b, a separate milestone to add to docs/foundations.md)

Resources, links, workloads, keyed instances and routes into the calculus (`Resource.lean` and
`Workload.lean` are already exact); delete the legacy `V2.step`; remove `Float` from `Value`
(JSON numbers as exact decimals, using `Num.ofDecimal`'s rational path, Number.lean:36-62).

## 6. Expected golden changes (each to be listed in the M2.5 and M2.9 commits)

| Golden | Change | Justification |
|---|---|---|
| all 88 | version-1 trace becomes version-2 trace (M2.9) | format 1 deleted; content checked equal by `strip` (`--lift`) |
| `fixture/expression-showcase` | input edited: `inexact := 0.1 + 0.2` removed (non-integer literal), `mixed := 1 == '1'` removed (ill-typed), `quo := a / b` (7/2, now `inexact`) changed to `(a - 1) / b`; trace re-recorded | the golden exercised `Float` behaviour that no longer exists; new goldens record `inexact`, `overflow` and refusal of decimals |
| `fixture/error-type`, `fixture/error-guard-not-boolean` | trace goldens replaced by refusal tests in `formal-elab.test.js` | `text - 1` and a guard `total + 1` are static type errors |
| `fixture/error-unknown-reference-guard`, `-effect`, `error-division-by-zero`, `error-modulo-by-zero`, `payload-field-present` | input re-recorded without `calc-type` and `calc-guard` (moved to a refusal-only behaviour); traces unchanged (`considered` lists only transitions on the delivered event) | the shared `calc-machine` would otherwise be refused as a whole |
| any golden, snapshot reads | none | section 3 |

## 7. Risks and open decisions

* Dependent `Fin`-indexed syntax can make `decide` slow and proofs fiddly; fallback: untyped indices
  plus a decidable `Sys.WF` and `Err.shape` on bad reads, with every theorem taking `sys.WF`
  (review-M1 finding 2's fallback). Decide in M2.1.
* `deriving DecidableEq`/`Hashable` for the nested `Lit` may need hand-written instances (pattern:
  Explore.lean:45-120).
* Static typing refuses inputs the legacy engines accept; the readiness rules in JavaScript should
  report the same errors at `validate` (M3 moves well-formedness to Lean anyway).
* Draw supports can be large (`uniform` up to `2^53` values); exploration of seeded scenarios stays
  bounded by a cap and says `incomplete`.
