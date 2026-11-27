# Foundations: from executable specification to established guarantees

This document records the design for evolving Exegra into an environment that establishes eight classes of
guarantee from one mathematical foundation, with Lean as the only authority on semantics. It is derived from an
adversarial assessment of the repository on 2026-11-26 by eight independent reviews (mathematical foundations,
Lean proof architecture, model checking, compositional reasoning, refinement and conformance, simulation science,
architecture and scalability, epistemic integrity), followed by a cross-challenge round. The reviews, with their
counterexamples, are kept in [assessment/2026-11-26/](assessment/2026-11-26/), and the executable demonstrations in
[assessment/2026-11-26/demos/](assessment/2026-11-26/demos/).

The order of the milestones below comes from dependency: a milestone is placed where the guarantees after it cannot
be stated, or cannot be trusted, without it.

## 1. What the assessment established

Each item was demonstrated through the code (D), or argued from source (A). Lean was not run during the
assessment; Lean-side items are therefore A unless they were later checked in CI.

**A specification has no mathematical meaning yet.** Its behaviour is whatever a chain of programs computes: the
JSONC text, the JavaScript model, `src/core/sim-input.js` (JavaScript, with no Lean counterpart), engine-input JSON,
and a deterministic Lean interpreter. Every Lean theorem about runs is a theorem about engine input, not about the
specification (A). There are two unrelated behaviour semantics, format 1 (Float time) and format 2 (Nat time,
resources, random streams); their agreement theorem `Lift.lift_agrees` is `sorry`, and every run theorem is about
format 1 (A).

**Lean is the authority for less than the documentation implies.** Model derivation, the semantic hash and the
engine are in Lean. Well-formedness (75+ error rules in `validate.js` against 16 codes in `Model.lean`), every claim
verdict except `proved`, the specification-to-engine lowering, admission and the statistical tests are JavaScript
only (D). The Rust engine mirrors the Lean definition deliberately (`MIRRORED`), so their agreement is not
independent evidence (A).

**Status inflation is possible through real code paths (all D):**

| Defect | Where | Demonstration |
|---|---|---|
| A skipped test is recorded as a pass | `countPassingTests`, `cli/commands.js`; `mergeRecordedResults` keeps an older pass when the test skips | `demos/skipped-test-counts-as-pass.test.js` |
| Recorded results carry no provenance: no tree stamp, specification hash or source hash; a stale pass keeps a claim supported, and a Lean record keeps a claim proved after its proof is replaced | `specs/exegra/evidence/results.json`, `leanTheoremChecks` | epistemics D2, D3; architecture |
| The `lean-theorem` checker accepts a theorem that proves nothing about its subject (it checks only that each `about` constant occurs in the type) | `src/core/claims.js` (`evaluateLeanTheorem`) | lean L1 |
| Nothing relates a claim's statement to what is checked: "P = NP" with an unrelated passing test is supported | `src/core/claims.js` | `demos/status-inflation.mjs` |
| Claim assumptions are inert: two claims citing contradictory assumptions are both verified, and 154 claims cite an assumption the specification itself records as false | `claims.js` copies `assumptions` and nothing reads them | `demos/composition-assumptions.mjs` |
| A metric claim reads `model-holds` while 40% of runs violate the bound (underpowered runs are left out for every class, since `openStarted` defaults to true and is never computed) | `src/core/metric-claims.js`, `metric-stats.js` | `demos/metric-demo1.mjs` |
| The `refines` check accepts an implementation that ignores `release` and holds a lease forever | `src/core/refinement.js` (ignored steps are not compared) | `demos/refines-ignore.mjs` |
| Live replay reports no divergence for a dropped field, a silently calibrated wrong value and a refused external event | `src/core/replay.js` | `demos/replay-blind.mjs` |
| `verify` and `admit` accept downgrades: a fall to not-evaluated, a removed verified claim, a new counterexample of a claim whose id is on the expected-violated list | `cli/admit.js`, `--expect-violated` | epistemics D8 |
| The explorer drops orderings whose step fails, so a model whose only transition has the guard `1/0>0` is "Verified by Lean" | `formal/Exegra/Explore.lean` `succOf` | foundations F6, modelchecking F7 |
| The bounded invariant search reports `holds` when runs were cut off at the step limit; `eventually` is judged on the final configuration of a run truncated at `maxSteps` | `Explore.lean`, `Temporal.lean` | modelchecking F2, F4 |
| `core-independent-of-ui` is verified on the declared graph, but `src/core/derivation-cache.js` writes files with `node:fs` | relationships are hand-declared | epistemics D5 |
| `pages-site-published-from-main` states more than the workflow does (a queued run superseded by a newer push is cancelled), and its test passes for five workflow edits that break publishing | `tests/core/pages-site.test.js` | `demos/pages-mutants.mjs` |

**Classes 4 to 8 have no foundation at all.** There is no notion of an infinite run, fairness, component
interface, environment, parallel composition operator, contract with assume/guarantee semantics, refinement
relation in Lean, probability measure over runs, measurement or calibration.

**What is sound and is kept:** the generic search and its proofs (`Search.lean`, `explore_sound`,
`explore_counterexample_real`, `tcheck_sound`); `Integrity.lean` (kernel reflection, `holds_of_eval`), which the
review judged the most rigorous part; format 2's number domain (integer time in a declared unit, exact rationals,
bit-specified integer inverse-CDF tables, SplitMix64 streams, exact binomial and sign tests); `Resource.lean`; the
proof that the optimised engine equals its reference definition (`Impl.runAnyValue_eq`) and its axiom pinning; the
trace format, recorder and replay design; and the scope discipline of the documentation, which is mostly accurate.

## 2. Disputes and how they were resolved

**Rewrite or evolve.** The foundations review first proposed rewriting the semantic core. Under challenge it
conceded that most of it evolves: the search core, integrity, resources, random streams and workloads are kept as
they are, and the format-2 step becomes one scheduler of a new transition relation, connected by a proved
correspondence. What must be rewritten is the value domain, and this was settled by a property rather than by
agreement: the unbounded invariant `n ≤ L` of a counter with guard `n < L` and effect `n := n + 1` needs
`n < L → n + 1 ≤ L`, which `omega` proves over `Int` and nothing proves over `Float`. If the new relation were over
`Int` while the executable step still computed in `Float`, the correspondence theorem itself would be unprovable. So
`Float` leaves the executable semantics too, and format 1 is deleted (or `lift_agrees` proved).

**Within-step order.** That a behaviour listed earlier in a scenario writes state a later one reads in the same step
is deliberate and documented (`docs/semantics.md`). It is still a defect against the objective: composition then
depends on the order of a list, and `explore_sound` is a theorem about the explorer's own successor function, not
about the system, whenever components may react to one event in either order (concrete case: `a: x := 1`,
`b: y := a.x`, invariant `b.y == 0` is verified for `[b, a]` and refuted for `[a, b]`). Resolution: snapshot reads (a
behaviour reads other machines from the state at the start of the step), proved by a permutation theorem.

**Canonical explorer state first, or typed core first.** The model-checking review showed that the current
configuration can be canonicalised (identities are unobservable, sequence numbers can be renumbered, `attempts` and
`delayedBy` must be kept), but conceded that proving a canonicaliser for a type about to be deleted is wasted; the
typed core's state is designed canonical from the start.

**Is fixing evidence bookkeeping in JavaScript wasted work.** Partly. Improving the JavaScript status rules is
wasted: they move to Lean. The facts those rules consume cannot move to Lean, because running a test, hashing a file
or invoking `lake` observes the outside world. The line: the status order, combination rules, freshness predicate,
regression order and fact schema are defined in Lean; stamping, dependency mapping and test-runner adapters are
small trusted tools outside it that emit facts in that schema.

## 3. The foundation

One object, from which the guarantee classes are propositions about it rather than separate features.

1. **Labelled transition systems.** `LTS σ α` with an initial-state predicate and a step relation. Reachability,
   runs (finite and infinite), traces and observations (projection of labels to an alphabet) are defined once.
2. **A typed core calculus** whose semantics is an LTS: typed values over `Int`, `Bool` and exact rationals; typed
   expressions with a total denotation (no strings parsed inside a step); guarded commands over a component's own
   state; components with an interface (input and output alphabets, owned variables). The executable step is one
   scheduler of the relation, proved sound (`step_sound`), and the explorer's successors are proved complete for it
   (`successors_complete`).
3. **Properties** as predicates on states, runs and traces: invariants, finite-trace LTL for terminating scenarios,
   infinite-trace LTL under declared fairness for liveness.
4. **Composition** as a parallel operator on components with synchronisation on shared labels, proved commutative
   and associative up to isomorphism, with the projection lemma.
5. **Contracts** as assumption/guarantee pairs over traces, with satisfaction, refinement, compatibility and the
   assume-guarantee composition rule, under explicit side conditions that rule out circular reasoning.
6. **Refinement** as simulation (with stuttering) through an abstraction function, proved to preserve trace
   inclusion and safety, and liveness under fairness.
7. **Quantitative semantics**: time as a non-negative integer in a declared unit (non-Zeno as an explicit
   property), resources as the existing `Resource.lean`, probability as a probability mass function over traces
   under idealised independent draws, so metric claims are statements about a measure and a statistical test is a
   proved level-α test of that statement.
8. **Guarantees and evidence**: a guarantee is a proposition about one of the objects above with a status of four
   parts, each tied to a distinction the objective requires: *strength* (refuted < undecided or asserted < checked on
   instances < explored to a bound < proved), *subject* (model, implementation, reality), *open assumptions*, and
   *freshness* (the stamps of everything it depends on). Strength comes only from fresh facts of the right kind; a
   conjunction takes its weakest part; contradicting evidence only lowers a status; staleness never raises one; a
   refuted assumption makes a claim undecided, not refuted; only a proved, fresh claim with no open assumptions is
   shown as established. A regression is any move down or to an incomparable status, or a removal.

Implementation conformance (class 7) and simulation fidelity (class 8) are relations between the model and things
outside Lean (code, measurements). Lean defines what the relation is and what a monitor or statistical test
establishes about it; the observations themselves are facts produced by trusted tools, and their trust is recorded.

## 4. Roadmap

Every milestone includes formal definitions, correctness obligations, machine-checked proofs where applicable,
positive and adversarial examples, an executable demonstration, integration with `specs/exegra/spec.jsonc`,
documented limitations, and the completion criteria listed. "Proved" below means checked by `lake build` in CI with
no `sorry` and no axiom beyond `propext`, `Classical.choice` and `Quot.sound`.

**M0. Stop overclaiming (no dependency).** Each demonstrated inflation path in section 1 is closed at the fact
producer, without improving the JavaScript status rules that M3 replaces: skip-aware test references on both the
fresh and reuse paths; results and Lean records stamped with the tree, specification and source hashes, and read as
`stale` on mismatch; the `lean-theorem` checker refuses `opaque` and empty `about` lists and records the theorem's
statement hash; `openStarted` computed, not defaulted; `admit` and `verify` treat any downgrade or removal as a
regression; `pages-site-published-from-main` restated to what its test establishes. *Done when* each demo in
`assessment/2026-11-26/demos/` that shows an inflation yields the honest status, as a unit test.

**M1. The LTS foundation and unbounded safety (no dependency).** `Exegra.Core`: LTS, reachability, invariants,
inductive invariants, `safe_of_inductive`, vacuity and deadlock, bounded reachability, closed-set certificates;
the bridge from the existing generic search (`Gen.search`) to LTS invariants, for `holds` results (under a coverage
obligation) and for counterexamples (under a soundness obligation); a minimal single-sorted guarded-command
calculus over `Int` with well-scoped variables (`Fin n`), total expressions, snapshot updates and steps labelled
by command. *Done when* the counter invariant `n ≤ L` is proved with no bound, a true but non-inductive invariant
is shown not to be accepted without strengthening, bounded invariance at every depth is shown not to imply
invariance, and a closed-set certificate proves an invariant of a finite system with no bound. k-induction is M4.
*Limitations:* the calculus is single-sorted and has no division, timers, events or faults (M2); there are no
runs, traces or observations yet (M5, M6); semantic completeness of inductive invariants is over arbitrary
predicates, not over the calculus's expressions.

**M2. Typed core calculus for Exegra behaviours (after M1).** Exegra's behaviour language (machines, events,
guards, effects, timers, faults) as a typed calculus whose semantics is an M1 LTS, with snapshot reads; the format-2
step proved to be one scheduler of it (`step_sound`), the explorer's successors complete for it; format 1 deleted.
*Done when* `step_sound` and `successors_complete` are proved, the `[a, b]` / `[b, a]` example gives one verdict, and
the golden traces are unchanged or each change is listed and justified.

*Plan* ([assessment/2026-11-26/plan-M2.md](assessment/2026-11-26/plan-M2.md)): format 2's values are `Float`
throughout, so `step_sound` cannot be proved against today's step; the integer fragment of the behaviour
language is elaborated into the calculus and run on a proved executable, and inputs outside the fragment run
on the legacy path, flagged in the trace and covered by no theorem. Increments: M2.1 core calculus with the
snapshot permutation theorem and the `[a, b]` / `[b, a]` example; M2.2 time, timers, faults and the full
relation; M2.3 the executable with `step_sound` and `successors_complete`; M2.4 elaboration; M2.5 dispatch,
Rust oracle and differential checks; M2.6 explorer and temporal monitors on the calculus; M2.7 counted
instances; M2.8 random draws; M2.9 deletion of format 1. Snapshot reads change no golden trace (checked by
`scripts/snapshot_diff.py` over 866 steps). Resources, links and workloads, and the removal of `Float` from
values, are a separate milestone M2b.

**M3. Lean owns lowering and verdicts (after M2, M0).** The specification-to-calculus lowering (`sim-input.js`,
`pools.js`, `distributions.js`) and the claim semantics move to Lean; the status lattice of section 3 is defined in
Lean with its rules as theorems; `claims.js` keeps formatting only. *Done when* `sim-input.js` is deleted, the
engine entry point is proved to equal `run ∘ lower`, and the JavaScript status rules are deleted.

**M4. Canonical state, fixpoints and k-induction in the explorer (after M2).** The explorer searches canonical
states, reports `holds` only on an empty frontier, separates quiescent, bound-hit and truncated runs, and emits a
closed-set certificate; k-induction is added with a soundness theorem. *Done when* eight independent clients explore 256 states, a counter that would fail beyond
the bound reports `incomplete`, and an invariant of Exegra's own `visual-edit-flow` is proved with no bound.

**M5. Liveness under fairness (after M4).** Infinite runs, weak and strong fairness, non-Zeno, lasso search with a
refutation theorem. *Done when* a blinker is refuted for "eventually always on" and proved for "always eventually
on" under weak fairness.

**M6. Interfaces, composition and contracts (after M2).** Component interfaces, the parallel operator and its
laws, contracts with the assume-guarantee rule, assumptions with a discharge graph checked acyclic. *Done when*
`compose_comm`, `compose_assoc` and `ag_compose` are proved and the two-product ledger example (each product safe
alone, the composition unsafe) is refused at installation.

**M7. Refinement and staged conformance (after M5, M6).** Simulation refinement with its preservation theorems;
conformance stages (structural, interface, transition, trace, runtime monitor, verified refinement), each with what
it establishes and does not. *Done when* the lease example is refused and the camera edit of conformance L1 makes
its claims stale or refuted.

**M8. Probability and statistics in Lean (after M2).** A probability mass function semantics, distribution tables
recomputed or checked in Lean, the binomial test proved a valid level-α test, seed and run count committed by hash.
*Done when* the false-holds rate at p = β stays at or below α under every workflow the command line allows.

**M9. Simulation fidelity (after M8).** Measurements with provenance, calibration parameters, error models,
validity domains, sensitivity and out-of-sample validation. *Done when* one of Exegra's own quantitative claims is
calibrated against measured runs with a stated error bound and validity domain, and goes stale when its domain is
left.

**M10. Change impact and admission over all artifacts (after M0, M3).** A dependency graph from guarantees to
specification entities, assumptions, Lean declarations, files and measurements; incremental re-verification;
admission over change sets of any artifact; changes to guarantees themselves shown separately. *Done when* editing
one assumption re-marks exactly the claims that depend on it, and a change that weakens a theorem is refused.

## 5. Capability matrix

The current state of each class, with the scope of what is established and what strengthens it. This table is
maintained with the milestones and moves into a generated artifact derived from the specification in M0.

| Class | Established today | Scope and limits | Next |
|---|---|---|---|
| 1. Well-formedness | Structural derivation in Lean (16 codes); most rules in JavaScript | JavaScript rules are not Lean; no single `WellFormed` predicate | M3 |
| 2. Consistency | None | Validation and integrity rules are not joint satisfiability; assumptions are text | M6, then a satisfiability check over typed assumptions |
| 3. Safety | (a) Bounded exhaustive exploration of format-1 scenarios, sound and complete within the bound for the explorer's own successor function. (b) Since M1: unbounded safety of any labelled transition system from an inductive invariant or a kernel-checked closed-set certificate, and a proved bridge from the generic search's `holds` to an unbounded invariant under a coverage obligation (`lts-foundation`) | (a) is bounded, drops failed steps, fixes within-step order and refuses format 2. (b) is proved for the guarded-command calculus, not yet for Exegra's behaviour language: the coverage obligation for Exegra's explorer is undischarged until M2 | M2, M4 |
| 4. Liveness | None (`eventually` is a property of the last state of a finite run) | | M5 |
| 5. Compositionality | None (structural graph claims over hand-declared relationships only) | | M6 |
| 6. Refinement | Program equivalence of the optimised and reference engines; a JavaScript trace check that is unsound (lease example) | Not a refinement relation | M7 |
| 7. Implementation conformance | Module paths exist; named tests pass | Tests are instances, not universal; results are not provenance-bound | M0, M7 |
| 8. Simulation fidelity | None (a verified per-seed run is not an accurate model) | | M8, M9 |
| Change impact | None (a whole-tree stamp reuses or reruns everything) | | M0, M10 |
