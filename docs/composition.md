# Behavioural composition along the hierarchy

How a composite element's behaviour is derived from its members', how a declared abstraction of a set of members is checked against them, how a scenario chooses the level each region runs at, and how claims move between levels (WG-5729, part of the multiscale milestone WG-5697; the audit is `docs/assessment/2026-11-27/multiscale.md`, sections 2.4, 3.4–3.6 and 4.2 Q7). The engine and its calculus are described in [simulation.md](simulation.md); this page builds on them and adds no engine of its own.

The code is `src/core/composition.js` (alphabets, interfaces, abstractions, cuts, the refinement check, order independence, claim transfer and the validation rules), `formal/Exegra/Boundary.lean` (hiding, projection and the comparison of two runs, with their laws proved) and the commands in `cli/composition-commands.js`.

## The one rule: composition is the kernel's

A scenario's machines already run as one system: `simulationInput` lists them in one engine input, and the elaborator turns that input into one calculus system `Core.Behav.Sys` whose step relation delivers each entry to every machine (synchronous broadcast on shared events, [simulation.md](simulation.md#formal-semantics)). **That is the composition operator.** Composing two sets of machines is listing them in one input; there is no second engine, no JavaScript interpreter of behaviours, and a composite's derived behaviour runs on exactly the semantics claims are evaluated on.

**Hiding is a projection of the kernel's trace.** The boundary trace of a run over a set `H` of hidden events is the subsequence of its steps whose event is not in `H`, in order (`Boundary.hide`). It is computed in Lean (`engine.boundary`), from the trace the Lean engine returned. A hidden step is a stutter of the composite: it changes only members' state that the boundary does not show.

So the derived behaviour of a composite `X` in a scenario is

> `M_X = (∥ members of X) \ H_X`

where the members are the scenario's machines whose subject is `X` or inside it, and `H_X` is the set of their events that no machine outside `X`, no scenario input and no injected fault uses. `exegra compose <element> --scenario <s>` prints it; its strength is **exact** (nothing is approximated: it is a projection of the run).

When WG-5685 lands `Sys.compose` (composition of two separately elaborated systems, with `Sig.append` and `Expr.lift`), the theorem it owes is that elaborating the concatenated input gives `Sys.compose` of the parts. The operator here is defined so that this is the statement: composition is concatenation of the machine lists of one input.

## Interfaces

Every event belongs to the interface of an element or a port.

- **Declared**: a component or port may carry `interface: {inputs, outputs, observables}`. `inputs` and `outputs` are event ids; `observables` are `"<behavior>.<variable>"` or `"<behavior>.state"`, the state of its behaviours that behaviours outside may read.
- **Inferred**: without a declaration, the interface is read off the behaviours (`inferredInterface`). The members of an element are the behaviours whose subject is the element or lies inside it, declared abstractions excluded so that a member set is not counted twice. An input is an event a member consumes that a behaviour outside emits, or that no behaviour emits (it comes from outside the model); an output is an event a member emits that a behaviour outside consumes, or that none consumes; the members' other events are internal. Observables are the members' state that behaviours outside read. `exegra interfaces [<element>]` reports both, whether they agree, and the cross-element reads into each element.
- **An event's interfaces** (`eventInterfaces`, `exegra interfaces --events`): the declared ones, the subject of every behaviour that consumes or emits it (inferred), and the element `producedBy` names.

Validation (`checkComposition`, called by `validateModel`):

| Code | When |
|---|---|
| `interface.undeclared-input`, `interface.undeclared-output` | A component declares an interface, and its members consume from (emit to) outside an event it does not list. A declared interface may list more than the members use today; it may not list less. |
| `interface.observable-unknown`, `interface.observable-foreign` | An exported observable is not `<behavior>.<variable|state>`, or names a behaviour of another element. |
| `behavior.reads-unexported` | A guard or effect reads `<B>.<x>` of a behaviour of another element, the read crosses the boundary of an element with a declared interface, and that interface does not export `<B>.<x>`. Such a read is an interaction; the declared interface is where it becomes visible. |
| `event.no-interface` | Once the specification declares any interface: an event no interface declares, no behaviour uses and no `producedBy` names. |

Inference keeps model-level behaviours without declared interfaces running exactly as before; nothing changes for a specification that declares none (the rules above are silent there).

## Declared abstractions

A behaviour may declare that it abstracts a set of members:

```jsonc
"abstracts": { "members": ["persistence-client-flow", "dev-server-flow", "workspace-disk-flow", "workspace-watcher-flow"],
               "hide": ["..."],        // optional: replaces the derived hidden set
               "timeScale": 1 }         // optional: member time units per abstract tick
```

- **Member sets.** The members are behaviours, of any elements; the abstraction's *region* is the set of their subjects. Its own subject must be one of those elements (an abstraction attached to the region's entry point, as `workspace-flow` is attached to `persistence-client`) or an element that contains them all (a composite carrying a behaviour).
- **Multiple levels.** A member may itself be an abstraction. `membersOf(..., {finest: true})` expands members of members; `exegra refine <a> --finest` checks the top against the leaves directly, which by transitivity (below) must agree with checking level by level.
- **Hiding.** Comparing a run of the abstraction with a run of its members hides the members' events that the abstraction does not know and that nothing outside the region (the scenario's other machines, its inputs and injected faults) uses. A hidden event that a machine outside uses is not hidden, so a member set that leaks an internal event shows up as a boundary difference.
- **Validation**: `behavior.abstraction-members` (no members, unknown, self, repeated), `behavior.abstraction-cycle`, `behavior.abstraction-subject`, `behavior.abstraction-hides-boundary`, `behavior.abstraction-hides-unknown`; and `scenario.levels-overlap` when a scenario runs an abstraction together with one of its members (one region at two levels at once).

### The refinement check

`checkAbstraction(model, a)` (`exegra refine <a>`, claim method `refines-composition`) runs each driving scenario twice through the kernel: with the region at the abstraction and at its members (the scenario's list with only that region replaced, `behaviorsAtLevels`), and asks Lean (`engine.refineBoundary`) to compare the two boundary traces:

- the same sequence of boundary steps, each with the same kind, event and payload (payloads compared structurally, key order ignored);
- the members' time of each step equal to the abstract time multiplied by `timeScale`;
- the same outcome;
- the same final configuration of every machine outside the region.

Hidden steps of the members are stutters and are listed as such. The result is per scenario either a **certificate**, the step correspondence (which members' step realises each abstract boundary step, and which members' steps are stutters), or a **counterexample**: the first differing boundary step on each side, the agreed prefix and the reason (`event`, `payload`, `kind`, `time`, `abstract-longer`, `concrete-longer`, `outcome`, `environment`).

The driving scenarios are the listed ones, else every scenario that runs the abstraction, else every scenario that runs all its members. Faults that act on a transition of a machine not running at one of the two levels are left out of both runs and listed.

### Strength

Each result that is not refuted carries one of four strengths, the claim-strength vocabulary of WG-5697 (a counterexample refutes the abstraction and has no strength):

| Strength | Meaning |
|---|---|
| `exact` | A derived composite: the members composed with the internal events hidden. Its boundary traces are those of the members by construction (`onto_hide_disjoint`). |
| `conservative` | A declared abstraction whose check gave a certificate on every driving run, with no member opaque and no fault left out. The abstraction allows at least what the members do on those runs. |
| `explored` | A declared abstraction whose certificate on every driving run is backed by an exploration of both systems (`refine --explore`): every boundary trace of the members, over every interleaving, fault mask and draw, is one the abstraction shows with the same active faults. |
| `incomplete` | An element of the region has no machine in a run (opaque), a fault had to be left out, a run delivered nothing, a scenario could not be run, or there was nothing to check. |

What a claim checks is the deterministic scheduler's run of each scenario, as for every trace claim: a certificate is refinement on those runs. Two things widen it (WG-5734):

- **Comparison up to commutation.** Two simultaneous deliveries of events that no running machine consumes both of change disjoint sets of machines, so they commute. The members' hidden steps can reorder such a pair (in `real-write-recorded` the members deliver `write-file-ok` after the recorder's `traffic-step-recorded`); the check compares the boundary traces up to the order of such pairs (`independentEvents` computes them, the region counting as one machine). In Lean, `commMatch` brings each concrete step's partner to the front past independent steps; `commMatch_sound` proves that what it accepts is a reordering by swaps of adjacent independent steps that then agrees position by position, and `commMatch_of_rel2` that every pair the comparison as sequences accepts is still accepted. A run says which comparison certified it (`comparison`: `sequence` or `commutation`). A negative of `refines-composition` may list pairs as `dependent`, which must then break the refinement.
- **Exploration.** `exegra refine <abstraction> --explore [--bound N] [--max-states N]` explores both systems in Lean (`engine.refineExplore`, `formal/Exegra/BoundaryExplore.lean`): the calculus's complete enumeration of each transition system, every delivery order among simultaneous entries, every fault mask and every draw. It searches the product of the members' system with sets of the abstraction's states (those that can have shown the same boundary trace, closed under silent steps) for a node with no abstract candidate left. `explore_holds` proves the certificate sound: trace inclusion on the boundary, every run of the members showing a trace a run of the abstraction with the same active faults shows (`exploreB_holds` on the calculus). A counterexample is the members' run (its fault mask, the picks, the replayed steps and the boundary trace no abstract run shows). The exploration compares boundary traces only: outcomes and the final configuration of the machines outside the region are compared on the scripted runs, and liveness is not compared. Exploring visits every product node of each scenario, so the self-specification's explorations run with the proof checks (`tests/proofs/refinement-explore.test.js`, the evidence of `declared-abstractions-refined-over-interleavings`), not in live claim evaluation.

### Laws (proved in `formal/Exegra/Boundary.lean`)

| Theorem | Statement |
|---|---|
| `onto_hide_disjoint` | **I1.** Hiding events not on the boundary does not change the trace over the boundary alphabet. |
| `hide_hide`, `hide_comm`, `hide_append`, `hide_nil` | P10: hiding composes (`(M \ H₁) \ H₂ = M \ (H₁ ∪ H₂)`), commutes, and is a homomorphism of concatenation (so of prefixes). |
| `zipCheck_none_iff` | The comparison is exact: no mismatch exactly when the projections are related position by position. A certificate means agreement; a counterexample is a real difference. |
| `Agrees.refl`, `Agrees.trans` | **I3**, preorder: agreement of boundary traces (the refinement the check decides) is reflexive and transitive. |
| `Agrees.hide_more` | **I3**, congruence under hiding: agreement over `H` implies agreement over `H ∪ H'`. |
| `invariant_rename` (`Core/BehavRename.lean`) | **I2**: the verdict of a safety property does not depend on the order in which machines are listed. |

Each is pinned to the standard axioms by `#guard_msgs`. Preservation of refinement by composition with a third system (`M ⊑ A ⇒ M ∥ E ⊑ A ∥ E`) is not proved here; it needs `Sys.compose` (WG-5685). The check exercises it on every run, since every driving scenario composes the region with the rest of the scenario.

## Behavioural cuts

A scenario declares its behavioural cut as data:

```jsonc
"cut": {
  "regions": [{ "abstraction": "workspace-flow", "level": "abstract" }],
  "environment": [{ "element": "simulation-engine", "events": ["claim-scenarios-run"],
                    "assumption": "engine-answers-run-scenario" }]
}
```

- **Regions**: the level each declared abstraction runs at, `abstract` (the abstraction runs) or `members` (its members run in its place). A region the scenario does not declare is inferred from the behaviours it lists. The listed behaviours must agree with the declared levels (`scenario.cut-region`).
- **Environment**: what the scenario omits, stated. Each entry names an element, the events it would receive, and optionally the assumption that justifies omitting it. `environmentReport` reads a run: every delivered event that no running machine reacts to and that an omitted element would receive (an element with a behaviour that consumes it, or whose declared interface lists it as an input) needs an entry covering that element and event; the others are reported as `scenario.environment-unassumed` by `exegra simulate` and `exegra environment`, and decided by the claim method `environment-assumed`. An environment entry for an element the scenario runs is `scenario.environment-element`.
- **Another level on demand**: `exegra simulate <s> --level <a>=members` (or `abstract`, `finest`) runs regions at another level. The level comes from the command line or the scenario, never from a view.

**No presentation state reaches simulation (I4).** The engine input is derived from the scenario and the fault list alone (`simulationInput(model, scenarioId, faults)`), the refinement check from the scenario and the abstraction, and claim verdicts from those runs. Nothing takes a collapse state, a selected view or a camera. A view may *display* a scenario's cut: it never chooses it. This supersedes the plan of WG-4666 that "a run chooses the level per region, following the view's collapse state": its depth goal is kept, its level now comes from declared cuts.

## Order independence (I2)

The scheduler visits machines in input order, and the order decides which queue position simultaneous emits get. `invariant_rename` proves that a safety verdict does not depend on that order in the calculus's relation (every interleaving). `orderIndependence` checks it on the scheduler's runs: each scenario, and each negative run of its claims, is run with its behaviours reversed and in every rotation, and the verdict of every invariant and temporal claim that lists it is compared, together with the trace up to the order of behaviours (`canonicalTrace`). `exegra order-check [<scenario>]` runs it; the claim method `order-independent` decides it.

## Claim transfer (I6)

A claim verdict at one level is asserted at another only through a stated preservation rule (`transferClaim`, `exegra transfer <claim> --abstraction <a>`, claim method `transfers`):

| Rule | Applies when |
|---|---|
| `safety-down-refinement` | A safety claim (`never`, `precedes`, `state-invariant`) over the abstraction's boundary alphabet, established where the abstraction runs, holds for its members when the refinement check certifies the abstraction. |
| exact composites | For a derived composite the boundary traces are equal, so a claim over its boundary transfers both ways. |
| none for liveness | `eventually` and `liveness` claims never transfer without a declared fairness hypothesis; with one, the hypothesis must be re-established for the members, so they are not transferred either. The reason is shown. |

Not transferred, with the reason: a failing or unchecked refinement; a claim that reads the abstraction's own state or names its transitions (not expressible at the members' level: "not expressible at this level", never quietly re-scoped); a claim that is not positive at its own level.

## One behaviour per element per level

Two behaviours of one subject that consume a common event, never run together in a scenario, and are not related by an abstraction or `refines` are **alternative machines**: two models of one element at one level that nothing shows agree. Each pair is reported (`gap.alternative-machines`, `exegra interfaces`) until it is reconciled into one behaviour per level, the coarser declared as an abstraction of the finer and checked. The claim method `alternatives-reconciled` decides it. In the self-specification the persistence elements are reconciled (`persistence-alternatives-reconciled`): `write-endpoint-flow` and `workspace-flow` are checked abstractions, and `write-client-flow` was removed. The session's two machines were split by concern and now run together in the edit scenarios (`session-flow` the commit pipeline, `project-session-flow` the save), the engine's two are one behaviour (`engine-flow`), and the claim `alternatives-reconciled-everywhere`, with no subject list, holds for every element.
