# Compositional verification and assume-guarantee reasoning: assessment

Team: composition. Read-only. The Lean core is not built, so nothing that goes through `src/core/lean.js` was run.
One demonstration ran pure JS (`claims.js` structural evaluators on a hand-built model). The script is
`demos/composition-assumptions.mjs`.

## 1. Verdict

There is no compositional foundation to evolve. Contracts are prose records. `assumptions` are labels that the
evaluator copies and never reads. Every claim is checked against one closed artefact: the whole declared graph, or
the fixed set of machines a scenario lists. No object exists for an interface or alphabet, an environment, a
composition operator, contract refinement or compatibility. The Lean model is untyped JSON (`Entity.data : Value`).
The useful parts (the honest scope and vacuity discipline, typed contract-event signatures, the forward-simulation
refinement check, layer namespacing) can be kept as checks that run *inside* a new A/G layer. The A/G layer itself
has to be designed from scratch in Lean. This is a new layer, not a rewrite of the parts that work.

## 2. Fundamental limitations and missing foundations

**F1. Assumptions are inert labels, so "verified within the stated assumptions" is false. BLOCKS-OBJECTIVE. DEMONSTRATED.**
- Where it happens: `src/core/claims.js:233` copies `claim.data.assumptions` into the result. No other line of
  `claims.js`, `validate.js`, `integrity.js` or `fault-model.js` reads them; the only other readers are display code
  (`generate/claims-report.js:55,109,164`).
- The type gives no hook for logic: `metamodel.json` defines `assumption` as `{statement: text, rationale}`, with no
  formula, no `dischargedBy` and no link to a claim. `claim.assumptions` can only refer to kind `assumption`, never to
  a claim or an environment guarantee.
- The demo shows the effect.
  - Claim c1 is `no-relationship X→Y`, transitive, with assumption `a-no` ("X never calls Y"). It is **verified**.
  - Claim c2 is `acyclic`, with assumption `a-yes` ("X calls Y on every request"). It is **verified**.
  - Claim c3 is the same check as c1 with **no** assumptions. It is **verified**.
  - So the status does not depend on the assumptions, and two contradictory assumptions coexist with nothing
    reporting it.
- Real case in the spec: assumption `relationships-match-imports` (spec.jsonc:14651) carries a rationale saying that
  when it was last checked by hand it was **false**: 12 import pairs between components had no declared relationship.
  `core-independent-of-ui` and `core-dependencies-acyclic` cite it and kept the status *verified* throughout. No
  mechanism re-checks the assumption, even though a script could decide it.
- Consequence for the objective: guarantee classes 2 (consistency of assumptions), 5 (A/G) and change impact
  ("which guarantees depend on this assumption") have nothing to stand on.

**F2. A contract is descriptive data, not an assume/guarantee pair. BLOCKS-OBJECTIVE. ARGUED.**
- In `metamodel.json`, `contract.preconditions`, `postconditions` and `obligations` are lists of `text`.
- The only semantic checks on contracts:
  - event payload signatures (`validate.js:491-530`, `typeAssignable`);
  - on a trace, payload shape and request/response pairing (`contract-trace.js:87-133`);
  - non-emptiness of the postconditions of a hand-written contract (`readiness.js:72`).
- Gap in the pairing check: a request that is never answered is not flagged, so even the liveness half of the
  protocol is unchecked.
- The contract has the *shape* of A/G (pre = assume, post = guarantee, obligations = environment duty), but nothing
  gives it meaning.

**F3. Ports and relationships have no compatibility semantics. LIMITS (BLOCKS for class 5). ARGUED.**
- A port is `{direction, contract}`, and `relationship.contract` is a separate reference.
- No rule checks any of the following:
  - that a relationship joins a `requires` port to a `provides` port;
  - that the port contracts are equal, or that one refines the other;
  - that `relationship.contract` agrees with either endpoint.
- Evidence: grep of `validate.js` and `integrity.js`; the only port evaluator is `has-port`, which checks that a
  port exists (`claims.js:770`).
- My hand-built mismatched model (provides→provides, three different contracts) could not be run through
  `analyzeSpec` because it needs Lean. That conclusion is unverified at runtime, but no code path that would refuse
  it exists.
- In Exegra's own spec: 15 ports and 23 relationships with a contract, and **0** relationship endpoints that are
  ports. Ports are not wired to anything.

**F4. Structural claims ignore hierarchy, so the composition contradicts the per-part results. LIMITS. DEMONSTRATED.**
- `componentGraph` (`query.js:109-123`) treats a subsystem as an ordinary node. `selectComponents`
  (`query.js:185-189`) expands a selector to descendants, but edges into or out of a subsystem are never related to
  edges of its children.
- Demo model: `X→S` where S is a subsystem, `s1` has parent S, and `s1→Y`.
  - `reachable X→S` is **verified**.
  - `no-relationship X→Y`, transitive, is **verified**.
  - `reachable S→Y` is **violated**, even though S's member reaches Y.
- The structural projection follows the opposite rule: "a collapsed subsystem stands for its members"
  (spec.jsonc:19493; `architecture.md` collapsing lifts edges). So the claim semantics and the view semantics
  disagree about what an edge on a composite means.
- For a "never depends" safety claim this is an under-approximation, which makes it unsound. It is latent in
  Exegra's own spec (0 of 347 relationships touch a subsystem) but allowed for any user.

**F5. Machines have no interface and can read each other's state, which kills modular reasoning. BLOCKS-OBJECTIVE. ARGUED from Lean.**
- `Semantics.lean:184-195` (`resolve`) lets any guard read `<B>.state` and `<B>.<var>` of any machine. A machine
  absent from the run reads as `.undef`.
- Validation of a transition guard has no scenario scope. `allowedBehaviors` is passed only for claim parameters
  (`validate.js:263-293`); guards go through `checkExpr` with `{behavior, event}` only.
- So a machine's behaviour in a scenario that omits B differs **silently** from its behaviour composed with B:
  `B.state != "x"` is evaluated against `undef`.
- Effects of the missing interface:
  - No alphabet: events are broadcast to "every instance of every behavior in the scenario that reacts to it"
    (`semantics.md:51`).
  - No hidden or local state.
  - No notion of the environment of a machine.
- Refinement is non-modular too: the abstract machine's expressions may read concrete machines in the same trace
  (`refinement.js:9-10`, `claims-and-evidence.md:95`).

**F6. Product layering is syntactic splicing, with no guarantee about composed products. BLOCKS-OBJECTIVE for class 5. ARGUED; counterexample below.**
- `layers.js:266-279` splices product entities into the platform text and evaluates over the merged closed model.
- "Products are independent" is enforced only *referentially* (`layer.cross-product-reference`). Products may
  declare `behaviors`, `events`, `scenarios` and `claims` (`layers.js:83-99`). `powerRules` (`layers.js:687-735`)
  restricts behaviors only by `level`; nothing restricts `subject`, emitted events or scenario membership.
- Concrete counterexample (each part valid under the rules as written; not executed, because Lean is not built):

  ```jsonc
  // platform: behavior "ledger" (subject "ledger-svc"), var held = 0; on "reserve": held = held + 1.
  //           event "tick", event "reserve".
  // product badges.jsonc  (imports: ledger, tick, reserve)
  "behaviors": [{ "id": "badges__awarder", "subject": "ledger-svc", "initial": "idle", "variables": [],
     "states": [{"id":"badges__idle"},{"id":"badges__done"}],
     "transitions": [{ "id":"badges__t", "from":"badges__idle","to":"badges__done","on":"tick",
                       "effects":[{"emit":"reserve"}] }] }],
  // (assumptions is not a product section; claim.assumptions could cite platform assumptions, to no effect, F1)
  "scenarios": [{ "id":"badges__s", "behaviors":["ledger","badges__awarder"], "steps":[{"at":0,"event":"tick"}] }],
  "claims": [{ "id":"badges__one-hold", "kind":"invariant", "statement":"At most one hold.",
     "evaluate":{"method":"state-invariant","expr":"ledger.held <= 1","scenarios":["badges__s"],
                 "negatives":[{"scenario":"badges__s","faults":["dup-reserve"]}]} }]
  // product promotions.jsonc: the same with promotions__awarder / promotions__s / promotions__one-hold.
  ```

- Each product's claim is *verified* on its own scenario. With both products installed, `tick` is broadcast to both
  awarders, two `reserve` events are emitted, and `held = 2`.
- Exegra never constructs, requires or even suggests the scenario `{ledger, badges__awarder, promotions__awarder}`.
  Nothing records that each claim was established against an environment that excludes the other product.
- The claims' `"assumptions"` field could say "only this product reserves", but per F1 that changes nothing and the
  two assumptions' joint inconsistency goes unnoticed.

**F7. Circular justification is invisible. LIMITS. ARGUED.**
- Claim → assumption has no link back to any guarantee, so circular A/G ("A assumes B's guarantee, B assumes A's")
  cannot even be *expressed*, let alone checked for well-foundedness.
- The one place where a cycle can be expressed goes unchecked:
  - `environment.guarantees[].source` is an any-kind reference (`model-and-format.md:121`).
  - So claim C can name `faultModel F` in environment E, while E's `message-loss: 0` guarantee names C as its
    source.
  - `fault-model.js:59-100` checks only that a source is present.
- Environment guarantees do not constrain evaluation in any case: a fault model affects only scope text
  (`fault-model.js:31-50`). That text is honest about this.

**F8. The Lean model has no component semantics. BLOCKS-OBJECTIVE. ARGUED.**
- `Model.lean:268-275`: an entity is `{id, kind, data : Value, ...}`.
- `ModelProps.lean` proves facts about reference resolution and the hash only.
- `grep` finds no composition, parallel or assume/guarantee notion anywhere in `formal/Exegra/*.lean`.
- Structural claims, contract checks, the layering rules and the refinement check all live in JS. So for class 5,
  "Lean as the sole authority for semantics" is currently empty.

## 3. Overclaims

- **`claim-methods.js:21`.** The `verified` label reads "Verified within the stated model and assumptions". The
  assumptions are not inputs to any evaluator (F1).
- **`claims-report.js:133`.** The generated report says "Verified means checked … within the stated scope and
  assumptions." Same defect.
- **`claims-and-evidence.md:123`.** "Every result carries … the assumptions" is true but misleading: it carries
  them as decoration.
- **Contract field names.** `preconditions`, `postconditions` and `obligations` read as a formal contract but
  are free text with no checking. This is mild: the docs do not claim they are checked.
- **"Products are independent of each other"** (`model-and-format.md:33`). It means referentially independent.
  Behaviourally, products interfere through shared platform machines and broadcast events (F6).
- **`core-independent-of-ui` reported *verified*** (`architecture.md:118`) while its own cited assumption is
  recorded as having been false. The docs disclose this; the status does not.
- **The `has-port` method** ("declares a port matching … contract"). It checks that the interface exists, not
  that the component satisfies it.

The scope texts are a credit to the project. Trace claims say "these traces, not all executions", and fault-model
coverage says how many modes were injected. I found no overclaim there.

## 4. What to preserve

- **The status discipline in `claims.js`.** Vacuity becomes `inconclusive`. A trace claim must have negatives
  (`claims.js:1106-1119`). Contradicting evidence demotes a result, never promotes it. Every result carries a scope.
  These are exactly the honesty rules an A/G engine needs for "assumption not discharged".
- **Typed contract-event signatures** (`validate.js:509-530`, `type-expr.js` `typeAssignable`). This is the seed of
  interface typing: an event carries a role (request/response/error) and a correlation key.
- **Forward-simulation refinement with an explicit mapping** (`refinement.js`). It is the right shape of check. It
  must be made modular (no reads of foreign machines) and lifted to contracts.
- **Explicit `faultModel` / `environment` / `failureMode` entities, each value with a `source`.** These are the
  natural carriers of environment assumptions, once they get formal content.
- **Layer namespacing and import discipline** (`layers.js`). They give a clean component boundary on which to hang
  "a product = a component with an interface".
- **The integrity-rule language with reflection proofs.** It suits the *meta* checks: every assumption is discharged
  or explicitly open, and the discharge graph is acyclic.

## 5. Architectural decisions that prevent the objective, and replacements

1. **Global, unencapsulated machine state (`<B>.var` readable anywhere; `.undef` for absent machines).** Replace it
   with an interface per behavior: input and output event alphabets plus exported observables. Foreign reads become
   only exported observables, and a guard over an absent machine is a static error.
2. **Claims always evaluated against a closed world** (the whole graph, or the machines a scenario lists). Replace
   this with claims *scoped to a component* and checked against an explicit environment object. The environment is a
   contract, or a most-general environment generated from the interface. A closed-scenario check stays available as
   testing, labelled as such.
3. **Assumptions as prose referring only to `assumption`.** Replace with assumptions that have a formal body
   (a rule-language or temporal formula over the component's interface). An assumption may be discharged by a claim
   or a contract guarantee (`dischargedBy`), or left open, and every result propagates the set of open assumptions.
   A result with open assumptions is `verified-under {A1..An}`, never plain `verified`.
4. **Contracts as free-text pre/post.** Replace them with `(A, G)` formulas over the contract's typed alphabet,
   with Lean definitions of satisfaction, refinement (`A' ⊇ A`, `G' ⊆ G` in the saturated form) and compatibility.
5. **Layering as text splicing.** Replace it with composition of components: platform ∥ product₁ ∥ … ∥ productₙ.
   Each product brings a contract, and installing a product checks compatibility against the platform and the other
   installed products. This makes F6 an admission-time refusal rather than a silent gap.
6. **Edges on subsystems unrelated to members.** Define a subsystem's relationships as the lifted union of its
   members' relationships, or forbid relationships on subsystems. Use the same rule in the projection and in claims.

## 6. Highest-leverage changes, in dependency order

1. **Interfaces in Lean.** Define `Interface := {inputs, outputs : Finset EventId, observables}` per behavior and
   per component. Port `resolve` so that a guard reads only its own variables or exported observables. Completion
   criterion: a Lean theorem `run_respects_interface` (a machine's step depends only on its own state, its input
   event and the exported observables), and a validation error, with a test, for the F5 guard over an absent machine.
2. **Parallel composition and the environment.** Define `compose : Machine → Machine → Machine` on the format-2
   semantics, matching events by alphabet, and prove it commutative and associative up to trace equivalence.
   Completion criterion: theorems `compose_comm` and `compose_assoc`, plus `traces (M ∥ N) ⊆ traces M ↾ αM` (the
   projection lemma).
3. **Contracts with semantics.** Define `Contract := (A G : TraceProp)` with `satisfies M C`, `refines C' C` and
   `compatible C₁ C₂`, plus a non-circular A/G rule with an explicit well-founded discharge order (or a sound
   circular rule for safety only). Completion criterion: a theorem
   `ag_compose : sat M₁ C₁ → sat M₂ C₂ → compatible C₁ C₂ → sat (M₁ ∥ M₂) (C₁ ⊗ C₂)` with only the standard axioms,
   and the F6 example rejected as incompatible.
4. **Assumption propagation and discharge in the claim evaluator.** Add formal assumption bodies, a `dischargedBy`
   link, and result status `verified-under` with a list of open assumptions. Add integrity rules: no cycle in the
   discharge graph, and no two assumptions that are jointly unsatisfiable over a finite interface (bounded check,
   labelled bounded). Completion criterion: the F1 demo yields c1/c2 `verified-under` with a reported conflict
   between `a-yes` and `a-no`, and `core-independent-of-ui` becomes `verified-under {relationships-match-imports}`
   until an import checker discharges it.
5. **Products as components.** Each product declares its contract over platform events and machines, and layering
   composes and checks compatibility. Change impact uses the discharge graph: editing assumption A invalidates
   exactly the results whose open or discharged set contains A. Completion criterion: installing both F6 products is
   refused, and a test shows that editing one assumption re-marks exactly its dependent claims.

## 7. Predictions about other teams

- **Safety and liveness teams** may report trace claims as "safety under assumptions". The assumptions never
  constrain the run, and the "environment" is whatever machines and faults a scenario lists. The real hypotheses are
  "this exact closed scenario", not the declared assumptions.
- **The refinement team** may credit `refines` as a basis for compositional refinement. It is trace-bounded and
  non-modular: the abstract model may read concrete machines (`refinement.js:9`). Refinement of contracts does not
  exist.
- **The well-formedness and consistency teams** may treat "validate reports no errors" plus integrity rules as
  consistency of assumptions. Integrity rules quantify over entity metadata, and assumption statements are opaque
  text, so joint satisfiability of assumptions is not checked at all.
- **Architecture and traceability reviewers** may accept `core-independent-of-ui` (verified) as evidence about the
  code. It is exact about hand-declared edges only, and its cited assumption was recorded as false at one point.
- **Anyone reading the Lean** may assume the kernel "derives the model, therefore owns component semantics".
  `Model.lean` derives untyped JSON. All component, port, contract and layer reasoning is JS.
- **The layering and product reviewers** may conclude that products are isolated because cross-product references
  are refused. Behavioural interference through shared platform machines is unconstrained.
