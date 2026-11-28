# Multiscale architectural modeling: audit and architectural direction

Task: WG-5687. Written 2026-11-27 against `main` at 67134ff, with that working tree's uncommitted changes to
`specs/exegra/spec.jsonc` and `cli/commands.js` present (they do not touch anything this document relies on).

This is an investigation, not an implementation. No code or specification was changed. The document says
what Exegra does today for describing one system at several levels of abstraction. It defines what that
should mean precisely and derives an architecture that delivers it. It then applies that architecture to
Exegra itself and lists the gaps, ordered by dependency.

## How this was established

- **Read in full:** `docs/` (architecture, semantics, simulation, model-and-format, claims-and-evidence,
  integrity-rules, decisions, verification) and the 2026-11-26 assessments. In `src/core/`: `metamodel.json`,
  `query.js`, `projections.js`, `layout/*`, `refinement.js`, `claims.js` (the structural and trace paths),
  `claim-strength.js`, `integrity.js`, `derivation-cache.js`, `layers.js`, `parse.js`, `project.js`. Also
  `src/app/session.js`, `tools/traceability.js`, and the Lean files `Model.lean`, `ModelProps.lean`,
  `Core/LTS.lean`, `Core/Behav.lean`, `Core/Calculus.lean`, `Core/BehavExec.lean`.
- **The self-specification:** every components, relationships, contracts, records, copies, behaviors,
  events, scenarios, claims, assumptions and views entry was read or processed by script. Component
  responsibilities were summarised, not read verbatim.
- **Computed on the tree:** scripts over the parsed specification (`jsonc-parser`, read-only), and the pure
  evaluators run in memory with `EXEGRA_NO_CACHE=1`. They produced the subsystem quotients in section 5, the
  emit/consume flow analysis, the comparison of the import graph with the declared relationships, and an
  integrity-rule probe. The quotient script is reproduced in appendix A.

Labels used below:
- **DEMONSTRATED:** computed or run on this tree.
- **VERIFIED:** read in the source, cited by `file:line`.
- **ARGUED:** reasoned from verified facts.

Citations of `spec.jsonc` give the line of the entity's `"id"`.

### Relation to the 2026-11-26 assessments

Those documents audited formal grounding: the composition, foundations, epistemics, Lean and model-checking
teams. This one does not repeat that audit, and it does not count the incomplete formal grounding against the
current system. It cites their findings only where they bear directly on multiscale modeling:

- assumptions are inert: composition F1, still true at `src/core/claims.js:253`;
- ports are unwired: composition F3;
- structural claims ignore hierarchy: composition F4;
- machines read each other's state: composition F5;
- composition is order-dependent: foundations F4. `Core/Behav.lean` has since proved `phase2_perm`
  (`Behav.lean:974`) for the typed calculus.

---

## 1. Assessment of the current multiscale capability

### 1.1 Verdict

Exegra has one level of structural containment and no semantic notion of abstraction.

- **Containment.** `component.parent` is a single reference to a `subsystem` (`metamodel.json:116`,
  `validate.js:70-76`). The self-specification uses it for exactly one level: 6 subsystems over 87
  components, and no subsystem has a parent (DEMONSTRATED).
- **No relationship lives above the leaves.** Every one of the 350 relationships joins two leaf components;
  none touches a subsystem (DEMONSTRATED).
- **The coarse view is drawn, not derived.**
  - A subsystem's relationships are computed only by the renderer's projection (`projections.js:186-311`),
    which keeps the first relationship of a bundle and discards the rest of the witnesses.
  - The claim evaluator does not lift at all (`query.js:109-123`). A coarse view and a coarse claim can
    therefore disagree about the same edge (composition F4).
- **Structure and behaviour are not tied together.**
  - Behaviour attaches only to leaf components (44 behaviors on 25 leaves, none on a subsystem;
    DEMONSTRATED).
  - Behaviours are composed only as the closed list of a scenario.
  - There is no hiding of internal events.
  - The only refinement check is one level deep and requires the refined machine to emit exactly what the
    abstract one emits (`refinement.js:353-355`), so a decomposition cannot have internal messages.
- **Coarse facts cannot be traced to fine ones.** All architecture facts are hand-declared. The only facts
  taken from code are module paths (`tools/traceability.js:87-127`).

The pieces that are already right are substantial:
- the text as the single authority;
- immutable derived models;
- a stratified, recursive rule language with a least-model semantics in Lean;
- a typed behaviour calculus with a relational LTS;
- a forward-simulation refinement check with an explicit mapping;
- typed contract events;
- an honest status discipline.

What is missing is a layer between the declared facts and the views: abstraction maps, derived coarse facts
carrying witnesses, composite interfaces, and behavioural composition with hiding. That layer is a new
semantic stratum. Exegra does not need to be restructured to get it.

### 1.2 Capability by requirement

Classes:
- **S:** genuinely semantic.
- **P:** approximated by presentation only.
- **A:** absent.

| Requirement | What exists | Class | Evidence |
|---|---|---|---|
| Semantic fidelity | Every scene node and edge is backed by an entity (`entityId`). A bundled edge is backed by its *first* relationship only. | S for leaves, P for coarse edges | `projections.js:291-311`; selecting a bundle selects that one relationship (`scene-view.js:280-281`, `main.js:25-27`) |
| Compositionality | `parent` groups components. No relation between a subsystem's facts and its members' facts, apart from claim selectors that expand to descendants. | A | `query.js:186-189` (selectors expand), `query.js:109-123` (graph does not lift) |
| Boundary preservation | Collapse lifts child edges to the outermost collapsed ancestor and bundles them by (from, to, kind). This happens only in the structural projection. | P | `projections.js:196-198`, `297-311` |
| Recoverability | Expanding a subsystem redraws its children. A bundle cannot be opened to list what it stands for; the only hint is a note. | P | note at `projections.js:316` |
| Cross-scale consistency | View lifting and claim evaluation use different rules for composite edges. Message classification depends on the collapse state. | A (contradictions possible) | `query.js:109-123` vs `projections.js:283-311`; `flows.js:113-141` |
| Independent coherence | Only `semantic-core` has responsibilities among the 6 subsystems. No subsystem has ports, contracts or behaviour. | A | DEMONSTRATED over the spec |
| Recursive decomposition | The schema allows nested subsystems. The rule "only a subsystem may contain" makes a composite a different kind from a leaf, and leaves are where all facts attach. | A in practice | `metamodel.json:110-116` |
| Mixed-scale reasoning | Collapse is per subsystem, so mixed views draw. It is viewer state, per project and not per view, and it has no meaning for claims or simulation. | P | `session.js:122-125`, `766-778` |
| Behavioural preservation | Leaf machines only. No composite behaviour. One-level refinement with no hiding of internal events. Scenarios are closed worlds. | A | `refinement.js:138-156`, `353-374`; `validate.js:196-199` |
| Traceability | Leaf entities point to module paths. Coarse edges have no witnesses. Claim results do not record what they read. | A for derived facts | `claims.js:362` (`involved` only); `claim-strength.js:154` |
| Non-redundancy | Coarse relationships are not declared (good), but they are not derivable as model facts either. Message interactions are declared twice, once as relationships and once as behaviour emits, with no check between them. | A | 3 of 121 cross-subject emit/consume pairs have no relationship (DEMONSTRATED, section 5.6) |

### 1.3 Where each deficiency lies

| Layer | Deficiency |
|---|---|
| Specification language | No construct for an abstraction map, a level or cut, a composite interface, or a connector; one overloaded edge kind (`calls`); `relationship.carries` exists but is unused. |
| Semantic model | One unnamed one-level hierarchy; composites are a separate kind; events and data belong to no element. |
| Model derivation | Derives entities, refs and expressions only (`Model.lean:867-877`); no derived relations stored as model facts (integrity relations are evaluated per rule, never stored). |
| Implementation | Lifting lives in `projections.js`, and the entity→component mapping is written three times (`projections.js:355-367`, `session.js:687-706`, `flows.js:84-91`). No code-fact extraction. |
| Self-specification | `semantic-core` is flat (41 children). The composition root `src/app/main.js` is filed under `visualization`. `builtin-types.js` is claimed twice. Same-subject alternative machines disagree. |
| Visualization | Bundles drop their witnesses; filters drop connections silently; collapse is per project, not per view; the "N inside" badge ignores filters (`projections.js:252`). |

### 1.4 Is Exegra's density intrinsic, representational or presentational?

Exegra's architecture view is dense: 104 components and 350 relationships. Lifting the declared
relationships to the six subsystems gives 38 subsystem-level edges, 35 of them of dependency kinds (section
5.2). The dependency-kind quotient has one strongly connected component:
`{application, visualization, agent-interface, tooling}`.

Its causes fall into three groups.

**Intrinsic.** The application uses the core widely: 38 dependency relationships go from `application` to
`semantic-core`. The tooling also uses the core widely (21). This fan-out is real and a coarse view should
show it.

**Introduced by the representation.**
- The cycle `visualization → application` exists because the composition root `src/app/main.js` is a module
  of `visual-interaction`, in `visualization`. The spec records why: traceability assigns each file to one
  component (`visual-interaction` unknowns). Its 9 "Mounts the …" relationships (for example
  `visual-interaction-calls-inspector`) are lifecycle composition, recorded as `calls`. A composition root is
  above both subsystems, not inside one of them.
- `tooling → agent-interface` is `test-suites-calls-agent-cli`. Tests are a different perspective (a
  verification harness), not a runtime dependency.
- `semantic-core → application` (`transactions-data-flow-session`) is the data a subscription delivers,
  recorded as `data-flow`. A data-flow edge points the opposite way to the dependency that carries it. The
  layout's "dependency layers" use every drawn edge regardless of kind (`layout/solve.js:46`), so this
  reverse edge is presentational noise on top of a representational ambiguity.

**Introduced by the presentation.**
- Bundles labelled only `calls ×25` hide the fact that the 25 edges mix imports, notifications and
  lifecycle.
- Filters drop paths silently.

So most of the coarse-level tangle that a reader would blame on Exegra's architecture is introduced by the
representation. Section 5 shows that a semantic quotient, with kinds that carry their own lifting meaning,
separates the three kinds of cause mechanically.

---

## 2. Target multiscale semantics

The definitions are kept to what the requirements need. Each is stated so that it can be computed, and
eventually proved.

### 2.1 The base: one fact base at the finest known grain

A specification denotes a **fact base** `F = (E, I, B, D, K, prov)`:

- **`E`: elements.** Things that exist in the system at some grain: a system, subsystem, service, component,
  module, function, store or external actor. Being an element does not depend on being a leaf. Whether an
  element is composite is a derived property: it has children in some hierarchy.
- **`I`: interactions.** Typed directed facts `i = (a, b, κ, attrs)` with `a, b ∈ E ∪ Ports`. The label `κ`
  is taken from an **interaction taxonomy** (section 2.3). The attributes are a contract, the events or data
  types carried, a multiplicity, and delivery guarantees.
- **`B`: behaviour.** Each element `a` may have a behaviour `M_a`: an open labelled transition system with an
  interface `Σ_a = (In_a, Out_a, Obs_a)`, its input events, output events and exported observables.
  Functional elements, such as a pure compiler pass, may instead have a function signature and body, which
  Exegra's `function` entity already supports.
- **`D`: data.** Records and copies with owners and holders. Data movement is the subset of `I` whose
  `attrs.carries` names data.
- **`K`: contracts and claims.** Obligations stated about elements, interactions and behaviours.
- **`prov`: provenance.** Every fact has one:
  - `declared`: written by an author;
  - `extracted`: produced from code by a named extractor of a given version, over a given source digest;
  - `observed`: recorded at run time, for example by the traffic recorder or the replay;
  - `derived`: computed by a named rule from listed input facts;
  - `assumed`: an assumption, with a discharge status.

  Within each region the authoritative grain is the finest one at which facts are known.

### 2.2 Hierarchies, abstraction maps and cuts

- **Hierarchy.** A hierarchy `H` is a rooted laminar family over `E`: any two blocks are disjoint or nested.
  In other words, it is a forest of containment.
  - The system is the root, so the system becomes an element. Today `system` is a separate singleton
    entity and the six subsystems are roots alongside the external actors.
  - A specification may declare several named hierarchies over the same elements: logical decomposition,
    deployment, ownership, trust zones. Each is one perspective. They cannot contradict each other, because
    every fact at any level of any hierarchy is a function of the same base (section 2.3).
- **Facet.** A grouping that is not laminar (a cross-cutting concern such as "styling", "diagnostics" or
  "the verdict kernel") is a facet: a named, possibly overlapping set of elements. A facet supports
  selection, claims and highlighting. It does not support contraction, because quotienting by overlapping
  sets is not well defined. Today's `tags` are facets.
- **Cut.** A cut `C` of a hierarchy is an antichain that covers every element. The level-`k` frontier is
  one cut. A mixed-scale view is any other cut. The abstraction map `α_C : E → C` sends each element to its
  unique ancestor-or-self on the cut.
  - Cuts are ordered by refinement: `C ≤ C'` when every block of `C'` is a union of blocks of `C`. For cuts
    `C ≤ C'` there is a unique `α_{C→C'}` with `α_{C'} = α_{C→C'} ∘ α_C`. This is what makes zooming
    through intermediate levels agree with zooming directly.

### 2.3 Derived structure: quotients, boundaries and interfaces

- **Interaction taxonomy.** Each kind declares how it lifts:
  - **dependency class:** whether it is a static dependency, a runtime control dependency, or neither;
  - **direction semantics:** whether control and data flow the same way or opposite ways;
  - **coarsening:** the parent kind it may be coarsened to. For example, `imports` and `invokes` coarsen to
    `depends-on`; `publishes` and `subscribes` through one connector coarsen to a mediated `notifies`.

  The kinds form a tree. A view may coarsen kinds, and that is an abstraction on labels independent of the
  one on elements.
- **Quotient (existential lift).** For a cut `C`, the quotient `F/C` has the cut's blocks as elements and,
  for each kind `κ`, an interaction `(X, Y, κ)` exactly when some base interaction `(a, b, κ)` has
  `α_C(a) = X`, `α_C(b) = Y` and `X ≠ Y`. Each lifted interaction carries:
  - its **witness set**: the base interactions it stands for;
  - **summarised attributes**, computed by monoid homomorphisms over the witnesses: count (sum); the sets
    of contracts, events and data types (union); the strongest and weakest delivery guarantee (meet and
    join).

  Because summaries are homomorphisms and witness sets are unions, lifting through `C` then `C'` equals
  lifting straight to `C'`.
- **Internal interactions.** An interaction with both ends inside one block `X` is internal at `C`. It is
  not shown at that level and stays in `X`'s fibre `F|X`, the sub-fact-base induced by `X`'s members.
- **Boundary and derived interface.**
  - The boundary of an element `X` (at any cut where `X` is a block) is `∂X = { i ∈ I : exactly one end of i
    is inside X }`.
  - The **derived interface** of `X` groups `∂X` by direction, kind and contract or event. These are `X`'s
    derived ports.
  - A **declared interface** (ports, contracts, purpose) is optional. When present it is a checked
    statement:
    - declared ⊇ derived: no boundary crossing that the interface does not declare (encapsulation);
    - declared ⊆ derived: no declared port that nothing realises (realisation).

    An element with a declared interface and no known members is **opaque**: its declared interface is
    authoritative at that grain until members are added, and from then on it is an obligation.
- **Recoverability.** `F` is the disjoint union of the fibres `F|X` for `X ∈ C` and the lifted
  interactions' witness sets. So `(F/C, {F|X}, witnesses)` determines `F` exactly. Nothing is lost by
  zooming out; what is intentionally omitted at level `C` is precisely the fibres and the witness detail,
  and both are one expansion away.

### 2.4 Derived behaviour: composition, hiding and refinement

- **Composite behaviour.**
  - For a block `X` whose members have behaviours, the derived behaviour is
    `M_X = (∥_{a ∈ X} M_a) \ H_X`.
  - `∥` is synchronous product on shared events. With interfaces, it is commutative and associative up to
    trace equivalence.
  - `H_X` is the set of events that are internal to `X`: produced and consumed only within `X`. They are
    hidden as τ.
  - `Σ_X = (In_X, Out_X, Obs_X)` is read off the boundary.
- **Abstract behaviour.** A declared behaviour `A_X` on a composite is a specification of the composite.
  It is valid when `M_X ⊑ A_X`. For safety, `⊑` is trace inclusion on `Σ_X` up to stuttering, with a
  declared time scale. A forward simulation with an explicit mapping, which is what `refinement.js` checks
  on one trace today, is the witness that makes `⊑` checkable.
- **Consistency through levels.**
  - Hiding composes: `(M \ H₁) \ H₂ = M \ (H₁ ∪ H₂)`.
  - `⊑` is a preorder that is preserved by `∥`: if `M ⊑ A` then `M ∥ E ⊑ A ∥ E`.
  - Hence deriving `M_Y` for `Y ⊃ X` from members' behaviours, or from `X`'s abstract behaviour composed
    with `Y`'s other members, gives a result the direct derivation refines.
- **Encapsulation of state.** A behaviour may read another element's state only through that element's
  exported observables. Each such read is itself an interaction on the boundary. Today any guard may read
  `<B>.<var>` of any machine (composition F5), which makes some interactions invisible to structure.

### 2.5 Levels, views and independent coherence

- **View.** A view is a tuple `(H, C, kind-coarsening, filter, projection)`. The semantic part
  `(H, C, coarsening)` determines a derived model. The filter and the projection only select and draw it.
  A filter that removes an element must either drop the connections through it, with a counted note, or
  replace them by **derived path summaries** labelled as such ("A reaches C through 1 hidden element").
  Silently losing connections is not allowed.
- **Coherence of a level.** A level (cut) `C` is **independently coherent** when:
  1. every block has a stated purpose or an explicit "grouping only" mark;
  2. every interaction at `C` has a kind and a non-empty witness set, or is declared at an opaque block;
  3. every claim stated at level `C` is evaluable on `F/C` (and `M_X` for its blocks) without naming a
     finer element;
  4. where the hierarchy designates `C` a layering level, the dependency-class quotient is acyclic.

  Conditions 1–3 are decidable. Condition 4 is a property a specification chooses to claim; it is not part
  of validity.

### 2.6 Partial knowledge and uncertainty

- Each element is **transparent** (members known, derived facts authoritative), **opaque** (declared
  interface authoritative) or **unknown** (placeholder; nothing derived through it is asserted).
- Provenance is visible on every derived fact. A lifted interaction whose witnesses are all `declared` is
  shown and reported differently from one with an `extracted` or `observed` witness.
- Claim results gain two meanings that do not exist today (`claim-methods.js:19-27`):
  - **verified under open assumptions:** the composition team's `verified-under {A…}`;
  - **not expressible at this level:** the claim names something hidden at the chosen cut.

  A claim is never silently dropped or silently re-scoped.

### 2.7 Requirement coverage

| Requirement | Satisfied by |
|---|---|
| Semantic fidelity | Every coarse fact is a quotient fact with witnesses (2.3). |
| Compositionality | Abstraction maps and quotients (2.2, 2.3); composite behaviour (2.4). |
| Boundary preservation | Boundary `∂X`, derived interface, existential lift (2.3). |
| Recoverability | Fibre decomposition (2.3). |
| Cross-scale consistency | Functoriality of lifting along cut refinement; hiding laws (2.2–2.4). |
| Independent coherence | Coherence conditions (2.5). |
| Recursive decomposition | One element kind, laminar hierarchy of any depth (2.1, 2.2). |
| Mixed-scale reasoning | Arbitrary cuts (2.2). |
| Behavioural preservation | Composition with interfaces, hiding, refinement (2.4); data in `carries` (2.1). |
| Traceability | Provenance and witness sets; read sets on claim results (2.1, 2.3, 4.2 Q13). |
| Non-redundancy | Coarse interactions, interfaces and message interactions derived; declared only at opaque blocks or as checked expectations (2.3, 4.2). |

---

## 3. Mathematical foundations and abstraction correctness conditions

### 3.1 Typed attributed graphs with a laminar hierarchy

The fact base is a typed, attributed, directed multigraph over `E ∪ Ports`. Edges are labelled by the kind
tree, and the vertices carry a forest. Exegra already has the typing (the meta-model is data:
`metamodel.json`, `vocabulary`) and the multigraph (relationships). It lacks named laminar families,
composite elements of the same kind as leaves, and interaction kinds that carry lifting semantics.

### 3.2 Quotient graphs and functoriality

A cut gives a surjection `α : E → C`, and the quotient graph is the image of edges under `α × α`, minus
self-loops. Two facts make zooming consistent.

1. **Composition of cuts.** For `C ≤ C'`, `α_{C'} = α_{C→C'} ∘ α_C`. This holds because the family is
   laminar.
2. **Lift functoriality.** `lift_{C'}(F) = lift_{C→C'}(lift_C(F))` on edge existence, on witness sets
   (union is associative) and on any attribute summary that is a monoid homomorphism.

   This is the precise sense in which "abstraction through intermediate levels agrees with direct
   abstraction". It fails for summaries that are not homomorphisms (for example "the label of the first
   relationship", which `projections.js:291-310` uses), and it fails for non-laminar groupings.

### 3.3 What a coarse structural verdict tells you about the base

Read the existential quotient as an abstraction in the Galois-connection sense:
- `α(S)` lifts a set of base edges;
- `γ(T)` is every base edge set whose lift is within `T`.

The quotient over-approximates connectivity. Hence the following transfer rules (ARGUED; they are proof
obligations P4–P6 in section 10).

| Coarse verdict at cut `C` | Transfers to the base | Notes |
|---|---|---|
| No `X → Y` edge of kind class `κ` | No base `κ` edge from any member of `X` to any member of `Y` | Absence transfers downward exactly. This is the sound way to check "the core never depends on the UI". |
| Base `a → b` edge (`α(a) ≠ α(b)`) | A coarse `α(a) → α(b)` edge exists | Presence transfers upward. |
| Coarse path `X → … → Z` | **Not** a base path in general | **Spurious paths**: `X → Y` may be witnessed by `a → y₁` and `Y → Z` by `y₂ → z`, with no path from `y₁` to `y₂` in `Y`. Coarse reachability is a may-property. A must-reachability needs path-witnessed lifting: concatenation with a connecting path in the fibre. |
| Coarse quotient acyclic (dependency class) | Every base dependency cycle lies inside a single block | Acyclicity at a level is a layering statement about blocks, not about the base. Base acyclicity does not imply coarse acyclicity: the coarse cycle can be real at block level (section 5.3). |
| Coarse edge count `n` | Exactly `n` witnesses | Only when count is a summary attribute, not the bundle "first" rule. |

So a claim must say at which level it is stated. Its truth at that level is a fact about blocks. The table
says when it transfers. Today `componentGraph` does not lift (`query.js:109-123`), so a claim naming a
subsystem treats it as a node with no edges (composition F4). That is unsound for absence claims written
against composite endpoints.

### 3.4 Interface-based composition, hiding and refinement

The appropriate formalism is **open labelled transition systems with interfaces**, in the I/O-automata
family:
- input, output and internal actions;
- parallel composition by synchronisation on shared actions;
- hiding of internal actions;
- refinement as trace inclusion on the external alphabet for safety, with forward simulation as the
  checkable witness.

Exegra already has the parts of this:
- `Core/LTS.lean`: a relational `LTS`, with `Reach`, `Invariant`, `Inductive` and `BoundedInvariant`
  (`LTS.lean:38-124`);
- a typed whole-system calculus, `Behav.Sys.lts` (`Behav.lean:813`), with `phase2_perm` (`:974`);
- a forward-simulation mapping, in `refinement.js`.

The missing parts are named in section 10:
- an interface per machine;
- a composition operator on separable parts (not one whole `Sys`);
- hiding;
- trace inclusion and simulation as relations between two systems.

Bisimulation is not the default equivalence. It is stronger than an architecture view needs, and it
distinguishes decompositions that differ only in internal branching, which a coarse view must be free to
forget. Trace inclusion on the boundary (safety) is the right default. Liveness needs explicit fairness
hypotheses and is not preserved by finite-trace inclusion. It is left out of the default notion and must be
claimed separately (foundations F3).

### 3.5 Structural validity does not imply behavioural validity

A structurally valid contraction does not make a behaviourally valid abstraction. Three examples, all drawn
from Exegra:

1. **The edges exist, but the order is not preserved.** In `visual-edit-flow` the save hop
   `session → workspace-service` lifts to `application → persistence`, which exists as a coarse edge
   (section 5.6). Structurally the coarse view is "consistent". Behaviourally, the scenario's
   `workspace-flow` is not shown to be an abstraction of
   `persistence-client-flow ∥ dev-server-flow ∥ workspace-disk-flow` with their internal `ws-*` events hidden.
   The two models even start from different disk hashes: `h1` and `h2` (behaviour audit; `spec.jsonc:7553`,
   `:8324`).
2. **The interface is preserved, the protocol is not.**
   - The relationship `dev-server-plugin-calls-workspace-service` and the port `workspace-write-in` declare
     the contract `write-file`.
   - The events on that hop (`ws-write`, `ws-write-done`) carry no contract.
   - So `checkContractEvents` (`contract-trace.js:87`) never checks the hop.
   - A coarse edge labelled `write-file` asserts a protocol that nothing establishes.
3. **Hidden state reads.** A guard reading `<B>.var` across a block boundary is an interaction with no
   structural edge (composition F5). A structural quotient cannot see it, so a block can appear decoupled
   while being behaviourally coupled.

Hence the validity conditions in 3.10 separate structural (V1–V4) from behavioural (V5–V7) obligations.

### 3.6 Abstract interpretation of claims

- A claim stated at a cut is evaluated in the abstract domain of that cut. Its soundness direction comes
  from 3.3 for structure and from refinement for behaviour.
- Safety over the boundary alphabet transfers **down** a refinement: if `A_X ⊨ φ` and `M_X ⊑ A_X`, then
  `M_X ⊨ φ`.
- A property of members does **not** transfer up to a declared abstract behaviour that allows more.
- For **derived** composite behaviour (exact hiding) the boundary traces are equal, so φ over `Σ_X`
  transfers both ways.

These are the only directions a level-aware claim evaluator may use. Any other "verified at a coarse level"
would overclaim.

### 3.7 Information preservation

Zooming out is lossless as an operation on the fact base, because of the fibre decomposition (2.3). It is
lossy as a *picture*, deliberately. What the picture omits is exactly:
- the fibres;
- the per-witness attributes beyond the summary;
- the internal events of composite behaviours.

A transformation is information-preserving when it is invertible given the omitted parts. Bundling that
keeps a witness set is information-preserving. Bundling that keeps the first relationship is not.

### 3.8 Summarising interaction through connectors

Some coarse summaries are not node quotients but **path contractions**. A producer reaches a consumer
through a broker topic or a channel, and the coarse view wants `producer ⇢ consumer`. That needs connectors
as first-class elements, and a coarsening rule: a path `publishes · subscribes` through a connector
contracts to `notifies`, with the connector in the witness. Exegra declares `publishes` and `subscribes`
kinds but uses `publishes` zero times. Without connectors, a coarse view must either show the broker as a
hub (correct but uninformative) or invent a direct edge (unfaithful).

### 3.9 Machinery deliberately not adopted

- Category-theoretic packaging (operads, string diagrams). The two functoriality facts in 3.2 are all
  the composition structure needed, and they are stated directly.
- Bisimulation as the default equivalence (3.4).
- Probabilistic abstraction. Foundations F10 covers the measure-theoretic gap. Multiscale structure does
  not depend on it.
- Graph-clustering heuristics as a *source* of hierarchy. Hierarchies are declared or derived from
  authoritative facts such as module paths. Clustering metrics may only *evaluate* a declared hierarchy
  (5.3).

### 3.10 Validity conditions of an abstraction

An abstraction at cut `C` is **valid** when V1–V4 hold. It is **behaviourally valid** when V5–V7 also hold.

- **V1. Well-formed partition.** `C` is a cut of a laminar hierarchy, and every element maps to exactly
  one block. Today `src/core/builtin-types.js` belongs to two components, so the module→element map is not
  a function.
- **V2. Witnessed coarse facts.** Every coarse interaction has a non-empty witness set, or it belongs to an
  opaque block.
- **V3. Interface agreement.** For every block with a declared interface, declared and derived interfaces
  agree (2.3).
- **V4. Kind preservation.** Every coarse kind is either a base kind or the declared coarsening of its
  witnesses' kinds.
- **V5. Structure–behaviour coherence.** Every boundary message, meaning a pair where an emit in `M_a` is
  consumed in `M_b` with `α(a) ≠ α(b)`, is witnessed by an interaction of a message kind between `a` and
  `b` (or their ports). Every cross-element state read is an interaction.
- **V6. Behavioural refinement.** For every block with a declared abstract behaviour, `M_X ⊑ A_X` on
  `Σ_X`.
- **V7. Contract conformance at boundaries.** Every boundary interaction that declares a contract has its
  events typed by that contract, so the protocol is checked where the edge claims it.

When a condition fails, the abstraction is **reported, not hidden**. The failing blocks are marked; claims
at that level that depend on them become `inconclusive`, with the failing condition as the reason; the view
draws the failing edge or block distinctly.

---

## 4. The proposed authoritative semantic architecture

### 4.1 Strata

```
 declared text (spec.jsonc)     extracted facts (tools/: imports, modules)     observed facts (traffic, replay)
            \                               |                                        /
             +------------------- fact base F (with provenance) ------------------+
                                            |
          derivation rules (declarative, stratified; generalising integrityRelations)
                                            |
     derived model: hierarchies, cuts, quotients + witnesses, boundaries, derived interfaces,
     derived message and data interactions, composite behaviours (∥ and hiding), coherence diagnostics
                                            |
          level-bound claims (with read sets)            views = (hierarchy, cut, coarsening, filter)
                                            |                                |
                                    claim results                  projection -> SceneModel -> renderer
```

Four principles govern the strata:
- **One authority per fact.** The text is the authority for declared facts, an extractor's output for
  extracted facts, and recordings for observed facts. Everything below the fact base is a function of it.
- **Declarative derivation.** Every derived fact is produced by a rule in a declarative language with a
  least-model semantics. This is what `integrityRelations` already is (`integrity.js:352-723`;
  `docs/integrity-rules.md:97-160`; Lean least-model meaning since b1068a3). The probe in this audit
  expressed the subsystem-summary rule in today's rule language: it parsed, it ran, and it reported 135
  counterexamples because the spec has no subsystem-level relationships (DEMONSTRATED). The language is
  sufficient for the lifting rules. It lacks only (a) storing the derived tuples as model facts that claims,
  views and other rules can read, and (b) recording witnesses.
- **Presentation consumes, never computes semantics.** `projections.js` stops lifting and bundling; it
  draws `F/C`. `flows.js` classifies messages against the semantic quotient, not against scene edges.
- **Change is tracked by provenance.** Each derived fact and each claim result records what it read, so an
  edit invalidates exactly its dependents (4.2, Q13).

### 4.2 Answers to the design questions

**Q1. What is the authoritative representation?**
- The fact base at the finest known grain: declared facts from the text, extracted facts from code, and
  observed facts from runs, each with provenance.
- The text stays the sole authority for what an author asserts. Extracted and observed facts are separate
  authorities for what code and runs show. They do not overwrite declarations; they confirm or contradict
  them, and a contradiction is a diagnostic.

**Q2. What is a semantically meaningful abstraction?**
- A block of a declared hierarchy that satisfies V1–V4. For behaviourally meaningful, V5–V7 as well.
- A stated purpose is required for a coherent level (2.5). Meaningfulness beyond that is not formal.
- Exegra should *measure* it, and must not pretend to decide it. Useful indicators:
  - derived interface size;
  - internal versus boundary interactions;
  - share of boundary interactions typed by contracts;
  - whether the dependency quotient at the block's level is acyclic.
- Section 5.3 shows these indicators separating a good grouping from a bad one on Exegra's own core.

**Q3. How are boundaries established?** By declared hierarchies, not by drawing. The boundary of a block is
computed (`∂X`). A declared interface is a checked expectation of the boundary, never a substitute for it,
except at an opaque block.

**Q4. How are higher-level entities derived?** Composite elements are declared as hierarchy blocks. Their
interactions, interfaces and behaviours are derived (2.3, 2.4). Their kind is not a separate entity kind:
"composite" is derived from having members. A composite may also own modules directly, such as an index
file or glue. That is modelled as an implicit member, so its code is not attributed to the composite's
boundary. Today `semantic-core` claims `src/core/types.js` this way.

**Q5. How are cross-boundary relationships derived and summarised?** By existential lift per kind, carrying
witness sets and homomorphic summaries (2.3). Path contraction is used only through declared connectors
(3.8).

**Q6. How are relationship types and interaction semantics preserved?**
- Kinds lift unchanged.
- A view may coarsen them only along the declared kind tree.
- Direction semantics are part of the kind, so a `data-flow` against a dependency is not read as a back
  dependency.
- The overloaded `calls` is split into `imports` (static), `invokes` (runtime control), `notifies`
  (callbacks and subscriptions delivered to a subscriber), and `composes` (lifecycle: mounts, constructs,
  wires).
  - In the self-spec these are distinguishable from the descriptions today: "Imports …", "Mounts …",
    "Listens for …".

**Q7. How are behavioural abstractions constructed?**
- Derived: `M_X = (∥ M_a) \ H_X`.
- Declared: `A_X` on the composite, checked by `M_X ⊑ A_X`, with a forward-simulation mapping as the
  certificate. The mapping generalises today's `refinement` property from one machine to a set of member
  machines, with the internal events hidden.
- A scenario chooses a **behavioural cut**: for each region, which level of behaviour runs. The cut is
  declared in the scenario. It is not inherited from the viewer's collapse state.
  - The current plan for depth says "a run chooses the level per region, following the view's collapse
    state" (`docs/simulation.md:1076`, WG-4666). That couples semantics to presentation. The run's level
    must be a declared, hashed part of the scenario, and a view may *adopt* a scenario's cut for display.

**Q8. How do external contracts relate to internal realisations?**
- A composite's declared contract is realised by a derived interface: a set of boundary interactions whose
  member endpoints carry the contract's events.
- The realisation check is V3 plus V7.
- A contract that passes through several hops, like `write-file` along
  `session → persistence-client → dev-server-plugin → workspace-service`, is one contract with a realisation
  path. Each hop is either typed by it or explicitly an internal hop of a block that hides it.

**Q9. Shared resources, cross-cutting concerns and overlapping responsibilities.**
- A shared element is placed at the lowest common ancestor of its users, or is its own block. It is not
  duplicated and not claimed twice. `builtin-types.js` must belong to one element, possibly a shared
  "types" element.
- A cross-cutting concern is a facet. It can be selected and claimed over, and is not contracted.
- A shared store is an element with records. Its readers and writers are interactions carrying those
  records.
- An overlapping responsibility is two elements with interactions to one shared element. The overlap is
  visible as fan-in, never as joint ownership.

**Q10. How can perspectives coexist without contradiction?**
- Several named hierarchies over one fact base. Each perspective's facts are derived, so they cannot
  disagree about the base.
- A perspective that needs facts the others do not have adds base facts, not perspective-local copies. A
  deployment link, for example, is an interaction of kind `network-link` between deployment elements.
- **Realisation maps** relate interactions across perspectives: a logical `invokes` is realised by a path
  of deployment `network-link`s, and the realisation is itself a checked fact.

**Q11. How does the system decide which abstractions are valid?** By V1–V7. V1–V5 and V7 are decidable on
the fact base. V6 is decidable on bounded exploration, or certified by a mapping. Its strength is reported
with the existing `claim-strength` vocabulary.

**Q12. What happens when an abstraction cannot preserve a relevant property?**
- The failing block is marked. Dependent claims become `inconclusive` with the failing condition.
- A claim that names a hidden element is "not expressible at this level", not quietly re-scoped.
- The view draws the failure. There is no silent fallback.

**Q13. How do changes invalidate or update derived abstractions?**
- Every derived fact records its rule and inputs: its witnesses, and for negation or absence its **query
  footprint**, for example "all `imports` edges from members of X to members of Y".
- Every claim result records its read set in the same form.
- An edit's affected entity set, which `Project.apply` already computes as `affected` (`project.js:206`) and
  does not use, intersected with recorded footprints, gives exactly what to recompute.
- Correctness condition: incremental evaluation equals full re-evaluation. Exegra already applies this
  discipline to the transaction index ("a transaction whose index is found not to match its model is
  replayed").

**Q14. How is uncertainty exposed?**
- Provenance on every fact.
- Transparent, opaque or unknown status on every element.
- "Verified under open assumptions" and "not expressible at this level" as result meanings.
- Planned elements (`implementation.status: not-implemented`) are opaque with a declared interface. Their
  derived interactions are drawn as planned.

### 4.3 How existing constructs map onto the architecture

| Existing construct | Role in the new architecture |
|---|---|
| `component` with `kind: subsystem` | element; "composite" derived from membership |
| `component.parent` | the default hierarchy (`logical`); more hierarchies by name |
| `tags`, `owner`, `trustZone`, vocabulary `runsIn` | facets, or hierarchies when laminar (`trustZone` is laminar by meaning) |
| `relationship` | interaction (declared provenance) |
| `link` | interaction of kind `network-link` in a deployment hierarchy |
| `port`, `contract` | declared interface; checked against derived interface |
| `event` with `contract`/`role`/`correlation` | interface alphabet of the element or port that produces it |
| `record.owner`, `copy.heldBy`, `copy.of` | data facts; `carries` on interactions links flows to them |
| `behavior.subject` | behaviour of an element at any grain |
| `behavior.refines` + `refinement` | certificate of `M_X ⊑ A_X`, generalised to member sets and hiding |
| `scenario.behaviors` | a behavioural cut plus an environment, declared |
| `integrityRelation` | the derivation-rule mechanism, extended to store derived tuples with witnesses |
| `view.filter.within`, collapse state | a cut (semantic, in the view), and selection (presentation) |
| `implementation.modules` | the map from module elements to their owning element (must be a function) |
| `failureMode.target` | a fault located at an element or interaction; lifts with the cut (section 6.2) |

---

## 5. Exegra itself at several scales

Every quotient below was computed from the declared relationships of `specs/exegra/spec.jsonc`
(DEMONSTRATED; script in appendix A). "Dependency kinds" means `depends-on`, `calls`, `subscribes`, `reads`,
`writes` and `submits-edits`.

### 5.1 Level 0: Exegra in its environment

**What it communicates:** what Exegra is for and what it touches. Exegra is one element, and the external
actors are the 11 external components.

Derived interactions: 12 edges; 314 relationships become internal.

| From | To | Witnesses (count by kind) |
|---|---|---|
| ai-coding-agent | exegra | calls 1 |
| exegra | filesystem | calls 6 |
| exegra | jsonc-parser-library | depends-on 7 |
| exegra | browser-platform | depends-on 4 |
| exegra | vite-dev-server | depends-on 3, observes 1 |
| exegra | browser-storage | writes 3 |
| exegra | playwright-runner | calls 1, depends-on 2 |
| exegra | threejs-library | depends-on 2 |
| exegra | markdown-specification-source | reads 2 |
| markdown-specification-source | exegra | data-flow 2 |
| exegra | external-test-runner | calls 1 |
| exegra | sqlite-engine | calls 1 |

**Why the boundary is meaningful:** it separates code in this repository from code and data it does not
own.

**Where the current model falls short:**
- **No human user.** The person editing through the browser is not an element. The `edit-requested` event
  comes from "outside", and no element produces it. A level-0 view therefore cannot show Exegra's primary
  interaction: a person edits a specification and sees it in 3D.
- **The system is not an element.** `system` is a separate singleton. "exegra" above had to be synthesised.
- **No library/actor distinction.** Libraries (`threejs-library`, `jsonc-parser-library`) and actors
  (`ai-coding-agent`) are all `external` components. A static dependency on a library and a runtime
  interaction with an actor are different kinds, and the split of `calls` (Q6) would make that visible.
- **No purpose-level interface.** Exegra's specification is its main input and output, yet the
  specification file appears inside `persistence` as a component (`specification-file`). At L0 the spec
  text is a store that Exegra owns. That is correct, but it should be a data element with records, not a
  "component" with zero modules.

### 5.2 Level 1: the six subsystems

Derived interactions: 38 edges over all kinds and 35 over dependency kinds; 179 relationships are internal
to a subsystem.

Largest edges by witness count:

| Edge | Witnesses |
|---|---|
| application → semantic-core | 39 (calls 25, reads 7, submits-edits 5, subscribes 1, observes 1) |
| tooling → semantic-core | 21 (calls 19, reads 1, depends-on 1) |
| agent-interface → semantic-core | 16 (calls 15, submits-edits 1) |
| tooling → persistence | 12 (calls 4, writes 4, data-flow 2, reads 1, generates 1) |
| visualization → application | 11 (calls 10, subscribes 1) |
| application → persistence | 8 |

**Layering check (dependency kinds):** one strongly connected component,
`{application, visualization, agent-interface, tooling}`. Its edges, and their causes (section 1.4):

| Edge | Cause | Class |
|---|---|---|
| `visualization → application` (11) | `src/app/main.js`, the composition root, is a module of `visual-interaction`; 9 of the witnesses are "Mounts …" | representational |
| `application → visualization` (4) | the session drives the projection and the layout | intrinsic |
| `tooling → agent-interface` (1) | `test-suites-calls-agent-cli` | perspective mixing |
| `agent-interface → tooling` (5) | the CLI runs the verification pipeline, the generators and others | intrinsic |

**What L1 communicates, once the representational causes are removed:**
- the semantic core at the bottom;
- application, visualization, agent CLI and tooling as clients of it;
- persistence as the boundary to disk.

That matches `docs/architecture.md`'s dependency table, which is today *asserted* there, not derived. The
claim `core-independent-of-ui` (`spec.jsonc:14931`) states one direction of it, against a hand-listed set of
12 targets. Four top-level components lie outside that list (claims audit).

**Abstracted at L1:** the 179 internal relationships, and every behaviour. No subsystem has a behaviour,
so L1 has no behavioural content at all. That is the main reason L1 is not independently coherent today.
The other reason is that only `semantic-core` states responsibilities.

### 5.3 Level 2: inside `semantic-core`

`semantic-core` has 41 children and no intermediate level. A reader expanding it gets a flat 41-node
graph. To show what a semantic decomposition looks like, and how the derived quotient guides it, a
candidate grouping was evaluated. It is a proposal, not a finding about the code.

| Candidate block | Members |
|---|---|
| model-kernel | metamodel, parser, model-derivation, model-hash, hash-binding, stable-serialization, lean-call-boundary, derivation-cache, spec-layers, queries, expression-language |
| editing | transactions |
| well-formedness | validator, integrity-rules, generation-readiness, data-model, contract-conformance, machine-coverage |
| verdicts | claim-evaluator, claim-method-registry, claim-strength, metric-claims, proof-export, reader-pages |
| simulation | simulation-engine, simulation-contract, fault-model, exhaustive-explorer, formal-semantics, lts-foundation, resource-model, workload-model, performance-metrics, self-model-replay, plus the 7 planned simulation and refinement components |

**First attempt (DEMONSTRATED):**
- Of the 99 dependency relationships inside `semantic-core`, 46 are internal to a block and 53 cross
  blocks.
- One cycle covers four blocks: `{model-kernel, well-formedness, verdicts, simulation}`.

The derived witnesses name the back edges exactly:
- `parser-reads-claim-method-registry` and `validator-reads-claim-method-registry`: the registry is
  meta-model data, so it belongs with the meta-model;
- `spec-layers-calls-validator` and `spec-layers-calls-generation-readiness`: layer analysis orchestrates
  validation, so it sits above the kernel;
- `lean-call-boundary-calls-formal-semantics`: the call boundary is a transport shared by model derivation
  and the engine, which makes it a connector;
- `validator-calls-metric-claims` and `integrity-rules-calls-proof-export`: validation reaching into claim
  machinery, and an integrity tool reusing the Lake runner.

**Second attempt (DEMONSTRATED):** with the registry moved to the kernel and layer analysis moved to
well-formedness, two small cycles remain:
- `{model-kernel, simulation}`, solely through `lean-call-boundary → formal-semantics`;
- `{well-formedness, verdicts}`, through the two calls named above.

Each is now one or two named relationships, which is the information an architect needs to decide whether
the coupling is intrinsic or a misplacement.

This is the intended workflow: hierarchies are declared, and the derived quotient tells you, with
witnesses, where a declared boundary leaks. The self-specification cannot support it today because the
quotient, its witnesses and the cycle check do not exist inside Exegra. They were computed for this audit by
a script outside it.

### 5.4 Level 3 and below: components, modules and functions

- **Components to modules.** 237 module entries over 72 components; 236 distinct paths, all of which exist.
  The import graph between those files (349 import edges, regex extraction, DEMONSTRATED by the derivation
  audit) gives a level-3 fact base that Exegra does not hold.
- **Lifted to components and compared with the declared relationships:**
  - **9 component pairs import without any declared relationship.** Examples:
    `simulation-contract → generation-readiness` (`pools.js → constructs.js`), `spec-store → hash-binding`,
    and `generation-readiness → contract-conformance` (3 imports of `type-expr.js`). One more pair
    (`generation-readiness → validator`) has only the reverse declared.
  - **140 declared pairs have no import in that direction.** 70 of them involve an external or file
    component; most of the rest are callback and subscription wiring through `main.js` and the session,
    which a static import graph cannot see.
- **Drift.** The assumption `relationships-match-imports` (`spec.jsonc:14841`), cited by 11 structural
  claims, records 12 and 121 at its last correction. It has drifted in both directions with no check. This
  is the textbook case for extracted facts (static dependencies, checked) next to declared facts (runtime
  wiring, optionally confirmed by observed traffic).
- **Functions.** No source function or symbol is an element. Behaviours attach at module or component
  granularity. Level 4 does not exist in the model.

### 5.5 Mixed-scale representations

**Persistence expanded, everything else collapsed** (dependency kinds, DEMONSTRATED): 49 edges. The save
path becomes visible as the chain
- `application → persistence-client` (3)
- `persistence-client → dev-server-plugin` (1)
- `dev-server-plugin → workspace-service` (1)
- `workspace-service → specification-file / layout-file / recorded-results-file / generated-artifacts`
  (writes)

Three side entries also appear:
- `agent-interface → workspace-service` (1): the CLI writes directly;
- `tooling → specification-file` (4);
- `tooling → spec-store`.

That is a correct and informative mixed-scale picture, and every edge in it is witnessed. Two things it
cannot say today:
1. Whether `persistence-client`'s outgoing edge realises the same `write-file` contract as the coarse
   `application → persistence` edge. Contracts do not lift, because bundles keep the first relationship.
2. Whether the data-file "components" are stores. They are drawn as components that receive `writes`.

**Semantic core expanded to the candidate blocks, everything else collapsed:** 64 edges (5.3). The tangle
inside the core is localised to the named witnesses, and the clients' fan-in is distributed per block: for
example, `application` reaches `model-kernel` 14 times, `editing` 10 times and `verdicts` 7 times. A reader
sees *which part* of the core each client uses, which the L1 edge `application → semantic-core (39)` hides.

### 5.6 End-to-end operations at several scales

**(a) A visual edit (`visual-edit-flow`, `spec.jsonc:13762`).** The scenario runs 10 behaviours on 10
leaves.

- **L2 (leaves):**
  - `visual-interaction` submits an operation to `transactions`;
  - `transactions` calls `parser` and `validator`;
  - `transactions` commits and notifies `session`;
  - `session` calls `projection-system`, which projects to `scene-renderer`;
  - `session` publishes to `inspector` and `source-editor`;
  - `session` emits `save-requested` (after 1) to `workspace-service`, which answers `save-succeeded`.
  - Every hop but the last two has a declared relationship. **`session ↔ workspace-service` has none**
    (DEMONSTRATED; 3 of 121 cross-subject emit/consume pairs are unwitnessed, and all three are on this save
    path).
- **L1:**
  - `visualization → semantic-core` (submits-edits);
  - `semantic-core` internal (parse, validate, commit);
  - `semantic-core → application` (commit notification, a `data-flow` witness);
  - `application → visualization` (projection);
  - `application → persistence` (save);
  - `persistence → application` (save result).
  - Every L1 hop **is** witnessed: the save hop lifts onto `application → persistence`, which exists
    because of `session-calls-persistence-client`.
- **Consistency verdict:**
  - The L1 picture is structurally consistent.
  - The L2 picture is not: the scenario's save hop skips `persistence-client` and `dev-server-plugin`.
  - The L1 consistency is an artefact of existential lifting over a *different* witness.
  - This is exactly why V5 must be checked on the base, and why `flows.js:113-141` (which classifies a
    message by looking for a *scene* edge) is unsound under collapse. Collapsed, it would call this message
    `edge`. Expanded, `undeclared`.
  - The scenario is legitimately a *mixed-scale behavioural model*: persistence is abstracted by
    `workspace-flow`. It is valid only if `workspace-flow` is shown to abstract the composed persistence
    machines with `ws-*` and `write-file-*` hidden (V6), and today the two models disagree on the initial
    disk hash.

**(b) An agent command (`cli-apply`, `spec.jsonc:14499`).**
- L2: `agent-cli` sends `ws-read`, `ws-write` and `ws-write-done` events to `workspace-service`
  (`cli-process-flow` with `workspace-disk-flow`).
- L1: `agent-interface → persistence`, witnessed by `agent-cli-calls-workspace-service`.
- L0: entirely internal to exegra, apart from the `ai-coding-agent → exegra` edge and the
  `exegra → filesystem` write.
- Consistent at all three levels structurally.
- Behaviourally, the hop is untyped. The `write-file` contract declared on the in-process workspace hop is
  never checked, because the `ws-*` events carry no contract (V7 fails).
- At L1 the coarse edge would show `contracts: {write-file}` once contracts become a summary attribute, and
  that would assert a protocol the base does not establish. The coarse view must show the edge's contract
  as "declared, not conformed".

**(c) Commit re-evaluates claims (`commit-reevaluates-claims`).**
- Behaviours:
  - `project-session-flow` and `session-claims-flow` (session);
  - `persistence-client-flow`, `dev-server-flow` and `workspace-disk-flow` (persistence);
  - `project-history-flow` (transactions);
  - `claim-evaluation-flow` (claim-evaluator).
- `claim-evaluation-flow` emits `claim-scenarios-run`, but `simulation-engine` has no behaviour in the
  scenario. The declared relationship `claim-evaluator-calls-simulation-engine` (with contract
  `run-scenario`) is therefore represented, in this scenario, by an emit that no element consumes.
- The scenario's environment silently abstracts the engine away. A declared behavioural cut, with "the
  engine is environment: assume `run-scenario` answers", would make that an explicit, checkable
  environment assumption instead of an omission.

### 5.7 Where the current model prevents an accurate multiscale representation of Exegra

1. The system is not an element, and people are not actors (5.1).
2. One unnamed hierarchy, one level deep; composites are a separate kind, so intermediate levels inside
   `semantic-core` cannot be added without making them `subsystem`s with no code, ports or behaviour (5.3).
3. Coarse interactions, their witnesses and their kinds are not model facts (5.2, 5.5).
4. `calls` conflates imports, invocations, notifications and lifecycle, so lifted kinds mislead (1.4).
5. Data files are components, not stores, and flows carry no records (`carries` unused).
6. Behaviour exists only on leaves. Scenarios abstract regions without saying so. Same-subject
   alternative machines disagree: `session-flow` vs `project-session-flow`, `write-endpoint-flow` vs
   `dev-server-flow`, `diskHash = h2` vs `diskSpec = h1` (5.6).
7. The module→element map is not a function (`builtin-types.js`). The composition root is misplaced
   (`main.js`).
8. Static dependencies are declared by hand and have drifted from the code (5.4).

---

## 6. Is the model overfitted to Exegra?

### 6.1 A compiler

**Hierarchy:**
- `compiler` contains `frontend {lexer, parser, sema}`, `middle {ir, passes {inline, dce, …}}` and
  `backend {isel, regalloc, emit}`.
- Shared parts: `diagnostics` and `symbol-table`.

**Interactions:** mostly data. Each stage passes an IR type to the next (`carries: Tokens, AST, TypedAST,
IR, MIR, Asm`), and every stage writes `diagnostics`.

**What the model gives:**
- **Lifting.** `frontend → middle (carries TypedAST)`, `middle → backend (carries IR)`.
- **Shared parts.** `diagnostics` placed at the root, as a shared element with fan-in from every stage.
  The L1 view shows it as a sink, not as a tangle. The *concern* "error reporting" is a facet.
- **Behaviour is functional, not reactive.** Each stage is a function, and the composite's behaviour is
  function composition: `compile = emit ∘ … ∘ lex`. The coherence obligation for a composite is that its
  declared signature equals the composition of its children's signatures (types line up), and that its
  declared semantics, when given, is refined by the composition. This is the functional analogue of
  `M_X ⊑ A_X`.
- **Requirement on Exegra.** A composite needs **functional behaviour composition**, not only state
  machines. Exegra's `function` entity has typed parameters, bodies and examples, but functions are not
  attached to elements and do not compose along a hierarchy.
- **Repeated passes.** An optimisation pipeline iterates to a fixed point. That is a loop over a sequence
  of functions, which needs a dataflow-style composite (sequence, iterate), not a quotient. The base model
  must allow a composite's behaviour to be *declared* as a composition of children's functions.

### 6.2 A distributed application

**Hierarchies:**
- **Logical:** `shop {catalog, cart, checkout {orders, payments}}`, with `orders-db` and `payments-db` as
  stores.
- **Deployment:** `region-eu {cluster-a {node-1, node-2}}`.
- **Interactions:** logical `invokes` (checkout → payments), asynchronous `publishes` (orders →
  `order-events` topic), and deployment `network-link` (node-1 ↔ node-2, with latency).

**What the model gives:**
- **Two hierarchies over the same elements.** Services are placed on nodes, and each perspective is a
  quotient of one base.
- **Realisation maps.** The logical `checkout → payments` is realised by a deployment path. A fault at a
  deployment block ("node-2 dies") lifts to the logical level as "payments unavailable" through the
  realisation map. This is **fault abstraction**, and it requires `failureMode.target` (today a component
  or relationship) to lift with the cut and through realisation.
- **Delivery guarantees.** At-least-once delivery on `order-events` must survive lifting: the coarse edge
  `checkout ⇢ fulfilment` carries `delivery: at-least-once` as a summarised attribute (a meet over the
  witnesses' guarantees), so a coarse reader sees that duplicates are possible.
- **Requirement on Exegra.** Multiple named hierarchies, and realisation maps between them. Exegra's
  `link` entity is already a deployment interaction with `from`, `to` and `latency`. It needs to become an
  interaction in a deployment hierarchy rather than a separate edge construct.

### 6.3 An event-driven system

**Elements:** producers (`sensor-gateway`), a broker with topics (`telemetry`, `alerts`), and consumers
(`aggregator`, `notifier`).

**Interactions:** `publishes` to a topic and `subscribes` from a topic.

**What the model gives:**
- **Connectors.** Topics are **connectors**. The coarse view either keeps the broker as a hub or contracts
  `publishes · subscribes` into `sensor-gateway ⇢ aggregator (notifies, via telemetry)` (3.8). Both are
  correct, as different coarsenings.
- **Hiding.** The choreography's end-to-end behaviour is `(gateway ∥ broker ∥ aggregator ∥ notifier) \
  {internal topics}`, and hiding gives exactly the externally visible alert behaviour.
- **Order.** Per-topic order (`ordered` on a link, or partitions) must be an attribute of the connector.
  Order-dependent claims are stated over it.
- **Requirement on Exegra.** First-class connectors and path contraction. Exegra has the `publishes` and
  `subscribes` kinds, and `link.ordered`, but no connector element and no contraction rule.

### 6.4 Conclusion

The core is fact base, hierarchies, cuts, existential lifting with witnesses, boundaries and derived
interfaces, composition with hiding, and refinement. It fits all three systems. They add four requirements
that Exegra's own architecture does not stress:
1. functional behaviour composition;
2. several hierarchies with realisation maps between them;
3. fault abstraction through realisation;
4. connectors with path contraction.

All four are in the roadmap (C2, C8, C9), so the direction is not specific to Exegra.

---

## 7. Gap analysis

Classes:
- **Foundational:** without it, multiscale semantics cannot be stated.
- **Major:** a property in section 2 cannot hold.
- **Supporting:** it degrades fidelity or usability.

### G1. No abstraction structure as a semantic object (Foundational)

| Field | Content |
|---|---|
| Missing capability | Named laminar hierarchies of any depth; the system as root element; cuts; abstraction maps; composites as ordinary elements. |
| Evidence | `component.parent` is a single ref to a `subsystem` (`metamodel.json:110-116`, `validate.js:70-76`); 6 subsystems, all roots, one level (DEMONSTRATED); `system` is a separate singleton; `tags`, `owner`, `trustZone` (0 uses) and `runsIn` (vocabulary) are ungoverned grouping attributes (structure audit §1c). |
| Why it blocks | Every multiscale property is defined relative to a cut of a hierarchy (2.2). With one implicit level there is nothing to zoom through, and perspectives cannot coexist. |
| Underlying cause | Containment was introduced as a grouping aid for the scene ("kind 'subsystem' marks a component that contains other components"), not as an abstraction relation. |
| Change | Generalise `parent` into named hierarchies over elements. Make "composite" derived. Make the system an element. Add a `cut` construct used by views and scenarios. |
| Related | Prerequisite for G2, G3, G6, G9 and G10. |
| Verification | A specification declaring two hierarchies of depth ≥ 3 validates; every element maps to exactly one ancestor on every declared cut; lift through an intermediate cut equals the direct lift on every cut pair of the self-spec (property test). |
| Proof obligations | P1 (cut map well defined), P2 (composition of abstraction maps). |

### G2. Coarse facts are drawn, not derived (Foundational)

| Field | Content |
|---|---|
| Missing capability | Quotient interactions as model facts, with witness sets and homomorphic summaries, readable by claims, rules and views. |
| Evidence | Lifting and bundling exist only in `projections.js:186-311`; a bundle is backed by its first relationship (`:291-311`) and loses labels (`:310`); `componentGraph` never lifts (`query.js:109-123`); `flows.js:113-141` classifies messages against scene edges. 0 of 350 relationships touch a subsystem (DEMONSTRATED). |
| Why it blocks | Fidelity, boundary preservation, recoverability and cross-scale consistency all need coarse facts that are functions of the base. Today two consumers compute two different coarse semantics, and neither keeps witnesses. |
| Underlying cause | The derivation pipeline stops at entities, refs and expressions (`Model.lean:867-877`). Derived relations exist (`integrityRelation`) but are evaluated per rule and never stored. |
| Change | A derived-fact stratum. Generalise integrity relations into derivation rules whose tuples are stored, with witnesses, as model facts. Move lifting from `projections.js` into rules. Projections consume the derived quotient. |
| Related | Needs G1 and G4. Enables G3, G5, G9, G10 and G8. |
| Verification | For the self-spec at L1, the derived quotient equals the 38 edges and counts in 5.2; every derived edge's witnesses re-lift to it; the structural projection's edges for any collapse set equal the derived quotient for the corresponding cut; selecting a coarse edge lists all witnesses. |
| Proof obligations | P3 (lift functoriality), P4 (absence transfer), P7 (recoverability). |

### G3. No composite interface; ports and contracts are unwired (Major)

| Field | Content |
|---|---|
| Missing capability | Derived boundary and interface of any composite; declared-versus-derived interface checks; port-level wiring; contract realisation along multi-hop paths. |
| Evidence | 15 ports on 9 components, 0 relationships with a port endpoint, no port/contract compatibility rule (structure audit §4; composition F3); 8 of 16 contracts used by nothing; no subsystem has ports or contracts; `write-file` declared on 5 ports and 3 relationships but its in-process hop is untyped (behaviour audit §6). |
| Why it blocks | Boundary preservation and "external contracts related to internal realisations" (Q8) need the boundary to be computed and compared with what is declared. |
| Underlying cause | Ports, contracts and relationships are three independent declarations with no derivation among them. |
| Change | Derive `∂X` and the derived interface. Check declared ports against it (V3). Allow relationships to end at ports. Represent a contract's realisation path. Mark opaque elements. |
| Related | Needs G2. Feeds G5 and G7. |
| Verification | On the self-spec: every declared port either matches a derived boundary group or is reported; every boundary interaction of a composite with a declared interface is matched or reported; the `write-file` hop is reported as declared-but-not-conformed until its events carry the contract. |
| Proof obligations | P5 (boundary characterisation: a derived interface depends only on `∂X`). |

### G4. Interaction kinds are overloaded and carry no lifting semantics (Major)

| Field | Content |
|---|---|
| Missing capability | A kind taxonomy with dependency class, direction semantics and coarsening; a split of `calls`; data carried by flows; one interaction primitive in place of several edge-like constructs. |
| Evidence | `calls` is 231 of 350 relationships; its descriptions say "Imports …" (4), "Mounts …" (9 in `visual-interaction` alone) and "Listens …"; the metamodel kinds carry only a `dependency` flag (`metamodel.json:69-76`); `carries` is unused (0 of 350); `link`, `copy.heldBy`, `record.owner`, `failureMode.target` and `emit.to` are other edge-like constructs; the layout uses every edge as a dependency (`layout/solve.js:46`). |
| Why it blocks | Lifting preserves kinds (V4). Overloaded kinds lift into misleading coarse edges and spurious cycles (1.4, 5.2). |
| Underlying cause | Kinds were chosen for drawing (line style and colour in the vocabulary) more than for semantics. |
| Change | A kind tree with lifting semantics, the four-way split of `calls`, `carries` linking flows to records and events, connectors as elements, and `link` as a deployment interaction. Migrate the self-spec's relationships by their descriptions. |
| Related | Prerequisite for G2's kind preservation and for G7's extracted static dependencies. |
| Verification | The self-spec's L1 dependency quotient, after migration, has no cycle caused by lifecycle, notification or test witnesses; every coarse edge's kind is a base kind or its declared coarsening. |
| Proof obligations | P3 extended to kind coarsening (lift commutes with label coarsening). |

### G5. Structure and behaviour are independent graphs (Foundational for behavioural preservation)

| Field | Content |
|---|---|
| Missing capability | Events owned by element or port interfaces; message interactions derived from behaviours; a coherence check (V5); behaviour on composites. |
| Evidence | Events have no owner, component or port (behaviour audit §4); 3 of 121 cross-subject emit/consume pairs have no relationship, all on the save path (DEMONSTRATED); no validator relates emits to relationships; 44 behaviours on 25 leaves and none on a subsystem; `flows.js` shows "no declared relationship" only as a display. |
| Why it blocks | Behavioural preservation needs one set of interactions that both structure and behaviour are views of; otherwise a coarse view can be structurally consistent and behaviourally false (5.6a). |
| Underlying cause | Behaviours were added as a simulation layer over scenarios, not as the behaviour of structural elements. |
| Change | Event ownership through the producing element's interface. Derive message interactions from emit/consume pairs (V5 becomes "derived ⊆ declared or extracted", or declared message relationships become derived). Allow behaviours on composites. Treat cross-element state reads as interactions. |
| Related | Needs G2 and G3. Prerequisite for G6. |
| Verification | V5 reported for the self-spec's three save-path pairs; after the fix, 0 unwitnessed pairs; a guard reading another element's variable without an exported observable is a validation error. |
| Proof obligations | P8 (derived message interactions are exactly the cross-element emit/consume pairs). |

### G6. No behavioural composition with interfaces, hiding or multi-level refinement (Foundational)

| Field | Content |
|---|---|
| Missing capability | `∥` on separable parts, hiding of internal events, composite derived behaviour, refinement `M_X ⊑ A_X` over member sets, behavioural cuts declared in scenarios, and reconciliation of same-subject alternative machines. |
| Evidence | Scenarios are closed lists (`docs/simulation.md:85`); refinement is one level (`validate.js:196-199`), requires identical emits (`refinement.js:353-355`), and is used by 0 claims in the self-spec; `Core/*` is whole-system only (behaviour audit §9); same-subject alternatives never co-run and disagree (`h1`/`h2`); the depth plan couples the run level to the view's collapse state (`docs/simulation.md:1076`, WG-4666). |
| Why it blocks | Behavioural preservation, recursive decomposition of behaviour, and mixed-scale simulation all need composition and hiding. |
| Underlying cause | The semantics was built as a whole-scenario interpreter. The foundations work (M2, `Core/Behav.lean`) is moving it to a relational calculus, but still for whole systems. |
| Change | Interfaces per machine (the composition team's milestone 1); `∥` and hiding in the calculus; composite derived behaviour; a refinement check that hides internal events and maps a set of member machines; scenarios declare their behavioural cut and environment; alternative machines of one element become one machine per level, related by refinement. |
| Related | Needs G5. Shares foundations with the 2026-11-26 composition and foundations milestones. Do not duplicate: build on M2's `Behav` calculus. |
| Verification | `workspace-flow` is checked as an abstraction of the three composed persistence machines, with `ws-*` hidden: either a certificate or a counterexample (today the initial hash mismatch must surface); the same claim gives the same verdict at two behavioural cuts where the abstraction is valid. |
| Proof obligations | P9–P12 (composition laws, hiding laws, refinement preorder and congruence, safety transfer). |

### G7. No provenance or knowledge status; architecture facts are hand-declared and drift (Major)

| Field | Content |
|---|---|
| Missing capability | Provenance per fact (declared, extracted, observed, derived, assumed); extracted static dependencies; observed runtime interactions; opaque and unknown elements; claims that distinguish code-backed from declared facts. |
| Evidence | Only module paths are checked against code (`tools/traceability.js:87-127`); 9 undeclared import pairs and 140 declared pairs without imports (DEMONSTRATED), against 12 and 121 recorded in `relationships-match-imports` (`spec.jsonc:14841`), which 11 structural claims cite and nothing checks; `claim-strength` grades every structural check `bound` whatever its source (`claim-strength.js:153-154`); `traffic-recorder` and `self-model-replay` exist but feed no structural facts. |
| Why it blocks | Traceability and non-redundancy require derived facts to rest on authoritative facts. Uncertainty must be visible (Q14). |
| Underlying cause | No extraction layer, and the core must stay Node-free (`docs/module-contracts.md`), so extraction has nowhere to live in the core. |
| Change | An extractor in `tools/` producing a fact file (modules, imports, exports) keyed by source digest; the core reads it as extracted facts; static-dependency relationships are checked against it (or derived from it); observed interactions from recorded traffic; provenance is shown in views and claim scopes; the assumption becomes a check. |
| Related | Needs G4 (an `imports` kind). Feeds G2 (witness provenance) and G8. |
| Verification | `relationships-match-imports` is replaced by a check whose result on the current tree lists the 9 + 1 pairs; every coarse edge reports its witnesses' provenance mix; an extracted import with no declared counterpart is a diagnostic. |
| Proof obligations | None in Lean. Extractor soundness is a trusted, tested component (10.3). |

### G8. No fact-level dependency tracking for derived facts and claims (Major)

| Field | Content |
|---|---|
| Missing capability | Read sets and query footprints on derived facts and claim results; invalidation by intersection with an edit's affected set; per-claim freshness. |
| Evidence | Claim results record `involved` only (`claims.js:362`); all claims are re-evaluated on every semantic change (`session.js:879`); `affected` is computed and not used (`project.js:206`); one tree stamp makes all 631 recorded results stale on any edit (claims audit §4); the derivation cache keys on the whole text (`derivation-cache.js:111-116`). |
| Why it blocks | "How do changes propagate into derived representations" (Q13). Without footprints, a derived quotient can only be recomputed whole, and traceability from a claim to the facts that justify it is absent. |
| Underlying cause | Results are computed by procedures that do not report what they read. |
| Change | Derivation rules and claim evaluators return footprints. Invalidation intersects footprints with `affected`. Evidence freshness is keyed by the footprint of its subject, which subsumes the architecture assessment's per-guarantee dependency graph (2026-11-26 architecture §2.5). |
| Related | Needs G2. Supports G10 and G9. |
| Verification | Editing one relationship re-evaluates exactly the claims and derived edges whose footprint contains it (test on the self-spec); incremental equals full evaluation over a randomised edit sequence. |
| Proof obligations | P13 (incremental equals full re-derivation, for stratified rules). |

### G9. Claims are not level-aware; assumptions are inert (Major)

| Field | Content |
|---|---|
| Missing capability | Claims bound to a hierarchy and cut; evaluation on the derived quotient with the transfer rules of 3.3; complement selectors ("outside X"); "not expressible at this level"; verdicts conditioned on assumptions. |
| Evidence | Structural claims run on the leaf graph (`query.js:109-123`); subjects are inert (`claims.js:242`, `362`); `core-independent-of-ui` enumerates 12 targets by hand and misses 4 top-level components (claims audit §3); `reachable` has no path-witness semantics; assumptions are copied, never read (`claims.js:253`; composition F1, still true). |
| Why it blocks | Independent coherence (a claim stated at a level must be evaluable there) and cross-scale consistency (claims at two levels must not contradict). |
| Underlying cause | Claims were designed against one flat graph. |
| Change | A `level` on structural claims; evaluators over `F/C`; absence, acyclicity and may-reachability per 3.3; complement selectors; result meanings for "verified under open assumptions" (from the composition milestone 4) and "not expressible at this level". |
| Related | Needs G1, G2 and G8. |
| Verification | `core-independent-of-ui` restated as "at the logical L1 cut, no dependency-class edge from semantic-core to anything outside {semantic-core, its libraries}" gives the same verdict as the leaf-level enumeration, plus the 4 missed components; a constructed spurious coarse path yields may-reachable, not verified-reachable. |
| Proof obligations | P4–P6. |

### G10. Views compute semantics, and presentation state drives semantics (Supporting)

| Field | Content |
|---|---|
| Missing capability | Views as `(hierarchy, cut, coarsening, filter)`; cuts in the view entity; path summaries or counted drops for filters; bundles that expose witnesses; message classification on the semantic quotient; one entity→element mapping in the core. |
| Evidence | Collapse is per project, not per view (`session.js:766-778`); filters drop connections silently (`projections.js:285`, notes only for hidden at `:182`); the bundle backs onto its first member (`:291`); "N inside" ignores filters (`:252`); the mapping is written three times (`projections.js:355-367`, `session.js:687-706`, `flows.js:84-91`); the depth plan follows the collapse state (WG-4666). |
| Why it blocks | The visualization must emerge from the semantic model. Today part of the semantic model emerges from the visualization. |
| Underlying cause | The scene projection was the only consumer of coarse facts, so it grew the logic. |
| Change | Projections consume the derived stratum. Cuts live in views (semantic) and collapse stays interaction state that selects a cut. Filters report what they cut. `flows.js` and claim focus use core queries. |
| Related | Needs G2. Benefits from G3, G5 and G7. |
| Verification | No lifting or bundling code remains in `src/core/projections.js`; for every view and collapse state, scene edges equal derived quotient edges after filtering; a filter that hides a path element produces a counted note or a labelled path summary. |
| Proof obligations | None beyond P3. The projection is presentation. |

### G11. Implementation correspondence stops at the component (Major for traceability)

| Field | Content |
|---|---|
| Missing capability | Module elements (and optionally exported symbols) as the finest declared grain; a total, functional module→element map; correct placement of composition roots and shared files. |
| Evidence | `implementation.modules` is a list of path strings; no module, function or symbol entity (`metamodel.json:127-136`); `builtin-types.js` is claimed twice and `traceability.js` does not report it (`:118`); `main.js` is filed under `visual-interaction` "because traceability assigns each file to one component" (spec unknowns); `formal/` and `engine/` are outside the traceability surface. |
| Why it blocks | Recoverability down to code. Level 3 and level 4 cannot be represented. |
| Underlying cause | Traceability was designed as a coverage check, not as the bottom level of a hierarchy. |
| Change | Modules become elements in the logical hierarchy (leaves under components), populated by the extractor. The map must be a function: shared files go to a shared element. Composition roots become an element above the subsystems they wire. Lean and Rust sources join the surface. |
| Related | Needs G1 and G7. |
| Verification | Every surface file belongs to exactly one element (error otherwise); the self-spec's L1 dependency quotient has no witness from a composition root inside a peer subsystem. |
| Proof obligations | None in Lean. |

### G12. The self-specification lacks intermediate levels and composite content (Self-specification)

| Field | Content |
|---|---|
| Missing capability | A logical hierarchy of Exegra with coherent levels, purposes and interfaces at each. |
| Evidence | `semantic-core` is flat with 41 children; only `semantic-core` has responsibilities; no subsystem has a behaviour or ports; candidate groupings show where boundaries leak (5.3); data files are modelled as components (5.1). |
| Why it blocks | Exegra cannot demonstrate multiscale modeling on its primary case study. |
| Underlying cause | The structural vocabulary (G1, G4) gave no reason to add levels. |
| Change | After G1–G4 and G7: add the system root and actors, intermediate blocks inside `semantic-core` evaluated by derived indicators, store elements for files, the composition-root element, and composite purposes and declared interfaces. All of it through transactions. |
| Related | Needs G1–G4, G7 and G11. |
| Verification | Every level of the self-spec's logical hierarchy satisfies the coherence conditions of 2.5; the L1 dependency quotient is acyclic, or every remaining cycle is recorded as an intrinsic coupling with its witnesses. |
| Proof obligations | None. It is an application of the others. |

---

## 8. Dependency-ordered roadmap of capabilities

Each capability has an independently meaningful outcome. They are ordered by what unblocks what; there is
no notion of size or duration here.

```
C1 Hierarchies & cuts ─────┐
C2 Interaction taxonomy ───┼──> C3 Derived-fact stratum ──┬──> C4 Level-aware claims ──┐
C6 Code-fact extraction ───┘    (witnesses, provenance)   ├──> C5 Composite interfaces ├──> C7 Structure–behaviour coherence ──> C8 Behavioural composition & refinement
   (needs C2; feeds C3)                                   ├──> C9 Semantic views        │
                                                          └──> C10 Change propagation ─┘
C11 Self-spec restructure  (after C1–C3, C6; refined after C5, C7, C8)
C12 Lean grounding of multiscale semantics  (structural part after C1–C3; behavioural part with C8)
```

- **C1. Hierarchies, elements and cuts.**
  - Named laminar hierarchies, the system as an element, composites derived, facets, and a cut construct.
  - Reads and writes the meta-model, the parser and Lean model derivation (hierarchy well-formedness), the
    validator, and `query.js`.
  - Outcome: a specification can say what its levels are.
- **C2. Interaction taxonomy and unified interaction primitive.**
  - The kind tree with dependency class, direction and coarsening; the split of `calls`; `carries`;
    connectors; `link` as a deployment interaction.
  - Outcome: a specification can say what its edges mean under abstraction.
- **C3. Derived-fact stratum.**
  - Derivation rules generalising `integrityRelations`, storing tuples as model facts with witnesses and
    provenance.
  - Built-in rules: quotient per cut, boundary, derived interface, and coherence diagnostics V1, V2 and V4.
  - The Lean least-model semantics extends to stored tuples.
  - Outcome: every coarse fact is computed and traceable.
- **C4. Level-aware claims.**
  - Structural claims with a level; evaluators over `F/C` with the transfer rules; complement selectors;
    "not expressible at this level".
  - Outcome: claims can be stated at any level, and verdicts across levels cannot contradict.
- **C5. Composite interfaces.**
  - Declared-versus-derived interface checks (V3), relationships ending at ports, contract realisation
    paths (V7), and opaque elements.
  - Outcome: boundaries are checked, not drawn.
- **C6. Code-fact extraction and correspondence.**
  - An extractor in `tools/` for modules, imports and exports, keyed by digest.
  - Observed interactions from recorded traffic.
  - Module elements; a functional module→element map.
  - The `relationships-match-imports` assumption replaced by a check.
  - Outcome: static structure is code-backed, and runtime wiring is marked declared or observed.
- **C7. Structure–behaviour coherence.**
  - Event ownership through interfaces; message interactions derived from behaviours; V5; behaviours on
    composites; cross-element reads as interactions.
  - Outcome: one interaction set underlies both structure and behaviour.
- **C8. Behavioural composition and multi-level refinement.**
  - Built on the M2 typed calculus and the composition team's interface milestone: interfaces, `∥`,
    hiding, composite derived behaviour, a member-set refinement check with hiding (V6), behavioural cuts
    declared in scenarios, and reconciliation of same-subject alternatives.
  - Outcome: behaviour can be viewed and checked at any level.
- **C9. Semantic views.**
  - Views carry `(hierarchy, cut, coarsening, filter)`; projections consume C3; bundles expose witnesses;
    filters summarise or count; `flows.js` and focus logic use core queries; WG-4666's level selection
    reads the scenario's declared cut.
  - Outcome: the visualization emerges from the semantic model.
- **C10. Change propagation by footprint.**
  - Footprints on derived facts and claim results, invalidation by `affected`, and per-claim freshness.
  - Outcome: an edit updates exactly what depends on it.
- **C11. Self-specification restructure.**
  - Applies C1–C10 to Exegra through transactions: the root and actors, intermediate levels in
    `semantic-core`, stores, the composition-root element, kind migration, composite interfaces and
    abstract behaviours (persistence first, because 5.6 already shows its two levels).
  - Outcome: Exegra demonstrates multiscale modeling on itself.
- **C12. Formal grounding of multiscale semantics.** Section 10.

The current capabilities are preserved throughout:
- relationships stay, as declared interactions;
- subsystems stay, as hierarchy blocks;
- collapse stays, as interaction state selecting a cut;
- scenario closed worlds stay, as a declared cut plus environment.

No semantics is dropped silently. Each replacement in section 11 names what subsumes the replaced
construct.

---

## 9. Acceptance criteria per capability

Each criterion can be checked on this repository, by a test or a command whose output is compared.

**C1**
1. A specification declaring hierarchies `logical` (depth ≥ 3) and `deployment` validates. An element
   placed in two blocks of one hierarchy is a validation error with the element's id.
2. For every declared cut of the self-spec, every element maps to exactly one block (test).
3. Property test over random laminar hierarchies and cut pairs `C ≤ C'`: `α_{C'} = α_{C→C'} ∘ α_C`.
4. The system is an element, and existing specifications load with the system as the root of `logical`,
   unchanged otherwise (migration test over every `specs/*`).

**C2**
1. Every relationship kind declares a dependency class, a direction semantics and a coarsening parent;
   validation refuses a kind without them.
2. The self-spec's 231 `calls` are migrated to `imports`, `invokes`, `notifies` or `composes`, with the
   migration list reviewable, and no `calls` remains whose description begins "Imports" or "Mounts".
3. A `publishes`/`subscribes` pair through a connector contracts to `notifies` at a cut that hides the
   connector (test).
4. `link` entities load as interactions of kind `network-link` (migration test).

**C3**
1. For the self-spec at the L1 cut, the derived quotient has exactly the edges and witness counts of
   appendix A's output (golden).
2. For every derived edge, the union of its witnesses lifts to exactly that edge, and removing all
   witnesses removes it (property test).
3. Lifting to `C'` directly equals lifting to `C` then to `C'`, for all cut pairs of the self-spec
   (property test).
4. Derived facts are readable by integrity rules: the rule from the probe in 4.1, restated over derived
   facts, holds.
5. The Lean least-model meaning covers the stored tuples (`lake build` checks the theorem of P3 for the rule
   fragment used).

**C4**
1. A structural claim with `level: L1` is evaluated on the L1 quotient, and its scope text names the cut.
2. `core-independent-of-ui`, restated with a complement selector at L1, reports the same verdict over the
   same leaves plus the 4 previously unlisted top-level components.
3. On a constructed model with a spurious coarse path (3.3), `reachable` at the coarse level reports
   may-reachable, not verified.
4. A claim naming an element hidden at its declared cut yields "not expressible at this level".

**C5**
1. Every declared port of the self-spec is matched to a derived boundary group, or is reported.
2. A relationship can end at a port, and a `requires` port wired to a `requires` port is an error.
3. The `write-file` contract's realisation path is reported, with the untyped in-process hop flagged until
   its events carry the contract.
4. An opaque element's declared interface is used for lifting, and adding a member makes it an obligation
   (test).

**C6**
1. The extractor's fact file for this repository lists every import edge between surface files, and a
   change to one source file changes only that file's facts (digest test).
2. A check replaces `relationships-match-imports`: on the current tree it reports the 9 import pairs
   without relationships and the 1 reversed pair.
3. Every surface file belongs to exactly one element, so `builtin-types.js` is an error until placed.
4. Lean and Rust sources are in the traceability surface.

**C7**
1. Every event is owned by an element's or port's interface (validation).
2. Cross-element emit/consume pairs are derived. On the current self-spec, V5 reports exactly the 3
   save-path pairs.
3. A guard reading another element's variable that is not an exported observable is a validation error.
4. A behaviour can have a composite subject.

**C8**
1. In `Core`: an `Interface`, a `compose` on separable systems, `hide`, and trace inclusion, with theorems
   P9–P12 checked by `lake build`, standard axioms only.
2. A refinement check over a member set with hiding: `workspace-flow` against
   `persistence-client-flow ∥ dev-server-flow ∥ workspace-disk-flow` hiding `ws-*` and `write-file-*`
   returns a certificate or a counterexample. On today's spec, the initial hash mismatch is reported.
3. A scenario declares its behavioural cut and environment. A scenario whose omitted element is the target
   of an emitted event without an environment assumption gets a diagnostic. `commit-reevaluates-claims`
   reports `claim-scenarios-run`.
4. A claim gives the same verdict at two behavioural cuts where V6 holds (test).

**C9**
1. No lifting or bundling logic remains in `src/core/projections.js` (code check), and scene edges equal
   derived edges for every view and collapse set of the self-spec (property test).
2. Selecting a coarse edge shows all witnesses, with kinds, contracts and provenance.
3. A filter that hides an element on a path emits a counted note or a labelled path summary (test).
4. Message classification in `flows.js` gives the same verdict collapsed and expanded for the save hop of
   `visual-edit-flow` (`undeclared` in both until C7's fix).
5. Collapse state is per view.

**C10**
1. Every claim result and derived fact records a footprint.
2. Editing one relationship of the self-spec re-evaluates exactly the claims and derived facts whose
   footprint contains it (instrumented test).
3. Incremental equals full evaluation over a randomised sequence of 200 edits of the self-spec (property
   test).

**C11**
1. Each level of the self-spec's logical hierarchy meets 2.5's conditions 1–3 (rule check).
2. The L1 dependency quotient has no SCC, or each remaining SCC is recorded as an intrinsic coupling with
   its witnesses.
3. Persistence has a declared abstract behaviour refined by its members (C8 criterion 2 passes).
4. `validate`, `traceability` and `verify` pass per `AGENTS.md`.

**C12**: the criteria are the theorems listed in section 10.

---

## 10. Formal verification strategy for multiscale semantics

### 10.1 What must eventually be guaranteed

**About the semantic model (Lean):**

| Id | Statement |
|---|---|
| P1 | For a laminar hierarchy and a cut, `α_C` is a total function and maps each element to its unique ancestor-or-self on the cut. |
| P2 | Cut refinement composes: `C ≤ C' → α_{C'} = α_{C→C'} ∘ α_C`. |
| P3 | Lift functoriality: lifting edges, witness sets and any monoid-homomorphic summary commutes with composition of cuts, and with kind coarsening. |
| P4 | Absence transfer: no coarse `X → Y` edge of class `κ` ⇒ no base `κ` edge between their members. |
| P5 | Boundary characterisation: the derived interface of `X` is a function of `∂X` alone, and `∂` composes with cut refinement. |
| P6 | Reachability and acyclicity transfer, as stated in 3.3, including the spurious-path counterexample as a theorem that the converse fails. |
| P7 | Recoverability: decompose-then-recompose is the identity on the fact base. |
| P8 | Derived message interactions are exactly the cross-element emit/consume pairs of the composed behaviours. |
| P9 | `compose` is commutative and associative up to trace equivalence. |
| P10 | Hiding laws: `hide H₁ ∘ hide H₂ = hide (H₁ ∪ H₂)`, and hiding commutes with composition for events local to one side. |
| P11 | `⊑` is a preorder and a congruence for `compose` and `hide`. |
| P12 | Safety transfer: `M ⊑ A → A ⊨ φ → M ⊨ φ` for φ over the external alphabet; liveness only under an explicit fairness hypothesis. |
| P13 | Incremental re-derivation of stratified rules from footprints equals full re-derivation. |

**About correspondence with software:** these are not Lean theorems about the model.
- The extractor reports exactly the static imports of the files it reads. This is a trusted component:
  tested against a corpus, and differentially against a second parser where practical.
- Observed facts are samples. Their claims are "observed in these runs", with the existing scope
  discipline.
- Forward-simulation certificates checked against implementation traces, the
  `implementation-refinement` intent (WG-4679), are per-trace evidence. They give a theorem only where an
  implementation-level machine is itself in the calculus.

### 10.2 Where each obligation lives

- **P1–P7 and P13** are about finite relational structures and stratified rules. They belong in the same
  Lean development as `Integrity.lean`, which already gives stratified programs a least-model semantics with
  a reflective checker (`eval_iff`, `least_eq_table`). Lifting rules are stratified Datalog, so P3 and P4
  can be proved once for the rule fragment, and per specification by reflection where needed.
- **P8–P12** extend `Core/LTS.lean` and `Core/Behav.lean`. `LTS` is already relational. What is needed:
  - an interface structure on `Behav.Sys`;
  - a product of two systems over disjoint machine sets;
  - `hide` as relabelling to τ;
  - trace and simulation relations between two LTSs.
- `phase2_perm` (`Behav.lean:974`) is the within-step independence fact the product construction will
  rely on.

### 10.3 Design constraints so that verification stays possible

1. Derived facts are produced only by declarative rules with a least-model meaning. No JS procedure may
   produce a derived fact that claims or views rely on. Today's lifting in `projections.js` is the
   anti-pattern.
2. Derivation is deterministic and finite. Witness sets are finite and canonical (sorted by id).
3. No presentation input — collapse state, viewport, layout method — reaches derivation, claims or
   simulation. Cuts are declared data.
4. Summaries are monoid homomorphisms. A summary that is not, such as "first label", is presentation only.
5. Extracted and observed facts enter as data with provenance, so a theorem quantifies over "the given
   facts" and never over "the code".
6. Behavioural cuts and environments are explicit in scenarios, so a theorem about a scenario states the
   environment it assumes.

### 10.4 What not to require

Lean proofs are not a prerequisite for any capability C1–C11. Each capability ships with its acceptance
criteria (section 9) checked by tests and validation. The theorems strengthen the evidence behind those
criteria; they do not gate them. This keeps multiscale modeling independent of the WG-4785 port of the
verdict kernel, while constraint set 10.3 makes sure nothing built now has to be rewritten to be proved
later.

---

## 11. Existing constructs: retain, generalise, derive, consolidate, remove

| Construct | Disposition | Why, and what subsumes it |
|---|---|---|
| Text as authority, transactions, Lean model derivation, semantic hash | **Retain** | The foundation of the fact base. The hash must cover new hierarchy and cut declarations, which it does automatically as top-level data. |
| `component.parent`, `kind: subsystem` | **Generalise** | Into named laminar hierarchies; "composite" becomes derived; the system becomes the root. |
| `tags`, `owner`, `trustZone`, vocabulary `runsIn` | **Generalise** | Into facets, or into named hierarchies when laminar. |
| `relationship` | **Retain, as declared interaction**; **consolidate** `link`, and the edge roles of `copy.heldBy`, `record.owner`, `failureMode.target` and `emit.to`, under one interaction primitive with kinds | Removes parallel edge constructs that cannot lift together. |
| Relationship kind `calls` | **Consolidate** into `imports`, `invokes`, `notifies` and `composes` | Overloaded today (G4). |
| Relationship kinds' `dependency` flag | **Generalise** | Into dependency class, direction semantics and coarsening. |
| `relationship.carries` | **Retain and use** | Links flows to records and events (data lineage). |
| `port`, `contract` | **Retain**; **derive** composite interfaces; check declared against derived | G3. |
| `event` | **Retain**; **derive** its owner from interfaces | G5. |
| Message-kind relationships duplicated by behaviour emits | **Derive** from emit/consume pairs where behaviours exist | Non-redundancy. Declared only when no behaviour exists, and then checked by V5. |
| Subsystem-level relationships | **Derive**, never declare | Already not declared. They become model facts. |
| `behavior.refines` / `refinement`, `refinement.js` | **Generalise** | To member sets, hiding and multiple levels. The forward-simulation shape is kept. |
| One-level refinement restrictions (`validate.js:196-199`) | **Remove** once C8 lands | Replaced by refinement along the hierarchy. |
| Same-subject alternative machines | **Consolidate** | One behaviour per element per level, related by refinement. |
| `scenario.behaviors` closed list | **Generalise** | To a declared behavioural cut plus environment. A closed list is the special case "these leaves, empty environment". |
| `integrityRelation` | **Generalise** | Into derivation rules with stored tuples, witnesses and footprints. |
| `query.componentGraph`, `componentOf` | **Retain** for leaves; **generalise** to cuts | `componentsOf(entity)` becomes the one core mapping. |
| Lifting and bundling in `projections.js` | **Remove**, moved to derivation | The scene draws derived quotients. |
| Entity→component mapping in `session.js` and `flows.js` | **Remove**, replaced by core `componentsOf` | Three copies today. |
| `flows.js` classification against scene edges | **Remove**, replaced by classification on the semantic quotient | Unsound under collapse (5.6a). |
| Collapse, hidden and isolate state | **Retain as interaction state**; collapse selects a cut; per view | Presentation stays presentation. |
| `view.filter.within` | **Generalise** | Into a cut plus filter. |
| `assumption` `relationships-match-imports` | **Remove**, replaced by the C6 check | A decidable fact should be checked, not assumed. |
| Hand-enumerated `to` lists in claims | **Remove** where a complement selector expresses the statement | `core-independent-of-ui`. |
| `implementation.modules` | **Retain**; module paths become module elements (extracted) | Must be a function. |
| `implementation.trusts` | **Retain**, but give it a reader (the assumption-discharge work) or merge it with `claim.assumptions` | Read by no code today (claims audit §6). |
| `claim-strength` grounding | **Generalise** | To report witness provenance (declared, extracted, observed). |
| Tree-stamp freshness | **Generalise** | To footprint freshness (C10). |
| `function` entity | **Retain and attach** to elements; composite function composition | Section 6.1. |

---

## 12. Decisions for the owner

These choices change what gets built, and the evidence does not settle them.

1. **Several hierarchies, or one hierarchy plus facets?**
   - Section 6.2 argues that a distributed system needs a deployment hierarchy beside the logical one,
     with realisation maps.
   - The alternative is one logical hierarchy, with deployment as a facet. It is simpler, but it gives up
     fault abstraction through realisation.
   - Recommendation: several named hierarchies, with `logical` as the default and the only one the
     self-spec uses at first.
2. **Static dependencies: derived or checked?**
   - Extracted imports could *replace* declared `imports` relationships (strict non-redundancy) or *check*
     them (a declared set compared with an extracted set).
   - Recommendation: derive, and keep declared static dependencies only for code outside the extraction
     surface.
3. **Granularity floor.**
   - Modules as elements is the minimum needed for recoverability to code (G11).
   - Exported symbols or functions as elements is possible from the same extractor, but it multiplies the
     fact base.
   - Recommendation: modules now, symbols only where a behaviour or a function entity attaches.

---

## Appendix A. Quotient computation used in section 5

Run from the repository root with Node. It only reads the specification. The L2 grouping and the
second-attempt changes are those of section 5.3.

```js
const fs = require('fs');
const j = require('jsonc-parser').parse(fs.readFileSync('specs/exegra/spec.jsonc', 'utf8'));
const parent = Object.fromEntries(j.components.map((c) => [c.id, c.parent ?? null]));
const external = new Set(j.components.filter((c) => c.category === 'external').map((c) => c.id));
const DEP = new Set(['depends-on', 'calls', 'subscribes', 'reads', 'writes', 'submits-edits']);

// Existential lift of the declared relationships through an abstraction map.
function quotient(alpha, depOnly) {
  const edges = new Map(); let internal = 0;
  for (const r of j.relationships) {
    if (depOnly && !DEP.has(r.kind)) continue;
    const a = alpha(r.from), b = alpha(r.to);
    if (a === b) { internal++; continue; }
    const k = `${a} -> ${b}`;
    const e = edges.get(k) ?? { witnesses: [], kinds: {} };
    e.witnesses.push(r.id); e.kinds[r.kind] = (e.kinds[r.kind] ?? 0) + 1;
    edges.set(k, e);
  }
  return { edges, internal };
}

const L0 = (id) => (external.has(id) ? id : 'exegra');
const L1 = (id) => parent[id] ?? id;
const mixedPersistence = (id) => (parent[id] === 'persistence' ? id : L1(id));
// L2: map semantic-core children to the blocks of section 5.3, everything else as L1.
```

Strongly connected components were computed with Tarjan's algorithm over the resulting edge set. The
import-graph comparison (5.4) used a regex extraction of static, re-export, side-effect and dynamic imports
over the traceability surface. Bare specifiers were not lifted.
