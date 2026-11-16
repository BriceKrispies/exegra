# Vision

## What Exegra is for

A system specification usually exists as several artifacts that drift apart: prose documents, diagrams, tickets, tests, and the code. Exegra keeps one authoritative semantic representation of a system and makes every other representation a projection of it or an editor over it:

- the JSONC specification text
- the 3D scene of components and relationships
- the inspector and its property controls
- behavior and claim views
- the discrete-event simulator
- the agent command line

An edit made in any of them is an operation on the same model, and all of them show the result. There is no second copy to synchronise, because the model is derived from the text on every commit (see [decisions.md](decisions.md), decision 1).

Exegra is also its own first subject. `specs/exegra/spec.jsonc` describes Exegra's components, contracts, edit and save flows, claims about them, and which parts are hand-written. Where the description and the code disagree, the specification says so and a claim reports it (for example `edits-only-via-transactions`, currently violated).

## Priorities

These are ordered. When two conflict, the earlier one wins.

1. **Accuracy.** A statement shown to the user must be true of what was actually checked. A claim is `verified` only when an evaluator examined the model, and every result states its scope. Vacuous checks are `inconclusive`, trace checks say they cover only the listed traces, and unsupported methods stay `not-evaluated`. See [claims-and-evidence.md](claims-and-evidence.md).
2. **Visibility.** What is specified, what is unknown, what is violated and what is merely declared must all be visible. Gaps, `unknowns`, `illustrative` marks and implementation status are first-class data, not footnotes.
3. **Visual-first.** The 3D scene is a primary way to read and edit a system, not a decoration of a text file. Position is presentation only; containment and relationships are semantic.
4. **Bidirectional editing.** Every visual edit appears in the text and every text edit appears in the scene, with comments and formatting preserved.
5. **Self-description.** Exegra's own structure, claims and limitations are expressed in its own format and checked by its own tools. See [self-hosting.md](self-hosting.md).
6. **Extensibility through semantics.** New categories, relationship kinds and component properties are added in a specification's `vocabulary`, not in code. The meta-model is data. See [model-and-format.md](model-and-format.md).
7. **Determinism.** The same text gives the same model, hash, layout, simulation trace, claim results and generated artifacts.
8. **Agent operability.** An agent uses the same operation protocol as the UI, through a command line that prints one JSON document per call. See [agent-interface.md](agent-interface.md).

## What Exegra deliberately does not claim

- It does not prove that code matches the specification. A component's `implementation.modules` are compared with files on disk by path only.
- It does not explore state spaces. Behavioral claims are checked on the scenario traces a claim lists.
- It does not measure performance. Claims that need measurement need external evidence, and without it they stay not evaluated.
- It does not generate its own runtime. Generated artifacts are reports and manifests about the model.

Open items of this kind are recorded in the model, not in this document: `system.notes` and the component `unknowns` in `specs/exegra/spec.jsonc`, the *Realisation* and *Verification* panels, `node cli/exegra.js gaps --project exegra`, and `specs/exegra/generated/tasks.json`.

## Intended use

A person or an agent describes a system as components, ports, contracts, relationships, behaviors and claims; looks at it in 3D; simulates scenarios with injected faults to see a property fail with a concrete counterexample; records what evidence supports each claim; and keeps the specification next to the code in the same repository, under version control, as plain text.
