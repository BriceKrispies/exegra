# Decisions

Architectural decisions in short form: context, decision, consequences. They describe the code as it is. Open limitations are recorded in the model (`system.notes` and component `unknowns` in `specs/exegra/spec.jsonc`, `node cli/exegra.js gaps --project exegra`), not here.

## 1. The source text is the authority; the model is derived

**Context.** A visual editor and a text editor over separate in-memory and serialized forms drift apart.
**Decision.** The JSONC text is the serialized authority. The model is derived from it on every commit. Every operation is a source-preserving text edit followed by re-derivation.
**Consequences.** Text and visual editing cannot diverge, since there is no second model; comments and formatting survive edits. The cost is a full re-parse and re-validation per commit, with no incremental parsing (within a transaction the model is derived once, not per operation; see [transactions-and-persistence.md](transactions-and-persistence.md)). That cost is not otherwise measured; the only test bound is that a transaction plus undo on the 396-component benchmark takes under 2000 ms (`tests/browser/interaction.spec.js`).

## 2. Presentation is a separate file and a separate operation

**Context.** Node positions help reading but carry no architectural meaning, and must not pollute the specification or its hash.
**Decision.** Positions live in `layout.jsonc`, written only by `MovePresentationNode` (and `ReplaceLayout`), which cannot edit the specification text. Pins are absolute `[x, z]` per view.
**Consequences.** Moving a node never changes the semantic hash or the specification. Pins do not follow a changed layout engine or model; nothing re-anchors them.

## 3. A validation gate on every transaction

**Context.** A model with errors cannot be projected, simulated or evaluated reliably.
**Decision.** A transaction whose resulting specification has any validation error is rejected atomically (`validation.failed`). A file that already has errors loads with diagnostics, and edits are rejected until the errors are fixed.
**Consequences.** The committed model is always valid after the first successful edit. A file with validation errors cannot be fixed one error at a time through operations that leave others in place; a source replacement that fixes all of them works. Syntax errors arriving from disk keep the last valid model.

## 4. One id namespace, indexed references

**Context.** Rename and delete need to find every use of an id, including inside claim parameters and effects.
**Decision.** All entities share one namespace of lower-case, hyphen-joined ids (underscores allowed inside a word; pattern in `metamodel.json`). References are indexed at parse time, including those in `claim.evaluate` and `emit` effects. Behavior names inside expressions (`worker-flow.acked`) are rewritten on rename and followed on cascade delete.
**Consequences.** Rename and delete repair every reference. Expression references are found by parsing expressions, not by a type-aware index; a declaration whose expression names a removed behavior is removed with it.

## 5. A small expression language

**Context.** Guards, effect values and invariants need evaluation, and specifications are shared and checked automatically.
**Decision.** A small side-effect-free language (`expr.js`) with a documented grammar. No executable JavaScript appears in specifications, and no host-language evaluation occurs.
**Consequences.** Expressions can be parsed, scope-checked, rewritten on rename and evaluated deterministically. They are limited to numbers, strings, booleans, comparison, arithmetic and implication over variables, event payloads and other machines' state.

## 6. Claims carry an explicit method and honest statuses

**Context.** A tool that shows a green mark for a statement nobody checked is worse than none.
**Decision.** Every claim names an evaluation method. Statuses are `verified`, `supported`, `violated`, `inconclusive`, `not-evaluated`. Vacuous checks are `inconclusive`; trace methods check only the listed scenario traces and say so in `scope`; unsupported methods stay `not-evaluated`; contradicting evidence turns a verified result into `violated`. Trace methods also refuse to pass for want of anything to check: an implication whose antecedent is never true, a trace of zero steps and a `never` about something that cannot occur in the scenario are `inconclusive`. Live checks in the simulator report *undecided* separately from *violated*.
**Consequences.** `verified` always means "an evaluator checked this, within this scope". Claims that need an exhaustive or probabilistic check remain `not-evaluated` (for example `ack-probability-bound`). `supported` can rest on author-entered evidence, and the explanation says so.

## 7. Local-first optimistic saving

**Context.** The interface should respond at once, and edits from other programs must not be silently destroyed.
**Decision.** A commit refreshes the projections immediately. The write to disk follows asynchronously with a base-hash check. A mismatch is a visible conflict (*Reload from disk* or *Overwrite disk*), never a silent overwrite.
**Consequences.** Views can show a revision that is not yet on disk. The order (commit, refresh, persist) differs from a strict persist-then-refresh pipeline, and the self-specification models it as it is (`session-flow`; claims `refresh-follows-commit`, `save-follows-refresh`, `conflict-never-overwrites`). Quick commits may be saved as one write; there is no automatic retry after a failed save. Adopting a change from disk clears the undo and redo history and is not itself undoable, because undoing would write older text over the newer file. Switching projects is refused while a save is pending, in conflict or in error, so that no edit is left behind.

## 8. Persistence is a development-only, confined middleware

**Context.** Writing files from a browser is a risk; a production build should never do it.
**Decision.** Persistence is a Vite middleware active only under `serve`, confined to `specs/<name>/`: validated names, resolved paths that stay inside the project, a fixed file map, loopback `Host` and `Origin` checks, a required custom header, no CORS headers. A production build contains no write path and labels itself read-only.
**Consequences.** The production build can view and simulate but not save. Protection against other local processes is limited to loopback and the header: any local process can use the endpoints while the dev server runs.

## 9. Rendering: Three.js, one object per element

**Context.** Scenes must be pickable, styleable and legible.
**Decision.** Three.js with `OrbitControls`, `CSS2DRenderer` labels and `Line2` fat lines. One mesh and outline per node and one line and arrowhead per edge, with no instancing.
**Consequences.** Simple per-element picking and styling. Draw calls grow with the element count; the overlay shows the count and the benchmark specification (396 components, 507 relationships) loads in the browser test, but no draw-call or frame-rate figure is recorded in the repository. The claim `benchmark-scene-interactive` is deliberately not evaluated until a threshold and a measurement exist.

## 10. Deterministic layouts with an automatic choice; position is not meaning

**Context.** Generated positions should be stable and readable, models range from a handful of components to thousands of entities, and no single arrangement suits every graph or every window shape.
**Decision.** Four deterministic methods, recursive over containers: `layered`, `layered-down`, `packed` and `radial`. An automatic choice runs all four and keeps the one with the lowest score (aspect against the viewport, mean edge length, crossings, whitespace; weights 3, 0.3, 1, 0.25 in `src/core/layout/score.js`). The method is a viewer preference, kept per project and view in browser storage; a view may declare a default with `display.layout`. Large models (over 30 components) first open as a subsystem overview with bundled relationships. Containment is semantic; position is presentation only.
**Consequences.** The same model, method and viewport shape give the same scene, and the choice never touches the specification, the layout file or the semantic hash. Automatic choice depends on the viewport's shape, so two windows can show different arrangements of one model. The score is a heuristic: it ranks the four methods, it does not measure readability. Distance and position must not be read as meaning, and each scene carries a note saying so. The `references` projection (decision 11) is laid out by the same methods.

## 11. The meta-model is data; vocabulary extends it

**Context.** Adding a category or a property should not need a code change.
**Decision.** `metamodel.json` drives the parser's structure checks and the inspector's controls. A specification's `vocabulary` can add categories, relationship kinds, properties of any entity kind (including `ref` and `list` properties that point at other entities), whole entity kinds with their own sections, and external verification methods. Projections and the claim methods Exegra evaluates itself are fixed per build. A fourth projection, `references`, draws the selected entity of any kind with its reference neighbourhood (depth 1 to 3, at most 150 entities), so entity kinds a specification declares can be explored without code that knows them.
**Consequences.** New properties and kinds are validated and editable at once, and references through them take part in rename and delete. A claim using an external method can only be `supported` by evidence, never `verified`. The built-in kinds are still defined in `metamodel.json`, not in a specification.

## 12. Evidence is recorded by executing it

**Context.** A claim backed by "a test exists" is not backed by the test passing.
**Decision.** `exegra verify` executes the tests an `evidence` entity references and records outcomes in `evidence/results.json`, keyed by evidence id. Only `test` evidence is executed, and a test reference that matches no test is recorded as a failure, not a pass.
**Consequences.** `supported` can mean a recorded pass. Recorded results are not bound to a code or model hash, so a stale result is not detected as stale; this is a recorded limitation.

## 13. One pipeline for the UI and agents

**Context.** A separate agent data model would duplicate rules and diverge.
**Decision.** The CLI builds a `Project` from disk and uses `Project.apply` with the same operations as the UI. Each command prints one JSON envelope.
**Consequences.** Anything the UI can change an agent can change under the same validation. The CLI has no undo history across invocations and checks `--expect-hash` where the UI does not pass an expected revision.

See [architecture.md](architecture.md), [transactions-and-persistence.md](transactions-and-persistence.md), [claims-and-evidence.md](claims-and-evidence.md) and [agent-interface.md](agent-interface.md).
