# The self-specification as a manifest of part files, recorded evidence

WG-5704. `specs/exegra/spec.jsonc` was one 1.4 MB file. It is now a manifest (`specParts`, `specSections`) over 27 part
files in `specs/exegra/parts/`. The format is described in
[model-and-format.md](../../model-and-format.md#a-specification-kept-as-a-manifest-of-part-files); the conversion is
`tools/split-spec.js` and the comparison is `tools/compare-spec.js`.

## The parts

Sizes in bytes at the conversion commit (the limit is 120 KB = 122,880). The manifest itself is 17,100 bytes with its
placement table. Later edits through `apply` change a few parts by a few hundred bytes.

| Area | Part | Bytes |
|---|---|---|
| System and vocabulary | `system` | 11,149 |
| Components and relationships | `structure-top` (top-level components, composition root, external systems, actors) | 12,961 |
| | `structure-application` | 56,246 |
| | `structure-visualization` | 13,819 |
| | `structure-persistence` | 19,087 |
| | `structure-agent-interface` | 16,967 |
| | `structure-tooling` | 38,277 |
| | `structure-core-model` (validation, model, transactions, layers, derivation, claim verdicts) | 100,989 |
| | `structure-core-engines` (simulation, formal core, generation) | 80,747 |
| Contracts | `contracts` | 49,012 |
| Events and behaviours | `events-faults` | 82,593 |
| | `behaviors-app` | 70,611 |
| | `behaviors-persistence` | 52,451 |
| | `behaviors-core-tools` | 56,209 |
| Scenarios, assumptions | `scenarios` | 35,836 |
| | `assumptions` | 10,216 |
| Claims and evidence | `claims-core-validation` | 95,180 |
| | `claims-core-derivation` | 73,483 |
| | `claims-core-verdicts` | 66,285 |
| | `claims-core-simulation` | 64,806 |
| | `claims-core-formal` | 52,942 |
| | `claims-core-generation` | 53,571 |
| | `evidence-core-generation` | 108,361 |
| | `claims-app-ui` | 50,698 |
| | `claims-persistence-agent-tooling` | 62,834 |
| Views and the rest | `records-and-decisions` | 74,026 |
| | `views-and-rest` | 11,129 |

The largest part is 108,361 bytes. The events have no `producedBy`, so there is nothing to compute an area from: events
and faults share one part. Each area groups the subsystems of the semantic core (`CORE_AREAS` in the split script).

## Same semantics

Both checks were made on the conversion commit, against the one-file specification of the commit before it (`0bf65aa`).

- **Semantic hash.** `node cli/exegra.js validate --spec <file>` prints `049e5cada5dc89` for the one file and
  `049e5cada5dc89` for the manifest: identical, with 0 errors and 0 warnings in both.
- **Resolved document.** `node tools/compare-spec.js <before.jsonc> specs/exegra/spec.jsonc` reports the documents
  JSON-equal, each section's entities compared by id. The entities are not in the original order in five sections
  (`components`, `relationships`, `behaviors`, `claims`, `evidence`), because a manifest concatenates its parts in order
  and an area gathers entities that were apart; the other sections keep their order. The semantic hash does not depend on
  the order of the entities of a section, and nothing else reads that order.
- **Comments.** The single file had 51 comment lines. Every comment inside an entity is in the part of its entity; a
  comment before an entity stays before it, a comment before a section goes with the section's first entity. The split
  adds one description line to each of the 27 parts and 3 to the manifest.

`tests/core/spec-split.test.js` repeats both checks on the current specification (split it again, assemble, compare the
hash and the document).

## Placement

`apply` writes each new entity where the manifest's `specSections` places it (rules in the format document):

| Section | Rule |
|---|---|
| `components` | by its own id or the nearest ancestor the table names (the subsystems and the sub-areas of the semantic core); no parent and no name: `structure-top` |
| `relationships` | by `from`, up the component parents |
| `behaviors` | by `subject`, up the component parents |
| `claims` | by the first of `subjects` that resolves to a named subsystem or ancestor; none: `claims-app-ui` |
| `evidence` | by its claim's `subjects`; none: `claims-app-ui` |
| `contracts`, `events`, `faults`, `scenarios`, `assumptions`, `records`, `copies`, `decisions`, `views` and the rest | one part per section, as in the table above |

A new section, or an entity of a section with no rule, goes beside its section's existing entities, else to the first part.

## Replay check

Sample operations (a tooling component, a semantic-core component, a child of that component created in the same batch, a
relationship from the tooling component, a claim about the child and the tooling component, an evidence record for that
claim, and `SetProperty` on the existing `parser`) were applied to the split specification with
`node cli/exegra.js apply --project exegra --file <ops>`, then reverted with git:

| Entity | Written to |
|---|---|
| `zz-replay-tool`, `zz-replay-tool-invokes-agent-cli` | `structure-tooling.jsonc` |
| `zz-replay-core`, `zz-replay-core-leaf`, `SetProperty` of `parser` | `structure-core-model.jsonc` |
| `zz-replay-claim`, `zz-replay-evidence` | `claims-core-derivation.jsonc` |

Three part files changed (62 lines added in all), and every comment between entities was kept. The only validation message
was the sample claim's own unsupported method. `AddClaim`, `ModifyClaim`, `SetProperty`, `CreateEntity` and
`CreateRelationship` go through the same placement.

## Source locations and the other paths

- `get`, `find`, `refs`, `list`, `show` and the diagnostics of `validate` print the part file and the line in it
  (`cli/locations.js`; `workspace.read` gives a locator for a manifest). The line never refers to the assembled text.
- Verified by running: `validate`, `traceability`, `claims`, `derive`, `cut`, `get`, `find`, `refs`, `list`, `show`,
  `deps`, `apply` (dry run and real), `store import` and `store export` (the export equals the assembled text),
  `tools/check-spec.js`. `generate` and `verify` read the project through the same loader and were not run here.
- Changed for the manifest: the Vite production build bundles a manifest resolved (the `import.meta.glob` of
  `specs/*/spec.jsonc` would otherwise ship the manifest alone); the workspace watch reloads the project when a part
  changes; `tools/record-goldens.js` and the tests that read the self-specification as a text use `readSpecFile`.
- The guard (`tools/spec-guard.js`) already refused the parts a manifest lists; it now also refuses a `Grep` or a shell
  command that names the directory holding them (`specs/exegra/parts`).
- The tree stamp covers every tracked or unignored file, parts included (`specs/*` is ignored except `specs/exegra/`).
