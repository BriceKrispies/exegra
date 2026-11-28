# Transactions and persistence

## The operation protocol

Every change to a project, from the 3D scene, the inspector, the source editor or the CLI, is an operation applied by `Project.apply(ops, opts)`. `node cli/exegra.js ops` prints the live table with parameters, preconditions, effects and persistence; this list is a summary.

| Operation | Edits | Notes |
|---|---|---|
| `CreateEntity` | spec | Any kind except `system`; nested kinds (port, state, transition) take an `owner`. Fresh id required. |
| `DeleteEntity` | spec + layout | Refused when anything refers to the entity, unless `cascade: true`. |
| `RenameEntity` | spec + layout | Changes an id and rewrites every reference, expression and layout pin. |
| `SetProperty` | spec | One value; dotted path allowed (`implementation.status`); `null` removes. `id` is refused. |
| `CreateRelationship`, `DeleteRelationship` | spec | Id derived as `<from>-<kind>-<to>` when omitted. |
| `AddClaim`, `ModifyClaim` | spec | Several properties change together or not at all. |
| `AddState`, `AddTransition` | spec | Transitions are tried in declaration order; `index` sets priority. |
| `ReplaceSource` | spec | The source editor and whole-text replacement. |
| `MovePresentationNode` | layout | Pins or resets one entity in one view. Cannot edit the specification text. |
| `ReplaceLayout` | layout | Whole layout text. |

Each operation computes JSONC edits against the current text with `jsonc-parser`'s `modify` (removal cuts exactly the node plus one comma; array insertion in `text-edit.js` copies neighbouring indentation). Comments and formatting of untouched declarations survive.

**One derivation per transaction.** Later operations in a transaction see the effects of earlier ones, but the model is not re-derived after every edit (on a 7 MB specification one derivation takes about 2.6 s). `Tx` keeps an index of where every entity is declared (id, kind, owner, path). The index follows creations (with the entities nested in them), property edits, removals of declarations (later items move up), replacements of a property that declares nested entities, and id changes; any other edit invalidates it, and the next lookup re-derives. Operations that read references, expressions or entity data (`DeleteEntity`, `RenameEntity`, `ReplaceSource`) read `tx.model`, which re-derives when the text changed. The result is analysed once, reusing the transaction's last parse.

Edits inside one top-level declaration are made on a window holding only that declaration's lines, and appends to a section are kept as pending insertions; the text is spliced together once. `jsonc-parser`'s edits depend only on the edited lines when the text has no carriage returns, so the result is byte for byte what the same edits make on the whole text. Declarations that share a line with other content, removals of whole declarations and files with CRLF line breaks are edited on the whole text.

`Project.apply(ops, { perOperation: true })` runs the reference path, which re-derives after every edit; `tests/core/batched-transactions.test.js` compares the two on seeded random transactions (set `EXEGRA_TX_DIFF_SEEDS` to multiply the seeds and `EXEGRA_TX_DIFF_SPEC` to add a large specification file). If a derivation finds that the index does not match the model, `Project.apply` replays the transaction on the reference path. Deletions and renames still need one derivation each (WG-4980), and validation of the result is still a full validation (WG-4974).

`RenameEntity` rewrites the declaration, every reference found by the parse-time index (including references inside `claim.evaluate` and `emit` effects), every expression that names a behavior as `<id>.<variable>`, and layout pins. `DeleteEntity` uses `planDelete`, also available as `exegra plan-delete <id>`: with `cascade`, list references are dropped, optional references unset, children of a removed subsystem move to its parent, and declarations that cannot exist without the entity (a required reference, or an expression naming a removed behavior) are removed too, to a fixed point.

## Atomicity and the validation gate

`apply` runs in this order and stops at the first failure, leaving the project untouched:

1. `op.empty`: at least one operation.
2. `revision.stale`: `expectRevision` or `expectHash` does not match the project.
3. `op.unknown`: each operation type is known.
4. `model.unavailable`: if the current text has syntax errors, only `ReplaceSource` and `ReplaceLayout` are accepted.
5. Each operation's preconditions (`OpError` codes such as `id.duplicate`, `entity.unknown`, `delete.referenced`, `op.param`).
6. `validation.failed`: the resulting specification text is analysed, and **any validation error rejects the transaction**, with the error diagnostics returned. Violations of integrity rules (`integrity.violated`) are not counted here; they go to the next step.
7. `integrity.violated`: the integrity rules are evaluated before and after; a violation of an `error` rule that the project did not have before rejects the transaction, with one diagnostic per new counterexample. Existing violations do not block unrelated edits (the ratchet, [integrity-rules.md](integrity-rules.md#enforcement-on-edit-the-ratchet)).
8. `layout.invalid`: the resulting layout must parse.

Consequence of step 6: a file that already has validation errors still loads, with its diagnostics, but every edit that leaves any error in place is rejected until the errors are fixed. A source edit that fixes them is accepted. A file with syntax errors has no model; the session keeps the last valid one when the error arrives from disk.

The source editor treats typed text as a draft. It analyses the draft after a pause and shows diagnostics. The draft becomes a `ReplaceSource` transaction only when applied, and a rejected draft is kept.

## Commit, revisions, history

A successful `apply` swaps the texts, re-derives the model, increments `revision` (every commit, undo, redo or reload), increments `semanticRevision` only if the semantic hash changed, appends a `HistoryEntry` (label, origin `ui`/`source`/`cli`/`external`/`undo`/`redo`/`import`, operation names, affected ids, `semanticChanged`, `specChanged`, `layoutChanged`, hashes before and after) and notifies subscribers synchronously. `MovePresentationNode` commits with `semanticChanged: false` by construction; the hash does not move. A commit that changes only the layout text leaves the specification text untouched, so the model is not re-derived (`specChanged` is false) and the same `Model` object stays in place.

**Undo and redo** restore the exact earlier spec and layout texts and commit them as new revisions. A new transaction clears the redo stack. Stacks are unbounded in memory and are not persisted: undo is lost on reload and per CLI invocation (a recorded unknown of the `transactions` component).

**Reload** (`Project.reload`) adopts text that changed outside the process. Text with syntax errors is refused and the last valid model is kept. Valid text is committed with origin `external` and recorded in the history, but **adopting an external change clears both the undo and the redo stack and is not itself undoable**: undoing it would write the older text over the newer file on disk. Earlier edits made in the process cannot be undone past a reload.

**Optimistic concurrency.** `expectRevision` and `expectHash` guard a transaction against a project that moved on. The CLI passes `--expect-hash`. The session does not pass either; it protects the disk copy with a base-hash check instead (below). That asymmetry is a recorded unknown.

## Local-first saving

The browser session saves in this order: **commit, refresh, persist**.

1. `Project.apply` commits in memory.
2. `onCommit` in `session.js` re-evaluates claims if the semantics changed, re-projects, re-lays-out, notifies the renderer, inspector and source editor, and records the change.
3. If the commit did not come from the disk (`origin !== 'external'`), the changed file is marked pending and `flush()` starts. The write is asynchronous.

`flush` writes the current text (not one write per revision, so quick commits may coalesce) with the SHA-256 `baseHash` last seen from the server. A matching base hash writes atomically and returns the new hash. A mismatch returns `409` with the current disk text; the session sets its save state to `conflict`, writes nothing and offers *Reload from disk* (adopts the disk text, which clears the undo history) or *Overwrite disk* (re-bases on the disk hash and writes). A failed request leaves the file pending and the state `error`; there is no automatic retry. Save state (`saved`, `saving`, `conflict`, `error`, `readonly`) is shown in the app bar: below desktop width as a badge on the overflow button and a line at the top of its menu, on a desktop as a small button when it needs attention. A conflict opens the menu from either.

This order differs from a strict persist-then-refresh pipeline: the views show a revision before it is on disk. The self-specification models it as it is (behaviors `session-flow` and `project-session-flow`, claims `refresh-follows-commit` and `save-follows-refresh`).

**Switching projects** is refused while a save is pending, in conflict or in error: the session reports that the pending save must be resolved or finished first and stays on the current project.

A file watcher streams changes over server-sent events. The session ignores its own writes (hash match), reloads valid external changes, reports invalid ones and keeps the last valid model, and defers to the pending write when it has unsaved edits so that the conflict is shown instead of hidden. Changes to `evidence/results.json` re-evaluate claims. The product files a `project.jsonc` lists are watched as one file, `products`: a changed, added or removed product file (or a changed list) is reported, and the session reads the project again and re-derives the layered model from the product layers on disk (`src/app/disk-reload.js`), keeping the platform text and layout in memory. A product file that does not parse is reported and the last valid model is kept. Tests: `tests/core/disk-reload.test.js`.

## Where a project keeps its files

A project is a directory `specs/<name>/`. Its specification is `spec.jsonc` there, unless the directory holds `project.jsonc` naming another file: `{"spec": "<path relative to the project directory, ending in .jsonc>"}`. That lets a specification live in the repository it describes (a linked project can point at `specifications/spec.jsonc` of a sibling checkout) while the project's layout, recorded results, journal and generated artifacts stay under `specs/<name>/`. Reads, writes (with the same base-hash check), listing, export, import and the change watch all follow the link; the source editor shows the real location. A project with both `spec.jsonc` and `project.jsonc` is refused, so a specification exists once, and `project.jsonc` itself is never written through the workspace, so no request can redirect a write. A production build bundles linked specifications through the virtual module `virtual:exegra-linked-specs`.

## The dev-server persistence boundary

Persistence exists only under `npm run dev`. `PERSISTENCE_AVAILABLE` is `import.meta.env.DEV`, and the plugin (`tools/vite-plugin-exegra.js`) has `apply: 'serve'`. A production build contains no write path, bundles the shipped `spec.jsonc` and `layout.jsonc` files, and labels itself read-only (Import is disabled).

The plugin is a thin HTTP wrapper over `tools/workspace.js`, under `/__exegra/`:

| Route | Purpose |
|---|---|
| `GET projects`, `GET project?name=` | List projects; read spec, layout and recorded results with hashes. |
| `POST write` | `{name, file: 'spec'|'layout', text, baseHash, meta}`; `200` with the new hash, or `409` conflict. |
| `POST generated` | Write generated artifacts (`.json` or `.md` only, under `generated/`). |
| `GET export`, `POST import` | Project bundle. |
| `GET events?name=` | Server-sent change events. |

Confinement: project names must match the name pattern; every path is resolved and must stay inside `specs/<name>/`, apart from the specification a `project.jsonc` names; the writable file map is fixed (`spec` and `layout`, plus `generated/` and the recorded-results file through separate calls); text is capped at 16 MB and bodies at 20 MB. Every request needs a loopback `Host`, a loopback `Origin` when one is sent, and the header `x-exegra-client: 1`. The event stream is a plain `GET` that `EventSource` cannot add headers to, so it is exempt from the header only. No CORS headers are sent, and the Vite server binds `127.0.0.1`. Writes are serialised per project, atomic (temporary file then rename; on Windows the rename is retried and then falls back to an in-place write, which is not atomic) and appended to the journal. This protection rests on loopback and the header alone: any local process can read and write projects while the dev server runs.

## Import and export

Export downloads `{format: "exegra-project", version: 1, name, files}` with `spec.jsonc` and, when present, `layout.jsonc` and `evidence/results.json`. Import validates the bundle shape (known file keys, strings, size), refuses, in the browser, a bundle whose `spec.jsonc` has syntax errors (a specification that cannot become a model), and then writes the project's files directly through the service and reopens the project.

**Import bypasses the transaction pipeline.** The only check before the write is that the specification parses (syntax errors are refused); a specification with validation errors is accepted and then loads with diagnostics, rejecting edits until they are fixed. There is no semantic validation as a transaction and no base-hash check, and the files are written one after another, not as one unit. The self-specification records this as a discrepancy and reports the claim `edits-only-via-transactions` as violated; `editing-surfaces-except-import-via-transactions` is verified. Recorded-result writes by `exegra verify` also carry no base-hash check.

## The CLI and persistence

`cli/commands.js` builds a fresh `Project` from disk per invocation, applies operations through `Project.apply` with origin `cli`, and writes through the workspace service with a base-hash check. The spec and layout writes are separate; if the layout write conflicts after the spec was written, the error says so. `--dry-run` validates and writes nothing. See [agent-interface.md](agent-interface.md).

Live record of open limitations here: `system.notes` and the unknowns of `transactions`, `session`, `workspace-service`, `dev-server-plugin`, `persistence-client` and `toolbar` in `specs/exegra/spec.jsonc`, and `node cli/exegra.js gaps --project exegra`.
