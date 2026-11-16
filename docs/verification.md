# Verification

How to run every check, what it establishes, and where results are recorded. A check only establishes what it exercises; the *Verification* tab and `specs/exegra/spec.jsonc` (`system.notes`, `unknowns`) state what is not covered.

## Summary

| Command | Establishes | Result goes to |
|---|---|---|
| `npm run build:engine` | the Rust simulation engine compiles to WebAssembly and is bound into `src/engine/pkg/` (run first by `dev`, `build`, `test`, `test:browser`, `typecheck`, `generate` and `verify`) | `src/engine/pkg/` (generated, not committed) |
| `npm run typecheck` | `tsc` with `checkJs` and `strict` over `src/core`, `src/persist`, `tools`, `cli` | terminal |
| `npm test` | semantic core, workspace service and CLI behave as tested | terminal |
| `npm run test:browser` | the running application, end to end, in Chrome | terminal, `screenshots/` |
| `npm run build` | the production bundle builds | `dist/` |
| `npm run verify` | for the `exegra` project: validation, traceability, test evidence executed; claims re-evaluated | `specs/exegra/evidence/results.json` |
| `npm run generate` | artifacts regenerate deterministically, for `exegra` | `specs/<project>/generated/` |
| `npm run import:markdown -- --project <name>` | converts a checkout that still has its Markdown specification ([importing-markdown.md](importing-markdown.md)); `node tools/import-markdown.js --project <name> --check` only compares | the file `specs/<name>/project.jsonc` names |
| `npm run benchmark:generate` | regenerates `specs/benchmark/spec.jsonc` | `specs/benchmark/spec.jsonc` |
| `node tools/check-spec.js <spec>` | one specification validates; claims and scenarios | terminal |
| `node tools/conformance.js [--engine "<command>"]` | an engine reproduces every golden trace of `tests/conformance/`: by default the WebAssembly engine through `src/core/engine.js`, or a command reading an input on stdin (the native `engine/target/release/exegra-sim`) | terminal |
| `node cli/exegra.js traceability` | declared modules exist; every source file is claimed | terminal |
| `npm run check` | typecheck, `npm test`, `npm run test:browser` in sequence | terminal |

Typecheck does not cover `src/render`, `src/ui` or `src/app`. Tests run with a limited number of jobs; `npm test` uses `--test-concurrency=2`, and Playwright runs one worker.

## `npm test`

`node --test` over `tests/core/*.test.js`. These suites use in-memory specifications, temporary directories and `node:test`; they do not need a browser.

| File | Covers |
|---|---|
| `model.test.js` | Parsing and indexing, duplicate ids, unresolved and mistyped references, unsupported constructs diagnosed, unknown claim methods as warnings, syntax errors, containment rules, expression checks, vocabulary extension (categories, relationship kinds, properties), gap diagnostics, normalisation equivalence, queries. |
| `vocabulary.test.js` | Model-defined vocabulary: declared entity kinds parse into entities with their own sections and properties; they are validated like built-in kinds (enum, required, unresolved and mistyped references, duplicate or unknown sections, unknown kinds in a `ref`); references through declared `ref` and `list` properties follow renames and block deletes; a claim using a declared external verification method is never reported as verified. |
| `roundtrip.test.js` | Visual and source edits change exactly the expected text; comments and formatting survive create, rename, connect and delete; rename rewrites references, claim evaluations and behavior names in expressions; delete refusal and cascade repair; atomic rejection; undo and redo restore exact text; layout moves cannot change the semantic hash; stale transactions refused; external reload adopts valid text, ends the undo history and keeps the last valid model on syntax errors. |
| `claims.test.js` | Each structural method (holding and failing, vacuous selectors inconclusive, `reachable` needs a path of at least one relationship); unsupported methods not evaluated; determinism; the evidence rules (none, document, unexecuted test, recorded pass, recorded fail, contradicting); each trace method; vacuity (an implication with an antecedent never true, zero-step traces, a `never` about an event that cannot occur are inconclusive); `checkTrace` on finished and unfinished runs, pending checks, and only for claims that list the scenario. |
| `sim.test.js` | Through `src/core/engine.js` on the WebAssembly engine: request/ack machines with emitted and delayed events, guards over payload and other machines, each fault kind, step limit, expression errors, reset, stepwise equals run (the trace cursor the Simulation tab steps through), trace immutability, determinism. |
| `conformance.test.js` | The Rust engine reproduces every golden trace of `tests/conformance/`: as WebAssembly from the model and from the committed input alone, and as the native binary `engine/target/release/exegra-sim` when it is built (skipped with a message otherwise); `simulationInput` derives exactly the committed inputs; the runner reports an altered trace at the right step and path. |
| `flows.test.js` | The message flow of every step of a scenario: sender from the emitting behavior or outside, receivers from the behaviors that fired; paths along the edge between the drawn nodes in either direction, never along an unrelated one; unshown when only a hidden relationship connects them, undeclared when none does; collapsed subsystems, dropped events and components not drawn. |
| `projections.test.js` | Implicit views, every scene element backed by an entity, collapse lifting, hide, isolate, view filters, claim status marking, custom projection registration, determinism; layout overlap, containment, flow direction, pins, cycles and cross-container edges; author-entered evidence and generated implementations never drawn in a verified colour. |
| `data-model.test.js` | Records and copies: the data slice fixture (`tests/fixtures/data-model/spec.jsonc`) validates with exactly one data-rule finding, its deliberately missing erasure point; wrong enums, unknown key and copy fields and numeric bounds without a unit are errors with their paths; each data rule reports its entity and field on a constructed violation; `data-model` claims are violated, verified or inconclusive as the findings say; the Data view. |
| `references.test.js` | The `references` projection: focus at depth 1 and 2, every node and edge backed by an entity, declared kinds take their shape and colour from the meta-model, violated claims coloured, `filter.entityKinds`, no focus, the implicit view, the cap of 150 with its note, determinism. |
| `layout.test.js` | The four layout methods: soundness (no sibling overlap, containers enclose children), determinism, levels, pins, empty scenes, unknown method refused; `chooseLayout` scores every method and takes the lowest total; `scorePlacement` agrees with it and prefers better aspect and fewer crossings; target aspect shapes packed and layered results; radial centre; a 400-node, 500-edge performance bound. |
| `generate.test.js` | Exactly five artifacts, byte-identical on rerun, insensitive to comments and key order, valid JSON carrying the semantic hash, violated claim becomes a high-severity task, every component named. |
| `import-markdown.test.js` | The Markdown importer: a requirement with every key becomes a claim, retired requirements and unknown keys, unresolved references counted not dropped, component and boundary rows, helpers; a small fixture specification (`tests/fixtures/markdown-import/`) converts through its import map, validates, is covered and deterministic; the importer's command line; a linked project resolved through `project.jsonc` whose documents the `markdown` command renders. |
| `workspace.test.js` | Name and path validation, base-hash writes, conflicts leave files untouched, only `spec` and `layout` writable, `generated/` confinement, export and import round trip, journal lines. |
| `cli.test.js` | `validate`, `list`, `show`, `deps`, `apply` (writes, stale hash, invalid operation, `--dry-run`), `plan-delete`, `simulate`, `ops`, usage errors with exit code 2; the test-count parsing that makes a reference matching no test a failure. |

## `npm run test:browser`

Playwright (`playwright.config.js`) starts its own Vite server on port 5199 (reusing one if running), one worker, Chrome via `channel: 'chrome'`, in three projects: `desktop` (1600x1000) runs every file except `mobile.spec.js`; `phone` (iPhone 13, 390x844, touch) and `tablet` (820x1180, touch) run the tests of `mobile.spec.js` tagged `@phone` and `@tablet`. `exegra verify` runs a referenced file without naming a project, so each test runs in the one project that selects it. **Tests never modify the shipped specifications.** `global-setup.js` copies the self-specification to `specs/zz-test-exegra` and the multiplayer example, a test fixture at `tests/fixtures/multiplayer/spec.jsonc`, to `specs/zz-test-multiplayer`; `resetScratch` recreates a copy before every test and `global-teardown.js` removes them. The shipped `benchmark` project is only read, and a local test of a linked project asserts that its file is unchanged afterwards. Tests drive the real UI (canvas clicks at projected positions) and check the model in the page, the DOM and the files on disk, and fail on any uncaught page error.

`tests/browser/exegra.spec.js`:

- self-specification renders in 3D
- selecting a component shows model-derived properties
- inspector rename persists to spec.jsonc and survives reload
- source edit updates the scene; invalid source is rejected and the draft is kept
- create, connect, delete with dependency warning, undo and redo
- moving a node changes layout.jsonc only
- views switch and keep the selected entity
- claim selection highlights involved components
- simulation steps through the trace; early-ack fault violates the invariant (on the multiplayer fixture)
- different specifications load through the same pipeline (the self-specification and the fixture)
- realisation panel reports implementation status

`tests/browser/interaction.spec.js`:

- nested subsystems collapse, expand and isolate without changing the model
- renaming an id rewrites every reference in the source
- external file changes reload; a concurrent change is a conflict and never a silent overwrite
- benchmark specification with hundreds of entities loads and reports render statistics
- stepping a simulation sends a labelled marker along the edge from sender to receiver (Exegra's own `visual-edit-flow`: the request enters from outside, the operation moves along the declared edge to the transaction system, and the save is marked as having no declared relationship)

`tests/browser/simulation-worker.spec.js`:

- a long simulation runs in a worker while the page stays responsive (a scenario added through a transaction loops up to 20000 steps: animation frames keep coming and the app bar keeps reacting while the run is shown as running, and the finished trace steps as before)

`tests/browser/mobile.spec.js` (by touch, on scratch copies):

- phone layout has no horizontal scroll and 44 px targets and the scene covers most of the screen (no sideways scroll and no visible control under 44 by 44 CSS px, offenders listed, with nothing open, with each destination's sheet at full height, in the menus, a dialog and search; with no sheet open at least 60% of the window is uncovered scene, sampled on a grid against the boxes of every visible piece of chrome)
- every function is reachable by touch on a phone (each destination, search, tapping the canvas to select, a property edit, undo and redo, create, connect mode, delete with cascade, rename, explorer actions, layout, camera, legend and statistics, a scenario stepped with the docked transport, faults and the timeline, verification, source, realisation, diagnostics, changes, export, view and project switching)
- panels open beside the scene on a tablet and the desktop shows explorer scene and context panel side by side (at 820 px no overlap between a panel and the canvas; a fresh 1600x1000 page lays out explorer, canvas and context panel without overlap)

Local tests (`tests/**/local-*`, git-ignored): `tests/browser/local-<project>.spec.js` and `tests/core/local-<project>.test.js` test a linked project (a specification in another repository, linked through `specs/<project>/project.jsonc`) when it is present. They skip themselves when it is absent, change nothing in it, and are not part of the tracked suites; the tracked tests cover the same capabilities on a fixture. A local browser test of a full-size project checks that its entity kinds and verification methods load, that nothing is reported as verified without evidence, that a requirement can be followed to what it traces to, and that a model with thousands of claims stays usable (windowed lists, filters, layout choice).

The benchmark test asserts that nodes and edges equal components and relationships (at least 300 and 400), that the overlay shows draw calls, that a click selects accurately in the dense scene, and that a transaction plus undo takes under 2000 ms. The bound is a guard, not a measurement. No frame rate or draw-call figure is recorded in the repository.

## `npm run build`

`vite build` to `dist/`. The build bundles `specs/*/spec.jsonc`, `layout.jsonc` and recorded results for read-only use. No test runs against the production build.

## `npm run verify`

Runs `exegra verify` for the self-specification, the only shipped project with test evidence:

```sh
node cli/exegra.js verify --project exegra --expect-violated edits-only-via-transactions --pretty
```

The pipeline, in order: validate the specification; run the traceability check; execute every `test` evidence reference; write `specs/<project>/evidence/results.json` (`results` keyed by evidence id with `outcome`, `ranAt` and, on failure, `detail`, plus `traceability`); re-evaluate all claims with those results. Exit code 1 results if there are validation errors, a failed test, or a violated claim not listed in `--expect-violated`. A specification with syntax errors fails the command without running anything.

An evidence `ref` is `<path>` (run the whole file) or `<path>#<title pattern>` (run matching tests). Files under `tests/browser/` run with `npx playwright test <file> -g <pattern>` and need Chrome; others run with `node --test`. A Node test reference that matches no test (a title pattern that selects nothing, or a file with no tests) is recorded as a failure with the detail "the reference matched no test"; Node itself exits 0 in that case, so the exit code alone is not trusted. References may contain only letters, digits, `_`, `.`, `/`, `-`, space, `#` and `:`. `--skip-browser` skips browser evidence and leaves it without a recorded result.

**Why some claims are expected to be violated.** `--expect-violated` names claims that are violated by design or by a known defect, so that a violation you did not expect fails the command and one you did expect does not:

- `edits-only-via-transactions` (exegra): a real discrepancy. Import writes through the persistence service without the transaction pipeline.
The multiplayer fixture carries two more such claims, `ack-implies-durable-under-early-ack` (a seeded behavioral defect, kept to demonstrate a counterexample) and `database-reached-only-by-runtime` (a seeded structural defect, `telemetry-reads-game-database`). They are not part of any script; the browser tests rely on them.

Only `test` evidence is executed. Measurement, document and review evidence stay author-entered. The recorded results are not tied to a code revision.

## `npm run generate`

`exegra generate --write` writes `manifest.json`, `ARCHITECTURE.md`, `claims-report.md`, `claims-report.json` and `tasks.json` under `specs/<project>/generated/`. Output is a pure function of the model, claim results (with recorded results), diagnostics and traceability: the same inputs give byte-identical files, and only changed files are rewritten. Comparing the files before and after a run shows drift between the model and the committed artifacts.

## `node tools/check-spec.js`

```sh
node tools/check-spec.js specs/exegra/spec.jsonc [--trace <scenarioId>]
```

Read-only. Prints diagnostics with line and column, the semantic hash, entity counts, each scenario's steps and outcome, and every claim's status with its explanation and counterexample; `--trace` lists one scenario's steps. Exit code 1 if there are validation errors. It does not use recorded results.

## `node cli/exegra.js traceability`

Compares `implementation.modules` of every component (repository-relative paths; a trailing `/` claims a directory) with disk. It reports `checkedModules`, `missingModules` (declared but absent) and `unclaimedFiles` (files under `src/`, `cli/`, `tools/` with extension `.js`, `.json`, `.css` or `.html`, plus `index.html` and `vite.config.js`, that no component claims). It compares paths only: it does not check that a module implements its component or that relationships match imports.

## Where results live

- `specs/<project>/evidence/results.json`: recorded test results and traceability.
- `specs/<project>/generated/`: `claims-report.*` and `tasks.json` snapshots.
- The *Verification* and *Realisation* tabs and `node cli/exegra.js gaps`/`claims`: current state, computed on demand.
