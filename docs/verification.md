# Verification

How to run every check, what it establishes, and where results are recorded. A check only establishes what it exercises; the *Verification* tab and `specs/exegra/spec.jsonc` (`system.notes`, `unknowns`) state what is not covered.

## Summary

| Command | Establishes | Result goes to |
|---|---|---|
| `npm run build:engine` | the Rust engine, kept as the differential oracle, compiles to WebAssembly and is bound into `src/engine/pkg/` (run first by `dev`, `build`, `test`, `test:browser`, `typecheck`, `generate` and `verify`) | `src/engine/pkg/` (generated, not committed) |
| `npm run build:formal-wasm` | the Lean core compiles to WebAssembly (wasm64) from pinned inputs into `src/engine/lean/`; this is the engine Exegra runs (run first by `dev`, `build`, `test`, `test:browser`, `generate` and `verify`) | `src/engine/lean/` (generated, not committed), with `build-info.json` naming every pinned input |
| `npm run typecheck` | `tsc` with `checkJs` and `strict` over `src/core`, `src/persist`, `tools`, `cli` | terminal |
| `npm test` | semantic core, workspace service and CLI behave as tested | terminal |
| `npm run test:browser` | the running application, end to end, in Chrome | terminal, `screenshots/` |
| `npm run build` | the production bundle builds | `dist/` |
| `npm run verify` | for the `exegra` project: validation, traceability, test evidence executed, the theorems of `lean-theorem` claims checked by Lean; claims re-evaluated | `specs/exegra/evidence/results.json` |
| `npm run generate` | artifacts regenerate deterministically, for `exegra` | `specs/<project>/generated/` |
| `npm run import:markdown -- --project <name>` | converts a checkout that still has its Markdown specification ([importing-markdown.md](importing-markdown.md)); `node tools/import-markdown.js --project <name> --check` only compares | the file `specs/<name>/project.jsonc` names |
| `npm run benchmark:generate` | regenerates `specs/benchmark/spec.jsonc` | `specs/benchmark/spec.jsonc` |
| `node tools/check-spec.js <spec>` | one specification validates; claims and scenarios | terminal |
| `node tools/conformance.js [--engine "<command>"]` | an engine reproduces every golden trace of `tests/conformance/`: by default the WebAssembly engine through `src/core/engine.js`, or a command reading an input on stdin (the native `engine/target/release/exegra-sim`) | terminal |
| `node cli/exegra.js integrity [--project <name>]` | every integrity rule of the project holds, with instances, or is violated with counterexamples ([integrity-rules.md](integrity-rules.md)) | terminal |
| `node cli/exegra.js prove-integrity [--project <name>]` | each integrity rule is proved in Lean (`holds`, by reflection) or refuted from concrete witnesses, kernel-checked with standard axioms only, after the Lean checker and the JavaScript evaluator agree; needs Lake | terminal, `formal/generated/integrity/` (ignored by git) |
| `node cli/exegra.js traceability` | declared modules exist; every source file is claimed (per realisation root, when the project declares roots) | terminal |
| `npm run check` | typecheck, `npm test`, `npm run test:browser`, `npm run verify` in sequence | terminal, `specs/exegra/evidence/results.json` |

Typecheck does not cover `src/render`, `src/ui` or `src/app`. Tests run with a limited number of jobs: `npm test` uses `--test-concurrency=2`, and Playwright runs two workers by default (`EXEGRA_TEST_WORKERS` changes it), each with its own scratch projects.

## `npm test`

`node --test` over `tests/core/*.test.js`. These suites use in-memory specifications, temporary directories and `node:test`; they do not need a browser. The run has a wall-clock budget of 120 s (`tools/run-unit-tests.js`): past it the test process tree is killed and the slowest tests so far are listed. The budget is never raised; a slow test is shrunk, or, when it re-checks a proof or runs a long differential, moved to `tests/proofs` (`npm run test:proofs`, which `npm run verify` and the Check workflow run).

The table below does not list every file. `tests/proofs` holds the tests that re-check proofs and run long differentials (`formal-semantics.test.js`, `formal-explore.test.js`, `formal-integrity.test.js`, `lean-theorem.test.js`, `integrity-nemo.test.js` and the two corpus sweeps of `model-kernel.test.js`); `npm run test:proofs`, `npm run verify` and the Check workflow run them, `npm test` does not. `tests/core` also holds `concordance.test.js`, `traffic.test.js`, `replay.test.js`, `distributions.test.js`, `metric-spec.test.js`, `metric-stats.test.js`, `runtime-data-complete.test.js`, `outcome-reuse.test.js`, `activity-pairing.test.js`, `fault-model.test.js`, `model-kernel.test.js` (the edge cases of the Lean derivation against the JavaScript it replaced), `references.test.js`, `queueing-fixtures.test.js` and `pool-fixture.test.js`. The last two are skipped unless `EXEGRA_FIXTURES=1` is set, and their claims stay inconclusive until `verify` records a result.

| File | Covers |
|---|---|
| `model.test.js` | Parsing and indexing, duplicate ids, unresolved and mistyped references, unsupported constructs diagnosed, unknown claim methods as warnings, syntax errors, containment rules, expression checks, vocabulary extension (categories, relationship kinds, properties), gap diagnostics, normalisation equivalence, queries. |
| `vocabulary.test.js` | Model-defined vocabulary: declared entity kinds parse into entities with their own sections and properties; they are validated like built-in kinds (enum, required, unresolved and mistyped references, duplicate or unknown sections, unknown kinds in a `ref`); references through declared `ref` and `list` properties follow renames and block deletes; a claim using a declared external verification method is never reported as verified. |
| `roundtrip.test.js` | Visual and source edits change exactly the expected text; comments and formatting survive create, rename, connect and delete; rename rewrites references, claim evaluations and behavior names in expressions; delete refusal and cascade repair; atomic rejection; undo and redo restore exact text; layout moves cannot change the semantic hash; stale transactions refused; external reload adopts valid text, ends the undo history and keeps the last valid model on syntax errors. |
| `claims.test.js` | Each structural method (holding and failing, vacuous selectors inconclusive, `reachable` needs a path of at least one relationship); unsupported methods not evaluated; determinism; the evidence rules (none, document, unexecuted test, recorded pass, recorded fail, contradicting); each trace method; vacuity (an implication with an antecedent never true, zero-step traces, a `never` about an event that cannot occur are inconclusive); `checkTrace` on finished and unfinished runs, pending checks, and only for claims that list the scenario. |
| `lean.test.js` | The Lean call boundary (`src/core/lean.js`): the core loads synchronously in Node and lists its registered functions; an unknown function, malformed arguments and a refused input are error values and the boundary keeps answering; `engine.run` returns the facade's trace, from text and from parsed arguments. |
| `lean-theorem.test.js` | The `lean-theorem` method: no recorded check is not evaluated; the rule on recorded facts (kernel, axioms, kind, statement mentions); with Lean, `Exegra.runInput_terminates` about `Exegra.runInput` is proved and theorems using `sorry`, `native_decide`, an own axiom, an off-topic statement and a missing name are refused (`tests/fixtures/lean-theorem/Refused.lean`). Skips the Lean part without `lake`. |
| `sim.test.js` | Through `src/core/engine.js` on the Lean WebAssembly engine: request/ack machines with emitted and delayed events, guards over payload and other machines, each fault kind, step limit, expression errors, reset, stepwise equals run (the trace cursor the Simulation tab steps through), trace immutability, determinism. |
| `conformance.test.js` | The Lean engine as WebAssembly, through `src/core/engine.js`, reproduces every golden trace of `tests/conformance/` from the model and from the committed input alone; the Rust engine, the differential oracle, reproduces them as WebAssembly (`tools/rust-engine.js`) with byte-identical traces to the Lean engine, and as the native binary `engine/target/release/exegra-sim` when it is built (skipped with a message otherwise); `simulationInput` derives exactly the committed inputs; the runner reports an altered trace at the right step and path. |
| `flows.test.js` | The message flow of every step of a scenario: sender from the emitting behavior or outside, receivers from the behaviors that fired; paths along the edge between the drawn nodes in either direction, never along an unrelated one; unshown when only a hidden relationship connects them, undeclared when none does; collapsed subsystems, dropped events and components not drawn. |
| `projections.test.js` | Implicit views, every scene element backed by an entity, collapse lifting, hide, isolate, view filters, claim status marking, custom projection registration, determinism; layout overlap, containment, flow direction, pins, cycles and cross-container edges; author-entered evidence and generated implementations never drawn in a verified colour. |
| `data-model.test.js` | Records and copies: the data slice fixture (`tests/fixtures/data-model/spec.jsonc`) validates with exactly one data-rule finding, its deliberately missing erasure point; wrong enums, unknown key and copy fields and numeric bounds without a unit are errors with their paths; each data rule reports its entity and field on a constructed violation; `data-model` claims are violated, verified or inconclusive as the findings say; the Data view. |
| `references.test.js` | The `references` projection: focus at depth 1 and 2, every node and edge backed by an entity, declared kinds take their shape and colour from the meta-model, violated claims coloured, `filter.entityKinds`, no focus, the implicit view, the cap of 150 with its note, determinism. |
| `layout.test.js` | The four layout methods: soundness (no sibling overlap, containers enclose children), determinism, levels, pins, empty scenes, unknown method refused; `chooseLayout` scores every method and takes the lowest total; `scorePlacement` agrees with it and prefers better aspect and fewer crossings; target aspect shapes packed and layered results; radial centre; a 400-node, 500-edge performance bound. |
| `generate.test.js` | Exactly five artifacts, byte-identical on rerun, insensitive to comments and key order, valid JSON carrying the semantic hash, violated claim becomes a high-severity task, every component named. |
| `import-markdown.test.js` | The Markdown importer: a requirement with every key becomes a claim, retired requirements and unknown keys, unresolved references counted not dropped, component and boundary rows, helpers; a small fixture specification (`tests/fixtures/markdown-import/`) converts through its import map, validates, is covered and deterministic; the importer's command line; a linked project resolved through `project.jsonc` whose documents the `markdown` command renders. |
| `disk-reload.test.js` | The browser app reloads product files: the watcher reports an added, changed and removed product file as `products`, the session's reload re-derives the layered model from them, a product file that does not parse keeps the last valid model. |
| `cli-project.test.js` | `project add`, `remove` and `list` (relative links, refusals without `--force`, bad names, a directory with its own `spec.jsonc`) and the project given inline with `--spec` and `--product`. |
| `workspace.test.js` | Name and path validation, base-hash writes, conflicts leave files untouched, only `spec` and `layout` writable, `generated/` confinement, export and import round trip, journal lines. |
| `external-realisation.test.js` | Realisation roots (fixture `tests/fixtures/external-root`): modules checked per root, an undeclared alias missing, unclaimed files only for roots with include globs, no roots giving the earlier result, malformed roots refused; a bun-shaped JUnit report parsed with its describe path; pass, fail and not-run per evidence entry, environmental failures not-run; `verify --ingest-only`, a root test command run, and a command that writes no report. |
| `integrity.test.js` | Integrity rules on `tests/fixtures/integrity`: the rule language and its syntax errors; every rule holds with its instance count; every rule of the fixture is falsified by its mutation in `mutations.json` with the stated counterexample, and a rule without a mutation fails the test; a decision resting on the gap it resolves holds; diagnostics with the rule severity at the first entity; invalid and vacuous rules; the ratchet of `apply`; the `integrity` command and `--rules`. |
| `formal-integrity.test.js` | Integrity rules in Lean (`formal/Exegra/Integrity.lean`, `exegra prove-integrity`): every fixture rule proved by reflection, kernel-checked, standard axioms only; every mutation refuted from its stated witness; on 25 seeded random mutations the Lean checker and the JavaScript evaluator agree on the verdict and the counterexamples of every rule. Skipped, with a message, without Lake. |
| `cli.test.js` | `validate`, `list`, `show`, `deps`, `apply` (writes, stale hash, invalid operation, `--dry-run`), `plan-delete`, `simulate`, `ops`, usage errors with exit code 2; the test-count parsing that makes a reference matching no test a failure. |
| `fact-producers.test.js` | The facts statuses rest on, without Lean (hand-built models): skip-aware test evidence on the fresh and reuse paths over `tests/fixtures/skipped-tests/demo.test.js`; a skip recorded as not run; stale and unverifiable reads of recorded results, external tool outcomes and Lean checks; the records stamp and the formal hash; the `lean-theorem` refusals (no `about`, opaque, implemented_by, extern, partial); open-startedness of metric claims; admit and verify regression gating. |
| `pages-site.test.js` | The Pages workflow read structurally (trigger, permissions, the build job's order with no condition or ignored failure, deploy needs build) and the relative Vite base; the checks fail on the five mutants of the 2026-11-26 assessment. |

## `npm run test:browser`

Playwright (`playwright.config.js`) starts its own Vite server on a port derived from the checkout path (5200-5999, `EXEGRA_TEST_PORT` overrides; reusing one if running), two workers, Chrome via `channel: 'chrome'`, in three projects: `desktop` (1600x1000) runs every file except `mobile.spec.js`; `phone` (iPhone 13, 390x844, touch) and `tablet` (820x1180, touch) run the tests of `mobile.spec.js` tagged `@phone` and `@tablet`. `exegra verify` runs a referenced file without naming a project, so each test runs in the one project that selects it. **Tests never modify the shipped specifications.** `global-setup.js` resets one scratch copy per worker slot of the self-specification (`specs/zz-test-exegra-w<n>`) and of the multiplayer example, a test fixture at `tests/fixtures/multiplayer/spec.jsonc` (`specs/zz-test-multiplayer-w<n>`), through `tests/browser/scratch.js`; `resetScratch` recreates a slot's copy before a test that uses it, and `global-teardown.js` calls `removeScratch`. The shipped `benchmark` project is only read, and a local test of a linked project asserts that its file is unchanged afterwards. Tests drive the real UI (canvas clicks at projected positions) and check the model in the page, the DOM and the files on disk, and fail on any uncaught page error.

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

`tests/browser/lean-core.spec.js`:

- the Lean core runs in the page and reproduces golden traces (`src/core/lean.js` loads the wasm64 module, lists the registered functions, answers an unknown function with an error value, and `engine.run` gives two golden traces exactly)

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
node cli/exegra.js verify --project exegra --expect-violated edits-only-via-transactions,core-logic-in-lean,core-dependencies-acyclic,core-static-dependencies-acyclic --pretty
```

The pipeline, in order: validate the specification; run the traceability check; execute every `test` evidence reference (evidence in a realisation root is decided from that root's JUnit reports, see [Realisation roots](#realisation-roots-code-and-tests-in-other-repositories)); check the theorems of the `lean-theorem` claims with Lean (`tools/lean-theorems.js`; without `lake` on the PATH, or with `EXEGRA_NO_LEAN=1`, the checks recorded before are kept, and each one checked on other `formal/` sources than the current ones reads as stale, so it proves nothing); write `specs/<project>/evidence/results.json` (`results` keyed by evidence id with `outcome`, `ranAt`, `stamp` (the records stamp of the tree, [claims-and-evidence.md](claims-and-evidence.md#freshness-of-recorded-facts)) and, on failure or skip, `detail`, plus `traceability` and `theorems`, keyed by theorem name, each with `formalHash`, `stamp` and `statementHash`); re-evaluate all claims with those results against the current stamps; compare the statuses with `claimBaseline`, the statuses the last passing run recorded, and on a passing run record the new ones there. Exit code 1 results if there are validation errors, a failed test, a violated claim not listed in `--expect-violated`, or a regression against the baseline:

- a claim that was `proved`, `verified`, `supported` or `model-holds` now has a lower status, `inconclusive` and `not-evaluated` included (a test that started to skip, a stale Lean check, a removed test);
- such a claim no longer exists;
- a claim listed in `--expect-violated` is violated with another counterexample than the one recorded (its fingerprint: summary, entities, path, step), so the violation is no longer the known one.

`--accept-change a,b` accepts the change of the named claims for this run, which then records the new baseline; a failing run keeps the earlier baseline, so running `verify` again does not wave a regression through. The first run that records a baseline compares with nothing. A specification with syntax errors fails the command without running anything.

An evidence `ref` is `<path>` (run the whole file) or `<path>#<title pattern>` (run matching tests). The references run in batches (`cli/test-batch.js`): one `node --test` process per test file, given every name pattern the file's references use (or no pattern when one of them names the whole file), and one Playwright run with two workers for all browser references, which needs Chrome. At most two processes run at a time; a Playwright run takes both slots. Each reference's outcome is read from the runner's per-test results with the rule below, so a failing test fails only the references whose pattern matches it. Verify has no option that runs a subset of the evidence (`--skip-browser` records browser evidence as not run).

**Reuse.** Each node test file's run records the repository files it loaded or read through `fs` (`tools/trace-reads.js`), the directories whose listing it read and the programs other than node and git it started, with a hash of their contents, under `coverage` in `results.json`; every reference of the file points at that record, so per-test coverage is not attempted and a reference depends on everything the file's referenced tests touched. A browser file's record is the application, the engine builds, the support files and fixtures and the specifications. A recorded pass or skip is reused, and marked `obtained: reused`, when its reference is unchanged and the record still hashes to the same value (formal/ sources stand for `lake`, the whole tree for any other program); otherwise the file runs again, with all its references. The same record feeds change impact (`verify --change`, `impact`).

**Reference names.** `validate` reports `evidence.ref-no-test` for a reference whose name matches no test the file declares (a static scan of its `test`, `it` and `describe` calls, `tools/test-names.js`); a file that names tests at run time is not checked.

 A Node test reference that matches no test (a title pattern that selects nothing, or a file with no tests) is recorded as a failure with the detail "the reference matched no test"; Node itself exits 0 in that case, so the exit code alone is not trusted. References may contain only letters, digits, `_`, `.`, `/`, `-`, space, `#` and `:`. A reference passes only when at least one matched test executed and passed and no matched test failed, skipped itself or is a `todo`; a `describe` block is never a test of its own. The same rule (`testsVerdict` in `cli/outcomes.js`) decides the fresh path (node's TAP output, Playwright's summary) and the reuse path (outcomes recorded by `npm test`). A reference whose matched tests skipped, wholly or in part, is recorded as `not-run` and never keeps an older pass, so a whole-file reference to a file with a test that skips where Lean or a native binary is missing is not a pass in that environment. `--skip-browser` skips browser evidence and records it as `not-run`, unless its earlier result was recorded on the same tree stamp. `--ingest-only` reads realisation roots' JUnit reports without running their test commands.

**Why some claims are expected to be violated.** `--expect-violated` names claims that are violated by design or by a known defect, so that a violation you did not expect fails the command and one you did expect does not:

- `edits-only-via-transactions` (exegra): a real discrepancy. Import writes through the persistence service without the transaction pipeline.
- `core-logic-in-lean` (exegra): the target of WG-4785. It lists the components of the verified kernel (tag `verdict-kernel`: model derivation, semantic hash, engine-input derivation, engine, explorer, claim verdicts, transactions) whose `implementation.language` is not yet `lean`, and stays violated until the per-module ports finish; then it is verified and leaves this list. JavaScript outside the kernel is in the trusted base (`trusted-js-shell`), outside the verdict path.
- `core-dependencies-acyclic` and `core-static-dependencies-acyclic` (exegra): real discrepancies found by extraction (WG-5696). The imports read from the code (`specs/exegra/extracted/facts.json`) give static dependency cycles among the components of the semantic core that the hand-declared relationships never showed: formal-semantics, resource-model and workload-model through `formal/Exegra/Format2.lean` and `Impl/Semantics.lean`; verdict-boundary, metric-claims, integrity-rules, validator, generation-readiness, simulation-contract, fault-model, exhaustive-explorer, proof-export, lean-call-boundary and parser through `src/core/` and `formal/Exegra/Api/Engine.lean`; property-controls and dialogs in the interface. They stay violated, with their counterexample recorded, until the ownership or the imports are changed; the claims are not weakened.
The multiplayer fixture carries two more such claims, `ack-implies-durable-under-early-ack` (a seeded behavioral defect, kept to demonstrate a counterexample) and `database-reached-only-by-runtime` (a seeded structural defect, `telemetry-reads-game-database`). They are not part of any script; the browser tests rely on them.

Only `test` evidence is executed. Measurement, document and review evidence stay author-entered. The recorded results are tied to the tree by their stamp: `exegra claims`, `evaluate`, `gaps`, `admit` and `generate` read a result recorded on another stamp as stale (not evaluated), and the application, which cannot stamp the tree, shows them with unverifiable freshness.

`exegra admit` ranks `not-evaluated` with `inconclusive`: a claim that falls from a positive status to `not-evaluated` is `admit.claim-regressed`, which cannot be accepted, and removing a claim that was positive is `admit.claim-removed`, which only `--accept admit.claim-removed` acknowledges.

## `npm run generate`

`exegra generate --write` writes `manifest.json`, `ARCHITECTURE.md`, `claims-report.md`, `claims-report.json` and `tasks.json` under `specs/<project>/generated/`. Output is a pure function of the model, claim results (with recorded results), diagnostics and traceability: the same inputs give byte-identical files, and only changed files are rewritten. Comparing the files before and after a run shows drift between the model and the committed artifacts.

## `node tools/check-spec.js`

```sh
node tools/check-spec.js specs/exegra/spec.jsonc [--trace <scenarioId>]
```

Read-only. Prints diagnostics with line and column, the semantic hash, entity counts, each scenario's steps and outcome, and every claim's status with its explanation and counterexample; `--trace` lists one scenario's steps. Exit code 1 if there are validation errors. It does not use recorded results.

## `node cli/exegra.js traceability`

Compares `implementation.modules` of every component (repository-relative paths; a trailing `/` claims a directory) with disk. It reports `checkedModules`, `missingModules` (declared but absent) and `unclaimedFiles` (files under `src/`, `cli/`, `tools/` with extension `.js`, `.json`, `.css` or `.html`, plus `index.html` and `vite.config.js`, that no component claims). It compares paths only: it does not check that a module implements its component or that relationships match imports. A project that declares realisation roots is checked against them instead (next section).

## Realisation roots: code and tests in other repositories

A project whose code lives in other repositories (a linked project such as a specification realised in three sibling repositories) declares those repositories as **realisation roots** in its `specs/<project>/project.jsonc`. A module or test evidence reference written `<alias>:<path>` then points into that root.

```jsonc
// specs/<project>/project.jsonc
{
  "spec": "../../../system-specs/system/spec.jsonc",
  "roots": {
    "platform": {
      "path": "../../../platform",                           // relative to this directory, or absolute
      "include": ["apps/*/src/**/*.ts"],                     // only roots with include globs report unclaimed files
      "exclude": ["**/*.test.ts", "**/*.d.ts"],
      "tests": [                                             // one object or a list
        { "command": ["bun", "test", "--reporter=junit", "--reporter-outfile=.exegra/junit.xml"],
          "cwd": "apps/api", "junit": "apps/api/.exegra/junit.xml" }
      ],
      "notRunWhen": ["ECONNREFUSED", "docker"]              // optional; replaces the default patterns
    },
    "database": { "path": "../../../database" }
  }
}
```

In the specification:

```jsonc
{ "id": "tenant-service", "implementation": { "status": "manual",
    "modules": ["platform:apps/api/src/tenant/", "database:migrations/0007_tenant.sql"] } }
{ "id": "ev-ten-2", "claim": "ten-2", "kind": "test",
  "ref": "platform:apps/api/test/auth/database-adapter.test.ts#database adapter > tenant scoping > rejects a cross-tenant read" }
```

**Why project.jsonc and not the specification.** A root's path, its globs and the command that runs its tests describe where a checkout sits on one machine and how to run it there; the specification describes the system and is shared. project.jsonc is already the machine-local binding of a project (it names where the specification is), it is ignored by git for linked projects, and keeping roots out of the specification needs no change to the meta-model. The specification carries only the alias, which is stable across machines. A `project.jsonc` may declare `roots` without `spec`; the specification is then `spec.jsonc` in the project directory.

| Field | Meaning |
|---|---|
| `path` | The root directory (required). |
| `include`, `exclude` | Globs (`path.matchesGlob`) over root-relative paths. Without `include` the root is not scanned and reports no unclaimed files; only its declared modules are checked. Only the directories an include glob can reach are walked, and `node_modules` and `.git` never are. |
| `tests` | Runs that produce JUnit XML: `junit` (the report, root-relative or absolute; required), `command` (program and arguments, run without a shell in `cwd`), `cwd` (root-relative, default the root), `base` (the directory the report's `file` attributes are relative to, default `cwd`). |
| `notRunWhen` | Case-insensitive regular expressions. A failure whose message matches one is an environmental failure. Default: `ECONNREFUSED`, `ENOTFOUND`, `EAI_AGAIN`, `docker`, `testcontainers`, `container runtime`. |

**Traceability with roots.** A module `<alias>:<path>` (trailing `/` claims a directory) is checked in that root; one naming an alias that is not declared is missing with `reason: "root not declared"`; a module without an alias is checked in this repository as before. Unclaimed files come only from roots with `include`, reported as `<alias>:<path>`; this repository's own surface is not scanned once roots are declared. The result adds `roots`: per alias `path`, `found`, `checkedModules`, `scanned`, `scannedFiles`, `unclaimedFiles`. With no roots the result is unchanged.

**Test evidence in a root.** `verify` runs each `tests` command of a root that has evidence pointing into it, then reads its JUnit report; `verify --ingest-only` runs nothing and reads the reports already on disk, which makes the result a pure function of the reports (`ranAt` is the report's modification time). A report that the command did not rewrite is ignored as stale. The command's exit code is not used: a runner exits non-zero when any test fails.

An external reference is `<alias>:<file>[#<describe> > ... > <test name>]`. The file is matched against the report's `file` attributes (made root-relative through `base`); the name path against the enclosing `testsuite` names (bun nests a suite per `describe`; a suite that stands for the file is skipped) followed by the test name. A path selects the test cases it equals or is a prefix of, so a describe path or a bare file selects all tests beneath it. The outcome of one evidence entry:

| Matched test cases | Outcome |
|---|---|
| any `<failure>` whose message matches no `notRunWhen` pattern | `fail` (detail: test path and message) |
| otherwise any `<error>`, or a `<failure>` matching a `notRunWhen` pattern | `not-run` (the environment, not the requirement) |
| otherwise at least one pass | `pass` (skipped tests beside it are ignored) |
| all skipped, none matched, no report, the command could not start or wrote no report, or the alias is not declared | `not-run` with the reason |

`not-run` is recorded in `results.json` but is never a failure: `verify` fails only on `fail`, and the claim evaluator treats `not-run` as no recorded result (a claim resting only on it is *inconclusive*). The verify result lists those ids in `notRun` and each root's `ran`, `reports` and `problems` in `roots`. bun writes JUnit with `bun test --reporter=junit --reporter-outfile=<file>`; a test file that fails to load is absent from bun's report and so is `not-run`.


## Where results live

- `specs/<project>/evidence/results.json`: recorded test results with their tree stamps, Lean theorem checks with the hash of the `formal/` sources, the claim baseline of the last passing `verify`, and traceability.
- `specs/<project>/generated/`: `claims-report.*` and `tasks.json` snapshots.
- The *Verification* and *Realisation* tabs and `node cli/exegra.js gaps`/`claims`: current state, computed on demand.
