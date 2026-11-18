# Exegra

Exegra is a self-describing, visual, executable system specification environment, written in vanilla JavaScript with Three.js and Vite. A system is specified in one JSONC text file. From that file Exegra derives a single semantic model and projects it into a 3D scene, an inspector, a source editor, claim and behavior views, a discrete-event simulator and an agent command line. Every editor changes the same text through the same transactional operations, so the views cannot disagree. Exegra is its own first subject: `specs/exegra/spec.jsonc` specifies Exegra, including what is not yet true of it.

## Capabilities

- **One specification, many views.** Components, relationships, contracts, requirements, decisions, claims, evidence, behavior models, fault models, and data records with their copies all live in one JSONC file, validated with positions. Views include a 3D architecture scene, an inspector, a source editor, and claims, behavior, data and realisation views. The interface is mobile first.
- **Transactional editing.** Every change, from the UI or from the agent command line (`exegra apply`), goes through typed operations with dry runs, undo and conflict detection.
- **Claims with evidence.** Claims are evaluated structurally (graph and data-model rules, such as erasure reaching every copy and no shared copy holding personal data), on simulated traces, or from recorded test evidence. A trace claim counts as verified only when its declared negative scenarios each violate it.
- **Simulation.** A discrete-event simulator, the Lean semantics itself compiled to WebAssembly, executes behavior state machines under injected faults. Steps play as message flows in the scene. Events can be the requests and responses of contracts, so a trace reads as a request log that is checked against those contracts.
- **Formal semantics in Lean 4.** The behavior language is defined as an executable semantics in `formal/`. It is the engine that runs: compiled to WebAssembly (wasm64) it runs in the browser and in Node, so the theorems are about the code that runs. The former Rust engine is kept as a differential oracle, checked against it on every golden trace and on generated inputs. Determinism, termination and the resource invariants are proved.
- **Verified exploration.** `exegra prove` explores every ordering of simultaneous events and every combination of declared faults within a bound, using an explorer proved sound in Lean. It reports state invariants and `never`, `precedes` and `eventually` claims as holding, or gives a real counterexample run.
- **Format 2, in progress.** Instances, resources with capacity, class queues and reservations, and seeded random streams are implemented in Lean and Rust. Workloads, latency, bandwidth and statistical metric claims are specified in `docs/simulation.md` but not built yet.

What Exegra establishes is the consistency of a *design*. Its models are hand-written abstractions: they do not show that an implementation behaves the same way, and they are not load or capacity measurements. `docs/simulation.md` states what each result does and does not mean.

## Requirements

- Node.js 24 or later.
- elan with the Lean toolchain of `formal/lean-toolchain`, git, and network access for the first `npm run build:formal-wasm` (it fetches emscripten 7.0.0, the Lean runtime sources and libuv into a cache outside the repository).
- Rust stable with the `wasm32-unknown-unknown` target (`rustup target add wasm32-unknown-unknown`) and `wasm-bindgen-cli` 0.2.122 exactly (`cargo install wasm-bindgen-cli --version 0.2.122 --locked`). The Rust engine (`engine/`) is the differential oracle the tests compare the Lean engine with. On Windows the MSVC toolchain is used (`stable-x86_64-pc-windows-msvc`) unless `RUSTUP_TOOLCHAIN` says otherwise.
- A browser with WebAssembly Memory64 to use the application: Chrome 133+ or Firefox 134+. Stable Safari does not support Memory64 yet, so Exegra does not run there.
- For `npm run test:browser`: an installed Google Chrome. The Playwright configuration uses `channel: 'chrome'`, so no browser is downloaded.

## Quick start

```sh
npm install
npm run dev
```

`npm run dev` first builds the Rust oracle and the Lean core (`npm run build:engine`, `npm run build:formal-wasm`, below). Open the URL Vite prints (default `http://127.0.0.1:5173/`). Switch project with the picker in the app bar. Saving works only under `npm run dev`; a production build (`npm run build`, `npm run preview`) bundles the shipped specifications and is read-only.

## Scripts

| Script | What it does |
|---|---|
| `npm run build:formal-wasm` | Builds the Lean core (`formal/`) to WebAssembly (wasm64) into `src/engine/lean/` from pinned inputs; the engine Exegra runs. Generated, not committed; caches downloads outside the repository ([docs/simulation.md](docs/simulation.md), "Building and loading the engine"). `dev`, `build`, `test`, `test:browser`, `generate` and `verify` run it first. |
| `npm run build:engine` | Builds the Rust engine, the differential oracle, for WebAssembly (`cargo build --release --target wasm32-unknown-unknown -p exegra-engine-wasm` in `engine/`, then `wasm-bindgen --target web --out-dir src/engine/pkg`). `src/engine/pkg/` is generated and not committed. `dev`, `build`, `test`, `test:browser`, `typecheck`, `generate` and `verify` run it first. |
| `npm run dev` | Vite dev server with the persistence middleware (the only place edits are saved). |
| `npm run build` | Production build into `dist/`. No write path; the app reports its save state as read-only. |
| `npm run preview` | Serves the production build. |
| `npm run typecheck` | `tsc` over `src/core`, `src/persist`, `tools`, `cli` with `checkJs` and `strict`. |
| `npm test` | Node test suites under `tests/core` (two at a time). |
| `npm run test:browser` | Playwright suites under `tests/browser`. The `exegra` and multiplayer-fixture tests work on scratch copies; the `benchmark` test and the local `local-*.spec.js` tests of linked projects only read their project. |
| `npm run check` | Typecheck, then `npm test`, then `npm run test:browser`. |
| `npm run exegra -- <command>` | Runs the agent CLI. |
| `npm run generate` | Writes deterministic artifacts to `specs/exegra/generated/`; `exegra generate --write --project <name>` does it for another project. |
| `npm run verify` | Executes the test evidence of the `exegra` project and records results in `specs/exegra/evidence/results.json`. |
| `npm run import:markdown -- --project <name>` | Converts a checkout of a repository that still has its Markdown specification (an earlier commit) into JSONC, as its import map says ([docs/importing-markdown.md](docs/importing-markdown.md)). |
| `npm run benchmark:generate` | Regenerates `specs/benchmark/spec.jsonc`. |

Details of each check are in [docs/verification.md](docs/verification.md).

## Tour of the interface

The interface is designed for a phone first and expands to a tablet and a desktop. The same panels serve every size; only where they sit changes.

- **Phone** (narrower than 768 px). The 3D scene fills the screen and stays live behind everything: drag to orbit, pinch to zoom, tap to select (rest a finger on a node to drag it). A one-row **app bar** floats over the top: the Exegra mark, a title button (the project small over the view) that opens a picker of views and projects, search (a full-screen sheet whose results select and frame the entity), a **status badge** (one dot coloured by the worst of errors, warnings and gaps, and their total; tap it for Diagnostics) and an overflow menu (⋮), badged when the save state needs attention, with the save state and the editing tools (select or connect mode, New, Delete), the layout method and Reset layout, the camera and Fit, the legend and render statistics, and Export and Import. A **bottom navigation** holds Explore, Inspect, Simulate, Verify and More (Changes, Diagnostics, Source, Realisation). Each destination is a **bottom sheet** with three heights: drag its header, flick it, tap the handle to step through peek, half and full, or tap the destination again (or press Escape) to put it away. Tapping an entity in the scene opens the inspector at peek with its name, kind and status. Undo and redo float at the bottom left, Fit and the camera pair at the bottom right. While a scenario is loaded a **transport** docks above the navigation (step back, play or pause, step, the step counter, run to end), so messages can be watched travelling through the scene. Dialogs are full-screen, tables are lists of cards and every control is at least 44 by 44 pixels.
- **Tablet** (768 px and wider). The navigation becomes a **rail** on the left with a button for every destination, search and undo/redo sit in the bar (the title button, status badge and overflow menu stay until desktop width), and a destination opens as a **side panel** beside the scene, with a close control and a width you can drag.
- **Desktop** (1200 px and wider). The **explorer** is a column of its own on the left, the scene in the middle and the **context panel** on the right (the inspector unless the rail chose Simulate, Verify, Changes, Diagnostics, Source or Realisation; the table-heavy ones open wider). Every tool sits inline in the app bar, with separate project and view selects, the three counts and a save button when the save state needs attention, the legend starts open when it is short and the render statistics are shown.

What each panel holds:

- **Explorer**: a filterable component tree and lists of relationships, contracts, behaviors, scenarios, claims, assumptions, evidence and views; the selected row's buttons hide, isolate and collapse it in the scene.
- **Scene**: the projected model. Select, drag to pin a node (presentation only), double-click to open or close a subsystem, Connect mode creates relationships.
- **Inspector**: controls built from the meta-model, so properties added through a specification's `vocabulary` get controls too; relationships, dependencies, claim results, and connect, rename and delete actions.
- **Simulation** (scenarios, faults, timeline, live claim checks), **Verification** (claims with status, scope and evidence), **Changes** (the revision log), **Diagnostics** (errors, warnings, gaps), **Source** (a plain text editor over the specification; a draft is applied only when it parses and validates) and **Realisation** (implementation status per component, generated artifacts, traceability).

## Projects

| Project | What it is |
|---|---|
| `exegra` | The self-specification: 58 components, 180 relationships, 25 claims, ten behaviors and four scenarios for the edit and save flows. |
| `benchmark` | Synthetic, generated by `tools/make-benchmark.js`: 396 components and 507 relationships for load and render testing. Marked `illustrative`. |

The illustrative multiplayer platform (a command-processing example with a seeded behavioral defect and a seeded structural defect) is not a shipped project. It is a test fixture at `tests/fixtures/multiplayer/spec.jsonc`; the browser tests copy it to a scratch project `specs/zz-test-multiplayer`.

### Linked projects, specifications in other repositories

Any other directory under `specs/` is a linked project: local data that git ignores (`.gitignore` ignores `specs/*` except the two shipped projects). Its `project.jsonc` names a specification file that lives in another repository (for example `{ "spec": "../../../other-repo/specifications/spec.jsonc" }`, so the two checkouts sit side by side), and edits made in Exegra are written to that file. The project's layout, recorded results and generated artifacts stay under `specs/<name>/`. A project can be created from a Markdown specification with `tools/import-markdown.js`, driven by an import map; `node cli/exegra.js markdown --project <name>` renders the documents it holds back to Markdown. How the conversion works and what it checks: [docs/importing-markdown.md](docs/importing-markdown.md).

## Try a scenario

The self-specification has executable scenarios: `visual-edit-flow`, `source-edit-flow`, `rejected-edit` (its own fault `validation-fails` is active) and `edit-with-disk-conflict` (its own fault `disk-changed-externally` is active). Each runs the state machines of the edit flow: interaction, transactions, validator, session, projection, renderer and workspace service.

1. `npm run dev`, open the app, keep the project `exegra`.
2. Open the *Simulation* tab and select the scenario `visual-edit-flow`.
3. Press Step. Each step delivers one event and shows the transitions that fired and the variables that changed. The run ends quiescent: the commit is followed by the projection refresh and, one tick later, by the write to disk. No claim is violated.
4. Tick the fault `disk-changed-externally` (it restarts the run), then press Run to end.
5. A violation banner names the claim `file-matches-model-after-save`: the write is refused as a conflict, so the file on disk never reaches the committed revision. Select the step at which `workspace-detect-conflict` fires to see the configuration. The scenario `edit-with-disk-conflict` has this fault built in; its claims `conflict-never-overwrites` and `conflict-is-flagged` are about that run.

Switch to the *Edit flow behavior* view to see the same step on the state machines.

The command-processing example with the early-acknowledgement fault (`early-ack`, claim `ack-implies-durable`) lives in the test fixture `tests/fixtures/multiplayer/spec.jsonc`. It is exercised by the browser test *simulation steps through the trace; early-ack fault violates the invariant* in `tests/browser/exegra.spec.js`.

## Command line

```sh
node cli/exegra.js claims --project exegra --status violated --pretty
node cli/exegra.js simulate edit-with-disk-conflict --project exegra --steps
node cli/exegra.js apply --project exegra --dry-run --ops '{"type":"SetProperty","id":"parser","property":"owner","value":"core-team"}'
```

Every command prints one JSON envelope (`ok`, `command`, `project`, `semanticHash`, `result`) on stdout. `exegra help` lists all commands. See [docs/agent-interface.md](docs/agent-interface.md).

## Repository layout

```
src/core/      semantic core: parse, validate, operations, project, expr, sim-input, engine (the simulation engine facade), claims, projections, layout, generate/
src/engine/    lean/: the Lean core as WebAssembly (npm run build:formal-wasm); pkg/: the Rust oracle (npm run build:engine); both generated
src/render/    Three.js scene view, camera rig, geometry, labels, palette
src/ui/        HTML panels (shell, toolbar, explorer, inspector, source editor, simulation, verification, realisation)
src/app/       session (the object UI modules talk to), main (composition root), the simulation worker and its runner
src/persist/   browser client of the dev-server persistence boundary
tools/         workspace service, Vite plugin, traceability, spec checker, engine build, conformance runner, benchmark generator, Markdown importer
formal/        the Lean core: the semantics, its proofs, the call boundary (Exegra/Api*), wasm/ (C glue and runtime patch)
engine/        the Rust engine, kept as a differential oracle: exegra-engine (library and the native binary exegra-sim), exegra-engine-wasm
cli/           agent command line
specs/         exegra, benchmark (spec.jsonc, optional layout.jsonc, evidence/, generated/); linked projects (git-ignored) hold project.jsonc, and import-map.jsonc when converted from Markdown
tests/         core (node:test), browser (Playwright), conformance/ (golden engine inputs and traces), fixtures/ (the multiplayer example)
docs/          documentation
```

The dependency rules behind this layout are in [docs/architecture.md](docs/architecture.md).

## Where the limitations are recorded

This repository keeps no status or known-limitations document. Open limitations are part of the model and are read from it:

- `system.notes` and the `unknowns` of each component in `specs/exegra/spec.jsonc`
- the *Realisation* and *Verification* panels in the application
- `node cli/exegra.js gaps --project exegra --pretty`
- the generated task list `specs/exegra/generated/tasks.json`

Examples recorded there: nothing in the runtime is generated yet; behavioral claims are checked on listed traces only; the Import action bypasses the transaction pipeline, so the claim `edits-only-via-transactions` is reported violated; no schema migration exists although the schema carries a version.

## Documentation

- [Vision](docs/vision.md)
- [Architecture](docs/architecture.md)
- [Model and format](docs/model-and-format.md)
- [Transactions and persistence](docs/transactions-and-persistence.md)
- [Simulation](docs/simulation.md)
- [Claims and evidence](docs/claims-and-evidence.md)
- [Integrity rules](docs/integrity-rules.md)
- [Self-hosting](docs/self-hosting.md)
- [Verification](docs/verification.md)
- [Importing a Markdown specification](docs/importing-markdown.md)
- [Decisions](docs/decisions.md)
- [Module contracts](docs/module-contracts.md) and [agent interface](docs/agent-interface.md)
