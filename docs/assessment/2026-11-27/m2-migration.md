# M2 migration of Exegra's own relationships (WG-5693)

Every relationship of the legacy kind `calls` and its new kind, decided from its description and the code it names. Rows marked for M5 become extracted facts there (WG-5696).

| id | new kind | evidence |
|---|---|---|
| parser-calls-derivation-cache | invokes | Runtime operation call: parseSpec asks the cache for the derived model of a text before deriving it. |
| validator-calls-derivation-cache | invokes | Runtime operation call: analyzeSpec asks the cache for the semantic diagnostics of a text before validating it. |
| validator-calls-queries | imports | Description begins "Imports". (to be replaced by extracted facts in M5) |
| validator-calls-parser | invokes | Runtime operation call: analyzeSpec calls parseSpec, then validates the model. |
| validator-calls-expression-language | invokes | Runtime operation call: Parses guards, effect values and claim expressions and lists their references. |
| transactions-calls-parser | invokes | Runtime operation call: Re-derives the model after every text edit and parses a replacement source. |
| transactions-calls-validator | invokes | Runtime operation call: Project calls analyzeSpec on every candidate specification and refuses results with errors. |
| transactions-calls-expression-language | invokes | Runtime operation call: Operations parse expressions when renaming ids that expressions mention. |
| transactions-calls-queries | invokes | Runtime operation call: Finds declaration sites and owned entities when creating and deleting. |
| claim-evaluator-calls-queries | invokes | Runtime operation call: Builds the component graph and selects components for structural claims. |
| claim-evaluator-calls-expression-language | invokes | Runtime operation call: Evaluates claim expressions against trace configurations. |
| claim-evaluator-calls-simulation-engine | invokes | Runtime operation call: Runs the listed scenarios for invariant and temporal claims. |
| projection-system-calls-queries | invokes | Runtime operation call: Resolves components, ancestors and descendants for projection. |
| scene-renderer-calls-composition-root | invokes | Runtime operation call: Invokes the onSelect, onHover, onActivate, onMoveEnd and onConnect callbacks the composition root supplied ... |
| composition-root-calls-scene-renderer | invokes | Runtime operation call: Creates the scene view and calls setScene, setSelection, setHighlight, setMode, setCameraMode, fit, pulse a... |
| composition-root-calls-session | invokes | Runtime operation call: Selects, hovers, toggles collapse, requests fits, sets mode, starts the session and reports the scene viewp... |
| composition-root-calls-dialogs | invokes | Runtime operation call: Opens the connect dialog after two successive node clicks in connect mode. |
| composition-root-calls-shell | composes | Description begins "Mounts": the source mounts the target into the page. |
| composition-root-calls-inspector | composes | Description begins "Mounts": the source mounts the target into the page. |
| composition-root-calls-source-editor | composes | Description begins "Mounts": the source mounts the target into the page. |
| composition-root-calls-simulator-panel | composes | Description begins "Mounts": the source mounts the target into the page. |
| composition-root-calls-verification-panel | composes | Description begins "Mounts": the source mounts the target into the page. |
| composition-root-calls-realisation-panel | composes | Description begins "Mounts": the source mounts the target into the page. |
| session-calls-transactions | invokes | Runtime operation call: Creates a Project per opened project and forwards apply, undo, redo and reload. |
| session-calls-claim-evaluator | invokes | Runtime operation call: Re-evaluates claims after a semantic change and checks the simulator's trace. |
| session-calls-simulation-engine | invokes | Runtime operation call: Runs the loaded scenario in the engine worker and steps through the finished trace with a cursor. |
| session-calls-projection-system | invokes | Runtime operation call: Lists views and projects the active view with the interaction context. |
| session-calls-layout-engine | invokes | Runtime operation call: Lays the scene out with the pins of the active view from the layout file: chooseLayout with the viewport's ... |
| session-calls-persistence-client | invokes | Runtime operation call: Lists and reads projects, writes spec and layout text after commits and watches for external changes. |
| shell-calls-session | invokes | Runtime operation call: Passes the session to the panels it mounts and calls select, fit, undo and redo. |
| shell-calls-toolbar | composes | Description begins "Mounts": the source mounts the target into the page. |
| shell-calls-explorer | composes | Description begins "Mounts": the source mounts the target into the page. |
| shell-calls-activity-panels | composes | Description begins "Mounts": the source mounts the target into the page. |
| shell-calls-overlay | composes | Description begins "Mounts": the source mounts the target into the page. |
| shell-calls-dialogs | invokes | Runtime operation call: The Delete shortcut opens the delete dialog for the selection. |
| toolbar-calls-session | invokes | Runtime operation call: Switches project and view, sets modes and the camera mode, fits, chooses the layout method of the view with... |
| toolbar-calls-queries | invokes | Runtime operation call: Labels search results. |
| toolbar-calls-validator | invokes | Runtime operation call: Import analyzes the bundle's spec.jsonc with analyzeSpec and refuses it when it has syntax errors. |
| toolbar-calls-dialogs | invokes | Runtime operation call: Opens the create and delete dialogs. |
| toolbar-calls-persistence-client | invokes | Runtime operation call: Export reads a project bundle and Import writes one. |
| explorer-calls-session | invokes | Runtime operation call: Selects entities and toggles collapse, hidden and isolate marks. |
| explorer-calls-queries | invokes | Runtime operation call: Labels entities and finds ancestors. |
| explorer-calls-projection-system | imports | Description begins "Imports". (to be replaced by extracted facts in M5) |
| activity-panels-calls-session | invokes | Runtime operation call: Reads diagnostics and the log; selects or reveals the entity of a row. |
| overlay-calls-session | invokes | Runtime operation call: Reads the scene's legend and notes. |
| inspector-calls-session | invokes | Runtime operation call: Reads the selection, model and claim results, selects linked entities and reveals source. |
| inspector-calls-queries | invokes | Runtime operation call: Lists relationships, dependencies, contracts, children and references of the selection. |
| inspector-calls-property-controls | invokes | Runtime operation call: Renders one control per meta-model property definition. |
| inspector-calls-dialogs | invokes | Runtime operation call: Opens connect, create and delete dialogs. |
| property-controls-calls-queries | invokes | Runtime operation call: Labels referenced entities and finds declaration sites. |
| property-controls-calls-dialogs | invokes | Runtime operation call: Opens the rename, delete and nested-entity dialogs from a property control. |
| dialogs-calls-session | invokes | Runtime operation call: Reads the model and applies the dialog's operation. |
| dialogs-calls-queries | invokes | Runtime operation call: Labels entities and finds references. |
| dialogs-calls-transactions | imports | Description begins "Imports". (to be replaced by extracted facts in M5) |
| dialogs-calls-property-controls | invokes | Runtime operation call: Renders draft fields and rejections. |
| source-editor-calls-session | invokes | Runtime operation call: Reads the committed text and applies the draft. |
| source-editor-calls-validator | invokes | Runtime operation call: Analyzes the draft with analyzeSpec for its diagnostics. |
| source-editor-calls-parser | invokes | Runtime operation call: Parses the draft to find the location of an entity to reveal. |
| simulator-panel-calls-session | invokes | Runtime operation call: Loads, steps, plays, seeks and resets the session's simulation and selects entities. |
| simulator-panel-calls-queries | invokes | Runtime operation call: Labels entities. |
| verification-panel-calls-session | invokes | Runtime operation call: Reads claim results and recorded results; selects claims and switches to the claims view. |
| verification-panel-calls-queries | invokes | Runtime operation call: Labels claims. |
| realisation-panel-calls-session | invokes | Runtime operation call: Reads the model, claim results and recorded traceability; selects components. |
| realisation-panel-calls-queries | invokes | Runtime operation call: Labels components. |
| realisation-panel-calls-generators | invokes | Runtime operation call: Generates the five artifacts from the session's model and results in the browser. |
| realisation-panel-calls-persistence-client | invokes | Runtime operation call: Writes generated artifacts to the project's generated directory (development server only). |
| toolbar-calls-dom-helpers | imports | Description: builds its elements with the shared helpers; dom-helpers is a pure helper module the source imports. (to be replaced by extracted facts in M5) |
| shell-calls-dom-helpers | imports | Description: builds its elements with the shared helpers; dom-helpers is a pure helper module the source imports. (to be replaced by extracted facts in M5) |
| explorer-calls-dom-helpers | imports | Description: builds its elements with the shared helpers; dom-helpers is a pure helper module the source imports. (to be replaced by extracted facts in M5) |
| activity-panels-calls-dom-helpers | imports | Description: builds its elements with the shared helpers; dom-helpers is a pure helper module the source imports. (to be replaced by extracted facts in M5) |
| overlay-calls-dom-helpers | imports | Description: builds its elements with the shared helpers; dom-helpers is a pure helper module the source imports. (to be replaced by extracted facts in M5) |
| inspector-calls-dom-helpers | imports | Description: builds its elements with the shared helpers; dom-helpers is a pure helper module the source imports. (to be replaced by extracted facts in M5) |
| property-controls-calls-dom-helpers | imports | Description: builds its elements with the shared helpers; dom-helpers is a pure helper module the source imports. (to be replaced by extracted facts in M5) |
| dialogs-calls-dom-helpers | imports | Description: builds its elements with the shared helpers; dom-helpers is a pure helper module the source imports. (to be replaced by extracted facts in M5) |
| source-editor-calls-dom-helpers | imports | Description: builds its elements with the shared helpers; dom-helpers is a pure helper module the source imports. (to be replaced by extracted facts in M5) |
| simulator-panel-calls-dom-helpers | imports | Description: builds its elements with the shared helpers; dom-helpers is a pure helper module the source imports. (to be replaced by extracted facts in M5) |
| verification-panel-calls-dom-helpers | imports | Description: builds its elements with the shared helpers; dom-helpers is a pure helper module the source imports. (to be replaced by extracted facts in M5) |
| realisation-panel-calls-dom-helpers | imports | Description: builds its elements with the shared helpers; dom-helpers is a pure helper module the source imports. (to be replaced by extracted facts in M5) |
| persistence-client-calls-dev-server-plugin | invokes | Runtime operation call: Sends HTTP requests to /__exegra/* and opens the events stream. |
| dev-server-plugin-calls-workspace-service | invokes | Runtime operation call: Delegates every route to the workspace service. |
| workspace-service-calls-filesystem | invokes | Runtime operation call: Reads, writes, renames, appends to the journal and watches directories with node:fs. |
| ai-coding-agent-calls-agent-cli | invokes | Runtime operation call: Runs one command per process and reads the JSON envelope. |
| agent-cli-calls-workspace-service | invokes | Runtime operation call: Reads projects and writes changed files with the hashes read at the start; records verification results and... |
| agent-cli-calls-queries | invokes | Runtime operation call: Answers list, show, deps, contracts and plan-delete. |
| agent-cli-calls-claim-evaluator | invokes | Runtime operation call: Evaluates claims for claims, evaluate, trace and verify. |
| agent-cli-calls-simulation-engine | invokes | Runtime operation call: Runs scenarios for simulate and trace. |
| agent-cli-calls-generators | invokes | Runtime operation call: The generate command derives the artifacts. |
| agent-cli-calls-verification-pipeline | invokes | Runtime operation call: The traceability and verify commands run the module-to-disk check. |
| agent-cli-calls-test-suites | invokes | Runtime operation call: verify executes test evidence by spawning node --test on a core test file. |
| agent-cli-calls-playwright-runner | invokes | Runtime operation call: verify executes browser test evidence by spawning Playwright, unless --skip-browser. |
| agent-cli-calls-filesystem | invokes | Runtime operation call: Reads operation files and checks paths. |
| build-system-calls-dev-server-plugin | composes | Registers the plugin with the specs directory (build-time wiring). |
| generators-calls-queries | invokes | Runtime operation call: Lists children, relationships and contracts for the architecture document. |
| verification-pipeline-calls-filesystem | invokes | Runtime operation call: Scans src, cli, tools and the root files and checks that declared modules exist. |
| spec-checker-calls-validator | invokes | Runtime operation call: Analyzes the file with analyzeSpec. |
| spec-checker-calls-claim-evaluator | invokes | Runtime operation call: Prints the status of every claim. |
| spec-checker-calls-simulation-engine | invokes | Runtime operation call: Runs every scenario and optionally prints a trace. |
| benchmark-generator-calls-validator | invokes | Runtime operation call: Checks that the generated specification analyzes. |
| markdown-importer-calls-filesystem | invokes | Runtime operation call: Reads the Markdown tree and the import map, and writes or compares the generated file, with node:fs. |
| test-suites-calls-transactions | exercises | Source is the test suites: a test-harness interaction that drives the target to check it. |
| test-suites-calls-parser | exercises | Source is the test suites: a test-harness interaction that drives the target to check it. |
| test-suites-calls-validator | exercises | Source is the test suites: a test-harness interaction that drives the target to check it. |
| test-suites-calls-claim-evaluator | exercises | Source is the test suites: a test-harness interaction that drives the target to check it. |
| test-suites-calls-simulation-engine | exercises | Source is the test suites: a test-harness interaction that drives the target to check it. |
| test-suites-calls-projection-system | exercises | Source is the test suites: a test-harness interaction that drives the target to check it. |
| test-suites-calls-layout-engine | exercises | Source is the test suites: a test-harness interaction that drives the target to check it. |
| test-suites-calls-generators | exercises | Source is the test suites: a test-harness interaction that drives the target to check it. |
| test-suites-calls-workspace-service | exercises | Source is the test suites: a test-harness interaction that drives the target to check it. |
| test-suites-calls-markdown-importer | exercises | Source is the test suites: a test-harness interaction that drives the target to check it. |
| test-suites-calls-agent-cli | exercises | Source is the test suites: a test-harness interaction that drives the target to check it. |
| simulation-engine-calls-simulation-aspect-registry | invokes | Runtime operation call: Runs the hooks of the aspects a specification enables (planned, WG-4665). |
| simulation-aspect-registry-calls-chaos-aspect | composes | Registered aspect: the registry wires the aspect in. |
| simulation-aspect-registry-calls-load-aspect | composes | Registered aspect: the registry wires the aspect in. |
| simulation-aspect-registry-calls-cost-aspect | composes | Registered aspect: the registry wires the aspect in. |
| refinement-checker-calls-simulation-engine | invokes | Runtime operation call: Runs the abstract and the refined behaviors of a component (planned, WG-4666). |
| claim-evaluator-calls-refinement-checker | invokes | Runtime operation call: Refinement checks are claims. |
| session-calls-simulation-overlays | invokes | Runtime operation call: Derives the overlays of the scrubbed time (planned, WG-4671). |
| session-calls-simulation-contract | invokes | Runtime operation call: Derives the engine input for the scenario the Simulation tab loads. |
| agent-cli-calls-simulation-contract | invokes | Runtime operation call: simulate and trace derive the engine input the same way. |
| shell-calls-responsive-layout | composes | Creates the responsive layout (a constructor call that owns the layout for the shell lifetime). |
| responsive-layout-calls-dom-helpers | imports | Description: builds its elements with the shared helpers; dom-helpers is a pure helper module the source imports. (to be replaced by extracted facts in M5) |
| toolbar-calls-responsive-layout | invokes | Runtime operation call: The overflow menu and the save-conflict menu use the shared menu controller. |
| shell-calls-queries | invokes | Runtime operation call: Labels the selection in the inspector's summary line. |
| shell-calls-claim-method-registry | imports | Names a selected claim status from the registry data: a data import. (to be replaced by extracted facts in M5) |
| shell-calls-simulator-panel | composes | Description begins "Mounts": the source mounts the target into the page. |
| claim-evaluator-calls-exhaustive-explorer | invokes | Runtime operation call: Claims evaluated exhaustively within bounds (planned, WG-4650). |
| exhaustive-explorer-calls-simulation-engine | invokes | Runtime operation call: A Rust explorer with the same semantics as simulation, for state spaces too large for the Lean one, checked... |
| claim-evaluator-calls-implementation-refinement | invokes | Runtime operation call: Refinement of implementation traces is a claim (planned, WG-4679). |
| validator-calls-fault-model | invokes | Runtime operation call: Runs the fault model rules (missing sources, bounds, realises outside the model) as part of validation. |
| claim-evaluator-calls-proof-export | invokes | Runtime operation call: Claims proved in Lean are reported as verified by proof (planned, WG-4686). |
| validator-calls-contract-conformance | invokes | Runtime operation call: Checks the payload of every contract event against the fields, types and errors of its contract. |
| claim-evaluator-calls-contract-conformance | invokes | Runtime operation call: checkTrace adds the automatic checks of the contract events of a trace. |
| session-calls-contract-conformance | invokes | Runtime operation call: Derives the request log of the loaded run for the simulator panel. |
| agent-cli-calls-contract-conformance | invokes | Runtime operation call: simulate lists the request log of the run. |
| test-suites-calls-contract-conformance | exercises | Source is the test suites: a test-harness interaction that drives the target to check it. |
| validator-calls-data-model | invokes | Runtime operation call: Runs the data rules and the record and copy consistency checks as part of validation. |
| claim-evaluator-calls-data-model | invokes | Runtime operation call: Evaluates data-model claims from the findings of the data rules. |
| data-model-calls-queries | invokes | Runtime operation call: Builds the component graph to find a path between a copy's holder and a record's owner. |
| projection-system-calls-data-model | invokes | Runtime operation call: The Data projection draws records, copies, owners and holders, and marks copies with findings. |
| inspector-calls-data-model | invokes | Runtime operation call: Lists a record's fields and copies and a copy's source fields. |
| proof-export-calls-simulation-contract | invokes | Runtime operation call: Builds the scenario's engine input with simulationInput, exactly as simulate does. |
| proof-export-calls-expression-language | invokes | Runtime operation call: Parses claim expressions and evaluates them on a counterexample's last configuration to explain it. |
| proof-export-calls-contract-conformance | invokes | Runtime operation call: Renders a counterexample's contract events as request-log lines. |
| agent-cli-calls-proof-export | invokes | Runtime operation call: The prove command explores a scenario and checks its state invariants in Lean. |
| simulation-engine-calls-resource-model | invokes | Runtime operation call: Settles resources after each step and runs service-done and wait-timeout entries (planned, WG-4664, WG-4715). |
| simulation-engine-calls-workload-model | invokes | Runtime operation call: Queues the next arrival of a workload when one is taken, runs link transfers and timers (planned, WG-4715). |
| simulation-engine-calls-performance-metrics | invokes | Runtime operation call: Accumulates the measured outputs of a run, in trace and metrics output modes (planned, WG-4715). |
| simulation-contract-calls-resource-model | invokes | Runtime operation call: Lowers resources, classes and service demand into the version-2 engine input (planned). |
| simulation-contract-calls-workload-model | invokes | Runtime operation call: Lowers workloads, rates, durations, distributions and links into the version-2 engine input (planned). |
| metric-claims-calls-simulation-engine | invokes | Runtime operation call: Runs the claim's scenarios once per seed in metrics mode (planned, WG-4715). |
| claim-evaluator-calls-metric-claims | invokes | Runtime operation call: Metric-bound claims are evaluated by the metric claims component (planned, WG-4715). |
| session-calls-traffic-recorder | invokes | Runtime operation call: Records the session's events, installs the persistence client's observer and reads the stream for Live mode. |
| composition-root-calls-traffic-recorder | invokes | Runtime operation call: src/app/main.js records page-loaded, the engine load, session-init-requested, camera events and step-pulsed. |
| responsive-layout-calls-traffic-recorder | invokes | Runtime operation call: src/ui/layout.js records panel-toggled and layout-preferences-written. |
| session-calls-self-model-replay | invokes | Runtime operation call: Live mode replays the recorded stream through the scenario live-session (createReplay, replayChecks). |
| self-model-replay-calls-simulation-contract | invokes | Runtime operation call: Reads the behaviors of the scenario from the engine input (simulationInput). |
| self-model-replay-calls-expression-language | invokes | Runtime operation call: Evaluates guards, effect values and emitted payloads. |
| simulation-engine-calls-lean-call-boundary | invokes | Runtime operation call: Runs every engine input as the Lean function engine.run. |
| lean-call-boundary-calls-formal-semantics | invokes | Runtime operation call: Dispatches engine.run, engine.explore and engine.temporal to runAnyValue, exploreValue and temporalValue of... |
| test-suites-calls-rust-engine-oracle | exercises | Source is the test suites: a test-harness interaction that drives the target to check it. |
| register-importer-calls-markdown-importer | imports | Reuses the importer text helpers, loss collection, coverage comparison and git commit reader: helper imports. (to be replaced by extracted facts in M5) |
| register-importer-calls-filesystem | invokes | Runtime operation call: Reads the Markdown file and the import map, and writes or compares the generated file, with node:fs. |
| test-suites-calls-register-importer | exercises | Source is the test suites: a test-harness interaction that drives the target to check it. |
| agent-cli-calls-external-realisation | invokes | Runtime operation call: traceability, generate and verify resolve the project's realisation roots; verify records external test evi... |
| verification-pipeline-calls-external-realisation | invokes | Runtime operation call: The traceability check delegates modules that name a root, and the scan of a root's include globs. |
| external-realisation-calls-filesystem | invokes | Runtime operation call: Checks modules and scans files in a root; reads JUnit reports. |
| external-realisation-calls-external-test-runner | invokes | Runtime operation call: verify spawns the test command a root declares, without a shell, unless --ingest-only. |
| validator-calls-integrity-rules | invokes | Runtime operation call: Reports invalid rules, vacuous rules and every current violation as diagnostics. |
| transactions-calls-integrity-rules | invokes | Runtime operation call: Project.apply refuses a transaction that adds a violation of an error rule (the ratchet). |
| agent-cli-calls-integrity-rules | invokes | Runtime operation call: The integrity and prove-integrity commands. |
| integrity-rules-calls-proof-export | invokes | Runtime operation call: prove-integrity uses the Lake runner of exegra prove (lakeAvailable, the exegra-lean binary). |
| composition-root-calls-reader-surface | composes | Description begins "Mounts": the source mounts the target into the page. |
| reader-surface-calls-reader-pages | invokes | Runtime operation call: Derives the page of the current reader view, a kind's page and section bodies. |
| reader-surface-calls-session | invokes | Runtime operation call: Selects entities; reads the model, the views, the current view and the scene's projection. |
| reader-surface-calls-dom-helpers | imports | Description: builds its elements with the shared helpers; dom-helpers is a pure helper module the source imports. (to be replaced by extracted facts in M5) |
| reader-pages-calls-queries | imports | Uses own() for keys the specification supplies: a helper import. (to be replaced by extracted facts in M5) |
| parser-calls-lean-call-boundary | invokes | Runtime operation call: Derives every model with the Lean function model.derive. |
| lean-call-boundary-calls-model-derivation | invokes | Runtime operation call: Dispatches model.derive to Exegra.Model.deriveValue. |
| lean-call-boundary-calls-model-hash | invokes | Runtime operation call: Dispatches hash.semantic and hash.normalize to the semantic hash and the normal form. |
| model-derivation-calls-model-hash | invokes | Runtime operation call: Computes the semantic hash of every derived model. |
| session-calls-stable-serialization | invokes | Runtime operation call: Hashes the spec and layout text with sha256Hex for the recorded events. |
| toolbar-calls-stable-serialization | invokes | Runtime operation call: Hashes the specification of an exported or imported bundle for the recorded events. |
| realisation-panel-calls-stable-serialization | invokes | Runtime operation call: Hashes the generated files for the recorded events. |
| agent-cli-calls-stable-serialization | invokes | Runtime operation call: Serialises results deterministically. |
| generators-calls-stable-serialization | invokes | Runtime operation call: Writes generated files with sorted keys. |
| simulation-contract-calls-stable-serialization | invokes | Runtime operation call: Writes the goldens with sorted keys (tools/record-goldens.js). |
| agent-cli-calls-claim-method-registry | imports | Reads the registry of claim methods for its usage and validation messages: a data import. (to be replaced by extracted facts in M5) |
| agent-cli-calls-markdown-importer | invokes | Runtime operation call: The markdown command renders the documents of a linked project through the importer's module. |
| agent-cli-calls-validator | invokes | Runtime operation call: Applies the evidence reference rule (src/core/evidence-ref.js) to the commands that run verification. |
| claim-evaluator-calls-simulation-contract | invokes | Runtime operation call: Derives the engine input of a scenario from the model before a trace claim runs it. |
| simulation-engine-calls-simulation-contract | invokes | Runtime operation call: Takes the engine input that simulation-contract derives (sim-input.js) and checks the input before it runs. |
| test-suites-calls-formal-semantics | exercises | Source is the test suites: a test-harness interaction that drives the target to check it. |
| test-suites-calls-simulation-contract | exercises | Source is the test suites: a test-harness interaction that drives the target to check it. |
| test-suites-calls-stable-serialization | exercises | Source is the test suites: a test-harness interaction that drives the target to check it. |
| markdown-importer-calls-workspace-service | invokes | Runtime operation call: Writes the converted specification and its import map through the workspace service (tools/workspace.js). |
| validator-calls-metric-claims | invokes | Runtime operation call: Validates metric-bound claims with the statistics of src/core/metric-stats.js. |
| composition-root-calls-persistence-client | composes | The composition root (src/app/main.js) constructs the persistence client and hands it to the session. |
| composition-root-calls-simulation-engine | composes | The composition root initialises the Lean engine (initEngine) before the first project opens. |
| transactions-calls-hash-binding | invokes | Runtime operation call: Computes the semantic hash of each committed model and the text hash of a project. |
| claim-evaluator-calls-hash-binding | invokes | Runtime operation call: Stamps every result with the semantic hash it was computed from. |
| generators-calls-hash-binding | invokes | Runtime operation call: Stamps artifacts with the semantic hash. |
| spec-checker-calls-hash-binding | invokes | Runtime operation call: Prints the semantic hash. |
| hash-binding-calls-lean-call-boundary | invokes | Runtime operation call: Hashes and normalizes a model that does not carry its hash with hash.semantic and hash.normalize. |
| validator-calls-generation-readiness | invokes | Runtime operation call: Runs the type, record and realisation consistency checks, and the readiness rules when system.generation is... |
| generation-readiness-calls-data-model | invokes | Runtime operation call: Reads the well-formed field declarations of a record. |
| agent-cli-calls-generation-readiness | invokes | Runtime operation call: The readiness command lists the gaps of a project. |
| generation-readiness-calls-expression-language | invokes | Runtime operation call: Parses the conditions, custom validation rules and audit captures of the cross-cutting constructs, and the ... |
| machine-coverage-calls-simulation-engine | invokes | Runtime operation call: Runs each scenario of a shipped machine, and each searched sequence, through runEngine. |
| machine-coverage-calls-simulation-contract | invokes | Runtime operation call: Derives the engine input of a scenario, and of the machine alone with its routes, with simulationInput. |
| machine-coverage-calls-validator | invokes | Runtime operation call: Reads whether a machine is shipped (effectiveRealisation). |
| machine-coverage-calls-expression-language | invokes | Runtime operation call: Parses guards and effect values for their literals, their references to time and the variables guards read. |
| machine-coverage-calls-generation-readiness | invokes | Runtime operation call: Resolves the declared type of a payload field (typeStructure) to choose representative values. |
| agent-cli-calls-machine-coverage | invokes | Runtime operation call: The cover-machines command reports the coverage table and the findings and writes the generated scenarios a... |
| agent-cli-calls-spec-store | invokes | Runtime operation call: store import and store export copy a project's specification into its store and back. |
| spec-store-calls-parser | invokes | Runtime operation call: Derives the model of an imported text for the references and the semantic hash of its rows. |
| spec-store-calls-validator | invokes | Runtime operation call: loadModelFromStore analyzes the exported text with analyzeSpec. |
| spec-store-calls-sqlite-engine | invokes | Runtime operation call: Holds the rows in a database opened with DatabaseSync in WAL mode. |
| test-suites-calls-spec-store | exercises | Source is the test suites: a test-harness interaction that drives the target to check it. |
| spec-layers-calls-parser | invokes | Runtime operation call: Parses the platform text alone for its model and semantic hash. |
| spec-layers-calls-validator | invokes | Runtime operation call: analyzeSpec derives and validates the combined text. |
| spec-layers-calls-generation-readiness | invokes | Runtime operation call: Reads type texts with parseTypeName to find the platform types a product names. |
| transactions-calls-spec-layers | invokes | Runtime operation call: A Project with product files analyses every candidate platform text with its product files layered on it. |
| agent-cli-calls-spec-layers | invokes | Runtime operation call: Trying integrity rules on a layered project analyses the platform text with its product files. |
| claim-strength-calls-simulation-engine | invokes | Runtime operation call: Runs the one scenario of a counter bound to decide restated-scenario. |
| claim-strength-calls-expression-language | invokes | Runtime operation call: Parses claim expressions, guards and effect values for the value analysis and the grounding. |
| claim-strength-calls-integrity-rules | invokes | Runtime operation call: Parses integrity rules to find the kinds they quantify over. |
| agent-cli-calls-claim-strength | invokes | Runtime operation call: Adds the check and grounding to claims and evaluate, and the strength review to admit. |
| generators-calls-claim-strength | invokes | Runtime operation call: Shows the check and grounding of each claim in the claims report. |
| test-suites-calls-claim-strength | exercises | Source is the test suites: a test-harness interaction that drives the target to check it. |
| scene-renderer-calls-visual-interaction | notifies | Invokes the onSelect, onHover, onActivate, onMoveEnd and onConnect callbacks the receiver supplied; the renderer imports nothing from the application. |
| spec-guard-calls-filesystem | invokes | Runtime operation call:  |
| ai-coding-agent-calls-spec-guard | invokes | Runtime operation call:  |
