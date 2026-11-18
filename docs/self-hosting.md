# Self-hosting

Exegra specifies itself in `specs/exegra/spec.jsonc`: components, ports and contracts, relationships, behaviors, scenarios, claims and evidence entities. The specification changes often, so this document gives no counts; `node cli/exegra.js list --project exegra --kind <kind>` lists the entities of one kind (kinds `component`, `relationship`, `behavior`, `scenario`, `claim`, `evidence`), and its `result` array is the current count. This document describes what that gives today and the order in which more could follow.

**Exegra is not self-hosting today.** Nothing in the running application is generated from the model. No component declares `implementation.status` as `generated` or `partially-generated`. Ten components are declared `not-implemented` (planned simulation aspects, overlays, deployment, reality loop and the implementation refinement), with claims that stay not evaluated. The model describes, checks and reports on Exegra; it does not build it.

## What is model-driven now

Implementation status as declared by the self-specification (`component.implementation.status`):

| Status | Components | Meaning |
|---|---|---|
| `model-configured` | `projection-system`, `scene-renderer`, `inspector`, `property-controls` | Behaviour driven by data read at runtime, but the code that reads it is hand-written. (`parser` is `manual`.) |
| `manual` | 66 components, six subsystems included (validator, expression language, transactions, claim evaluator, simulation engine, layout engine, session, shell, toolbar, dialogs, source editor, workspace service, CLI, generators, ...) | Hand-written. |
| `not-implemented` | 10 components (simulation aspect registry, refinement checker, chaos, load and cost aspects, simulation overlays, deployment model, infrastructure generator, implementation refinement, reality loop) | Planned, not built. |
| undeclared | 9 external actors and libraries (Three.js, Vite, the browser platform, browser storage, the file system, `jsonc-parser`, Playwright, the Markdown specification source, and the person or agent who edits code) | Outside the system; `implementation.status` is not applicable and the *Realisation* panel lists them as undeclared. |

What "model-configured" covers, concretely:

- **Meta-model.** `metamodel.json` defines entity kinds, properties, categories, relationship kinds, shapes and colours. The parser's structure checks, the inspector and `property-controls` (editable fields per property type, enum values from `valuesFrom`), and the create and connect dialogs read it. A specification's `vocabulary` extends it: categories, relationship kinds, properties of any kind (scalar, enum, `ref` and `list`), whole entity kinds with their own sections, shapes and colours, and external verification methods. A property or kind added through `vocabulary` is validated, gets inspector and create-dialog controls, takes part in rename and delete, and is drawn by the `references` projection without a code change. A specification converted from Markdown (a linked project) declares eight entity kinds this way ([importing-markdown.md](importing-markdown.md)).
- **Claim methods.** `claim-methods.js` is a registry: the validator checks `claim.evaluate` against it and the inspector describes methods from it. The evaluator implements the methods separately, so adding a registry entry without code leaves a claim not evaluated.
- **Views and projections.** Views, filters, colour modes, shapes and colours are data. Projection functions are code registered by name.

What is hand-written: the operation table, validator rules, the expression language, the evaluators, the simulator, layout, rendering and all panel code.

## Generated artifacts

`src/core/generate/` derives five artifacts from the model, claim results, diagnostics and traceability. They are deterministic and reproducible byte for byte; `exegra generate --write` stores them in `specs/<project>/generated/` (`npm run generate` does it for `exegra`) (and the *Realisation* panel can write them under the dev server).

| Artifact | Content |
|---|---|
| `manifest.json` | Counts and every entity with its data, sorted. |
| `ARCHITECTURE.md` | Components by containment, ports, contracts, relationships, behaviors, claims. |
| `claims-report.md`, `claims-report.json` | Each claim with status, scope, explanation, assumptions, evidence, counterexample. |
| `tasks.json` | Agent-consumable work list: violated claims, validation errors, not-implemented components, traceability gaps, inconclusive and unevaluated claims, undeclared realisation, unknowns, gaps; each with severity, entities and source line. |

These are documents and reports. No generator emits code or any part of Exegra's runtime. `tasks.json` is the live work list; it is regenerated from the model, so it cannot drift from it.

## Traceability

`implementation.modules` on a component lists the files that implement it. `exegra traceability` (and every `verify`) compares them with disk: declared modules must exist and every file in `src/`, `cli/` and `tools/` (plus `index.html`, `vite.config.js`) must be claimed by some component. A linked project realised in other repositories declares them as realisation roots in its `project.jsonc` and addresses modules and test evidence as `<alias>:<path>` ([verification.md](verification.md#realisation-roots-code-and-tests-in-other-repositories)). This is a path-level check. It does not show that a module does what its component says, and the declared relationships are maintained by hand, so the structural claims about the code rest on the assumption `relationships-match-imports`.

## The bootstrap boundary

Exegra's tools must run before any model exists, so a trusted hand-written base remains whatever else is generated: the JSONC parser dependency, the operation protocol, the meta-model loader, the validator and the claim evaluator. A claim about that base is checked by the base itself. The self-specification therefore treats its structural and trace claims as evidence of consistency within the declared model, and records for each what it rests on (assumptions such as `machines-abstract-the-code`, `tests-exercise-shipped-modules`, `recorded-results-reflect-current-code`).

## Where the open limitations are

This repository does not keep a status or limitations document. They are in the model:

- `system.notes` and each component's `unknowns` in `specs/exegra/spec.jsonc`
- the *Realisation* panel (status, traceability, generated artifacts) and the *Verification* panel
- `node cli/exegra.js gaps --project exegra --pretty`
- `specs/exegra/generated/tasks.json`

Examples recorded there: no runtime code is generated; behavioral claims cover listed traces only and the scenario machines are hand-maintained abstractions; Import bypasses transactions (claim `edits-only-via-transactions` violated); no schema migration exists; recorded results are not bound to a code or model hash; no performance measurement exists for the benchmark specification.

## Roadmap

Ordered by dependency: each step needs what the previous ones provide. Items describe what they touch, not when they happen. None is implemented.

1. **Generated documentation and manifests.** *Exists now*: the five artifacts above.
2. **Module skeletons and contract stubs from component ports and contracts.** Touches the generators and adds a new artifact kind that emits source files. Needs a rule for where generated files live and how traceability treats them (the component's `implementation.status` becomes `partially-generated`, and `implementation.modules` names generated files).
3. **Inspector and validator rule tables generated from the meta-model**, beyond what is data-driven now. Touches `metamodel.json`'s description of constraints (cross-property rules, required references by kind), the validator and the inspector's controls, and requires that existing behavior be reproduced exactly from the generated tables.
4. **The meta-model expressed as an Exegra specification.** Partly unblocked: a specification can now declare its own entity kinds, with properties, `ref` and `list` types, sections, shapes and colours, so a specification could in principle carry entities that describe entity kinds and properties. What is still missing: the built-in kinds are still defined in `src/core/metamodel.json` and not in any specification; the vocabulary cannot yet express everything `metamodel.json` does: enum values read from the model with `valuesFrom`, and object, expression and effect property types; and there is no bootstrapping step that reads the hand-written meta-model to validate its own specification, nor a check that the two agree.
5. **Recorded evidence bound to code and model hashes.** Touches `verify`, `results.json`, the claim evaluator (stale detection) and the verification panel. It requires a stable notion of a code revision for the files an evidence reference exercises. This closes the recorded limitation that stale results are not detected.
6. **An MCP server wrapping `cli/commands.js`.** Touches a new entry point over the existing command table and envelope; no new data model, because the CLI already shares the UI's pipeline. Long-running sessions would also need to address the CLI's lack of undo history across invocations.
7. **Agents reconstructing modules from the task manifest and contracts**, verified against the same claims. Needs steps 2, 5 and 6: contract stubs to implement against, evidence bound to the code revision to judge the result, and a protocol to read tasks and submit work. Success is judged by the claims and test evidence, not by the agent.
8. **Accurate simulation: aspects, depth, chaos, load and cost.** Specified in `specs/exegra/spec.jsonc` as `not-implemented` components with not-evaluated claims, and planned in WG-4663; see [simulation.md](simulation.md#roadmap-accurate-simulation-as-far-as-it-goes). Its first step, the simulation core (WG-4664), depends on nothing above.

How work on Exegra stays tied to this specification (specification first, through Exegra's own transactions; done means its claims are verified or supported by recorded evidence) is in [AGENTS.md](../AGENTS.md).
