# Working on Exegra

Exegra is its own first subject. `specs/exegra/spec.jsonc` (a manifest of the part files in `specs/exegra/parts/`, see the front door below) specifies Exegra: its components, what each is responsible
for, how they relate, how its pipelines behave, and the claims that must hold. Exegra is built from that specification
and validated against it with Exegra's own tools. Keep it that way: no part of Exegra exists only in code.

## The rule: specification first, through Exegra

Every change that adds or alters behavior starts as a change to `specs/exegra/spec.jsonc`, made through Exegra's own
transactions (the application, or `node cli/exegra.js apply --project exegra --file ops.json`, with `--dry-run`
first). Hand edits of the text are allowed for prose, but the result must validate.

What goes into the specification:

- **Components.** A new module gets a component, or joins an existing one: purpose, responsibilities, the files in
  `implementation.modules`. `node cli/exegra.js traceability` lists the source files no component claims (`unclaimedFiles`) and the
  declared modules that do not exist (`missingModules`); it exits 0 either way, so read both lists.
- **Relationships.** A new dependency between components is a relationship of the right kind (`imports`, `invokes`,
  `notifies`, `composes`, `data-flow`, `projects`, ...; `calls` is legacy, see docs/model-and-format.md#interaction-kinds). Claims such as `core-independent-of-ui` and `core-dependencies-acyclic` are evaluated over them.
- **Behavior.** A change to a pipeline Exegra simulates about itself (scenarios such as `visual-edit-flow`) changes
  its behaviors, events and scenarios too, so the simulation keeps describing Exegra as it is.
- **Claims and evidence.** Each new capability gets at least one claim saying precisely what must hold, and an
  `evidence` entity naming the test that shows it (`tests/core/<file>.test.js`, or `tests/browser/<file>.spec.js#<test
  title>`). A claim the model can decide (structure, traces) uses that evaluation method instead of evidence.
- **Unknowns.** What a component cannot do yet goes in its `unknowns`, naming the Workgraph task that would close it.

Planned work is specified too: components with `implementation.status` `not-implemented` and claims that stay
*not evaluated* until evidence exists. The simulation roadmap (WG-4663) is recorded this way.

## Front door: never open the specification file

`specs/<project>/spec.jsonc` (and the part files of a manifest specification) is large: Exegra's own specification is
over a megabyte in total, and one full read costs a large share of your budget. Do not `Read`, `Grep`, `cat` or hand-edit it.
Use the command line, which answers from the semantic model and gives source lines:

- **Read:** `node cli/exegra.js get --project exegra <id> [<id> ...]` (declaration, owner, source line, references both
  ways); `find --kind K [--where prop=value] [--refers-to ID] [--referenced-by ID] [--text "..."] [--fields a,b]
  [--limit N]`; `refs <id>`. `list`, `show`, `deps` and `claims` exist too.
- **Write:** `apply --project exegra --file ops.json --dry-run`, then `apply` without `--dry-run`.
- A script that parses the file with `jsonc-parser` and prints only what it needs is allowed.
- **The self-specification is a manifest.** `specs/exegra/spec.jsonc` lists the part files of `specs/exegra/parts/` (27 files,
  one per area of components, claims, behaviours and the rest, each at most about 120 KB) and a `specSections` table that
  tells `apply` which part a new component, relationship, claim, evidence record or behaviour is written to; `get`, `find`
  and `refs` print the part file and line. **To add a part:** create `specs/exegra/parts/<name>.jsonc` holding the
  sections it takes, list it in `specParts`, and name it in `specSections` where new entities should land there (the
  rule format is in docs/model-and-format.md, "A specification kept as a manifest of part files"). A script that reads
  the self-specification as one text uses `readSpecFile` of `tools/spec-manifest.js`, never `fs.readFileSync` of
  `spec.jsonc`.

`.claude/settings.json` wires `tools/spec-guard.js`, a PreToolUse hook that refuses `Read`, `Edit`, `Write`,
`MultiEdit`, an explicit `Grep` and `cat`-like shell commands aimed at a specification file, and names these commands
in its message. A `Read` of the first 60 lines (the header comment) is allowed. The commands are described in
`docs/agent-interface.md`.

## Done means validated by its own specification

A change is done when:

1. `node cli/exegra.js validate --project exegra` reports no errors;
2. `node cli/exegra.js traceability --project exegra` reports no missing modules and no unclaimed files;
3. `npm run verify` executes the evidence and records the results, and every claim of the change is **verified** or
   **supported** (or **proved**, for a `lean-theorem` claim); the only violated claims are the ones the script expects
   (`edits-only-via-transactions`, deliberately recorded as a known gap, and `core-logic-in-lean`, which lists the
   components of the verified kernel (tag `verdict-kernel`) not yet ported to Lean until WG-4785 finishes, and `core-dependencies-acyclic` and `core-static-dependencies-acyclic`, which the static imports read from the code show to be violated: see docs/verification.md);
4. `npm run generate` has rewritten the derived artifacts under `specs/exegra/generated/`;
5. the user-visible part has been seen working in the running application, with screenshots.

Claims are never weakened to pass, and never marked positive without evidence. A claim that only rests on evidence is
*supported*, not *verified*; Exegra shows a green verified status only for what it established by checking the model
itself. Where a new feature can be demonstrated on Exegra's own specification, demonstrate it there: the simulated
message flows were shown on `visual-edit-flow`, and they exposed a gap in Exegra's own model (WG-4661).

## Checks and tests

- Cheap checks while working: `npx tsc -p jsconfig.json --noEmit` (`npm run typecheck` does the same after building
  the engine), `node --check <file>`, `node cli/exegra.js validate` and `apply --dry-run`, and in `engine/`
  `cargo check`, `cargo fmt` and `cargo clippy`.
- The simulation engine is the Lean core (`formal/`), run as WebAssembly through `src/core/engine.js` and
  `src/core/lean.js`. `npm run build:formal-wasm` builds it into `src/engine/lean/` (generated, wasm64 only); new Lean
  functions for the shell are registered in `formal/Exegra/Api.lean`. The Rust engine (`engine/`) stays as a
  differential oracle: `npm run build:engine` builds it into `src/engine/pkg/` (generated); `dev`, `build`, `test`,
  `test:browser`, `typecheck`, `generate` and
  `verify` build it first.
- Test suites: `npm test` (Node, two at a time) and `npm run test:browser` (Playwright). They run once on a stack of
  changes, not after every change. Subagents run only the cheap checks; the coordinator runs the suites and
  `npm run verify`.

## Records

- Workgraph is the status record. Open limitations and planned work are tasks, referenced from `unknowns` and claim
  rationales; there are no TODO, status or known-limitations files in this repository.
- Commits carry a `Task-ID: <KEY>` trailer and never mention AI, models or assistants.
- Never estimate how long work will take. Order work by dependency and describe scope by what a change touches.

## Where things are

- `docs/self-hosting.md`: how far Exegra already describes and generates itself, and what is next.
- `docs/architecture.md`, `docs/module-contracts.md`: the module boundaries the specification declares.
- `docs/claims-and-evidence.md`, `docs/verification.md`: claim statuses, evidence, and what each check covers.
- `docs/simulation.md`: the simulator and its roadmap.
