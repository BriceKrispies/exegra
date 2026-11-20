# Agent interface

Exegra's command line for AI coding agents. It is a structured interface to the same
semantic model and transaction pipeline the UI uses. There is no separate agent data
model, and no command edits specification text directly.

## Invocation

```
node cli/exegra.js <command> [args] [--project <name>] [--specs <dir>] [--pretty]
```

- `--project` defaults to `exegra`.
- `--specs` defaults to `<repo root>/specs`, resolved from the location of the CLI file.
- `--pretty` indents the JSON by two spaces. The default is one compact line.
- stdout carries exactly one JSON document. Human-oriented notes go to stderr.

## Envelope

Success:

```json
{ "ok": true, "command": "list", "project": "exegra", "semanticHash": "3f9a0c1e2b4d6a", "result": [] }
```

Failure:

```json
{ "ok": false, "command": "apply", "project": "exegra",
  "error": { "code": "revision.stale", "message": "..." }, "diagnostics": [] }
```

- `semanticHash` is present when the command read a project. It is the hash of the
  specification as it is on disk after the command. `projects`, `ops` and `help` omit it.
- On a failure, `result` is also present for `validate` and `verify`, which report their
  findings even when they fail.
- Diagnostics are serialised as `{code, severity, message, entityId, line, column}`.
  `entityId`, `line` and `column` are `null` when unknown.
- Entities are serialised as `{id, kind, owner, label, source: {line, column}, data}`.
  `list` omits `data`.

## Exit codes

| Code | Meaning |
|---|---|
| 0 | `ok: true` |
| 1 | The command failed (`ok: false`). Includes validation errors, stale hashes, rejected operations, failed verification. |
| 2 | Usage error: unknown command, missing or invalid argument. The JSON error document is still printed. |

Error codes starting with `usage.` mean exit 2. Other codes mean exit 1.

## Commands

Every example result is abbreviated.

### `projects`
```
node cli/exegra.js projects
```
```json
{"ok":true,"command":"projects","project":"exegra","result":[{"name":"exegra","title":"Exegra"}]}
```

### `project`
Registers, removes and lists linked projects, so a script (a continuous-integration job in another repository) can say "treat this spec file as project `strata`" in one command. Nothing else is written, and the specification is never touched.
```
node cli/exegra.js project add strata --spec ../strata/specs/platform.jsonc --product ../strata/specs/products
node cli/exegra.js project remove strata
node cli/exegra.js project list
```
- `project add <name> --spec <file> [--product <file or directory>]... [--force]` writes `specs/<name>/project.jsonc` as `{"spec": ..., "products": [...]}` with every path stored relative to the project directory and forward slashes (so the specs directory and the files must be on one drive). Paths on the command line are relative to the working directory. The spec must be a readable `.jsonc` file and every product a readable `.jsonc` file or directory, or nothing is written. It refuses with `project.exists` when `specs/<name>/project.jsonc` exists (replace it with `--force`) or when the directory keeps its own `spec.jsonc`, and with `name.invalid` for a name that is not a project name (`a-z 0-9 - _`, starting with a letter or digit, at most 64 characters). The envelope's `project` is the name given.
- `project remove <name>` deletes `project.jsonc`, and the directory when it is then empty; a layout, recorded results or history stay. It refuses with `project.not-found` when the name is not a registered link.
- `project list` returns `[{name, title, spec, products}]`; `projects` returns names and titles only.

### Inline projects
`validate`, `list`, `show`, `deps`, `contracts`, `claims`, `evaluate`, `gaps`, `plan-delete`, `simulate`, `prove`, `integrity`, `prove-integrity` and `readiness` accept the project inline instead of `--project`: `--spec <file>` and any number of `--product <file or directory>`, relative to the working directory. Nothing is registered or written, there is no layout and no recorded results, and the envelope's `project` is `null`.
```
node cli/exegra.js validate --spec specs/platform.jsonc --product specs/products
```
`--spec` with `--project`, or `--product` without `--spec`, is a usage error; commands that write (`apply`, `generate`, `verify`, ...) do not take the options.

### `validate`
Returns `{errors, warnings, gaps, diagnostics}` as counts and the full list. `ok` is true only when there are no errors. With errors, the command fails with `validation.failed`.
```
node cli/exegra.js validate
```
```json
{"ok":true,"command":"validate","project":"exegra","semanticHash":"…","result":{"errors":0,"warnings":0,"gaps":3,"diagnostics":[…]}}
```

### `list [--kind <kind>] [--owner <id>]`
Entities in declaration order, without `data`.
```
node cli/exegra.js list --kind component
```
```json
{"ok":true,"command":"list","project":"exegra","semanticHash":"…","result":[{"id":"client","kind":"component","owner":null,"label":"Client","source":{"line":12,"column":7}}]}
```

### `show <id>`
The entity with `data`, plus `ownedEntities`, `referencedBy` (`[{from, via}]`). Components also get `relationships` (`[{id, kind, direction, other}]`), `children` and `ancestors`.
```
node cli/exegra.js show semantic-core
```
```json
{"ok":true,"command":"show","project":"exegra","semanticHash":"…","result":{"id":"server","kind":"component","data":{"name":"Server","category":"logical"},"ownedEntities":["server-api"],"referencedBy":[{"from":"client-calls-server","via":"to"}],"relationships":[{"id":"client-calls-server","kind":"calls","direction":"in","other":"client"}],"children":[],"ancestors":[]}}
```

### `deps <id> [--direction out|in] [--transitive] [--kinds a,b]`
Dependencies of a component. Default: `out` (what it depends on), direct only. Without `--kinds`, only relationship kinds flagged as dependencies are followed.
```
node cli/exegra.js deps visual-interaction --transitive
```
```json
{"ok":true,"command":"deps","project":"exegra","semanticHash":"…","result":[{"id":"server","via":"client-calls-server","depth":1}]}
```

### `contracts [<componentId>]`
All contracts, or the contracts bound to a component through its ports and relationships.
```
node cli/exegra.js contracts session
```
```json
{"ok":true,"command":"contracts","project":"exegra","semanticHash":"…","result":{"component":"server","bindings":[{"contract":"request-contract","via":"server-api","role":"provider"}],"contracts":[{"id":"request-contract","kind":"contract","data":{…}}]}}
```

### `claims [--status <status>]`
Evaluated claim results, each with the claim's `statement` and `kind`; a trace claim also carries `negatives` (each declared negative run: `scenario`, `faults`, `violated`, `outcome`, `stepIndex`, `explanation`). `--status` is one of `verified`, `supported`, `violated`, `inconclusive`, `not-evaluated`.
```
node cli/exegra.js claims --status violated
```
```json
{"ok":true,"command":"claims","project":"exegra","semanticHash":"…","result":[{"claimId":"no-direct-db","kind":"structural","method":"no-relationship","status":"violated","explanation":"…","counterexample":{"summary":"…","entities":["…"]},"statement":"The client never calls the database directly.","evidence":[]}]}
```

### `evaluate [<claimId>]`
One claim, or all claims. Returns `{results, summary}`. A violated claim is a finding, so the command still succeeds with `ok: true`.
```
node cli/exegra.js evaluate core-dependencies-acyclic
```
```json
{"ok":true,"command":"evaluate","project":"exegra","semanticHash":"…","result":{"results":[{"claimId":"no-direct-db","status":"violated","…":"…"}],"summary":{"total":1,"verified":0,"supported":0,"violated":1,"inconclusive":0,"not-evaluated":0}}}
```

### `gaps`
Unspecified or inconsistent things, grouped: `diagnostics` (warnings and gaps), `unknowns` (`[{component, text}]`), `unevaluatedClaims` (ids with status `not-evaluated`), `undeclaredRealisation` (components with no `implementation` declaration).
```
node cli/exegra.js gaps
```
```json
{"ok":true,"command":"gaps","project":"exegra","semanticHash":"…","result":{"diagnostics":[…],"unknowns":[{"component":"server","text":"…"}],"unevaluatedClaims":["…"],"undeclaredRealisation":["client","server"]}}
```

### `ops`
The operation protocol: each operation of `OPERATIONS` with `type`, `doc`, `params`, `preconditions`, `effects`, `persistence` and `semantic`. `exegra ops` is the authoritative version; the summary below may lag behind it.
```
node cli/exegra.js ops
```

### `apply [--file <ops.json> | --ops '<json>'] [--expect-hash <hash>] [--dry-run] [--label <text>]`
Applies one operation or an array of operations. Operations come from `--file`, from `--ops`, or from stdin when neither is given.

```
node cli/exegra.js apply --expect-hash 3f9a0c1e2b4d6a --ops '{"type":"SetProperty","id":"server","property":"name","value":"Order server"}'
```
```json
{"ok":true,"command":"apply","project":"exegra","semanticHash":"…","result":{"revision":4,"semanticHashBefore":"3f9a0c1e2b4d6a","semanticHashAfter":"…","semanticChanged":true,"affected":["server"],"written":["spec"],"dryRun":false}}
```

Result fields: `revision`, `semanticHashBefore`, `semanticHashAfter`, `semanticChanged`, `affected` (entity ids), `written` (`spec` and/or `layout`), `dryRun`.

Failure codes:
- `revision.stale`: `--expect-hash` does not match. Nothing was applied.
- `validation.failed`, `entity.unknown`, `id.duplicate`, and other operation codes: the transaction was rejected. `diagnostics` says why. Nothing was written.
- `write.conflict`: the file changed on disk after it was read. Nothing was written, or only the spec was written when the layout conflicted (the message says which).

With `--dry-run` the transaction is fully validated and nothing is written. The envelope's `semanticHash` is then the hash before the command.

### `plan-delete <id>`
What a cascade delete would remove (`entities`), repair (`repairs`) and what depends on it (`dependents`). Changes nothing.
```
node cli/exegra.js plan-delete hash-binding
```
```json
{"ok":true,"command":"plan-delete","project":"exegra","semanticHash":"…","result":{"entities":["client","client-calls-server"],"repairs":[],"dependents":[]}}
```

### `simulate <scenarioId> [--faults a,b] [--steps]`
Runs a scenario and checks the claims that apply to its trace. `--faults` replaces the scenario's own fault list. `--steps` includes the full `steps` array. When the scenario has contract events (events with a `contract` and a `role`), `checks` also holds their automatic conformance checks and `requestLog` lists them as request-log lines (see [simulation.md](simulation.md#contract-events-in-a-trace)).
```
node cli/exegra.js simulate visual-edit-flow
```
```json
{"ok":true,"command":"simulate","project":"exegra","semanticHash":"…","result":{"scenarioId":"basic-exchange","faults":[],"outcome":"quiescent","stepCount":4,"final":{…},"checks":[]}}
```

### `trace <scenarioId> [--faults a,b] [--out <file>]`
The complete trace. With `--out`, the trace is written as stable JSON (sorted keys, two-space indent) to that file, relative to the current directory. The result is then `{written, stepCount}` with `written` as the absolute path.
```
node cli/exegra.js trace visual-edit-flow --out ./trace.json
```
```json
{"ok":true,"command":"trace","project":"exegra","semanticHash":"…","result":{"written":"C:\\dev\\exegra\\trace.json","stepCount":4}}
```

### `generate [--all] [--write]`
Runs `generateAll` from `src/core/generate/index.js`. Generation is deterministic: the same model and recorded evidence give the same bytes. Each file is reported with its `bytes` and `sha256`, so an agent can check reproducibility. `--all` is accepted; generation always covers everything. `--write` also stores the files under the project's `generated/` directory and reports `written`.
```
node cli/exegra.js generate
```
```json
{"ok":true,"command":"generate","project":"exegra","semanticHash":"…","result":{"files":{"report.md":{"bytes":2310,"sha256":"…"}}}}
```

### `traceability`
Compares each component's declared `implementation.modules` with the files on disk. Returns `{checkedModules, missingModules, unclaimedFiles, claimedFiles}`. A module ending in `/` claims every file beneath it. The surface is `src/`, `cli/` and `tools/` (`.js`, `.json`, `.css`, `.html`), plus `index.html` and `vite.config.js`.
```
node cli/exegra.js traceability
```
```json
{"ok":true,"command":"traceability","project":"exegra","semanticHash":"…","result":{"checkedModules":12,"missingModules":[],"unclaimedFiles":["tools/old.js"],"claimedFiles":40}}
```

### `verify [--skip-browser] [--ingest-only] [--fresh] [--expect-violated a,b]`
The verification pipeline:

1. Validate.
2. Check traceability.
3. Execute every `test` evidence. Its `ref` is `<test file>` or `<test file>#<name pattern>`. Files under `tests/browser/` run through `npx playwright test`. Other files run through `node --test`. A reference may contain only `A-Z a-z 0-9 _ . / - space # :` (the rule of `src/core/evidence-ref.js`, which `exegra validate` also applies as `evidence.ref-unsafe`), and its file must lie inside the repository. Anything else is recorded as `unsafe reference`, with the reason. A missing file is recorded as `test file not found`. A failure keeps the last 20 lines of output as `detail`. A `ref` written `<alias>:<file>[#<describe> > <name>]` points into a realisation root that `project.jsonc` declares: the root's test commands run once and the outcome (`pass`, `fail` or `not-run`) comes from its JUnit report ([verification.md](verification.md#realisation-roots-code-and-tests-in-other-repositories)).
4. Write the results to `evidence/results.json` with `ranAt` timestamps. Results from earlier runs are replaced.
5. Re-evaluate the claims with the new results.

`--fresh` runs every test again instead of reusing the outcomes recorded on the same tree (reuse happens only while the tree stamp matches; see `tests/core/outcome-reuse.test.js`). `--ingest-only` runs no realisation root's test command and reads the JUnit reports already on disk. `--skip-browser` leaves browser evidence unexecuted. It has no recorded result, so its claims are evaluated as they would be without a run.

`--expect-violated a,b` names claims that are deliberately violated. The command still succeeds when those are the only violations. Unknown ids are rejected.

The command fails with `verify.failed` when validation has errors, any executed evidence failed (`not-run` is not a failure), or any claim is violated outside `--expect-violated`. The failure carries the full report in `result`.

```
node cli/exegra.js verify --skip-browser --expect-violated edits-only-via-transactions
```
```json
{"ok":true,"command":"verify","project":"exegra","semanticHash":"…","result":{"validation":{"errors":0,"warnings":0,"gaps":3},"traceability":{…},"evidence":[{"id":"unit-tests","kind":"test","ref":"tests/core/cli.test.js","outcome":"pass","ranAt":"2026-11-14T10:00:00.000Z"}],"claims":{"summary":{…},"violated":["no-direct-db"],"expectedViolated":["no-direct-db"],"unexpectedViolated":[]}}}
```

### `integrity [<ruleId>] [--rules <file>] [--limit N]`
Evaluates the integrity rules ([integrity-rules.md](integrity-rules.md)): per rule `status` (`holds`, `violated`, `invalid`), `instances`, `vacuous`, `counterexampleCount` and the first `--limit` (default 20) counterexamples as bindings `{variable, entity, kind, line}`. `--rules` adds rules from a JSON array of `integrityRule` entities in memory, without editing the file. Fails with `integrity.violated`, carrying the result, when an error rule is violated or a rule is invalid.
```
node cli/exegra.js integrity closes-agrees-with-resolved-by
```
```json
{"ok":true,"command":"integrity","project":"exegra","semanticHash":"…","result":{"total":1,"holds":1,"violated":0,"invalid":0,"rules":[{"ruleId":"closes-agrees-with-resolved-by","severity":"error","status":"holds","instances":4,"vacuous":false,"counterexampleCount":0,"counterexamples":[],"ms":0.7}]}}
```

### `prove-integrity [<ruleId>] [--rules <file>] [--max-witnesses N]`
Proves or refutes integrity rules in Lean: per rule `result` (`holds`, `violated` or `incomplete`), the exported `facts`, the `differential` comparison with the JavaScript evaluator, the proof `file`, `theorems`, `axioms` and the times (`evaluateMs`, `exportMs`, `leanEvalMs`, `checkMs`). Needs Lake. Fails with `integrity.incomplete` when a rule could not be decided.

### `prove <scenarioId> [--bound N] [--max-states N] [--steps]`
Explores every configuration of a scenario within a bound with the verified explorer of the Lean semantics, and checks the state-invariant and temporal claims that list the scenario. Needs `lake`. Its output is not written to `results.json`.

### `markdown [<documentPath>] [--out <dir>]`
Renders the document entities of a specification that holds them (a linked project converted from Markdown). With no argument it lists the document paths; with a path it prints that document; with `--out` it writes every document under the directory.

### `cover-machines [<behaviorId>] [--bound N] [--max-runs N] [--write <dir>]`
Transition and guard-outcome coverage of every shipped implementation machine (or one): `summary`, a `table` row per machine (transitions and guard outcomes covered/total, generated scenarios, open items), the `machines` in detail and the `findings`. What the scenarios leave out is searched for with bounded sequences of the machine's input events (default 12 actions and 5000 engine runs per machine). A transition nothing reaches is `machine.transition-unreachable`, a warning, or an error under `system.generation`, which fails the command with `cover.unreachable`. `--write <dir>` writes the generated scenarios to `<dir>/ops.json` as operations for `apply`. See [Coverage](coverage.md).

### `cover-functions [<functionId>] [--branches]`
Branch coverage of the function examples: `summary` (functions, those with branches, those fully covered, branches covered/total) and per function the branches covered/total, the examples and failing examples, and each uncovered branch with its location. `--branches` lists every branch. Always exits 0; the readiness rule `ready.function-branch-uncovered` reports the gaps. See [Coverage](coverage.md).

### `help`
The list of commands with usage and summary.

## The operation protocol

Every change is one operation or an array of operations. An array is atomic: all operations apply, or none do. Each operation is validated against the meta-model, and the resulting model must have no errors. Operations are applied by `Project.apply`, the same call the UI makes.

| Operation | Parameters | Preconditions | Persistence |
|---|---|---|---|
| `CreateEntity` | `kind`, `data` (with a fresh `id`), `owner` (nested kinds), `index` | Known kind; well-formed unused id; owner exists | spec |
| `DeleteEntity` | `id`, `cascade` (default false) | Exists; not the system; nothing refers to it unless `cascade` | spec + layout |
| `RenameEntity` | `id`, `newId` | Exists; `newId` well-formed and unused | spec + layout |
| `SetProperty` | `id`, `property` (name, dotted path or array), `value` (`null` removes) | Exists; not `id` | spec |
| `CreateRelationship` | `kind`, `from`, `to`, optional `id`, `label`, `description` | Known relationship kind; endpoints identify components or ports | spec |
| `DeleteRelationship` | `id`, `cascade` | Exists and is a relationship | spec |
| `MovePresentationNode` | `view`, `id`, `x`, `z` or `reset` | Exists; finite coordinates | layout only |
| `AddClaim` | `data` | Well-formed unused id | spec |
| `ModifyClaim` | `id`, `changes` (`null` removes) | Exists and is a claim; `changes` has no `id` | spec |
| `AddState` | `behavior`, `data` | Behavior exists; well-formed unused id | spec |
| `AddTransition` | `behavior`, `data`, `index` | Behavior exists; states and event resolve | spec |
| `ReplaceSource` | `text` | Parses and validates | spec |
| `ReplaceLayout` | `text` | Valid layout document | layout only |

Effects are listed in full by `exegra ops`. `MovePresentationNode` and `ReplaceLayout` cannot change the semantic hash.

## Optimistic concurrency

1. `exegra validate` returns `semanticHash`.
2. The agent builds its operations against that model.
3. `exegra apply --expect-hash <semanticHash> --ops ...` applies them only if the project still has that hash. Otherwise the result is `revision.stale`, with nothing applied and nothing written.

The hash covers the normalised semantic content. Comments, whitespace and key order do not change it. Layout changes do not change it either.

## One pipeline

The CLI, the UI and any future tool share one path: an operation goes to `Project.apply` in `src/core/project.js`, which validates it and produces a new model, and the changed files are then written by `tools/workspace.js`. There is no command that edits `spec.jsonc` or `layout.jsonc` without going through an operation. The only other write is `evidence/results.json` from `verify`, which records execution results and does not change the specification.

## Future MCP server

`cli/commands.js` exports `runCommand(name, args, options)` and `COMMANDS`. An MCP server can expose each command as one tool. Its arguments map onto the command's positionals and the flags listed in its `usage` string, and its output is the returned envelope. The envelope is already JSON with stable ids and diagnostic codes.

## What the CLI does not do

- It never reports a claim as verified because it exists. A claim's status comes only from a `ClaimResult`, which `evaluate` and `claims` report. `verify` reports that status after recording evidence, and it does not change it.
- It does not execute a claim that has no evidence. Such a claim stays `not-evaluated`.
- It does not write implementation code. `generate` produces artifacts from the model; it does not edit source files.
- It does not commit to git or push.
- It does not run tests on its own. `verify` runs the test evidence the specification names, and `--skip-browser` leaves browser evidence unexecuted.
