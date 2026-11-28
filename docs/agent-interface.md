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

### `get <id> [<id> ...]`
Targeted read. Prints the named entities, in the order given, so an agent never has to open the specification text.
```
node cli/exegra.js get core-independent-of-ui transactions
```
Each result is `{id, kind, owner, label, source: {file, line, column}, data, refersTo: [{path, target, line}], referencedBy: [{from, path, line}]}`. `data` is the declaration as written; `refersTo` lists the entity's outbound references by property path, `referencedBy` the inbound ones; both come from `model.refs`. An unknown id fails with `entity.unknown`. The example above, on the Exegra specification, prints 11,022 bytes, against a specification of 1.33 MB.

### `find [--kind K] [--where prop=value]... [--refers-to ID] [--referenced-by ID] [--text "..."] [--fields a,b] [--limit N]`
Targeted search. Every filter given must hold.
- `--kind`: entity kind. `--where prop=value` (repeatable): a property of the declaration, dotted paths allowed (`implementation.status=manual`), equal to the value as text; for an array, any element.
- `--refers-to ID`: entities holding a reference to ID. `--referenced-by ID`: entities that ID refers to.
- `--text`: case-insensitive substring of any string in the declaration.
- `--fields a,b`: data fields (dotted paths) to print; without it only id, kind, label and source are printed. `--limit N` defaults to 100.

Result: `{total, returned, truncated, entities: [{id, kind, label, source, fields?}]}`.

### `refs <id>`
The references of one entity: `{id, outbound: [{path, target, line}], inbound: [{from, path, line}]}`, exactly what `model.refs` holds.

### The guard
`tools/spec-guard.js` is a Claude Code PreToolUse hook, wired in `.claude/settings.json` with the matcher `Read|Edit|Write|MultiEdit|Grep|Glob|Bash`. It reads the hook JSON on stdin, exits 2 with the reason on stderr to refuse and 0 silently to allow.
- Refused: Read, Edit, Write and MultiEdit of a specification file or a part file of a manifest specification; a Grep whose path or glob names one; shell commands that print or edit one (`cat`, `type`, `Get-Content`, `head`, `tail`, `less`, `sed`, `grep`, redirections).
- Allowed: a Read of at most 60 lines from the top (the header comment), any other file, a repository-wide Grep, `node cli/exegra.js ...`, and scripts that use `jsonc-parser`.
- Every refusal names `get`, `find` and `refs` for reading and `apply --dry-run`, then `apply`, for editing.

### `deps <id> [--direction out|in] [--transitive] [--kinds a,b]`
Dependencies of a component. Default: `out` (what it depends on), direct only. Without `--kinds`, only relationship kinds flagged as dependencies are followed.
```
node cli/exegra.js deps composition-root --transitive
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
Evaluated claim results, each with the claim's `statement` and `kind`, its `check` and `grounding`, and the sentences and lists behind them in `strength` ([claims-and-evidence.md](claims-and-evidence.md#check-strength-and-grounding)); a trace claim also carries `negatives` (each declared negative run: `scenario`, `faults`, `violated`, `outcome`, `stepIndex`, `explanation`). `--status` is one of `verified`, `supported`, `violated`, `inconclusive`, `not-evaluated`.
```
node cli/exegra.js claims --status violated
```
```json
{"ok":true,"command":"claims","project":"exegra","semanticHash":"…","result":[{"claimId":"no-direct-db","kind":"structural","method":"no-relationship","status":"violated","explanation":"…","counterexample":{"summary":"…","entities":["…"]},"statement":"The client never calls the database directly.","evidence":[]}]}
```

### `evaluate [<claimId>]`
One claim, or all claims. Returns `{results, summary}`; each result carries `check`, `grounding` and `strength`, as in `claims`. A violated claim is a finding, so the command still succeeds with `ok: true`.
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

### `admit [--file <ops.json> | --ops '<json>'] [--label <text>] [--write] [--accept <code[,code...]>]...`
Decides whether a change set (a list of operations, as for `apply`) may be folded into the specification. It evaluates the specification before, applies the operations to an in-memory copy through `Project.apply` (the same preconditions, validation and integrity ratchet as `apply`), evaluates the result, and reports the difference and a verdict. It writes only with `--write`, and only when the verdict is `admitted`; a rejected change never writes. The file is written as `apply` writes it (`--label` becomes the history label).

```
node cli/exegra.js admit --project exegra --ops '[{"type":"CreateRelationship","id":"r-web-db","kind":"calls","from":"web","to":"db"}]'
```
```json
{"ok":false,"command":"admit","project":"shop","error":{"code":"admit.rejected","message":"Rejected: admit.claim-regressed (c-no-direct). Nothing was written."},"diagnostics":[],"result":{"verdict":"rejected","reasons":[{"code":"admit.claim-regressed","id":"c-no-direct","before":"verified","after":"violated","message":"Claim \"c-no-direct\" moved from verified to violated."}],"diff":{"claims":{"changed":[{"id":"c-no-direct","before":"verified","after":"violated","direction":"worse","explanation":"Relationship \"r-web-db\" leads from \"web\" to \"db\", although no relationship was to exist."}],"added":[],"removed":[]},"validation":{"errors":{"new":[],"resolved":[]},"warnings":{"new":[],"resolved":[]}},"readiness":{"new":[],"resolved":[]},"integrity":{"new":[],"resolved":[]}},"counts":{"changedClaims":1,"regressedClaims":1,"addedClaims":0,"removedClaims":0,"…":"…"},"transaction":{"accepted":true,"affected":["r-web-db"],"semanticChanged":true},"semanticHashBefore":"…","semanticHashAfter":"…","written":[]}}
```

The envelope is `ok: true` with exit 0 when admitted. When rejected it is `ok: false` with code `admit.rejected` and exit 1, and `result` still holds the full report (as `verify` does with `verify.failed`).

Result fields: `verdict` (`admitted` or `rejected`), `reasons`, `transaction` (`accepted`; `code`, `message` and `diagnostics` when refused), `diff` (null when the transaction was refused), `counts` (`before` and `after` per side, and the number of changed, regressed, added and removed claims and of new and resolved validation errors, warnings, readiness gaps and integrity violations), `acknowledged`, `pendingRealisation`, `semanticHashBefore`, `semanticHashAfter`, `written`. The diff has `claims` (`changed` with `before`, `after`, `direction` and the evaluator's explanation after; `added` with status; `removed`), `validation` (`errors` and `warnings`, each `new` and `resolved`), `readiness` and `integrity` (each `new` and `resolved`; a violation is the rule id, its severity and the counterexample bindings) and `privilege` (`added`: each capability a role, grant, delegation or token scope gained; `removed`: each capability taken away, informational). Every list is sorted by id. Claims are evaluated exactly as `evaluate` does, with the project's recorded results.

Whether a claim regressed is decided in Lean (`Exegra.Verdict.isRegression`, formal/Exegra/Verdict.lean) over the status tuple each claim carries (`verdict`: strength, subject, open assumptions, freshness): a move is a regression unless the new status is at least the old one in the status order, so a fall to a lower or incomparable strength, a new open assumption, a change of subject or a loss of freshness is `admit.claim-regressed`. Every claim the change removes is `admit.claim-removed`. Both sides read the recorded results against the same current stamps ([claims-and-evidence.md](claims-and-evidence.md#freshness-of-recorded-facts)).

Admitted only when all of these hold; every failing one is listed in `reasons`, not only the first:

| Reason code | Meaning |
|---|---|
| `admit.transaction-refused` | The transaction was refused (unknown operation or id, a failed precondition, `validation.failed`, `integrity.violated` by an error rule, and so on). The reason carries `transactionCode`, `message` and `diagnostics`. |
| `admit.claim-regressed` | An existing claim moved to a worse status (`id`, `before`, `after`), `not-evaluated` included. |
| `admit.claim-removed` | Acknowledgeable. A claim that was `proved`, `verified`, `supported` or `model-holds` is removed by the change (`id`, `before`). |
| `admit.new-error` | A validation error the specification did not have before. |
| `admit.new-violation` | A violation of an integrity rule of any severity (`id` is the rule, with its `counterexample`) that did not exist before. |
| `admit.new-claim-weak` | A claim the change creates is not `verified` or `proved` (`id`, `status`), where a model method could decide it (see Pending realisation). Not acknowledgeable. |
| `admit.requirement-without-milestone` | A new requirement that is realised by code names no `milestone` (`id`, `status`). Not acknowledgeable. |
| `admit.privilege-change` | Acknowledgeable. `change: "capability-added"`: a role, grant, delegation or token scope gained a capability (`entity`, `kind`, `level` and `holders` where it has them, `capability`; a new entity gains all its capabilities). `"no-max-duration"`: a new or changed grant or delegation has no `maxDuration`. `"max-duration-longer"`: a `maxDuration` grew (`before`, `after`). |
| `admit.guarantee-weakened` | Acknowledgeable, with `before` and `after`. `"copy-freshness-looser"` / `"copy-erasure-looser"`: a new or changed copy class has a bound longer than the tightest other class of the same record (durations compared in nanoseconds across units; bounds that are not times are skipped). `"retention-changed"`: a retention's `keepFor`, `until`, `then`, `fields` or `archiveTo` changed, or it was removed. `"integrity-rule-changed"`: a rule's `rule`, `statement` or `severity` changed, or it was removed. `"claim-changed"`: a claim's `statement` or `evaluate` changed, or it was removed. |
| `admit.claim-vacuous` | A claim the change creates cannot fail on a correct model: its check is `holds-by-construction` or `restated-scenario` (`id`, `check`, `grounding`, `acknowledgeable: true`). |
| `admit.claim-single-trace` | A claim the change creates is decided only by running hand-written scenarios, with no exploration and no refinement: check `single-trace` (`acknowledgeable: true`). |
| `admit.claim-self-contained` | A claim the change creates reads nothing of the platform: grounding `self-contained`, its behaviors anchored to no refined behavior, record, contract event or anchored behavior (`acknowledgeable: true`). |
| `admit.theorem-weakened` | The change weakens the theorem of a `lean-theorem` claim, decided in Lean (`Exegra.Impact.weakening`) between the check recorded before the change and the check after it: the theorem is gone, its axioms gained a member, its `about` set changed, or its statement hash changed and the claim names no `supersedes` theorem of type new statement → old statement that passes the Lean gate (`weakening`: `removed`, `axioms-gained`, `about-changed`, `statement-changed`). Acknowledged only by `--accept <claim id>`, never by its code. |

The last three come from the strength of the claim ([claims-and-evidence.md](claims-and-evidence.md#check-strength-and-grounding)) and are raised for claims the change creates only; one claim can have several. They are acknowledgeable like the reasons above.

Reasons that carry `acknowledgeable: true` are decisions, not failures. `--accept <code>` (repeatable, or comma separated) acknowledges every reason with that code: it no longer blocks admission and is listed in `result.acknowledged`. A code that no reason carries is ignored. Accepting a code whose reason is not acknowledgeable (`admit.claim-regressed`, `admit.new-error`, `admit.new-violation`, `admit.new-claim-weak`, `admit.requirement-without-milestone`, `admit.transaction-refused`) fails with `admit.not-acknowledgeable` and exit 1; fix the change instead.

**Pending realisation.** `admit.new-claim-weak` applies to claims Exegra can decide when they are written: those of a method in `CLAIM_METHODS` other than `external-evidence` (structural, data-model, integrity, lean-theorem, state, temporal, metric and refinement methods). A new claim realised by code, which only executed evidence or a tool such as Concordance can settle, is a requirement whose method Exegra does not evaluate, a claim whose method the vocabulary declares in `verificationMethods`, or one of `external-evidence`. Such a claim that names a `milestone` and is `not-evaluated` or `inconclusive` for lack of evidence is admitted and listed in `pendingRealisation` (`id`, `kind`, `method`, `milestone`, `status`). Without a milestone, a requirement is `admit.requirement-without-milestone` and another code-realised claim stays `admit.new-claim-weak`. A code-realised claim already `supported` is admitted without being listed.

**Change sets.** `--change <file>` takes a change set `{ops, files}` instead of `--ops`: the operations, and the repository files the change touches (Lean sources, tests, measurement files). The result then also has `impact.remark` (the claims the change re-marks, as `impact` computes them) and, as for every admission, `guaranteeChanges`: each change of what a claim guarantees, apart from the diff (`claim`, `change`: `statement`, `evaluate`, `added`, `removed` or `theorem-statement`, with `before` and `after`).

### `impact --change <change.json>`
The claims a change set re-marks: those that depend on an entity its `ops` add, change or remove, on an entity it names in `entities`, or on a file it names in `files`, through the dependency graph of src/core/impact.js (a claim depends on the assumptions it cites, an assumption on the claim that `discharges` it, a claim on the entities its `evaluate` names, on its evidence, test evidence on its test file and the files its run covered, a `lean-theorem` claim on its theorem, the theorem on the declarations its statement uses and their files, measurement evidence on its files). Decided in Lean (`Exegra.Impact.impacted`). `result`: `remark`, `guaranteeChanges` (as in admit) and `changed` (the changed nodes). Changes nothing.
```
node cli/exegra.js impact --project exegra --change change.json
```

### `plan-delete <id>`
What a cascade delete would remove (`entities`), repair (`repairs`) and what depends on it (`dependents`). Changes nothing.
```
node cli/exegra.js plan-delete hash-binding
```
```json
{"ok":true,"command":"plan-delete","project":"exegra","semanticHash":"…","result":{"entities":["client","client-calls-server"],"repairs":[],"dependents":[]}}
```

### `replay-edits --file <capture.json>`

Check the replies to two overlapping conditional edits of one record and an independent read of the stored value after both decisions. Run from the Exegra checkout:

```sh
node cli/exegra.js replay-edits --project exegra --file capture.json
```

The selected specification supplies the `two-session-edit-race` scenario. The checker runs its simultaneous requests in both serial orders. The first scenario payload represents the first submission in `attempts`, and the second represents the second submission. Each payload supplies a distinct symbolic value. This capture matches the order `["alice", "bob"]`.

```json
{
  "format": "exegra-edit-history", "version": 1, "complete": true,
  "scope": {"tenant": "news", "record": "article-1"}, "base": "7",
  "attempts": [
    {"id":"alice","tenant":"news","record":"article-1","base":"7","value":"Spring"},
    {"id":"bob","tenant":"news","record":"article-1","base":"7","value":"Summer"}
  ],
  "observations": [
    {"kind":"reply","attempt":"bob","outcome":"conflict"},
    {"kind":"reply","attempt":"alice","outcome":"accepted"},
    {"kind":"stored","tenant":"news","record":"article-1","revision":"8","value":"Spring"}
  ]
}
```

The collector identifies each browser's own attempt and reads the record after both decisions. It supplies observations in capture order and sets `complete` only if observation covered the whole run. A witnessed transport loss can supply `{"kind":"reply-lost","attempt":"alice"}`. The stored revision and base are opaque strings. A successful write changes the revision. Product-specific revision arithmetic, isolation and external effects require their own observations and checks.

`result.verdict` is `compatible` when an order explains the observations, `incompatible` when the observations eliminate both orders, and `inconclusive` when evidence is incomplete. On a divergence `observationIndex` identifies the first unexplained observation, starting at zero. Only `compatible` exits successfully. The result is conditional on both edits being eligible, aiming at the same base, overlapping and being the only writers during capture.

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
Compares each component's declared `implementation.modules` with the files on disk. Returns `{checkedModules, missingModules, unclaimedFiles, claimedFiles, multipleOwners, errors}`. A module ending in `/` claims every file beneath it. The surface is `src/`, `cli/` and `tools/` (`.js`, `.json`, `.css`, `.html`), the Lean sources under `formal/` (`.lean`), the Rust sources under `engine/` (`.rs`), plus `index.html` and `vite.config.js` (`tools/surface.js`). Each declared module path is a module element; a surface file covered by two module elements (two components declaring it, or a directory and a file inside it) is the error `traceability.multiple-owners`, and the command fails.
```
node cli/exegra.js traceability
```
```json
{"ok":true,"command":"traceability","project":"exegra","semanticHash":"…","result":{"checkedModules":12,"missingModules":[],"unclaimedFiles":["tools/old.js"],"claimedFiles":40,"multipleOwners":[],"errors":[]}}
```

### `extract [--check]`
Runs the static extractor (`tools/extract.js`) over the implementation surface and writes `specs/<project>/extracted/facts.json`: per file its sha-256 digest and its imports (JavaScript static imports, re-exports, dynamic imports marked `dynamic`, `require` and builtins; Lean `import` lines; Rust `mod` and `use`), each resolved to the file it names or marked external, with the extractor's `id` and `version`. A fact is a function of the file bytes (line endings normalised) and the extractor version. The project reads the file as data: the model carries one `imports` relationship per pair of module elements the extracted imports connect, with provenance `extracted`, so extracted imports are witnesses of the derived interactions at every cut. With `--check` nothing is written and the command exits 1 when the file does not describe the tree (`extract.stale`). Static structure only.

### `reconcile [--observed <facts file>]`
Reconciles the declared relationships with the extracted facts (`reconcile.static-declared-redundant`, `reconcile.static-declared-unwitnessed`, `reconcile.static-direction`, `reconcile.static-kind`, all warnings: inside the surface a static dependency is derived from the code, not declared; an extracted dependency with no declared counterpart is not reported) and, with `--observed` naming a fact file written by `node tools/observe.js <recording.json>`, with a recorded session: `reconcile.observed-undeclared` (an observed interaction between components with no declared relationship) and `reconcile.not-observed` (a declared runtime interaction the recording does not show; not observed is not false). Runtime wiring is never flagged for being unextracted.

### `derive [--cut <id>] [--hierarchy <id>] [--depth N | --expand a,b | --finest] [--coarsen <kinds>|all]`
The derived architectural model at a cut ([model-and-format.md](model-and-format.md#elements-hierarchies-facets-and-cuts), "The derived model at a cut"): `blocks` (with `implicit` blocks for the facts of opened elements), `interactions` (key, from, to, kind, class, lifted, sorted `witnesses`, `summary`, `footprint`), `fibres`, `boundaries`, `interfaces` (derived groups and the declared ports they match), `connectors`, `contracts` (realisation paths with flagged hops), `realisations` and `diagnostics`. `--coarsen` relabels each kind to its nearest listed ancestor kind, or with `all` to the kinds directly under `interacts-with`. An ill-formed cut fails with `cut.invalid`. No renderer code is loaded.

```sh
node cli/exegra.js derive --project exegra --cut l1
```

### `cut [--cut <id>] [--hierarchy <id>] [--depth N | --expand a,b | --finest]`
A cut of a hierarchy (docs/model-and-format.md, "Elements, hierarchies, facets and cuts"): its blocks, the elements it opens, and its abstraction map, every element at or below the cut to its block. `--cut` names a declared cut; otherwise `--hierarchy` (default `logical`) with `--depth`, `--expand` or `--finest` gives an ad hoc one. With no option it lists the hierarchies and the declared cuts. An ill-formed cut fails with `cut.invalid`.
```
node cli/exegra.js cut --cut l1
```
```json
{"ok":true,"command":"cut","project":"exegra","semanticHash":"…","result":{"cut":"l1","hierarchy":"logical","blocks":[{"id":"semantic-core","kind":"subsystem","elements":60}],"expanded":["exegra"],"map":{"semantic-core":"semantic-core","parser":"semantic-core","module:src/core/parse.js":"semantic-core"}}}
```

### `verify [--skip-browser] [--ingest-only] [--fresh] [--expect-violated a,b] [--accept-change a,b]`
The verification pipeline:

1. Validate.
2. Check traceability.
3. Execute every `test` evidence. Its `ref` is `<test file>` or `<test file>#<name pattern>`. Files under `tests/browser/` run through `npx playwright test`. Other files run through `node --test`. A reference may contain only `A-Z a-z 0-9 _ . / - space # :` (the rule of `src/core/evidence-ref.js`, which `exegra validate` also applies as `evidence.ref-unsafe`), and its file must lie inside the repository. Anything else is recorded as `unsafe reference`, with the reason. A missing file is recorded as `test file not found`. A failure keeps the last 20 lines of output as `detail`. A `ref` written `<alias>:<file>[#<describe> > <name>]` points into a realisation root that `project.jsonc` declares: the root's test commands run once and the outcome (`pass`, `fail` or `not-run`) comes from its JUnit report ([verification.md](verification.md#realisation-roots-code-and-tests-in-other-repositories)).
   A reference passes only when at least one matched test executed and passed and none failed, skipped itself or is a `todo`; one whose matched tests skipped, wholly or in part, is recorded as `not-run`.
4. Write the results to `evidence/results.json` with `ranAt` timestamps and the records stamp of the tree (`stamp`). Results from earlier runs are replaced; an older pass is never kept for a reference that skipped.
5. Re-evaluate the claims with the new results, against the current stamps.
6. Compare the claim statuses with `claimBaseline`, those of the last passing run; a passing run records its own there.

`--fresh` runs every test again instead of reusing the outcomes recorded on the same tree (reuse happens only while the tree stamp matches; see `tests/core/outcome-reuse.test.js`). `--ingest-only` runs no realisation root's test command and reads the JUnit reports already on disk. `--skip-browser` leaves browser evidence unexecuted and records it as `not-run`, unless its earlier result was recorded on the same tree stamp.

`--expect-violated a,b` names claims that are deliberately violated. The command still succeeds when those are the only violations, as long as each keeps the counterexample recorded in the baseline. Unknown ids are rejected. `--accept-change a,b` accepts, for this run, a regression of the named claims against the baseline.

The command fails with `verify.failed` when validation has errors, any executed evidence failed (`not-run` is not a failure), any claim is violated outside `--expect-violated`, or `result.claims.regressions` is not empty: `verify.claim-regressed` (a positive claim now has a lower status, `inconclusive` and `not-evaluated` included), `verify.claim-removed` (a positive claim no longer exists) or `verify.counterexample-changed` (an expected-violated claim's counterexample changed). A failing run keeps the earlier baseline. The failure carries the full report in `result`.

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

### `prove-integrity [<ruleId>] [--rules <file>] [--max-witnesses N] [--timeout S] [--max-candidates N]`
Proves or refutes integrity rules in Lean: per rule `result` (`holds`, `violated` or `incomplete`), the exported `facts` (with the derived `relations` and their `candidates` tuples), the `differential` comparison with the JavaScript evaluator (verdict, witnesses and relation tables), the proof `file`, `theorems`, `axioms` and the times (`evaluateMs`, `exportMs`, `leanEvalMs`, `checkMs`). Each Lean process stops after `--timeout` seconds (default 300), and a rule whose relations have more than `--max-candidates` candidate tuples (default 500) is not sent to the kernel; both give `incomplete` with the reason. `--max-witnesses` is at least 1. Needs Lake. Fails with `integrity.incomplete` when a rule could not be decided.

### `prove <scenarioId> [--bound N] [--max-states N] [--steps]`
Explores every configuration of a scenario within a bound with the verified explorer of the Lean semantics, and checks the state-invariant and temporal claims that list the scenario. Needs `lake`. Its output is not written to `results.json`.

### `markdown [<documentPath>] [--out <dir>]`
Renders the document entities of a specification that holds them (a linked project converted from Markdown). With no argument it lists the document paths; with a path it prints that document; with `--out` it writes every document under the directory.

### `cover-machines [<behaviorId>] [--bound N] [--max-runs N] [--write <dir>]`
Transition and guard-outcome coverage of every shipped implementation machine (or one): `summary`, a `table` row per machine (transitions and guard outcomes covered/total, generated scenarios, open items), the `machines` in detail and the `findings`. What the scenarios leave out is searched for with bounded sequences of the machine's input events (default 12 actions and 5000 engine runs per machine). A transition nothing reaches is `machine.transition-unreachable`, a warning, or an error under `system.generation`, which fails the command with `cover.unreachable`. `--write <dir>` writes the generated scenarios to `<dir>/ops.json` as operations for `apply`. See [Coverage](coverage.md).

### `cover-functions [<functionId>] [--branches]`
Branch coverage of the function examples: `summary` (functions, those with branches, those fully covered, branches covered/total) and per function the branches covered/total, the examples and failing examples, and each uncovered branch with its location. `--branches` lists every branch. Always exits 0; informational only: readiness does not ask for every branch to be taken. See [Coverage](coverage.md).

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
- It does not run tests on its own. `verify` runs the test evidence the specification names, and `--skip-browser` leaves browser evidence unexecuted (recorded as `not-run`).
