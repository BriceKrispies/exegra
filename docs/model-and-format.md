# Model and format

## Files of a project

A project is the directory `specs/<name>/` (name matches `^[a-z0-9][a-z0-9_-]{0,63}$`):

| File | Role |
|---|---|
| `spec.jsonc` | The specification. The serialized authority. |
| `layout.jsonc` | Presentation only: pinned node positions per view. Optional; created on the first move. |
| `evidence/results.json` | Recorded results of executing test evidence, written by `exegra verify`. |
| `project.jsonc` | Optional, never written by Exegra: `spec` names a specification kept in another repository, and `roots` declares the repositories the project is realised in, which modules and test evidence address as `<alias>:<path>` ([verification.md](verification.md#realisation-roots-code-and-tests-in-other-repositories)). |
| `generated/` | Artifacts derived from the model ([self-hosting.md](self-hosting.md)). |
| `.history/journal.jsonl` | Append-only record of each saved write (sequence, file, hash, base hash, label, origin, size). |

## The specification format

`spec.jsonc` is JSON with comments and trailing commas allowed (`jsonc-parser`). Comments and formatting are preserved by every operation. The top level is an object whose keys are the sections declared in `src/core/metamodel.json`:

```
exegra  system  vocabulary  components  relationships  contracts  events
behaviors  faults  environments  failureModes  faultModels  records  copies  scenarios  assumptions  claims  integrityRules  evidence  views
```

`exegra` is the schema version string, currently `"0.1"`; a missing or different value is an error (`schema.missing`, `schema.version`). `system` is a single object; every other entity section is an array. An unknown top-level section or property is an error: nothing is dropped silently.

Every entity has an `id` matching `^[a-z][a-z0-9_]*(-[a-z0-9_]+)*$` (lower-case words joined by hyphens, underscores allowed inside a word). There is **one id namespace** for all entity kinds, including nested ports, states and transitions; a duplicate is `id.duplicate`.

```jsonc
{
  "exegra": "0.1",
  "system": { "id": "multiplayer-platform", "name": "Example multiplayer platform", "illustrative": true },
  "components": [
    {
      "id": "web-client", "name": "Web client", "category": "client",
      "purpose": "The player-facing program that submits game commands and shows their outcome.",
      "owner": "client-team", "trustZone": "public", "dataClassification": "session",
      "ports": [
        { "id": "client-command-out", "name": "Command out", "direction": "requires", "contract": "submit-command" }
      ]
    }
  ],
  "relationships": [
    { "id": "client-calls-api", "kind": "calls", "from": "client-command-out", "to": "api-command-in", "contract": "submit-command" }
  ]
}
```

(The snippet is abridged from the illustrative example in `tests/fixtures/multiplayer/spec.jsonc`, a test fixture, not a shipped project.) A relationship endpoint may be a component or a port; queries resolve ports to their component.

## Entity kinds

Defined in `metamodel.json`; the parser and the inspector both read it.

| Kind | Declared in | Purpose |
|---|---|---|
| `system` | `system` | Name, description, version, `illustrative`, `notes`. |
| `component` | `components` | `category`, `kind` (`component` or `subsystem`), `parent` (must be a subsystem; cycles are errors), `purpose`, `responsibilities`, `owner`, `trustZone`, `ports`, `unknowns`, `tags`, `implementation` (`status`, `modules`, `notes`). |
| `port` | owned by a component | `direction` (`provides`/`requires`), `contract`, `protocol`. |
| `relationship` | `relationships` | Typed, directed `from`/`to` between components or ports. |
| `contract` | `contracts` | Inputs, outputs, preconditions, postconditions, errors, obligations; optional `binding` (`protocol`, `method`, `path`, `operation`; display only). An input or output may be marked `optional: true`. |
| `event` | `events` | Name and payload fields; optional `contract`, `role` and `correlation` make it a request, response or error of a contract (see [Contract events](#contract-events)). |
| `behavior` | `behaviors` | State machine of one `subject` component: `variables`, `states`, `transitions`, `initial`. |
| `state`, `transition` | owned by a behavior | Transition: `from`, `to`, `on` (event), `guard`, `effects`, `faultOnly`. |
| `fault` | `faults` | `drop-event`, `delay-event`, `enable-transition`, `disable-transition`, `inject-event`; optional `realises` (the failure mode the injection is an instance of; never read by the engine). |
| `environment` | `environments` | What a deployment target guarantees: `guarantees`, each `{aspect, value, unit?, source}`. `aspect` is `clock-skew`, `message-delay`, `message-loss`, `message-duplication`, `message-reordering`, `storage-durability`, `api-consistency`, `zone-count`, `region-count` or `other`. |
| `failureMode` | `failureModes` | One way something can fail: `kind` (`crash`, `stop`, `restart`, `partition`, `delay`, `loss`, `duplicate`, `reorder`, `clock-skew`, `slow-storage`, `storage-loss`, `corruption`, `eventual-consistency`, `partial-apply`, `concurrent-change`, `overload`, `dependency-outage`, `other`), `target` (a component, relationship or environment), `scope` (`instance`, `process`, `host`, `zone`, `region`, `provider`), `rate` `{value, per, source}` (`per` is `second`, `minute`, `hour`, `day`, `week`, `month`, `year` or `run`), optional `duration` `{typical?, max?, unit, source}`. |
| `faultModel` | `faultModels` | A named set of failure modes in an `environment`, with `bounds`: `{scope?, modes?, maxConcurrent, source}`, for example at most one zone-scoped failure at once. |
| `record` | `records` | A kind of stored record: `owner` (component), `key`, `fields` (`{name, type, personal?, refersTo?, role?, description?}`), `retention`, `source` (see [Data model](#data-model)). |
| `copy` | `copies` | Fields of one or more records kept outside their owner: `of`, `fields`, `heldBy`, `scope`, `freshness`, `erasure`, `dependsOnAuthority`. |
| `scenario` | `scenarios` | Behaviors, timed input `steps`, active `faults`, `maxSteps`; optional `faultModel`. |
| `assumption` | `assumptions` | A statement accepted without evidence. |
| `claim` | `claims` | `kind` (`structural`, `invariant`, `temporal`, `measured`, `requirement`), `statement`, `evaluate`; optional `faultModel`. |
| `integrityRule` | `integrityRules` | `statement`, `severity` (`error`, `warning`), `rule` (a formula of the rule language), `rationale`, `basis`. A consistency rule over the whole specification, evaluated on every edit ([integrity-rules.md](integrity-rules.md)). |
| `evidence` | `evidence` | `claim`, `kind` (`test`, `measurement`, `document`, `review`), `ref`, `supports`, `observed`. |
| `view` | `views` | `projection` (`structural`, `claims`, `behavior`, `references`, `data`, `reader`), `filter` (including `entityKinds`), `display` (`colorBy`, `showPorts`, `depth`, `layout`), `reader` (`blocks`, for the reader projection). |

A specification can declare further kinds in its `vocabulary` (below); they are entities like these, in sections of their own.

`implementation.status` is one of `manual`, `model-configured`, `partially-generated`, `generated`, `not-implemented`. `illustrative: true` on a system, component, relationship or assumption marks content as an example, not a description of real software.

## Fault models and sources

What can fail, and what the environment guarantees, are entities, so a claim can say what it holds under. An `environment` lists guarantees, a `failureMode` says how one component, relationship or environment fails and how often, and a `faultModel` collects failure modes with concurrency bounds. A claim or scenario names its model in `faultModel`; a scenario fault names the failure mode it injects in `realises`. `realises` is presentation of intent for the reader and for validation: the engine input (`sim-input.js`) copies only the fields the engine reads, so it never changes a trace.

Every `rate`, `duration`, `guarantees[]` item and `bounds[]` item names a `source`, the entity that justifies the value: a requirement or other claim, an assumption, an evidence entity, or an entity of any kind the specification declares (a project's constraints, for example). A source is a reference whose allowed kinds are `["*"]`: the **any-kind reference**. It resolves to any entity, and it takes part in the reference index like every other reference, so renaming a source rewrites it and deleting a source that is still cited is refused (or repaired by cascade). The same `"ref": ["*"]` is available to a specification's own `vocabulary` properties. A value whose justification is only an estimate cites an `assumption` that says so.

Diagnostics specific to this model: `failure-mode.no-rate-source` (error: no rate, or a rate with no source), `failure-mode.no-duration-source`, `environment.guarantee-no-source` and `fault-model.bound-no-source` (errors), `failure-mode.value`, `environment.guarantee-value` and `fault-model.bound-value` (errors for impossible values), `fault-model.bound-mode-outside` and `scenario.fault-outside-model` (warnings: a bound limits a mode the model does not list; a scenario fault realises a mode that is not in the scenario's fault model), and `gap.no-fault-model` (info: an invariant, temporal or measured claim names no fault model while the specification declares at least one). Wrong enums, unresolved references and wrong kinds are the generic `property.enum`, `ref.unresolved` and `ref.kind`. The rules live in `src/core/fault-model.js`.

## Data model

Records and copies make a system's data part of its specification, so that rules about erasure, identity keying, shared copies and freshness are computed over the model instead of read from hand-maintained tables. The kinds are built into the meta-model, not declared as vocabulary: a field list is a list of objects with references and enums, which vocabulary properties cannot express (their lists hold scalars or references and do not nest), and the rules that read them are evaluated by Exegra itself, which only built-in kinds and methods can be.

```jsonc
"records": [
  { "id": "trade", "name": "Trade", "owner": "commerce-unit", "key": ["trade-id"],
    "fields": [
      { "name": "trade-id", "type": "trade-id" },
      { "name": "party-a", "type": "principal-id", "refersTo": "principal", "role": "party" },
      { "name": "counterpart-name", "type": "display-name", "personal": "name", "role": "snapshot" }
    ],
    "retention": "The financial record retention (COM-218)." }
],
"copies": [
  { "id": "store-page-variant", "name": "Store-page variant", "of": ["game"], "fields": ["game-id", "title", "price"],
    "heldBy": "cdn", "scope": "shared",
    "freshness": { "bound": 60, "unit": "second", "mechanism": "surrogate-key purge" } }
]
```

| Property | On | Meaning |
|---|---|---|
| `owner` | record | The component whose state the record is (required). |
| `key` | record | Field names that identify a record; each must be a declared field (`record.key-field`). |
| `fields[].type` | record | Free type text. A type containing the word `name` or `handle` counts as a name. |
| `fields[].personal` | record | Personal-data class: `identifier`, `contact`, `name`, `credential`, `financial`, `activity`, `location` or `other`. |
| `fields[].refersTo` | record | The id of a record whose key the field holds, or the literal `"principal"` for a principal id. A record id is an indexed reference (renamed and cascaded like any other); `"principal"` is not a reference, so no entity can be referred to by the id `principal`. |
| `fields[].role` | record | `party` (a principal taking part in the act), `subject` (the principal the record is about) or `snapshot` (a value as it was at the time of the act). |
| `of` | copy | The records it holds fields of: one, or several for a projection (required, at least one: `copy.of-empty`). |
| `fields` | copy | Field names of the source records, or `record-id.field` where two sources declare the name (`copy.field-unknown`, `copy.field-ambiguous`). Omitted: every field of every source. |
| `heldBy` | copy | The component that holds it (required). |
| `scope` | copy | `shared` (served as stored to more than one viewer: a CDN, a shared cache), `per-session`, `per-principal`, or `internal` (held server-side and never served as stored; every answer passes a read-time authority filter). |
| `freshness` | copy | `{bound, unit?, mechanism?, source?}`. `bound` is a number with a `unit` (`millisecond` to `day`, `tick`, `position`; a number without a unit is `copy.bound-unit`) or a text such as `zero`, `K-62` or `the read stamp`. |
| `erasure` | copy | `{point, bound?, unit?, basis?, source?}`: when a deletion (or the end of the source record) has reached the copy, and the basis for keeping it beyond a deletion when it is kept. |
| `dependsOnAuthority` | copy | `true` when its content depends on who is asking. |

`internal` is a fourth scope beyond `shared`, `per-session` and `per-principal`. Read models (a leaderboard view keyed by board, for example) hold principal ids and are erased on deletion, but they are not answered as stored: the authority facts and display names are applied when an answer is read. Calling them `shared` would report every read model as breaking the rule that shared copies hold no personal data, and calling them `per-principal` would misstate their key.

A record field with a duplicate name is `record.field-duplicate`. Wrong enums and unresolved references are the generic `property.enum`, `ref.unresolved` and `ref.kind`, with their positions.

### Data rules

`validate` computes five rules and reports each finding as a warning `data.<rule>` with the path of the field concerned; the claim method `data-model` evaluates the same findings ([claims-and-evidence.md](claims-and-evidence.md)). The rules live in `src/core/data-model.js`.

| Rule | Checks | Reports |
|---|---|---|
| `erasure-point` | Every copy that holds a personal field or a principal reference states `erasure.point`. Principal references count as well as personal fields, as in an erasure table whose rows include derived-view rows that hold a principal only by reference. | The copy, path `erasure`, and every such field as `record.field`. |
| `no-principal-in-shared` | No `shared` copy holds a field that is personal or refers to the principal, and none has `dependsOnAuthority: true` (D-136). | The copy and the first offending field, or `dependsOnAuthority`. |
| `party-by-id` | Every field with role `party` has `refersTo: "principal"` and a type that is not a name (D-137). | The record and the field. |
| `freshness-bound` | Every copy states a freshness bound. | The copy, path `freshness`. |
| `holder-reaches-owner` | A copy's holder is the owner of each source record, contains it or is inside it, or a directed relationship path of any kind leads from one to the other. Either direction counts, because a copy may be pulled (the holder reads the owner) or pushed (the owner publishes to the holder). | The copy, path `heldBy`, per source record. |

A `data-model` claim names the rules it states (`rules`, default all five) and may narrow them to some `records` and the copies of them. It is verified only when every listed rule had something to check and found nothing; a listed rule with nothing to check (no shared copy, no party field) makes it inconclusive.

A view of the `reader` projection draws no scene: the application shows a page in its place, built by `src/core/reader.js` from the view's `reader.blocks`. A block has a `type`: `text` (a paragraph of plain Markdown), `counts` (the entities of a `kind` counted by a `property`, as a bar and a legend, optionally per `groupBy`), `table` (a `kind` as rows with `columns`), `list` (a `kind` as items with a `titleProperty`, `bodyProperty`, `metaProperties` and `statusProperty`), `document` (the outline of a `document` and the section open in it), `sections` (the sections or tables named in `ids`, with the tables their `{{entity:id}}` markers place) or `index` (every kind with a count; each opens a page listing that kind). Rows meet every condition in `where` (`property` with `set`, `equals` or `matches`). `classify` maps a text property to a status by its first matching pattern, with a label and a tone (`done`, `partial`, `todo`, `open`, `danger`, `none`); a column marked `status` and a list's `statusProperty` use it. `facet` makes a property's values filter choices (`facetSeparator` splits one text into several), `hideWhenSet` hides rows with that property set until the reader asks for them, and `search` (default on) adds a text filter. `groupBy`, columns, facets and conditions accept a dotted path that follows references and nested objects, such as `table.section` or `evaluate.method`. An unknown block field is a validation error. A view without blocks, and the implicit Reader view of a specification that declares none, shows the system's description, the index of kinds and the first document. Every entity on the page is a link that selects it, so the inspector shows and edits it.

The Data view (the `data` projection, listed only when a specification declares records or copies) draws records, copies and the components that own or hold them, with edges from `of`, `heldBy` and `owner`; a copy or record with a finding is marked violated, with the rule as a badge. The inspector lists a record's fields and copies, and a copy's source records and the fields it holds.

`tests/fixtures/data-model/spec.jsonc` models a slice of a multi-tenant platform's data (sign-in sessions, display names and their history, receipts and trades with name snapshots, a CDN store-page variant, a leaderboard read model) with values taken from that platform's case tables. It leaves out the erasure point of the trade name snapshot on purpose, and rule `erasure-point` finds it. Exegra's own specification declares the specification text as a record with three copies (the session model, the command line's project, the generated documents); the claim `specification-copies-fresh-and-related` is verified on them. Declaring them found a gap: nothing related the generated documents to the specification file, so `holder-reaches-owner` failed until the data flow between them was declared.

## Meta-model and vocabulary

The meta-model is data. `metamodel.json` lists entity kinds with typed properties (`string`, `text`, `boolean`, `number`, `enum`, `ref`, `list`, `object`, `entities`, `expr`, `effect`, `evaluation`, `map`, `any`), default categories (shape and colour per category) and relationship kinds (line style, colour, `dependency` flag). The parser checks structure against it; the inspector builds property controls from it; projections take shapes and colours from it.

A specification extends it through `vocabulary`. Five keys are accepted:

| Key | Adds |
|---|---|
| `categories` | Component categories: label, shape, colour, description. |
| `relationshipKinds` | Relationship kinds: label, line style, colour, `dependency` flag. |
| `properties` | Properties on any entity kind, built-in or declared: `entity`, an alphanumeric `name`, and a type that is one of `string`, `text`, `boolean`, `number`, `enum` (with `values`), `ref` (with `ref`: the entity kind or kinds it may point to) or `list` (with `items`: a scalar, enum or `ref` type; lists do not nest). Also `label`, `doc`, `required` and `expected`. |
| `entityKinds` | New entity kinds: `label`, `section` (the top-level key their entities are declared under), `shape`, `color`, `doc` and `properties` (an object keyed by property name, with the same types as above). |
| `verificationMethods` | Evaluation methods carried out by tools outside Exegra: `label` and `description`. A claim whose `evaluate.method` names one is evaluated as external evidence ([claims-and-evidence.md](claims-and-evidence.md#external-verification-methods)). |

Shapes, colours and line styles come from fixed lists in the meta-model. Unknown keys, bad values and name clashes (with a built-in kind, a section or a built-in method) are `vocabulary.*` errors. A declared kind is validated like a built-in one: structure, required properties, enum values, and the kinds a `ref` may point to (`property.required`, `property.enum`, `ref.unresolved`, `ref.kind`), and an unknown top-level section is still `spec.unknown-section`. The inspector and the create dialog read the declared kinds and properties from the same meta-model, so they need no code change. References through `ref` and `list` properties are indexed like built-in ones: a rename rewrites them and a delete is refused, or cascades, because of them ([transactions-and-persistence.md](transactions-and-persistence.md)). Projections, and claim methods that Exegra evaluates itself, are still fixed per build.

A small example, from `tests/core/vocabulary.test.js`:

```jsonc
"vocabulary": {
  "entityKinds": {
    "goal": { "label": "Goal", "section": "goals", "shape": "diamond", "color": "green",
      "properties": { "statement": { "type": "text", "required": true },
                      "stage": { "type": "enum", "values": ["r1", "r2"] } } },
    "boundary": { "label": "Boundary", "section": "boundaries", "shape": "hex", "color": "teal",
      "properties": { "name": { "type": "string", "required": true },
                      "providedBy": { "type": "list", "items": { "type": "ref", "ref": ["component"] } } } }
  },
  "properties": [
    { "entity": "claim", "name": "traces", "type": "list", "items": { "type": "ref", "ref": ["goal"] }, "label": "Traces to" },
    { "entity": "claim", "name": "boundary", "type": "ref", "ref": "boundary", "label": "Stated at" }
  ],
  "verificationMethods": { "property": { "label": "Property test", "description": "Checked by a property-based test outside Exegra." } }
},
"goals": [ { "id": "g-1", "statement": "Decisions are deterministic.", "stage": "r1" } ],
"boundaries": [ { "id": "b-17", "name": "Kernel API", "providedBy": ["kernel"] } ],
"claims": [
  { "id": "krn-002", "kind": "requirement", "statement": "Same input, same output.", "subjects": ["kernel"],
    "traces": ["g-1"], "boundary": "b-17", "evaluate": { "method": "property" } }
]
```

A specification converted from a large Markdown specification (a linked project) is a full-size case: it declares eight entity kinds (goal, non-goal, boundary, decision, constraint, open question, release stage, milestone), reference-typed properties on claims and components, and the verification methods its requirements name ([importing-markdown.md](importing-markdown.md)). The shipped relationship-kind example is still plain vocabulary:

```jsonc
"vocabulary": {
  "relationshipKinds": {
    "authenticates-with": { "label": "Authenticates with", "line": "dotted", "color": "violet",
                            "dependency": true, "description": "The source obtains or verifies identity assertions through the target." }
  }
}
```

Defining the vocabulary in the specification means a new property or kind already has a validated field and an inspector control without a code change.

## Validation and diagnostics

Diagnostics have a stable `code`, a severity, a message and a location (line, column). `parseSpec` reports syntax errors, structure, ids and references; `validateModel` runs only when structure is sound.

- **error**: syntax, unknown properties, wrong types, duplicate or malformed ids, unresolved or wrongly typed references (`ref.unresolved`, `ref.kind`), containment cycles, bad expressions, bad effects, bad faults, bad scenarios.
- **warning**: self-relationships, duplicate relationships, unreachable states, a fault enabling a transition not marked `faultOnly`, an unknown claim method.
- **info (gaps)**: `gap.no-fault-model`, missing expected properties (`purpose` on components, `description` on relationships), unconnected components, empty subsystems, components with `unknowns`, unused events, `external-evidence` claims with no evidence.

References are indexed when the text is parsed, including those inside `claim.evaluate` and in transition effects (`emit`). That index drives rename and cascade delete ([transactions-and-persistence.md](transactions-and-persistence.md)).

## Expression language

Guards, effect values and claim invariants use a small language in `src/core/expr.js`. No host-language code is evaluated anywhere, and specifications cannot contain executable JavaScript.

- Literals: numbers, `'single'` or `"double"` quoted strings, `true`, `false`, `null`.
- Operators, lowest to highest precedence: `=>` (right-associative), `||`, `&&`, `==` `!=`, `<` `<=` `>` `>=`, `+` `-`, `*` `/` `%`, unary `!` and `-`; parentheses. `==` is strict equality; `+` also joins two strings.
- References: `name` (a variable of the current behavior, or `time`), `event.field` (payload field, inside a transition), `behavior-id.variable` or `behavior-id.state` (another machine, e.g. `workspace-flow.conflict`).
- Type errors, unknown references and division by zero are evaluation errors. In a simulation they stop the run with an `error` outcome on that step; in claim evaluation they make the claim `inconclusive`.

```jsonc
"evaluate": { "method": "state-invariant", "scenarios": ["edit-with-disk-conflict"],
              "expr": "workspace-flow.conflict => workspace-flow.persistedRevision == 1",
              "negatives": [ { "scenario": "edit-with-disk-conflict", "faults": ["conflict-overwrites"] } ] }
```

`negatives` lists runs that must violate the claim: a listed scenario with extra faults. A trace claim is verified only when it holds and each negative violates it ([claims-and-evidence.md](claims-and-evidence.md#negatives)).

The validator checks every expression statically: syntax, and that each reference is in scope (`expr.syntax`, `expr.reference`).

## Behaviors

A behavior's effect is `{ "set": "<variable>", "to": <literal or expression string> }` or `{ "emit": "<event>", "after": <ticks>, "payload": { ... } }`. String values in `to` and `payload` are expressions; other JSON values are literals. Transitions are tried in declaration order. See [simulation.md](simulation.md).

```jsonc
{ "id": "workspace-detect-conflict", "from": "workspace-clean", "to": "workspace-conflicted", "on": "save-requested",
  "faultOnly": true,
  "effects": [ { "set": "conflict", "to": true }, { "emit": "save-conflicted" } ] }
```

## The layout file

```jsonc
{
  // Presentation only. Nothing in this file carries architectural meaning.
  "exegraLayout": "0.1",
  "views": { "architecture": { "positions": { "web-client": [-12.5, 3.2] } } }
}
```

`views.<view-id>.positions.<entity-id>` is an absolute `[x, z]` on the ground plane, rounded to 0.01. Pins are per view and apply to leaf nodes only. They are not relative to anything: a changed layout engine or model leaves old pins where they were. The layout never enters the semantic hash. Deleting or renaming an entity removes or renames its pins in the same transaction. The choice of layout method ([architecture.md](architecture.md)) is not in this file either: a view may declare a default with `display.layout` in the specification, and the viewer's own choice is a browser preference. A layout that does not parse is treated as empty and an edit that would produce one is rejected (`layout.invalid`).

## Semantic hash

`hash.js` normalizes the model (entities sorted by id, object keys sorted, locations and layout excluded; array order kept because it can be meaningful) and hashes it with cyrb53, rendered as 14 hex digits. It identifies revisions and detects change. It is not cryptographic. Two texts differing only in comments, whitespace, key order or top-level declaration order have the same hash.

Not implemented: schema migration. The `exegra` version is checked, but no `exegra migrate` command exists although the error message mentions one. This is recorded in the self-specification (component `parser`).

## Contract events

An event may be a request, a response or an error of a contract at a boundary, so that a simulated trace is checked, and reads, like a request log.

| Property | On | Meaning |
|---|---|---|
| `contract` | event | The id of a contract. An unknown id is a reference error. |
| `role` | event | `request`, `response` or `error`; required when `contract` is set, and not allowed without it. |
| `correlation` | event | The name of a payload field that pairs a response or error with its request (the request must carry a field of that name). |
| `binding` | contract | `{protocol?, method?, path?, operation?}`, used only to label a request in the request log. |
| `optional` | contract input or output | `true` when a request may leave the input out. |

Field and type strings (`string`, `number`, `boolean`, `null`, literals such as `'a' | 'b'` or `true`, unions with `|`, arrays such as `string[]`) are read by `src/core/type-expr.js`; any other type text (`Operation[]`, `{text, hash}`) is opaque and accepts every value.

`validate` reports, with the position of the event: a missing role (`event.role-missing`), a role or correlation without a contract, a request payload field that is not an input (`event.contract-field`), an input that is not optional and missing (`event.contract-missing`), a field type that is not assignable to the contract's (`event.contract-type`), a response field that is not an output (an output typed `{ok: true, hash}` contributes the keys `ok` and `hash`), an error without a `code` field or whose literal codes are not among the contract's errors (`event.error-code`; an error named `a / b` declares both), and a correlation field that is not a payload field (`event.correlation`). The trace check and the request log are described in [simulation.md](simulation.md#contract-events-in-a-trace).
