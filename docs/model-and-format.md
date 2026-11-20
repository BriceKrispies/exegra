# Model and format

## Files of a project

A project is the directory `specs/<name>/` (name matches `^[a-z0-9][a-z0-9_-]{0,63}$`):

| File | Role |
|---|---|
| `spec.jsonc` | The specification. The serialized authority. |
| `layout.jsonc` | Presentation only: pinned node positions per view. Optional; created on the first move. |
| `evidence/results.json` | Recorded results of executing test evidence, written by `exegra verify`. |
| `project.jsonc` | Optional, written only by `exegra project add` and removed by `project remove` ([agent-interface.md](agent-interface.md#project)): `spec` names a specification kept in another repository, `products` lists product files layered on it ([Product files](#product-files)), and `roots` declares the repositories the project is realised in, which modules and test evidence address as `<alias>:<path>` ([verification.md](verification.md#realisation-roots-code-and-tests-in-other-repositories)). |
| `generated/` | Artifacts derived from the model ([self-hosting.md](self-hosting.md)). |
| `.history/journal.jsonl` | Append-only record of each saved write (sequence, file, hash, base hash, label, origin, size). |
| `<spec>.sqlite` | Optional: the SQLite store of the specification, beside it (`exegra store import`). Rebuilt from the JSONC, never committed ([store.md](store.md)). |

A linked project (a specification kept in another repository) has a `project.jsonc` in its directory: `{"spec": "<path relative to project.jsonc>"}` names the specification, and `{"concordanceResults": "<path relative to project.jsonc>"}` names a per-claim results file written by Concordance. Each `claims` entry of that file with outcome `pass` or `fail` becomes a derived `test` evidence item of its claim (id `concordance-<claim id>`), in the evaluation only; it is not a spec entity, is never written back and does not change the semantic hash. The file's `source` must name the project's specification (matched on trailing path segments), and its `tool` must be `concordance`; otherwise, a missing or invalid file, or an entry for an unknown claim, is a warning and only the affected statuses stay as they are ([claims-and-evidence.md](claims-and-evidence.md#concordance-results)).

### Product files

A specification can be a platform file plus product files beside it (`src/core/layers.js`, WG-4989). `project.jsonc` lists them: `{"spec": "...", "products": ["<file.jsonc or directory>", ...]}`, paths relative to `project.jsonc`; a directory contributes its `*.jsonc` files in name order. A product file is a JSONC object with a header and sections of entities:

```jsonc
{
  "product": {
    "id": "badges", "name": "Badges",
    "imports": { "spec": "../spec.jsonc", "entities": ["tenant-id", "product-module", "content-write"] }
  },
  "records": [ { "id": "badges-badge", "owner": "product-module", ... } ]
}
```

`imports.spec` is the platform file, relative to the product file; `imports.entities` lists every platform entity the product uses: a reference, a type named in a type text, or a capability in a `capabilities` or `requires` list. A product may declare only tenant metadata: `records`, `types`, `screens`, `forms`, `actions`, `liveBindings`, `errorMessages`, `behaviors`, `events`, `contracts`, `roles`, `scenarios`, `uiScenarios`, `claims`, `evidence` and `capabilities` (names that tenant roles grant, which only that product may name), and the typed sections `objects`, `policies`, `segments`, `settings`, `ledgerUnits`, `ledgerPools`, `ledgerLimits`, `mailTemplates`, `noticeTemplates`, `tokens`, `triggers`, `automations` and `operations`. A typed section is a list of values of a platform type with an id (`object-type-def`, `policy-def`, `segment-decl`, `setting-def`, `ledger-unit-decl`, `ledger-pool-decl`, `ledger-limit`, `mail-template-decl`, `notice-template-decl`, `token-decl`, `trigger-def`, `automation-def`, `tenant-operation-def`); `src/core/layer-values.js` checks each value against its type (struct fields, union variants by tag, enums, lists, maps, ids by pattern, scalars) and an expression is written as rule-language text. Every entity id begins with the namespace of its product, the product id with each hyphen replaced by an underscore and two underscores (`badge-milestones` gives `badge_milestones__`). Products are independent of each other: a product refers only to platform entities and its own.

Exegra splices the product entities into the platform text at the end of their sections and validates the combined model; every location names its own file (`file` in the CLI's diagnostics and sources). The refusals are `layer.header-missing`, `layer.header-invalid`, `layer.section-invalid`, `layer.kind-not-allowed`, `layer.import-mismatch`, `layer.import-unknown`, `layer.import-missing`, `layer.reference-unknown`, `layer.redefines-entity`, `layer.cross-product-reference`, `layer.namespace-missing`, `layer.value-invalid` (a typed value that does not have the shape of its platform type), `layer.outside-catalogue` (a union variant the platform type lacks, such as a trigger event or an automation step outside the published catalogue), `layer.platform-power`, `layer.platform-references-product`, `layer.product-id-duplicate`, `layer.entity-id-invalid` and `layer.entity-id-missing`; each message says what to change. The typed sections are not spliced into the combined model. A product capability is entitled by installing the product, so only a role or grant that confers it is checked. `validate` reports the hash of the platform text alone as `semanticHash` (adding a product file changes neither it nor anything generated from the platform) and the combined model's hash as `layeredHash`. Transactions edit only the platform file; a product file is edited as a file.

## The specification format

`spec.jsonc` is JSON with comments and trailing commas allowed (`jsonc-parser`). Comments and formatting are preserved by every operation. The top level is an object whose keys are the sections declared in `src/core/metamodel.json`:

```
exegra  system  vocabulary  components  relationships  contracts  events
behaviors  faults  environments  failureModes  faultModels  types  functions  exampleFixtures  records  copies  policies  validations  retentions
quotas  retries  audits  scenarios  assumptions  claims  integrityRules  integrityRelations  evidence  views
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
| `system` | `system` | Name, description, version, `illustrative`, `notes`, `generation`. |
| `component` | `components` | `category`, `kind` (`component` or `subsystem`), `parent` (must be a subsystem; cycles are errors), `purpose`, `responsibilities`, `owner`, `trustZone`, `ports`, `unknowns`, `tags`, `implementation` (`status`, `modules`, `notes`). |
| `port` | owned by a component | `direction` (`provides`/`requires`), `contract`, `protocol`. |
| `relationship` | `relationships` | Typed, directed `from`/`to` between components or ports. |
| `contract` | `contracts` | Inputs, outputs, preconditions, postconditions, errors, obligations; optional `binding` (`protocol`, `method`, `path`, `operation`, display only; `case`, the wire case, see [Wire naming and json](#wire-naming-and-json); and `suppliedBy`, see [Supplied inputs](#supplied-inputs)). An input or output may be marked `optional: true`. |
| `event` | `events` | Name and payload fields; optional `contract`, `role` and `correlation` make it a request, response or error of a contract (see [Contract events](#contract-events)). |
| `behavior` | `behaviors` | State machine of one `subject` component: `variables`, `states`, `transitions`, `initial`. |
| `state`, `transition` | owned by a behavior | Transition: `from`, `to`, `on` (event), `guard`, `effects`, `faultOnly`. |
| `fault` | `faults` | `drop-event`, `delay-event`, `enable-transition`, `disable-transition`, `inject-event`, `duplicate-event`, `lose-event`, `retry-event` (with `attempts`; [semantics.md](semantics.md#faults-the-runtime-can-produce)); optional `realises` (the failure mode the injection is an instance of; never read by the engine). |
| `environment` | `environments` | What a deployment target guarantees: `guarantees`, each `{aspect, value, unit?, source}`. `aspect` is `clock-skew`, `message-delay`, `message-loss`, `message-duplication`, `message-reordering`, `storage-durability`, `api-consistency`, `zone-count`, `region-count` or `other`. |
| `failureMode` | `failureModes` | One way something can fail: `kind` (`crash`, `stop`, `restart`, `partition`, `delay`, `loss`, `duplicate`, `reorder`, `clock-skew`, `slow-storage`, `storage-loss`, `corruption`, `eventual-consistency`, `partial-apply`, `concurrent-change`, `overload`, `dependency-outage`, `other`), `target` (a component, relationship or environment), `scope` (`instance`, `process`, `host`, `zone`, `region`, `provider`), `rate` `{value, per, source}` (`per` is `second`, `minute`, `hour`, `day`, `week`, `month`, `year` or `run`), optional `duration` `{typical?, max?, unit, source}`. |
| `faultModel` | `faultModels` | A named set of failure modes in an `environment`, with `bounds`: `{scope?, modes?, maxConcurrent, source}`, for example at most one zone-scoped failure at once. |
| `type` | `types` | A declared data type: `kind` (`id`, `scalar`, `enum`, `struct`, `union`), `repr`, `values`, `fields`, `variants`, `encoding`, `constraints` (see [Types, contract details and generation readiness](#types-contract-details-and-generation-readiness)). |
| `language` | `languages` | An expression language the users of the specified system write, such as a tenant rule language: `ast`, `values`, `shapes`, `anyShape`, `scopes`, `operators`, each operator bound to a primitive of a fixed catalogue (see [Languages](#languages)). |
| `exampleFixture` | `exampleFixtures` | A value declared once for function examples: `type`, `value`, optional `description`. An example refers to it as `{"fixture": id}` (see [Example fixtures](#example-fixtures)). |
| `function` | `functions` | A pure function a generator compiles: `params`, `returns`, `errors` (a union), `let`, `body` in the function body language, and `examples` that validation evaluates (see [Functions](#functions)). Not mirrored in Lean. |
| `record` | `records` | A kind of stored record: `owner` (component), `key`, `fields` (`{name, type, personal?, classification?, refersTo?, role?, description?}`), `retention`, `erasure`, `source` (see [Data model](#data-model)). |

| `type` | `types` | A declared data type: `kind` (`id`, `scalar`, `enum`, `struct`, `union`), `repr`, `values`, `fields`, `variants`, `encoding`, `constraints`, `metamodel` (see [Types, contract details and generation readiness](#types-contract-details-and-generation-readiness)). |
| `record` | `records` | A kind of stored record: `owner` (component), `key`, `fields` (`{name, type, personal?, classification?, refersTo?, role?, description?}`), `retention`, `erasure`, `scope`, `describedBy`, `realisation`, `source` (see [Data model](#data-model)). |
| `copy` | `copies` | Fields of one or more records kept outside their owner: `of`, `fields`, `heldBy`, `scope`, `freshness`, `erasure`, `dependsOnAuthority`. |
| `policy`, `validation`, `retention`, `quota`, `retry`, `audit` | `policies`, `validations`, `retentions`, `quotas`, `retries`, `audits` | Cross-cutting constructs: who may do what, what a value must meet, how long records are kept, how often a scope may act, how a call or emit is retried, what an act writes to an audit log (see [Cross-cutting constructs](#cross-cutting-constructs)). |
| `capability`, `plan`, `role`, `grant`, `delegation`, `tokenScope`, `featureFlag` | `capabilities`, `plans`, `roles`, `grants`, `delegations`, `tokenScopes`, `featureFlags` | What a principal may do: capabilities that contracts require, plans entitle, roles and grants confer, delegations and token scopes pass on and flags gate per tenant (see [Capabilities, plans and roles](#capabilities-plans-and-roles)). |
| `region`, `tenantClass`, `residencyException` | `regions`, `tenantClasses`, `residencyExceptions` | Residency: the regions data may be required to stay in, the classes of tenants provisioned in them with the records they confine, and approved, bounded exceptions for one copy or flow (see [Residency](#residency)). Components state a `placement` and relationships the records they `carries`. |
| `quotaPool` | `quotaPools` | Limits shared by a group of tenants: fair share, headroom, the over-share rule and its exemption, run as machines by the scenarios that list the pool in `pools` (see [Pooled quotas](#pooled-quotas)). |
| `screen`, `form`, `action`, `liveBinding`, `errorMessage`, `uiScenario` | `screens`, `forms`, `actions`, `liveBindings`, `errorMessages`, `uiScenarios` | User interface: pages with their routes and view-model contracts, forms and actions that call contracts, events that refresh open pages, the wording of refusals, and user journeys that become browser tests (see [User interface](#user-interface)). |
| `scenario` | `scenarios` | Behaviors, quota `pools`, timed input `steps`, active `faults`, `maxSteps`; optional `faultModel` and `tags` (`generated-coverage` marks a scenario `exegra cover-machines` generated, see [Coverage](coverage.md)). |
| `assumption` | `assumptions` | A statement accepted without evidence. |
| `claim` | `claims` | `kind` (`structural`, `invariant`, `temporal`, `measured`, `requirement`), `statement`, `evaluate`; optional `faultModel`; for a requirement, optional `realisation` and `realisedBy` (constructs). |
| `integrityRule` | `integrityRules` | `statement`, `severity` (`error`, `warning`), `rule` (a formula of the rule language), `rationale`, `basis`. A consistency rule over the whole specification, evaluated on every edit ([integrity-rules.md](integrity-rules.md)). |
| `integrityRelation` | `integrityRelations` | `statement`, `params` (`[{name, kinds}]`, kinds a list of entity kinds or `"*"`), `clauses` (formulas of the rule language), `rationale`, `basis`. A derived relation for integrity rules: the least relation over its parameter domains closed under its clauses, used as an atom `id(t1, ..., tn)` ([integrity-rules.md](integrity-rules.md#derived-relations)). |
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
| `fields[].personal` | record | Personal-data class: `identifier`, `contact`, `name`, `credential`, `financial`, `activity`, `location` or `other`. This is the one way to say that a field is personal data. |
| `fields[].classification` | record | Optional, one of `public`, `internal`, `personal`, `credential`. `personal` is accepted only with a `personal` class (`field.classification-personal`), and a field with a class takes no other classification (`field.classification-conflict`): a classification of `personal` confirms the class, it is not a second way to say personal. `credential` is an ordinary classification for every rule except `record-erasure-point`, which treats it as personal. A specification without classifications is unchanged. |
| `fields[].refersTo` | record | The id of a record whose key the field holds, or the literal `"principal"` for a principal id. A record id is an indexed reference (renamed and cascaded like any other); `"principal"` is not a reference, so no entity can be referred to by the id `principal`. |
| `erasure` | record | `{point?, bound?, unit?, basis?, source?}`: when a principal's deletion (or the end of the record's retention) has removed the record, or a bound with a unit, and the basis for keeping it beyond a deletion. A record holding personal data states one of them (rule `record-erasure-point`). The `retention` text is prose and is not checked. A `bound` must come with a `unit` (`record.bound-unit`). |
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

`validate` computes six rules and reports each finding as a warning `data.<rule>` with the path of the field concerned; the claim method `data-model` evaluates the same findings ([claims-and-evidence.md](claims-and-evidence.md)). The rules live in `src/core/data-model.js`.

| Rule | Checks | Reports |
|---|---|---|
| `erasure-point` | Every copy that holds a personal field or a principal reference states `erasure.point`. Principal references count as well as personal fields, as in an erasure table whose rows include derived-view rows that hold a principal only by reference. | The copy, path `erasure`, and every such field as `record.field`. |
| `record-erasure-point` | Every record with a field that is personal data (a personal class, or classification `personal` or `credential`) states `erasure.point`, or `erasure.bound` with `erasure.unit`, or has a `retention` construct that deletes it or anonymises every such field. The `retention` text does not count, since it is prose. | The record, path `erasure`, and every such field as `record.field`. |
| `no-principal-in-shared` | No `shared` copy holds a field that is personal or refers to the principal, and none has `dependsOnAuthority: true` (D-136). | The copy and the first offending field, or `dependsOnAuthority`. A field counts as personal only through the markers the model declares (`personal`, or a reference to the principal); an unmarked field that holds personal data, such as an email address, is not seen, and the scope of a result for this rule and `erasure-point` says so. |
| `party-by-id` | Every field with role `party` has `refersTo: "principal"` and a type that is not a name (D-137). | The record and the field. |
| `freshness-bound` | Every copy states a freshness bound. | The copy, path `freshness`. |
| `holder-reaches-owner` | A copy's holder is the owner of each source record, contains it or is inside it, or a directed relationship path of any kind leads from one to the other. Either direction counts, because a copy may be pulled (the holder reads the owner) or pushed (the owner publishes to the holder). | The copy, path `heldBy`, per source record. |

A `data-model` claim names the rules it states (`rules`, default all six) and may narrow them to some `records` and the copies of them. It is verified only when every listed rule had something to check and found nothing; a listed rule with nothing to check (no shared copy, no party field) makes it inconclusive.

A view of the `reader` projection draws no scene: the application shows a page in its place, built by `src/core/reader.js` from the view's `reader.blocks`. A block has a `type`: `text` (a paragraph of plain Markdown), `counts` (the entities of a `kind` counted by a `property`, as a bar and a legend, optionally per `groupBy`), `table` (a `kind` as rows with `columns`), `list` (a `kind` as items with a `titleProperty`, `bodyProperty`, `metaProperties` and `statusProperty`), `document` (the outline of a `document` and the section open in it), `sections` (the sections or tables named in `ids`, with the tables their `{{entity:id}}` markers place) or `index` (every kind with a count; each opens a page listing that kind). Rows meet every condition in `where` (`property` with `set`, `equals` or `matches`). `classify` maps a text property to a status by its first matching pattern, with a label and a tone (`done`, `partial`, `todo`, `open`, `danger`, `none`); a column marked `status` and a list's `statusProperty` use it. `facet` makes a property's values filter choices (`facetSeparator` splits one text into several), `hideWhenSet` hides rows with that property set until the reader asks for them, and `search` (default on) adds a text filter. `groupBy`, columns, facets and conditions accept a dotted path that follows references and nested objects, such as `table.section` or `evaluate.method`. An unknown block field is a validation error. A view without blocks, and the implicit Reader view of a specification that declares none, shows the system's description, the index of kinds and the first document. Every entity on the page is a link that selects it, so the inspector shows and edits it.

The Data view (the `data` projection, listed only when a specification declares records or copies) draws records, copies and the components that own or hold them, with edges from `of`, `heldBy` and `owner`; a copy or record with a finding is marked violated, with the rule as a badge. The inspector lists a record's fields and copies, and a copy's source records and the fields it holds.

### Metadata model: platform records and tenant data

A multi-tenant system can keep its tenants' data as data: each tenant describes its own object types, fields, constraints, workflows and policies in a schema, and the platform stores every tenant record in a few generic tables. The database model is then data too, and a fixed record type per tenant object would misstate it. Three properties and one type property say this (WG-4950):

| Property | On | Meaning |
|---|---|---|
| `metamodel` | type | The part of the tenant-schema metamodel the type is: `tenant-schema` (a tenant's schema, the root), `object-id` (the id of a tenant object type), `field-id` (the id of a field of one), `values` (the field values of one tenant record), `definition` (any other part: object, field, constraint, workflow or policy definitions). |
| `scope` | record | `platform`: a fixed table of the platform, its declared fields are its whole shape (tenant directory, sessions, accounts, events, journal, snapshots). `tenant-meta`: a fixed table of the platform whose rows carry tenant-defined data as data (generic records, their index, the schema history), shaped at run time by the tenant schema. |
| `describedBy` | record | For `tenant-meta`: the type with metamodel `tenant-schema` that describes the rows. |
| `realisation` | record | `shipped` (default): the running system has the table as declared. `target`: a record of the target design the running system does not have yet, kept for the machines that model it. |

| Code | Checks |
|---|---|
| `record.tenant-data-fixed` | A record that names a tenant object (a field whose type, through `list` and `option`, has metamodel `object-id`) or carries tenant field values (a field of a `values` type, or a `map<K, V>` whose key has metamodel `field-id`) has scope `tenant-meta`. Any other record with such a field is a fixed record type standing for tenant domain data, and is refused at its first such field. |
| `record.scope-missing` | Once some type has metamodel `tenant-schema`, every record states its `scope`. A specification without a tenant schema needs none. |
| `record.described-by` | A `tenant-meta` record has `describedBy`, naming a type with metamodel `tenant-schema`; a record of any other scope has no `describedBy`. |

The rule reads only the declared types, so it finds a fixed tenant record by what its fields hold, not by its name: a record of tenant content that holds neither an object type id nor field values is not seen. The rules live in `src/core/tenant-data.js`; `tests/fixtures/tenant-data/fixtures.js` has a passing metadata model and one negative fixture per way of breaking each rule.

`tests/fixtures/data-model/spec.jsonc` models a slice of a multi-tenant platform's data (sign-in sessions, display names and their history, receipts and trades with name snapshots, a CDN store-page variant, a leaderboard read model) with values taken from that platform's case tables. It leaves out the erasure point of the trade name snapshot on purpose, and rule `erasure-point` finds it. Exegra's own specification declares the specification text as a record with three copies (the session model, the command line's project, the generated documents); the claim `specification-copies-fresh-and-related` is verified on them. Declaring them found a gap: nothing related the generated documents to the specification file, so `holder-reaches-owner` failed until the data flow between them was declared.

### Residency

Where data may be is part of the data model (WG-5277). A **region** is a place data may be required to stay in. A **tenant class** is the tenants with one feature flag on, or on one plan, or every tenant; it names the regions its tenants may be provisioned in (each tenant has one, its home region) and the records whose data of such a tenant is confined. Each component says where it holds and processes data (`placement`), and a relationship that passes record content on says which records it `carries`. A **residency exception** lets one copy class or one flow of confined data sit outside the region, approved by a role, for a bounded time, with the purge obligation for when it expires.

```jsonc
"regions": [ { "id": "eu-central", "name": "EU central" }, { "id": "ca-central", "name": "Canada central" } ],
"featureFlags": [ { "id": "regulated-sector", "name": "Regulated sector", "gates": [] } ],
"tenantClasses": [
  { "id": "harbour", "name": "Harbour tenants", "flag": "regulated-sector", "provisionedIn": ["eu-central", "ca-central"],
    "confinement": "home", "binds": ["tenant-record", "attachment"] }
],
"components": [
  { "id": "search-index", "name": "Search index", "category": "storage", "placement": "per-region" },
  { "id": "delivery-network", "name": "Global delivery network", "category": "infrastructure", "placement": "global" },
  { "id": "rendition-sandbox", "name": "Rendition sandbox", "category": "computational", "placement": "per-region" }
],
"relationships": [
  { "id": "attachment-to-sandbox", "kind": "data-flow", "from": "file-store", "to": "rendition-sandbox", "carries": ["attachment"] }
],
"residencyExceptions": [
  { "id": "edge-acceleration-exception", "name": "Edge copy for accelerated pages", "tenantClass": "harbour",
    "copy": "edge-page-accelerated", "feature": "accelerated-pages", "approvedBy": "compliance",
    "maxDuration": "90 d", "renewalWindow": "14 d", "purgeWithin": "72 h",
    "residual": "Copies already served to a cached viewer may remain until that viewer's cache lifetime ends." }
]
```

| Property | On | Meaning |
|---|---|---|
| `name`, `jurisdiction` | region | The region's name, and the law or authority it answers to, as text. |
| `flag`, `plan` | tenant class | Which tenants are in the class: those with the flag on, or on the plan. At most one; with neither, every tenant. |
| `provisionedIn` | tenant class | The regions a tenant of the class may be provisioned in (required, not empty). |
| `confinement` | tenant class | `home` (default): the bound data stays in each tenant's home region. `provisioned-regions`: anywhere among `provisionedIn`. `none`: no rule. |
| `binds` | tenant class | The records whose data is confined. Their copies, and the relationships that carry them, are bound too. |
| `placement`, `regions` | component | `per-region`: an instance in each region listed (every region when none is), holding and processing a tenant's data in its home region. `fixed`: runs only in the listed regions, whatever the tenant's home. `global`: anywhere. |
| `carries` | relationship | The records whose content passes along it, so the rules follow the data to the receiving component (a processing component such as a rendition sandbox or a model provider receives data this way). |
| `tenantClass`, `copy` or `flow` | residency exception | The class, and the one copy class or relationship it lets outside the region (exactly one of the two). |
| `feature`, `approvedBy` | residency exception | The one product feature it is for (a capability or flag), and the role whose holders approve it (required). |
| `regions` | residency exception | Where it lets the data be; omitted, wherever the holder runs. |
| `maxDuration`, `renewalWindow`, `purgeWithin` | residency exception | How long one approval lasts; a renewal received this long before expiry continues the approval without restarting its clock; how soon after expiry what it let out is purged. Durations as in the constructs. |
| `residual`, `status` | residency exception | What may remain after the purge and why; `active` (default), `expired` or `revoked`. Only an active exception covers its target. |

**Where the data is.** For each tenant class whose confinement is not `none`, the data of a bound record is at the record's owner, at the holder of every copy of it, and at both ends of every relationship that carries it. A component fits the class when it is `per-region` and has an instance in every region the class provisions in; when it is `fixed` and, for `home`, the class has one region and the component runs there alone, or, for `provisioned-regions`, every region it runs in is one the class provisions in. A `global` component never fits. The rules are static: they hold for every tenant of the class, whichever region it was provisioned in, and need no scenario.

| Code | Checks |
|---|---|
| `residency.record-outside` | The owner of a bound record fits the class. Records have no exceptions. |
| `residency.copy-outside` | The holder of a copy of a bound record fits the class, or an active exception of the class names the copy (and, when the exception lists regions, the holder is fixed inside them). |
| `residency.flow-outside` | Both ends of a relationship that carries a bound record fit the class, or an active exception of the class names the relationship. |
| `residency.placement-missing` | A component that holds or receives bound data states its placement (reported once, on the component). |
| `residency.region-uncovered` | A per-region component that holds or receives bound data has an instance in every region the class provisions in. |
| `component.placement-regions` | A fixed component names its regions, a global one names none, and regions come only with a placement. |
| `tenant-class.selector` | A tenant class names at most one of `flag` and `plan`. |
| `tenant-class.provisioned-in` | A tenant class names at least one region, none twice. |
| `residency.exception-target` | An exception names exactly one of `copy` and `flow`, and that copy holds, or that flow carries, a record its class binds. |
| `residency.exception-duration` | `maxDuration`, `renewalWindow` and `purgeWithin` are positive durations. |
| `residency.exception-purge` | An exception with a `maxDuration` states `purgeWithin`. |
| `residency.exception-renewal` | A `renewalWindow` comes with a `maxDuration` and is shorter than it. |

An exception's expiry, renewal and purge happen at run time. The format records them as obligations of the exception, not as bounds of the copy, so a copy under an exception keeps its own freshness and erasure bounds. Whether a running system purges within `purgeWithin` is shown by evidence, not by these rules.

**Integrity rules read regions.** The properties above are flat references, so the rule language reads them like any other, and a derived relation can follow data across flows. `tests/fixtures/residency/harbourline.jsonc` declares `holds-bound(t, c)` (component `c` owns a bound record of `t`, holds a copy of one, or receives a flow carrying one from a component that holds bound data) and the rule that every such component is per-region or holds the data under an exception; it also says, as a rule over the copy's fields, that notification payloads to mail dispatch carry only a reference and a title. That fixture is Harbourline BR-04 and BR-05 written on the structure, with no scenario. The rules live in `src/core/residency.js`; `tests/core/residency.test.js` breaks each one once.

## Types, contract details and generation readiness

A code generator needs every name a record, contract or event uses to mean one thing, and every hand-written piece to be named. These constructs say that; all are optional, and a specification that uses none of them is unchanged.

**Types** (`types`, kind `type`). `{id, name, kind, repr?, values?, fields?, description?}` with `kind` one of `id`, `scalar`, `enum`, `struct`, `union`. An `id` or `scalar` names a built-in representation in `repr`; an `enum` has a non-empty `values`; a `struct` has `fields` `{name, type, optional?}` whose types resolve. The built-in representation types are in `src/core/builtin-types.js`: `bool`, `u8`, `u16`, `u32`, `u64`, `i32`, `i64`, `f64`, `string`, `bytes`, `timestamp`, `duration`, `uuid`, `json`, `unit`. `json` is any JSON value (see [Wire naming and json](#wire-naming-and-json)); it is never the `repr` of an id or scalar. `unit` (WG-4957) is the type with one value, Rust's `()`, written `null` in JSON: a function that can fail but gives nothing returns `unit` (`Result<(), E>`), and no one-variant union stands in for it. It is not the `repr` of an id or scalar either (`type.repr-not-builtin`), and a declared type named `unit` shadows it (`type.shadows-builtin`). A type name *resolves* when it is a built-in, the id of a declared type, `list<T>` / `set<T>` / `option<T>` / `shared<T>` of a name that resolves, or `map<K, V>` of a key and a value that resolve. Type texts nest: the arguments of `map<K, V>` are split at the comma outside angle brackets, so `map<K, map<K2, V>>` is a map of maps and `list<map<K, V>>` a list of maps.

**Sets (WG-4956).** `set<T>` is a JSON array of distinct items, in order (a `BTreeSet` in generated Rust: ascending, and decoding refuses a repeated item). It resolves, keys maps and closes recursion as `list<T>` does, and has the class `list` in guard expressions. A scenario value of a set type that repeats an item does not have the type (`scenario.input-type`).

**Sharing hints (WG-4960).** `shared<T>` is a sharing hint, identical to T on the wire: a field, payload, variant field or contract type written `shared<T>` is read and checked as `T` everywhere (resolution, class, map keys, recursion, scenario values, telemetry sensitivity, record fields). A code generator may hold it behind a shared pointer (`Arc<T>` in Rust); the spec does not change what the value is.

**Unions, maps and constraints (WG-4925).** A `union` has `variants` `[{name, fields?: [{name, type, optional?}], newtype?, tuple?}]`. A variant without fields is a unit variant; a variant with fields is struct-like; `newtype: true` marks a variant with exactly one field that is written without the field's name (serde's newtype variant); `tuple: true` (WG-4956) marks a variant with two or more positional fields, written as a JSON array of their values in declaration order, as serde writes a tuple variant (`Cmp(CmpOp, Expr, Expr)` is `{"Cmp": ["Eq", a, b]}`). A tuple field's name documents it and is not written; a tuple field is never `optional` (use `option<T>` for a position that may be null). A variant may name its own union through a field type (`list<value>`). `encoding` `{tag?, tagField?, contentField?, variantCase?}` says how a value is written, in serde's forms:

| `tag` | Written as |
|---|---|
| `external` (default) | `{"Variant": content}`; a unit variant is the bare string `"Variant"`; content is the object of the fields, the value itself for a newtype variant, or the array of the values for a tuple variant. |
| `internal` | one object `{<tagField>: "Variant", ...fields}`; needs `tagField`; variants are unit or struct-like (no newtype or tuple), and no field is named like the tag. |
| `adjacent` | `{<tagField>: "Variant", <contentField>: content}` (content left out for a unit variant); needs `tagField` and `contentField`, which differ. |
| `untagged` | (WG-4968) the variant's own JSON, with no name: a unit variant is `null`, a newtype variant the value of its field, a tuple variant the array of its values, any other variant the object of its fields (serde's `#[serde(untagged)]`). A reader tries the variants **in declaration order** and takes the first that reads the value, with an unknown member refusing a struct-like variant. It takes no `tagField`, `contentField` or `variantCase` (no name is written), no two variants are written as the same shape (a unit variant is `null`, a newtype `value <type>`, a tuple `array [<types>]`, a struct-like variant `object {<field>: <type>}`), and a newtype over `json`, which reads any value, is the last variant. |

An untagged union (`"encoding": {"tag": "untagged"}`) is what a service means by *plain JSON*: `plain-json` with variants `Null`, `Bool`, `Number`, `Text`, `Items` (`list<plain-json>`) and `Members` (`map<string, plain-json>`) is written as the raw JSON itself, which an external tag is not. Exegra writes and reads every tag in `src/core/wire.js` (`toWire`, `fromWire`; a struct's field names follow the `wireCase` option), so a value round-trips; examples of functions keep using the external form whatever the encoding. `variantCase` (`PascalCase`, `snake_case`, `kebab-case`) writes the variant names on the wire in that case, from their words (`variantWireName` in `src/core/type-shapes.js`); without it they are written as declared. Field names follow the wire case of the contract that reaches the type ([Wire naming and json](#wire-naming-and-json)). A map type `map<K, V>` is a JSON object; `K` is `string`, an integer built-in (`u8`, `u16`, `u32`, `u64`, `i32`, `i64`) or an id or scalar type represented as one of those. An `id` or `scalar` type may state `constraints` `{pattern?, minLength?, maxLength?}`: `pattern` (a regular expression) needs a `string` representation; `minLength` and `maxLength` (non-negative integers) need `string` or `bytes`. In guard expressions a union and a map value have the opaque class of `json`: compared only with `==` and `!=`.

**Records.** A field gains `optional`, `constraints` (`min`, `max`, `maxLength`, `pattern`) and `onDelete` (`restrict`, `cascade`, `set-null`; only with `refersTo`). A record gains `unique` (sets of field names), `indexes` (`{name, fields}`), `schemaVersion` (an integer of at least 1) and `changes` (`{version, description}`, one for each version from 1 to `schemaVersion`).

**Contracts.** A contract gains `ref` (a stable code such as `CT-012`), `realisation` (`generated`, `hand`, `derived`, `facade` or `target`; `derived` and `facade` are [Derived and facade contracts](#derived-and-facade-contracts), `target` is [below](#target-contracts)), `implementedBy` (a component), `deployment` (`shipped` or `target`: the code exists or is the enterprise target; default `target` when `implementedBy` names a component with `implementation.status` `not-implemented`, otherwise `shipped`; an explicit `shipped` on a not-implemented component is the error `contract.deployment-subject`), `exposure`, `auth`, `readOnly`, `tenantScope`, `development`, `idempotent` and `timeoutMs` (exposure and auth: [Contract exposure and auth](#contract-exposure-and-auth)); an error condition may carry a payload `type` and state its `status` or `kind` ([Contract errors on the wire](#contract-errors-on-the-wire)). A contract with `realisation: "hand"` is a *hole*: code written by hand against its postconditions. Its `ref` is `H-` and one to four digits, it names its `implementedBy` component, and it states at least one postcondition. A hole may state a `milestone`, like a requirement: Concordance expects its implementation once that milestone is started.

**Requirement realisation.** A claim of kind `requirement` may state `realisation`: `construction` (generated code guarantees it), `checked` (hand-written code, checked by tests) or `operational` (measured on a running deployment). See [Claims and evidence](claims-and-evidence.md#requirement-realisation).

**Scenario input types (`scenario.input-type`).** Every value a scenario feeds a machine must have the type its event declares. A step's `payload`, and the `payload` of an `inject-event` fault, are checked against the `payload` fields of the event they deliver (`src/core/scenario-input.js`):

- a field of a built-in representation: `uuid` is eight, four, four, four and twelve hexadecimal digits separated by hyphens; `u8`, `u16`, `u32`, `u64`, `i32` and `i64` are integers within the range of the type; `timestamp` and `duration` are integers; `f64` is a finite number; `bool`, `string` and `bytes` are what they say; `json` is anything;
- a field of a declared type: an `id` or `scalar` has the rule of its `repr`, an `enum` is one of its `values`, a `struct` is an object that has each of its non-optional fields, gives each field its type and has no field the struct does not declare; `list<T>` is an array of `T`;
- a field must be present unless its type is `option<T>` (or the field is a struct field marked `optional`), where it may be absent or `null`; a payload field the event does not declare is refused; an event that declares no payload is not checked;
- a type text that does not resolve (free text, or the loose forms `number`, `boolean` and `'a' | 'b'`) is judged only by the loose rules of `type-expr.js`, which accept what they cannot read.

The finding is an error when the specification sets `system.generation`, since the generated machines refuse such input, and a warning otherwise. Instance keys are payload fields, so a `uuid` key such as `"move-1"` is refused; use real, distinct UUIDs.

**Consistency rules** always apply, with or without the switch below, and are errors:

| Code | Rule |
|---|---|
| `record.set-null-required` | A field with `onDelete: "set-null"` is `optional: true`. |
| `record.on-delete-without-refers-to` | `onDelete` appears only on a field with `refersTo`. |
| `record.unique-field` | Every name in `unique` is a declared field of the record. |
| `record.index-field` | Every field of an index is a declared field of the record. |
| `record.schema-version` | `schemaVersion` is an integer of at least 1. |
| `record.changes-version` | `changes` lists versions 1 to `schemaVersion` in order, without gaps. |
| `type.repr-missing`, `type.repr-not-builtin` | An `id` or `scalar` type has a built-in `repr`. |
| `type.values-missing` | An `enum` type has a non-empty `values`. |
| `type.fields-missing`, `type.field-unresolved` | A `struct` type has `fields`, and each field's type resolves. |
| `type.repr-json` | An `id` or `scalar` type is not represented as `json`. |
| `type.union-variants` | A `union` has a non-empty `variants`, each named once (and written differently on the wire), with fields named once; a `newtype` variant has exactly one field; a `tuple` variant is not also a newtype, has two or more fields, and none of them is `optional`; only a union has `variants`. |
| `type.union-field` | The type of each variant field resolves. |
| `type.encoding` | Only a union has an `encoding`; `tagField` only with an `internal` or `adjacent` tag, and then required; `contentField` only with `adjacent`, and then required and different from `tagField`; an `internal` union has no newtype or tuple variant and no field named like its `tagField`; an `untagged` union has no `tagField`, `contentField` or `variantCase`, no two variants written as the same JSON shape, and a newtype over `json` only as its last variant. |
| `type.map-key` | The key of a `map<K, V>` (also inside `list`, `set`, `option` and another map), wherever a type is written (fields, variant fields, record fields, contract inputs, outputs and errors, event payloads, machine variables), is `string`, an integer built-in, or an id or scalar over one. A key that does not resolve is left to the readiness rules. |
| `type.recursion` | A struct does not contain itself through struct fields alone. A cycle through a union variant, `list`, `set`, `option` or `map` is allowed. |
| `type.constraints` | `constraints` only on an `id` or `scalar`; `pattern` a valid regular expression over a `string`; `minLength` and `maxLength` non-negative integers over a `string` or `bytes`, `minLength` at most `maxLength`. |
| `type.shadows-builtin` | A type id is not the name of a built-in type. |
| `requirement.construction-unmodelled` | A `construction` requirement is named in the `models` property of some claim, or names a construct in `realisedBy` ([Cross-cutting constructs](#cross-cutting-constructs)). |

**Readiness.** `system.generation` (for example `{"target": "rust"}`) declares that code is generated from the specification. When it is set, validation also reports the readiness rules below as errors (`src/core/readiness.js`); when it is not, `validate` does not report them, and `node cli/exegra.js readiness --project <name>` lists them (`{gaps: [{code, severity, message, entityId}]}`, exit code 0 either way).

| Code | Rule |
|---|---|
| `ready.field-type-undeclared` | The type of every record field resolves. |
| `ready.on-delete-missing` | Every field with `refersTo` states `onDelete`. |
| `ready.schema-version-missing` | Every record states `schemaVersion`. |
| `ready.contract-input-type-undeclared`, `ready.contract-output-type-undeclared` | Every input and output of a contract has a type that resolves. |
| `ready.contract-error-type-undeclared` | An error condition that states a `type` states one that resolves. |
| `ready.event-payload-type-undeclared` | Every event payload field has a type that resolves. |
| `ready.contract-realisation-missing` | Every contract states `realisation`. |
| `ready.hole-ref-invalid`, `ready.hole-implemented-by-missing`, `ready.hole-postcondition-missing` | A `hand` contract has an `H-` ref, an `implementedBy` component and at least one postcondition. |
| `ready.requirement-realisation-missing` | Every requirement states `realisation`. |
| `ready.error-status-missing` | Every error of a contract with `implementedBy` has a status: its own `status`, the status of its `kind`, or the default `errorKind` or `errorStatus` ([Contract errors on the wire](#contract-errors-on-the-wire)). |
| `ready.error-kind-missing` | With an `errorBody`, every error of a contract with `implementedBy` has a kind: its own `kind` or the default `errorKind`. |

### Wire naming and json

Specifications name fields in kebab-case; a service's JSON may use another convention. **`system.generation.wireCase`** is `snake_case`, `kebab-case` or `camelCase` (default `kebab-case`: the names as written), and a contract may override it with **`binding.case`** (same values). The specification keeps its kebab-case names and the generator converts them. The wire case governs the JSON names of a contract's inputs, outputs and error payloads, of the struct types they use (transitively, through `list<T>` and `option<T>`), and of the payloads of events that cross a contract (`contract` set on the event). A record's serialised form follows it only when the record is itself a contract payload. A value outside the three is the generic `property.enum` at its position.

**`json`** is a built-in type for any JSON value, such as free-form view parameters or preview blocks. A generator maps it to its language's JSON value (Rust `serde_json::Value`, JavaScript any value). In expressions it is its own class: `==` and `!=` with another `json` value or `null`; no ordering, arithmetic or concatenation; a form control cannot edit it, a toast cannot show it, and no path reaches into it, since nothing types its members.

## Languages

A specification may describe an expression language that the users of the specified system write, such as Strata's tenant rule language (constraints, policy conditions, workflow guards, defaults and query filters). A language is stated as data, so that a generator can produce its parser, printer, static checker and evaluator from it (WG-4929; generation is WG-4931).

**It is not Exegra's guard language.** Guards, effects and claim invariants keep using the [expression language](#expression-language) of `src/core/expr.js`, which Exegra evaluates and the Lean kernel mirrors. A `language` entity is **not mirrored in Lean**: the rules below are checked by `src/core/language.js`, and claims about a language are *checked*, never *proved*. Exegra evaluates, checks and prints a language only where a [function](#functions) calls `eval`, `check` or `print` on it in an example (`src/core/language-eval.js`).

**Format** (`languages`, kind `language`):

```jsonc
{ "id": "rule-language", "name": "Tenant rule language",
  "ast": "expr",            // a union type: one variant per expression form
  "values": "value",        // a union type: what an expression evaluates to
  "shapes": ["bool", "int", "str", "time", "ref", "list", "any"],
  "anyShape": "any",        // the shape of null and of what the checker cannot pin down
  "scopes": [ {"name": "new", "kind": "record-scope", "value": "New", "attributes": [{"name": "$id", "shape": "ref"}]},
              {"name": "param", "kind": "param"}, {"name": "now", "kind": "constant"}, {"name": "has_role", "kind": "role-test"} ],
  "operators": [ {"name": "and", "variant": "And", "syntax": {"form": "keyword-infix", "token": "and", "precedence": 2, "assoc": "n-ary"},
                  "operands": ["bool"], "result": "bool", "nulls": "kleene-and", "primitive": "and3"} ] }
```

- **`ast`** and **`values`** are ids of `union` types ([Unions, maps and constraints](#types-contract-details-and-generation-readiness)). A variant field typed as the AST union (or `option<ast>`) is one expression operand; a field typed `list<ast>` makes the variant n-ary.
- **`shapes`** are the static shapes the generated checker gives expressions. An operand accepts the `anyShape` wherever it expects another shape.
- **`scopes`** say how names are read. A `record-scope` is written `<scope>.<field>` (and `<scope>.<field>.<attribute>` for a one-hop reference); `value` is the value of the AST's scope field it stands for (stated on all record scopes or none), and `attributes` are its system attributes, each `{name, shape}` with a name starting with `$`. A `param` scope is written `<scope>.<name>`; a `constant` is a bare word; a `role-test` is `<scope>(<role id>)`, the role a name and not an expression.
- **`operators`**: one per AST variant, or, when a variant stands for several operators (the kernel's `Cmp(CmpOp, ...)`, `Lit(Value)`), one per value of one of its fields: `case: {field, value}`, where the field is an enum (a value) or a union (a variant name). Each operator states:
  - `syntax.form` and `token`: `infix` (a symbol token made of `= ! < > + - * / % & | ^ ~ ? :`, not `( ) [ ] , .`), `keyword-infix` (a word), `prefix-word` (a word), `call` (a word, the function name), `literal` (a literal form: `null`, `bool`, `int`, `string`, `time`, `ref`, `list`), or `scope` (read through a scope: the token names the scope for `param`, `constant` and `role-test` reads; record-scope reads take no token and read every record scope);
  - `syntax.precedence` (a positive integer, higher binds tighter) on binary and prefix operators only, and `syntax.assoc` on binary operators only: `left`, `right`, `none` (at most one occurrence: `a == b == c` is refused) or `n-ary` (a run of the operator is one list operand, as `a and b and c` is `And([a, b, c])`). All binary operators of one precedence share one associativity;
  - `operands`: one shape per expression operand, or a list of the shapes it accepts (`[["str", "list"], "any"]`); an n-ary operator states one shape, which every item has;
  - `result`: a shape, or `operand:<n>` (1-based) for the shape of the n-th operand;
  - `nulls`: `propagate` (null if any operand is null), `kleene-and`, `kleene-or`, `kleene-not` (three-valued logic), `total` (null is an ordinary value; the operator adds no null rule of its own) or `null-is-false` (a null condition takes the false branch); it must equal the primitive's;
  - `primitive`: an entry of the catalogue below, which fixes what the operator means.

**Parsing and printing** are fixed per form, so a generated printer is byte-identical to the kernel's `Display` and a generated parser reads back what it prints (`crates/substrate/src/syntax.rs`):

| Form | Parsed | Printed |
|---|---|---|
| `infix`, `keyword-infix` (`left`, `right`, `none`) | precedence climbing: an operand is parsed at the next higher level (a primary above the highest binary level) | `(` left ` ` token ` ` right `)` |
| `keyword-infix` / `infix`, `n-ary` | the operands of a run of the operator, each at the next higher level, into one list; a single operand is not wrapped | `(` items joined by ` ` token ` ` `)`; an empty list is the primitive's identity literal (`true` for `and3`, `false` for `or3`) |
| `prefix-word` | the token, then an operand at the operator's own level (`not not a`) | token `(` operand `)` |
| `call` | the token, `(`, the arguments separated by `,`, each a whole expression, `)` | token `(` arguments joined by `, ` `)` |
| `literal` | `null`, `true`/`false`, an optional `-` and digits (i64), a single-quoted string with the escapes `\'` `\\` `\n`, `time(<int>)`, `ref(<int ≥ 0>)`, `[` literals separated by `,` `]` | the same; a string escapes `'`, `\` and a newline |
| `scope` | `<scope>.<name>`, `<scope>.<field>.<name>`, `param.<name>`, a constant word, `<role-test>(<role>)` | the same |

A parenthesised expression is a primary everywhere. White space separates tokens and is otherwise ignored. An n-ary run of one operand prints in parentheses (`(a)`), as the kernel's `write_joined` does. A record-scope read prints the name of the record scope whose `value` the AST's scope field holds. The [function](#functions) operation `print(L, e)` is this printer (`printLanguage` in `src/core/language-eval.js`), so a function can state the printed form of a condition the kernel writes into its evidence.

**Error texts are the kernel's** (WG-4957). Exegra's evaluator and checker of a language give the text `crates/kernel/src/expr.rs` gives, as specc's generated evaluator writes it, where `<op>` is the operator's token (`and`, `or`, `not`, `in`, `len`, `lower`, `contains`, `starts_with`, `is_slug`, `if`), `<kind>` is the kernel's `Value::kind` of the value (`null`, `bool`, `int`, `string`, `timestamp` for a time, `reference` for a ref, `list`: `LITERAL_KINDS` in `src/core/language.js`) and `<Shape>` the shape's name in PascalCase (Rust's `{:?}` of `Shape`: `Str`, `Any`):

| Where | Text |
|---|---|
| eval: an operand of the wrong kind | `<op> does not apply to a <kind>` (for and, or, not, in (the list), len, lower, contains and starts_with (the first operand), is_slug, if (the condition), +, - and * (the left operand, then the right), ms_between, days, hours, minutes, concat (the first operand, then the second) and text); `ordering does not apply to a <kind>` for an ordering of two values of one kind other than int, time and string; `following a reference does not apply to a <kind>` for a hop through a field that holds no reference |
| eval: comparison | `cannot compare a <kind> with a <kind>` |
| eval: checked arithmetic and text | `integer-overflow` when an integer operand or the result of +, -, *, ms_between, days, hours or minutes is outside -(2^53-1) to 2^53-1; `string-too-long` when concat would give more than 4096 bytes of UTF-8 |
| eval: a record name | `unknown attribute <name>` for a name that is neither a declared system attribute nor a valid field id; a hop through a field name that is not a field id is `invalid field identifier: "<name>"` (Rust's `{:?}` of the name) |
| eval: a hop through a reference | `<field> cannot be followed here` (there is no lookup) |
| check: an operand of the wrong shape | `<op> does not accept a <Shape> operand`; `and/or` for and and or, `ordering` for the orderings |
| check: comparison, if | `cannot compare <Shape> with <Shape>`, `if branches differ: <Shape> and <Shape>` |
| check: names | `unknown field <name>`, `invalid field identifier: "<name>"`, `<field> is not a single reference` (its shape is not the ref shape), `undeclared parameter <name>`, `unknown role <role>` |

A valid field id is the kernel's `FieldId` rule (`ids.rs is_name`): an ASCII lower-case letter, then lower-case letters, digits and `_`, at most 64 bytes. The checker checks operands in the kernel's order: a comparison, `in` and `contains` check both operands, then their shapes; every other operator one operand after another, so `starts_with(1, record.missing)` reports the first operand. The shared case table `tests/fixtures/language/kernel-cases.json` lists expressions, environments and the kernel's result or exact text, with each expression's printed source so that the kernel's tests can parse and run the same cases; `tests/core/language-kernel-cases.test.js` runs it against Exegra.

**The primitive catalogue** is owned by the generator (`LANGUAGE_PRIMITIVES` in `src/core/language.js`) and pinned to the Strata kernel at `crates/kernel/src/expr.rs` (`eval` for evaluation, `check` for the static check) and `crates/substrate/src/syntax.rs` (the authoring syntax). A language cannot add a primitive; a new one is a change to Exegra and to the kernel together. An evaluation error is an error result, never a silent `false`; each use site decides what null means (a constraint is violated only by `false`, a policy, guard or filter passes only on `true`: `holds` in `expr.rs`).

| Primitive | Operands | Forms | Nulls | Evaluation | Static check | Kernel |
|---|---|---|---|---|---|---|
| `eq` | 2 | infix | `propagate` | null if either operand is null (so null == null is null); an error if the two values are of different kinds; otherwise whether the values are equal (structural equality of Value). | check, Expr::Cmp: the two shapes agree unless one is the any shape. | `crates/kernel/src/expr.rs: eval, Expr::Cmp(CmpOp::Eq) -> compare` |
| `ne` | 2 | infix | `propagate` | null if either operand is null (so null != null is null); an error if the two values are of different kinds; otherwise whether they differ. | check, Expr::Cmp: the two shapes agree unless one is the any shape. | `crates/kernel/src/expr.rs: eval, Expr::Cmp(CmpOp::Ne) -> compare` |
| `lt` | 2 | infix | `propagate` | null if either operand is null (so null < null is null); an error if the two values are of different kinds; otherwise true when the left orders before the right; ordering applies to Int (numeric), Time (numeric) and Str (by Unicode scalar values, Rust str::cmp), and is an error on other kinds. | check, Expr::Cmp: the two shapes agree unless one is the any shape, and each is Int, Time or Str. | `crates/kernel/src/expr.rs: eval, Expr::Cmp(CmpOp::Lt) -> compare` |
| `le` | 2 | infix | `propagate` | null if either operand is null (so null <= null is null); an error if the two values are of different kinds; otherwise true unless the left orders after the right (orderable kinds as for lt). | check, Expr::Cmp: the two shapes agree unless one is the any shape, and each is Int, Time or Str. | `crates/kernel/src/expr.rs: eval, Expr::Cmp(CmpOp::Le) -> compare` |
| `gt` | 2 | infix | `propagate` | null if either operand is null (so null > null is null); an error if the two values are of different kinds; otherwise true when the left orders after the right (orderable kinds as for lt). | check, Expr::Cmp: the two shapes agree unless one is the any shape, and each is Int, Time or Str. | `crates/kernel/src/expr.rs: eval, Expr::Cmp(CmpOp::Gt) -> compare` |
| `ge` | 2 | infix | `propagate` | null if either operand is null (so null >= null is null); an error if the two values are of different kinds; otherwise true unless the left orders before the right (orderable kinds as for lt). | check, Expr::Cmp: the two shapes agree unless one is the any shape, and each is Int, Time or Str. | `crates/kernel/src/expr.rs: eval, Expr::Cmp(CmpOp::Ge) -> compare` |
| `and3` | list | keyword-infix | `kleene-and` | operands left to right: the first false gives false without evaluating the rest; a non-boolean, non-null operand is an error; otherwise null if any operand was null, else true. The empty list is true and is printed as the literal true. | check, Expr::And: every operand has the Bool or any shape; the result is Bool. | `crates/kernel/src/expr.rs: eval, Expr::And -> tri_and` |
| `or3` | list | keyword-infix | `kleene-or` | operands left to right: the first true gives true without evaluating the rest; a non-boolean, non-null operand is an error; otherwise null if any operand was null, else false. The empty list is false and is printed as the literal false. | check, Expr::Or: every operand has the Bool or any shape; the result is Bool. | `crates/kernel/src/expr.rs: eval, Expr::Or -> tri_or` |
| `not3` | 1 | prefix-word | `kleene-not` | true gives false, false gives true, null gives null; any other value is an error. | check, Expr::Not: the operand has the Bool or any shape; the result is Bool. | `crates/kernel/src/expr.rs: eval, Expr::Not` |
| `in-list` | 2 | keyword-infix, infix | `propagate` | null if either operand is null; an error if the right is not a list; otherwise whether the list holds an element equal to the left (structural equality, no kind check). | check, Expr::In: the left is checked; the right has the List or any shape; the result is Bool. | `crates/kernel/src/expr.rs: eval, Expr::In` |
| `is-null` | 1 | call | `total` | whether the operand is null; never null, never an error of its own. | check, Expr::IsNull: the operand is checked; the result is Bool. | `crates/kernel/src/expr.rs: eval, Expr::IsNull` |
| `len` | 1 | call | `propagate` | null gives null; a string gives its count of Unicode scalar values (chars, not bytes); a list gives its element count; anything else is an error. | check, Expr::Len: the operand has the Str, List or any shape; the result is Int. | `crates/kernel/src/expr.rs: eval, Expr::Len` |
| `lower` | 1 | call | `propagate` | null gives null; a string gives its full Unicode lower case (Rust str::to_lowercase); anything else is an error. | check, Expr::Lower: the operand has the Str or any shape; the result is Str. | `crates/kernel/src/expr.rs: eval, Expr::Lower` |
| `contains` | 2 | call | `propagate` | null if either operand is null; two strings: whether the second is a substring of the first; a list and any value: whether the list holds an element equal to it; a first operand that is neither, or a string with a non-string second, is an error. | check, Expr::Contains: the first has the Str, List or any shape; when it is Str the second has the Str or any shape; the result is Bool. | `crates/kernel/src/expr.rs: eval, Expr::Contains` |
| `starts-with` | 2 | call | `propagate` | null if either operand is null; two strings: whether the first begins with the second; anything else is an error. | check, Expr::StartsWith: both have the Str or any shape; the result is Bool. | `crates/kernel/src/expr.rs: eval, Expr::StartsWith` |
| `is-slug` | 1 | call | `propagate` | null gives null; a string gives whether it matches [a-z0-9]+(-[a-z0-9]+)* in ASCII (non-empty, single hyphens, no hyphen at either end); anything else is an error. | check, Expr::IsSlug: the operand has the Str or any shape; the result is Bool. | `crates/kernel/src/expr.rs: eval, Expr::IsSlug -> is_slug` |
| `if` | 3 | call | `null-is-false` | the condition is evaluated first; true evaluates and gives the second operand; false or null evaluates and gives the third; any other condition is an error. Only the chosen branch is evaluated. | check, Expr::If: the condition has the Bool or any shape; the branch shapes agree unless one is the any shape; the result is the then shape, or the else shape when the then shape is the any shape. | `crates/kernel/src/expr.rs: eval, Expr::If` |
| `add-checked` | 2 | infix | `propagate` | null if either operand is null; the left plus the right: an int and an int give an int, a timestamp and an int give the timestamp that many milliseconds later; a left operand that is neither an int nor a timestamp, then a right operand that is not an int, is an error (so int + timestamp is an error); an operand or a result outside -(2^53-1) to 2^53-1 is the error integer-overflow. | check, Expr::Arith: the left has the Int, Time or any shape and the right the Int or any shape; the result is the shape of the left. | `crates/kernel/src/expr.rs: eval, Expr::Arith(ArithOp::Add) -> checked` |
| `sub-checked` | 2 | infix | `propagate` | null if either operand is null; the left minus the right: an int and an int give an int, a timestamp and an int give the timestamp that many milliseconds earlier; a left operand that is neither an int nor a timestamp, then a right operand that is not an int, is an error (so int - timestamp is an error); an operand or a result outside -(2^53-1) to 2^53-1 is the error integer-overflow. | check, Expr::Arith: the left has the Int, Time or any shape and the right the Int or any shape; the result is the shape of the left. | `crates/kernel/src/expr.rs: eval, Expr::Arith(ArithOp::Sub) -> checked` |
| `mul-checked` | 2 | infix | `propagate` | null if either operand is null; two ints give their product; a left operand that is not an int, then a right operand that is not an int, is an error; an operand or a result outside -(2^53-1) to 2^53-1 is the error integer-overflow. | check, Expr::Arith: both operands have the Int or any shape; the result is Int. | `crates/kernel/src/expr.rs: eval, Expr::Arith(ArithOp::Mul) -> checked` |
| `time-difference` | 2 | call | `propagate` | null if either operand is null; two timestamps a and b give b minus a in milliseconds, as an int; a first operand that is not a timestamp, then a second that is not, is an error; an operand or a result outside -(2^53-1) to 2^53-1 is the error integer-overflow. | check, Expr::MsBetween: both operands have the Time or any shape; the result is Int. | `crates/kernel/src/expr.rs: eval, Expr::MsBetween -> checked` |
| `days-ms` | 1 | call | `propagate` | null gives null; an int n gives n times 86400000 (milliseconds in days); anything else is an error; an operand or a result outside -(2^53-1) to 2^53-1 is the error integer-overflow. | check, Expr::Duration: the operand has the Int or any shape; the result is Int. | `crates/kernel/src/expr.rs: eval, Expr::Duration(DurationUnit::Days) -> checked` |
| `hours-ms` | 1 | call | `propagate` | null gives null; an int n gives n times 3600000 (milliseconds in hours); anything else is an error; an operand or a result outside -(2^53-1) to 2^53-1 is the error integer-overflow. | check, Expr::Duration: the operand has the Int or any shape; the result is Int. | `crates/kernel/src/expr.rs: eval, Expr::Duration(DurationUnit::Hours) -> checked` |
| `minutes-ms` | 1 | call | `propagate` | null gives null; an int n gives n times 60000 (milliseconds in minutes); anything else is an error; an operand or a result outside -(2^53-1) to 2^53-1 is the error integer-overflow. | check, Expr::Duration: the operand has the Int or any shape; the result is Int. | `crates/kernel/src/expr.rs: eval, Expr::Duration(DurationUnit::Minutes) -> checked` |
| `concat-checked` | 2 | call | `propagate` | null if either operand is null; two strings give the first followed by the second; a first operand that is not a string, then a second that is not, is an error; a result longer than 4096 bytes of UTF-8 is the error string-too-long. | check, Expr::Concat: both operands have the Str or any shape; the result is Str. | `crates/kernel/src/expr.rs: eval, Expr::Concat` |
| `to-text` | 1 | call | `propagate` | null gives null; an int, a timestamp or a reference gives its decimal digits (a leading - when negative); a bool gives true or false; a string gives itself; a list is an error. | check, Expr::Text: the operand has the Int, Time, Ref, Bool, Str or any shape; the result is Str. | `crates/kernel/src/expr.rs: eval, Expr::Text` |
| `has-role` | 0 | scope (role-test) | `total` | whether the acting principal holds the named role in the context; never null. Written `<token>(<role id>)`, the role a name, not an expression. | check, Expr::HasRole: the role is declared at the definition site; the result is Bool. | `crates/kernel/src/expr.rs: eval, Expr::HasRole; crates/substrate/src/syntax.rs: primary, "has_role"` |
| `now` | 0 | scope (constant) | `total` | the context timestamp, as a Time value; never null. | check, Expr::Now: the result is Time. | `crates/kernel/src/expr.rs: eval, Expr::Now` |
| `principal` | 0 | scope (constant) | `total` | the acting principal's id as a string for a user; null for an anonymous or system principal. | check, Expr::Principal: the result is Str. | `crates/kernel/src/expr.rs: eval, Expr::Principal` |
| `param` | 0 | scope (param) | `total` | the named parameter of the context; null when it is not supplied. Written `<scope>.<name>`. | check, Expr::Param: the parameter is declared at the definition site; the result is the any shape. | `crates/kernel/src/expr.rs: eval, Expr::Param` |
| `var` | 0 | scope (record-scope) | `total` | the record of the scope (null when the scope has no record, such as old on a create); a system attribute ($id a Ref, $version an Int, $created_at and $updated_at Times, $created_by the creator's id as a string or null); otherwise the field's value, null when unset; a name that is not a valid field id is an error. Written `<scope>.<name>`. | check, Expr::Var -> attribute_shape: a system attribute has its declared shape; a field is declared on the record at the definition site and has the shape of its field type. | `crates/kernel/src/expr.rs: eval, Expr::Var -> attribute` |
| `through` | 0 | scope (record-scope) | `total` | one reference hop: null when the scope has no record or the reference field is null; an error when the field holds something other than a Ref, when the field is not a single reference of the record's object type, or when no lookup is available or the lookup does not cover the target; null when the target record does not exist; otherwise the target's attribute, as var reads it. Written `<scope>.<field>.<name>`. | check, Expr::Through: the field is declared and is a single reference; the target object type exists; the result is the shape of the attribute on the target type. | `crates/kernel/src/expr.rs: eval, Expr::Through` |
| `literal` | 0 | literal (null, bool, int, string, time, ref) | `total` | the value written. null is the null value; printed as written in the literal forms (strings single-quoted with \' \\ and \n escaped). | check, Expr::Lit -> shape_of_value: the shape of the value; null has the any shape. | `crates/kernel/src/expr.rs: eval, Expr::Lit; write_value; crates/substrate/src/syntax.rs: tokenize, primary` |
| `list-literal` | 0 | literal (list) | `total` | the list of the literal values written; an item that is not a literal is a parse error. Printed [a, b]. | check, Expr::Lit: the result is List. | `crates/kernel/src/expr.rs: eval, Expr::Lit(Value::List); crates/substrate/src/syntax.rs: primary, "["` |

**Consistency rules** always apply and are errors:

| Code | Rule |
|---|---|
| `language.operator-duplicate` | Operator names are unique within a language. |
| `language.token-clash` | No word or symbol is claimed twice: infix symbols, keyword, prefix and call words, the words a literal form reserves (`null`, `true`, `false`, `time`, `ref`), each literal form itself, and scope names. |
| `language.syntax` | Each form has the token it needs, in its lexical class (a symbol for `infix`, a word for `keyword-infix`, `prefix-word` and `call`, a literal form for `literal`); the primitive is written in that form (and, for a literal, takes that literal form). |
| `language.precedence` | Binary and prefix operators state a positive integer precedence; binary ones an associativity; primaries (`call`, `literal`, `scope`) state neither; one precedence level has one associativity. |
| `language.primitive-unknown` | A `primitive` names an entry of the catalogue. |
| `language.arity` | The operands agree with the primitive's arity (an n-ary operator states one shape), with the form when there is no primitive, and with the AST variant's expression fields; `operand:<n>` names an operand that exists. |
| `language.shape-unknown` | `shapes` is non-empty with names once; `anyShape`, every operand shape, every result shape and every attribute shape is one of them. |
| `language.nulls` | An operator's `nulls` is its primitive's. |
| `language.variant` | `ast` and `values` are unions; an operator names a variant of `ast`, and its `case` a value of an enum or union field of that variant; no variant has two operators, nor two operators for one case, nor a mix of a plain operator and cases. |
| `language.scope` | Scope names are words, declared once; `attributes` and `value` only on a record scope, attribute names start with `$` and appear once, record scope values are distinct and stated on all or none; a scope-form operator's token names a scope of the kind its primitive reads (record reads need at least one record scope and take no token); every scope is read by some operator. |

**Readiness** (errors when `system.generation` is set, listed by `readiness` otherwise): a language is complete.

| Code | Rule |
|---|---|
| `ready.language-variant-uncovered` | Every AST variant has an operator; a variant split into cases has an operator for every value of its case field. |
| `ready.language-primitive-missing` | Every operator names a primitive. |

## Functions

A specification may state pure functions, so that the decision logic of the specified system (a kernel's intent decision, policy evaluation, validation, workflow steps, view assembly) is stated in the specification and a generator compiles it into a pure crate (WG-4933; generation is WG-4934). A function takes typed parameters and gives a value of its return type, or fails with a variant of its error union. It has no effects: no clock, no randomness, no I/O.

**Exegra evaluates the examples.** Validation runs every example of every function in JavaScript (`src/core/function.js`) and refuses a wrong one, which gives each function a checked meaning. Functions are **not mirrored in Lean**: claims about them are *checked* by their examples and tests, never *proved*.

**Format** (`functions`, kind `function`):

```jsonc
{ "id": "check-version",
  "description": "transition.rs check_version",
  "params": [{"name": "version", "type": "u64"}, {"name": "expected", "type": "option<u64>"}],
  "returns": "unit",                        // the built-in unit: Result<(), DomainError>
  "errors": "domain-error",                 // a union: the ways it can fail
  "body": "match expected { Some(v) => if v != version then fail(domain-error.VersionConflict{message: format('record is at version {}, expected {}', version, v)}) else (), None => () }",
  "examples": [
    {"args": {"version": 2, "expected": 1}, "error": {"VersionConflict": {"message": "record is at version 2, expected 1"}}},
    {"args": {"version": 2, "expected": null}, "result": null} ] }
```

- **`params`**: each `{name, type}`; the name is a plain name (letters, digits, `_`, inner hyphens), not a keyword, and unique among the parameters and lets; the type is a type text that resolves ([Types](#types-contract-details-and-generation-readiness)), or `result<T, E>`.
- **`returns`**: the type of the body. **`errors`**: the id of a union type; only a function with `errors` may use `fail`, and `try` passes on errors of that union only.
- **`let`**: names bound in order before the body, each seeing the parameters and the lets before it.
- **`examples`**: each `{args, result}` or `{args, error}` (and an optional `description`). `args` is an object of the parameters; a parameter left out is null.

**The JSON null (WG-4968).** The literal `null` has the type *option of unknown*, which fits every `option<T>`; it also stands where a `json` value is expected, so `if keep then blob else null` is a `json` and `view-block{kind, params: null}` sets a `json` field to the JSON null. Nothing else takes it: where a string, number, bool, struct or list is expected, `null` is `function.expr-type`. In memory the JSON null and an absent `option<json>` are both null; an example writes a `json` field as `null` and it is present.

**Values in examples** are JSON: bool, number and string as themselves; the unit value as `null`; an enum value as its name; an id or scalar as its representation; a struct as an object of its fields (an absent optional or option field is null); `list<T>` an array; `option<T>` null or the value; `map<K, V>` an object (integer keys as decimal strings); a union in serde's external form whatever its wire encoding: a unit variant is its name (`"Unit"`), a newtype variant `{"Name": value}`, any other variant `{"Name": {fields}}`; `result<T, E>` is `{"Ok": t}` or `{"Err": e}`. A result compares structurally with what the function gives.

### Example fixtures

A tenant or a schema that a function takes is long, and every example of every function that takes one repeats it. A specification declares such a value once, in the section `exampleFixtures` (kind `exampleFixture`), and examples refer to it (WG-4963):

```jsonc
"exampleFixtures": [
  { "id": "tenant-alpha", "type": "tenant", "description": "An owner, two writers and an editor.",
    "value": { "members": {"alpha:owner": ["owner"]}, "policies": {} } },
  { "id": "note-stored", "type": "subject", "value": { "old": {"title": {"Str": "First"}}, "new": {"title": {"Str": "First"}} } } ]
// in an example:
{ "args": { "tenant": {"fixture": "tenant-alpha"},
            "subject": {"fixture": "note-stored", "with": {"old.title": {"Str": "Other"}, "new.title": {"Str": "Other"}}} },
  "result": ... }
```

- **`type`** is a type text that resolves (or `result<T, E>`) and **`value`** a value of it, written as examples write values. A fixture stands where its type, or an option of it, is expected.
- **A reference** is an object whose `fixture` is a fixture id and whose only other key, if any, is `with`. It can be an argument, a `result` or an `error` of an example; any other object is a value of its own, so a struct with a field named `fixture` is still written out. References do not nest inside values.
- **`with`** is an object of dotted path to value; each pair replaces the value at the path, in order. A path goes through struct fields, map keys, list indexes (decimal) and the name of the variant of a union value written `{"Variant": content}`, and looks through options; the last step of a path may also add a map key or fill a field that is absent or null. A map key that has a dot cannot be named. The fixture itself is never changed.
- Exegra resolves every reference before it evaluates the example, so an example with fixtures is checked exactly as one with the values written out.

| Code | Meaning |
|---|---|
| `example.fixture-unknown` | An example refers to a fixture that is not declared. |
| `example.fixture-type` | A fixture's type does not resolve or its value is not of its type; or a fixture, with its overrides, is not the type of the parameter, result or error it stands for. |
| `example.fixture-override` | An override path does not lead into the fixture's value (a field or key that is not there, an index out of range, a step into a scalar, an empty step), or `with` is not an object. |

A generator reads the same references: specc writes one function per fixture into the test module of the generated code, and an example calls it and applies its overrides in code.

### The body language

The body language is Exegra's [guard language](#expression-language) (its literals, names, operators and precedence) extended with field access, `if`, `let`, `match`, constructors, list literals, the operations below, calls of other functions, `fail` and `try`. The parser is `src/core/function-syntax.js`.

```
expr     : implies
implies  : or ( '=>' implies )?                       right associative
or       : and ( '||' and )*
and      : equality ( '&&' equality )*
equality : compare ( ( '==' | '!=' ) compare )*
compare  : additive ( ( '<' | '<=' | '>' | '>=' ) additive )*
additive : multiply ( ( '+' | '-' ) multiply )*
multiply : unary ( ( '*' | '/' | '%' ) unary )*
unary    : '!' unary | '-' unary | 'try' unary | postfix
postfix  : primary ( '.' word )*
primary  : number | string | 'true' | 'false' | 'null' | '(' ')' | '(' expr ')'   () is the unit value
         | '[' ( expr ( ',' expr )* )? ']'                   list literal
         | '{' '}'                                           the empty map
         | 'if' expr 'then' expr 'else' expr
         | 'let' name '=' expr 'in' expr
         | 'match' expr '{' arm ( ',' arm )* ','? '}'        the scrutinee takes no struct constructor
         | 'call' name '(' ( expr ( ',' expr )* )? ')'       a call of another function
         | name '(' args ')'                                 an operation
         | path '{' ( init ( ',' init )* ','? )? '}'         struct T{..} or union variant T.V{..}
         | path '(' expr ')'                                 newtype union variant T.V(e)
         | path                                              a name and its fields, a unit variant T.V, an enum value T.V
path     : name ( '.' word )*                                word: a name, or a keyword
init     : word ':' expr | name                              name alone is name: name
arm      : pattern '=>' expr
pattern  : '_' | word | word '(' bind ')' | word '{' field ( ',' field )* '}'
field    : word ':' bind | name
bind     : name | '_'
args     : binder ',' expr                                   map, filter, find, any, all, sortBy
         | binder ',' name '=' expr ',' expr                 fold
         | ( expr ( ',' expr )* )?                           every other operation
binder   : name 'in' expr
word     : a name or a keyword
```

Strings are single- or double-quoted with no escapes, numbers are decimal (a minus is the unary operator), and white space separates tokens. The keywords `let in if then else match call try true false null` name nothing else: no parameter, let or bound name is a keyword.

**Keyword-named variants and fields** (WG-4957). A union variant, an enum value or a field may be named like a keyword, as Strata's value union names its null variant `null` and its expression union has the variants `if` and `in` and the fields `then` and `else`. Such a name is written as it is wherever the grammar reads a *word*: after a `.` (`value.null`, `expr.if{condition: c, then: a, else: b}`, `x.then`), as the name of a match pattern (`null => ...`, `if{then: t, else: e} => ...`, `in(x) => ...`) and before the `:` of a constructor field or a pattern field. No expression begins in these places, so nothing is ambiguous. The shorthand that binds a field to its own name (`{then}`) is refused for a keyword-named field, since the keyword cannot be bound: write `then: t`. `if`, `let` and `match` reach as far right as they can (`if a then b else c + 1` adds to `c`). A name is resolved in this order: a parameter, let or bound name (then `.f` reads its field `f`); `T.V` where `T` is an enum (the value `V`) or a union (the unit variant `V`).

**Typing.** Every expression has a type: a type of the format, `result<T, E>`, *never* (the type of `fail`, which fits anything) or *unknown* (the element of `[]` and `{}`, the inner type of `null`, which fits anything). Ids and scalars are compared and passed as their representation (a `role-id` over `string` is a string); the integer types, `f64`, `timestamp` and `duration` are numbers to each other; enums, structs and unions are equal only to themselves. A `T` fits where `option<T>` is expected (it is the present value); an `option<T>` never fits where `T` is. The guard operators keep their rules: `!`, `&&`, `||`, `=>` take bools; `-`, `*`, `/`, `%` and the orderings take numbers; `+` takes two numbers or two strings; `==` and `!=` take two values one of which fits the other, compared structurally. Integer arithmetic is checked in the operand's type (an overflow or a division by zero is an evaluation error; `/` truncates). The branches of `if`, the arms of `match` and the items of a list have one type. A struct read `.f` needs a struct with a field `f`; an optional field reads as `option<T>`. A constructor sets every field that is neither optional nor an option, each once, with a value that fits; `T.V(e)` builds a variant with exactly one field. The types come from `typeStructure` in `src/core/codegen-model.js`, which extends the classes of `typeClass` with each struct's fields and each union's variants; a `set<T>` is typed and held as a `list<T>`. `unit` is its own class: `()` has it, it fits only `unit`, and it is compared with `==` and `!=`.

**`match`** takes a union (its variants), an `option<T>` (`None`, `Some(x)`), a `result<T, E>` (`Ok(x)`, `Err(e)`) or an enum (its values as bare names). `V` matches the variant whatever its fields; `V(x)` binds the one field of a variant that has one; `V{f, g: y}` binds fields by name (`_` binds nothing). Arms are tried in order. A match covers every variant or ends with `_`; no variant has two arms and no arm follows `_`.

**`call f(a, b)`** calls function `f` with arguments that fit its parameters. When `f` declares `errors`, the call gives `result<R, E>`: match on it, or write **`try call f(...)`**, which gives the `R` and fails the caller with the same error when `f` fails; the caller must declare the same error union. **`fail(e)`** fails the function with `e`, a value of its error union. The call graph is acyclic but for structural recursion, and every list operation runs over a finite list, so every function is total.

**Structural recursion** (WG-4957). A function may call itself, as the kernel's `mentions_field` walks an expression tree, when every call of itself passes, at one parameter position shared by all of them, a *strict sub-value* of that parameter, whose type is a union. A strict sub-value is a name bound by a `match` on the parameter (or on a strict sub-value of it) to a field of one of its union variants (`Not(a)`, `Cmp{left, right}`), an item of a list such a name holds (`any(i in items, call f(i))`), an item or value of a list or map such a name holds as `values`, `get`, `find`, `filter`, `take` and `sortBy` give it (`match get(m, k) { Some(x) => call f(x), None => ... }`), or a field read from any of these; `Some(x)` and `Ok(x)` of a sub-value bind a value as strict as the matched one, and a `let` passes a sub-value on. Every call then works on a strictly smaller value, so the recursion ends. Exegra checks the rule (`selfRecursion` in `src/core/function.js`); a call of itself on anything else (the parameter itself, a value the body builds, a parameter that is not a union) and every cycle through two or more functions is `function.recursion`.

```
match e { Var{name} => !startsWith(name, '$'), Through => true, Not(a) => call mentions-field(a),
          And(items) => any(i in items, call mentions-field(i)),
          Cmp{left, right} => call mentions-field(left) || call mentions-field(right), _ => false }
```

**Operations** (`xs` a `list<T>`, `m` a `map<K, V>`; a binder `x in xs` binds `x` to each item in order):

| Operation | Type | Meaning |
|---|---|---|
| `map(x in xs, e)` | `list<typeof e>` | `e` for each item, in order. |
| `filter(x in xs, c)` | `list<T>` | The items for which the bool `c` holds, in order. |
| `find(x in xs, c)` | `option<T>` | The first item for which `c` holds, or null. |
| `any(x in xs, c)`, `all(x in xs, c)` | `bool` | Whether `c` holds for some item (false for none) or for every item (true for none). |
| `fold(x in xs, acc = init, e)` | the type of `init` | `acc` starts as `init`; for each item, `acc` becomes `e`; the last `acc`. An early exit is a state the step keeps (`if acc.done then acc else ...`). |
| `sortBy(x in xs, k)` | `list<T>` | The items ordered by the key `k`; stable. The key is a number, a string, a bool, an enum value, or a `list`, `option`, struct or union of those (`json`, a map and `result` are not ordered). Numbers numerically, strings and enum values by Unicode scalar values, false before true, null before any value of an `option`, a list item by item with a prefix before the longer list (Rust's `Vec` order), a struct field by field in declaration order, and a union by the position of its variant in the declaration and then its fields in order: Rust's derived `Ord`, so declaring the kernel's `Value` as `Null, Bool, Int, Str, Time, Ref, List` orders its values as the kernel does (WG-4968). |
| `take(xs, n)` | `list<T>` | The first `n` items (all of them when there are fewer). |
| `concat(a, b)` | `list<T>` | The items of `a`, then those of `b`. |
| `keys(m)`, `values(m)` | `list<K>`, `list<V>` | The keys in order (numbers numerically, strings by Unicode scalar values, as a Rust `BTreeMap` iterates), the values in the order of their keys. |
| `get(m, k)`, `get(xs, i)` | `option<V>`, `option<T>` | The value of key `k`, or the item at index `i` (from 0), or null. |
| `insert(m, k, v)`, `remove(m, k)` | `map<K, V>` | The map with `k` set to `v`, or without `k`. |
| `format("policy:{}", x)` | `string` | The literal text with each placeholder replaced by the next value; the number of placeholders equals the number of values. See [format](#format-placeholders) below. |
| `eval(L, e, env)`, `eval(L, e, env, lookup)` | `result<V, string>` | Evaluate `e`, a value of the AST union of the declared [language](#languages) `L`, in the environment `env`; `V` is `L`'s value union. The optional `lookup` is a `map<string, map<string, map<string, V>>>` that following a reference (`through`) reads (WG-4968). |
| `check(L, e, env)` | `result<string, string>` | Check `e` statically against `env`: `Ok` of its shape, or `Err`. |
| `print(L, e)` | `string` | `e` in `L`'s authoring syntax, by the printing rules of [Languages](#languages): byte for byte the kernel's `Display` of `Expr` (`crates/kernel/src/expr.rs`) and specc's generated printer. |
| `startsWith(s, p)`, `endsWith(s, p)` | `bool` | Whether `s` begins (ends) with `p`: Rust `str::starts_with`, `str::ends_with`. |
| `length(s)`, `length(xs)` | `u64` | The number of Unicode scalar values of a string (Rust `s.chars().count()`, as expr.rs `len` counts; not `str::len`, which counts bytes), or of items of a list. |
| `trim(s)` | `string` | `s` without leading and trailing white space: Rust `str::trim`, which removes the characters with the Unicode White_Space property (U+0009 to U+000D, U+0020, U+0085, U+00A0, U+1680, U+2000 to U+200A, U+2028, U+2029, U+202F, U+205F, U+3000; not U+FEFF). |
| `chars(s)` | `list<string>` | The Unicode scalar values of `s`, each a one-character string: Rust `s.chars()`. |
| `isAsciiLowercase(s)`, `isAsciiUppercase(s)`, `isAsciiAlphabetic(s)`, `isAsciiDigit(s)`, `isAsciiAlphanumeric(s)` | `bool` | Whether `s` is not empty and every character of it is in the class: for one character, Rust `char::is_ascii_lowercase` (`a`-`z`), `is_ascii_uppercase` (`A`-`Z`), `is_ascii_alphabetic`, `is_ascii_digit` (`0`-`9`), `is_ascii_alphanumeric`. With `chars` and `get` they state the kernel's `FieldId::new` (`ids.rs is_name`): `match get(chars(s), 0) { Some(c) => isAsciiLowercase(c) && length(s) <= 64 && all(x in chars(s), isAsciiLowercase(x) \|\| isAsciiDigit(x) \|\| x == '_'), None => false }`. |
| `snakeCase(s)` | `string` | The kernel's snake_case of a PascalCase name (`transition.rs snake_case`): each ASCII capital becomes lower case, preceded by `_` unless it is the first character (`UnknownRecord` is `unknown_record`); every other character is kept. `snakeCase(format('{:?}', kind))` is the rule name of a refusal. |
| `parseTime(s)` | `result<i64, string>` | The substrate's `plain.rs parse_time`: `YYYY-MM-DD` or `YYYY-MM-DDTHH:MM[:SS]Z` (UTC) as milliseconds since the epoch; the date and time split at the first `T`, the time must end in `Z`, the year is four bytes, each number is read as Rust's `i64::from_str` reads it (a leading `+` or `-` is allowed), the month is 1 to 12, the day 1 to 31 (in any month), the hour 0 to 23, the minute and second 0 to 59; otherwise `Err` of `not a UTC timestamp: "<s>"` (Rust's `{:?}` of `s`). |
| `fail(e)` | never | Fail with `e`, a value of the function's error union. |

#### Format placeholders

`format` has three placeholders (WG-4957), each pinned to what the Rust a generator emits writes:

| Placeholder | Takes | Writes |
|---|---|---|
| `{}` | numbers, strings, bools, enum values | Rust's `Display`: a string as it is, an integer in decimal, an `f64` in decimal without an exponent (`1.0` is `1`, `1e21` is `1000000000000000000000`), a bool as `true` or `false`, an enum value as its declared name. |
| `{:?}` | every value but `json` and `bytes` | Rust's derived `Debug` of the type specc generates (types and variants in PascalCase, fields in snake_case, as `crates/spec-compiler/src/naming.rs` names them): an id or scalar is a newtype, `ObjectTypeId("note")`, `RecordId(3)`; an enum value or a unit variant its name, `Update`; a newtype variant `Object(ObjectTypeId("note"))`; a tuple variant `Cmp(Eq, Lit(Int(1)), Now)`; a struct or struct-like variant `RuleCheck { rule: "p", passed: true }`; a string in double quotes with `\0 \t \r \n \\ \"` escaped and a combining mark or a character Rust does not print as `\u{hex}`; an `f64` as Rust's `{:?}` (`1.0`, `0.5`, `1e16`, `1.5e-7`: exponential below 1e-4 and from 1e16); an option `Some(x)` or `None`; a list `[a, b]`; a set `{a, b}` in order; a map `{k: v}` in key order; a result `Ok(x)` or `Err(e)`; unit `()`; a uuid hyphenated, without quotes. So `format('{:?} on {:?}', action, resource)` is the kernel's `Update on Object(ObjectTypeId("note"))`. |
| `{:json}` | strings, numbers, bools, `json`, and options and lists of them | serde_json's compact text (`serde_json::to_string`): a string in double quotes with `\" \\ \b \f \n \r \t` escaped and any other character below U+0020 as `\u00XX`; an integer type in decimal; an `f64` as ryu writes it (decimal with at least one fractional digit from 1e-5 up to 1e16, `1.0`, `0.1`; exponential otherwise, `1e16`, `1.5e-7`; a non-finite one is `null`); `null` for an absent option; a list as an array; a `json` value with its object keys in order (serde_json's default map) and its whole numbers as integers. |

**`eval` and `check` of a language.** An expression is a value of the language's AST union, not source text, as the kernel stores parsed expressions. Each operator means what its primitive means in the [catalogue](#languages). The environment of `eval` is a struct with one field per scope of the language, named as the scope: a `record-scope` is an `option<map<string, V>>` (the record's fields and its system attributes such as `$created_by`; null when there is no record), a `param` scope a `map<string, V>`, a `constant` a `V`, and a `role-test` a `list<string>` of the roles held. Which variant of `V` is which kind of value (null, bool, int, string, time, ref, list) is the one the language's literal operator for that form names. The environment of `check` is a struct with `fields: map<string, string>` (the shape of each field at the definition site), `params: list<string>` and `roles: list<string>`. An AST field typed `string` or an id or scalar over string (`has_role`'s `role-id`) is read as a name (WG-4962). Exegra's evaluator (`src/core/language-eval.js`) has no lookup, so a hop (`through`) from no record or through an empty field is null, as in the kernel, and a hop through a reference is the error `<field> cannot be followed here`, as in the kernel without a lookup; `check` gives a hop through a field of the ref shape the shape of a declared system attribute it names, and the any shape otherwise. The text of an `Err` is the kernel's ([error texts](#languages)), so an example may state it.

**Consistency rules** always apply and are errors (each function reports its first finding):

| Code | Rule |
|---|---|
| `function.expr-syntax` | The body and every let parse. |
| `function.expr-reference` | Every name, field, variant, enum value, type, function, language and operation an expression names exists. |
| `function.expr-type` | Every expression is well typed by the rules above, and the body fits the return type. |
| `function.match-exhaustive` | A match covers every case of what it matches, or ends with `_`; no case has two arms and no arm follows `_`. |
| `function.recursion` | No function calls itself through others, and a function calls itself only by structural recursion: at one parameter position, a union, every call of itself passes a strict sub-value of that parameter (reported once per cycle). |
| `function.error-unknown` | `errors` names a union type; `fail` is used only in a function with `errors` and with a value of that union; `try` passes on only errors of the caller's union. |
| `function.param` | Parameters and lets have plain names, not keywords, each once; parameter and return types resolve. |
| `function.example-failed` | Every example is `{args, result}` or `{args, error}`, names only parameters, gives values of the declared types, and evaluates to its result or error. Examples are evaluated only when the function and every function it calls are free of findings. |

**Readiness** (errors when `system.generation` is set, listed by `readiness` otherwise):

| Code | Rule |
|---|---|
| `ready.function-example-missing` | Every function has an example that succeeds, and an example of each error variant it can fail with: the variants its own `fail` constructors name (every variant when `fail` is given something other than a constructor) and those of the functions it calls with `try`. |
| `ready.function-branch-uncovered` | Every branch of every function is taken by some example: both branches of each `if`, each arm of each `match` (`_` included), the value and the error path of each `try` (the error path only when the called function can fail) and each `fail`. A branch taken through a call from another function's example counts. One gap per function, naming each uncovered branch with its line and column in the body or let. Not reported for a function that misses an example `ready.function-example-missing` asks for or has an example that fails, nor while any function has a consistency finding. `system.generation.functionBranches: "gap"` lists it with severity info instead of as an error, while the examples are being completed. `exegra cover-functions` reports the coverage; see [Coverage](coverage.md). |

### Contract errors on the wire

A served contract answers each of its errors with an HTTP status and a body. The specification states both.

**Error kinds.** `system.generation.errorKinds` maps each kind of failure to its status: `{"unauthenticated": 401, "forbidden": 403, "not_found": 404, "conflict": 409, "invalid": 422}`. A status is an integer from 400 to 599.

**The status of an error.** An error condition states `status` (an integer from 400 to 599) or `kind` (a key of `errorKinds`), not both. An error that states neither takes the default: `system.generation.errorKind` (a kind) or `system.generation.errorStatus` (a status), at most one of the two. Nothing defaults to 422 unless the specification says so. A contract with `implementedBy` whose error has no status is the readiness gap `ready.error-status-missing`.

**The error body.** Without `system.generation.errorBody`, a generated route answers with the runtime's own failure body. With it, every failed call is answered with one struct type:

```jsonc
"errorBody": {
  "type": "api-error",            // a struct type
  "code": "code",                 // its field holding the kind: an enum whose values include every kind
  "message": "message",           // its string field holding a message safe to show
  "correlation": "correlation",   // optional: its string field the route fills with the caller's correlation id
  "runtime": {                    // the kind of each failure the serving runtime reports itself
    "unauthenticated": "unauthenticated", "forbidden": "forbidden", "invalid-request": "invalid",
    "timeout": "unavailable", "unavailable": "unavailable", "internal": "internal"
  }
}
```

Every other field of the type is optional, since a body made for a runtime failure, or for an error with no payload, leaves it out. An error whose payload is the body type is answered with that payload, its code set to the error's kind and its correlation to the caller's; any other error is answered with a body of its kind whose message is the error's name. With an error body every error of a served contract has a kind (`ready.error-kind-missing`), since the body says what kind of failure it is.

| Code | Rule |
|---|---|
| `contract.error-status` | An error's `status` is an integer from 400 to 599. |
| `contract.error-kind-unknown` | An error's `kind` is a key of `system.generation.errorKinds`. |
| `contract.error-status-kind` | An error states `status` or `kind`, not both. |
| `generation.error-kinds` | `errorKinds` maps each kind to an integer status from 400 to 599. |
| `generation.error-status` | `errorStatus` is a status from 400 to 599, `errorKind` is a declared kind, and not both are set. |
| `generation.error-body-kinds` | An `errorBody` comes with `errorKinds`. |
| `generation.error-body-type` | The body type is a struct, and every field other than its code, message and correlation is optional. |
| `generation.error-body-field` | `code`, `message` and `correlation` name required fields of the body type; the code field is an enum, the message and correlation fields are `string`. |
| `generation.error-body-code` | The values of the code field's enum include every error kind. |
| `generation.error-body-runtime` | `runtime` maps exactly the runtime failures `unauthenticated`, `forbidden`, `invalid-request`, `timeout`, `unavailable` and `internal`, each to a declared kind. |

### Contract exposure and auth

Who may call a contract, and from where, is data, so validation can check the security posture and a generator can build the authorizer from it instead of reading words (`src/core/access.js`).

**Exposure.** `exposure` is `public` (reachable from browsers and the internet, through the gateway), `internal` (the service network only) or `local` (an in-process call, never a route). `system.generation.gateway.prefix` (such as `/api`) is the path public routes are served under through the gateway; only a public contract may be bound under it, and a local contract states no HTTP binding at all.

**Auth.** `auth` is an object:

```jsonc
"auth": {
  "scheme": "session",        // how the caller proves who it is (below)
  "requires": ["content-publish"], // the capabilities a call needs, every one ([Capabilities, plans and roles](#capabilities-plans-and-roles))
  "roles": ["author"],        // any one of these roles admits the caller (session, delegation, in-process)
  "policies": ["p-save"],     // policies of this contract that must permit the call (session, delegation, in-process)
  "tenantPolicies": true,     // the tenant's own policies, data the running system holds, decide in the handler
  "csrf": true,               // a browser call carries the request token of its session or visit (session, anonymous)
  "origin": true,             // a browser call comes from an origin of the site it addresses (session, anonymous)
  "stepUp": "15 min",         // the caller proved who it is this recently (session, delegation)
  "description": "Any member who may write."
}
```

| Scheme | The caller presents |
|---|---|
| `anonymous` | nothing; `justification` says why that is allowed |
| `session` | a session established by signing in (a cookie, for a browser) |
| `service` | the credential of a platform component |
| `provisioning-token` | the provisioning token of one realm |
| `signature` | a request signed with the named `secret` |
| `signed-address` | an address signed with the named `secret` |
| `delegation` | a token an agent holds on behalf of a person |
| `in-process` | nothing: a local call inside the process |

A member on a scheme it does not apply to is refused. Nothing unstated is admitted: a generated authorizer refuses a contract whose auth it cannot read, and the scheme decides everything the route checks.

**Read-only, tenant scope, development.** `readOnly: true` marks a contract that changes no state. `tenantScope` says what tenant data it reads and returns: `request` (only the data of the tenant the request is made in, which a principal's own tenant must match), `none`, or `platform` (across tenants). `development` names the deployment condition (one of `system.generation.developmentConditions`, such as `STRATA_DEV`) without which a development or fixture contract does not exist.

**Prose.** Without `system.generation`, `auth` may still be a sentence and `exposure` may be left out. With it, both are required on every contract and a sentence is refused.

| Code | Rule |
|---|---|
| `contract.auth-structured` | With `system.generation`, every contract states `auth` as an object; always, an object auth has a known `scheme`, only members of that scheme, and well-formed values (roles and policies non-empty lists, `stepUp` a duration, a `secret` for `signature` and `signed-address`). |
| `contract.exposure` | With `system.generation`, every contract states `exposure`; the `in-process` scheme is exactly the scheme of local contracts. |
| `exposure.gateway` | A local contract has no HTTP binding, and an internal one is not bound under the gateway's prefix; the prefix is `/` and plain segments. |
| `auth.public-write` | A public contract that is not `readOnly` is called with a session (or, for a visitor, anonymously) with `csrf` and `origin` checked, or with a verified credential no browser attaches by itself: `signature`, `signed-address`, `provisioning-token` or `delegation`. |
| `auth.anonymous` | An anonymous public contract is `readOnly` or states a `justification`, and a quota limits it; an anonymous internal contract (a health check) is `readOnly` and justified. |
| `auth.service-public` | The `service` scheme is never on a public contract. |
| `auth.policy-unknown` | Every policy an auth names is a policy of this contract. |
| `auth.dev-only` | A development contract names a declared development condition, is never anonymous, and a public one names the roles that may use it. |
| `contract.tenant-scope` | With `system.generation`, a public contract states its `tenantScope`; a public contract is never `platform`. |

## Derived and facade contracts

A contract's implementation can be stated rather than written (WG-4935, NC-4 and NC-5 of WG-4895). A **derived** contract (`realisation: "derived"`) is built from [functions](#functions) and from other contracts, as `contract.derivation` says; a generator emits its implementation. A **facade** (`realisation: "facade"`) has no server implementation at all: a client lowers it onto a generic contract that is served. The checks are `src/core/derivation.js`.

**Kinds of derivation:**

```jsonc
"derivation": { "kind": "pure", "function": "visible" }
"derivation": { "kind": "read", "needs": "read-needs", "load": "load-records", "decide": "read-view" }
"derivation": { "kind": "read", "needs": "header-needs", "load": "load-records", "decide": "decide-read",
                "insufficient": "InsufficientState", "needRounds": 32 }
"derivation": { "kind": "read", "needs": "read-needs", "load": "load-records", "decide": "read-view", "header": true }
"derivation": { "kind": "command", "needs": "intent-needs", "load": "load-records", "decide": "decide-intent",
                "commit": "commit-changes", "conflict": "conflict", "insufficient": "InsufficientState",
                "needRounds": 32, "retries": 8 }
```

- **pure**: the implementation is the function. Its parameters are inputs of the contract, and what it gives is the contract's outputs.
- **read**: `needs` gives the list of needs (`list<N>`) from the inputs; the `load` contract loads them; `decide` gives the outputs from the inputs and the load contract's outputs. A read may also name `insufficient` and `needRounds`, both or neither: the need loop of a command without its commit, for a read whose needs are known only once something is loaded (Strata's `query` loads the schema before it knows which object type a named query reads). While `decide` fails with the variant `insufficient`, carrying one more need that is not already asked for, and fewer than `needRounds` extra needs were asked for, the need is added and loaded again; once the bound is spent it is the contract's error of the same name.
- **command**: the load-decide-commit loop of a store (Strata's `crates/storage-api/src/lib.rs`, `execute`). Load what `needs` gives and run `decide`. While `decide` fails with the variant `insufficient`, which carries one more need `N`, and that need is not already asked for and fewer than `needRounds` extra needs were asked for, add it and load again. Then call `commit` with what `decide` gave. While the commit fails with its error `conflict` and fewer than `retries` commits were retried, start over from the needs. Any other failure is the contract's error of the same name; so are `insufficient` and `conflict` once their bound is spent.
- **`header: true`** (WG-4968, a read or a command) is the header step of storage-api: `execute` and `query` first `load(tenant, [])`, which holds what every load holds (the schema, members, counters), compute the needs from it, and load them **together in one round**. With a header the `load` contract is first called with no needs, its outputs are parameters of `needs` as well as of `decide`, and the needs `needs` gives are loaded in one round that **does not count** against `needRounds`: only the extra needs `decide` asks for do. Without one, `needs` reads the inputs alone. A conflict retry starts again from the header.
- Every kind may name **`fault`**, an error of the contract without a payload, which an integer overflow or a division by zero in a function becomes (a generator refuses a function that can fault without it).

**Running a derivation.** `runDerivation` in `src/core/derivation.js` runs a read or command against a store the caller supplies (`load(needs)`, `commit(decided, loaded)`), calling the functions through the evaluator, and reports every list of needs it asked the store to load, the extra need rounds and the conflict retries, so the load count and the bounds can be checked on examples.

**Matching.** Values are matched by name and type: a function parameter is an input of the contract (for `decide`, also an output of the load contract) of the same name and type; an optional field of type `T` has the type `option<T>`. An input of the load contract is an input of the contract of the same name and type, or the needs (by type); an input of the commit contract is an input of the contract or an output of the load contract, or what `decide` gives (by type); an optional input that nothing fills is left out. What a pure function or a read's `decide` gives is the type of the contract's one output, or a struct whose fields are exactly the outputs. Each output of a command is an output of the commit contract, or a field of what `decide` gives, of the same name and type. Error variants of the functions and errors of the load and commit contracts are errors of the contract: a variant matches the error whose name has the same words (`VersionConflict` is `version-conflict`), a newtype variant of type `T` an error with payload `T`, a unit variant an error without one.

**Facades.** A facade states `bffRoute` `"<METHOD> <path> <shape> ..."`, a property the specification declares in its `vocabulary` (Strata's BFF route, `crates/spec-compiler/src/web_kernel.rs`). Exactly one *served* contract (not a facade, with `implementedBy`) states a `bffRoute` with the same method, path and shape: the generic contract the facade is lowered onto, such as `POST /api/records records` for every `records` facade. A facade names no `implementedBy`, so a generator gives it no trait method and no route.

**Consistency rules** always apply and are errors (each contract reports its first finding):

| Code | Rule |
|---|---|
| `derivation.kind` | A derived contract states a `derivation`, and only a derived contract does; its `kind` is `pure`, `read` or `command`; it has every field of its kind and no field of another (a read's `insufficient` and `needRounds` are its own, named together); function fields are function ids. |
| `derivation.signature` | The functions fit: parameters are inputs (or load outputs) of the same name and type; `needs` gives a list; what `function` or a read's `decide` gives is the outputs; every error variant is an error of the contract; `insufficient` (of a command, or a read with a need loop) is a variant of `decide`'s errors carrying one need; `fault` is an error of the contract without a payload. |
| `derivation.load` | The load contract is not a facade or the contract itself; every input it requires is filled; exactly one input takes the needs; no output is named like an input of the contract; every error it has is an error of the contract. |
| `derivation.commit` | The commit contract is not a facade or the contract itself; every input it requires is filled; exactly one input takes what `decide` gives; `conflict` is one of its errors; every error it has is an error of the contract; every output of the contract is a commit output or a field of what `decide` gives. |
| `derivation.bounds` | A command states `needRounds` and `retries`, and a read with a need loop `needRounds`, each a non-negative integer. |
| `contract.facade-route` | A facade names no `implementedBy`, and its `bffRoute` has a method, a path and a shape that exactly one served contract states. |

**Readiness** (errors when `system.generation` is set, listed by `readiness` otherwise):

| Code | Rule |
|---|---|
| `ready.derived-function-missing` | Every function a derivation names (`function`, `needs`, `decide`) is declared. A derivation may name functions before they are written; nothing else of it is checked until they are. |

### Capabilities, plans and roles

What a principal may do is data too: a *capability* is a named thing to do, and every other construct of access names capabilities, so validation can check that the model is closed and a generator can build one check from it (`src/core/capabilities.js`).

"capabilities": [
  { "id": "content-publish", "name": "Publish content", "core": true },  // core: every plan has it
  { "id": "content-schedule", "name": "Schedule publications" }          // only the plans that entitle it
],
"plans": [{ "id": "business", "name": "Business", "capabilities": ["content-schedule"] }],
"roles": [
  { "id": "visitor", "level": "platform", "holders": ["anonymous"], "capabilities": ["content-read"] },
  { "id": "owner", "level": "tenant", "holders": ["person", "team"], "capabilities": ["content-publish", "content-schedule", "support-read"] }
],
"grants": [{ "id": "support-grant", "issuer": "owner", "grantee": "support", "capabilities": ["support-read"], "perTenant": true, "maxDuration": "72 h" }],
"tokenScopes": [{ "id": "content-write", "name": "content:write", "capabilities": ["content-publish", "content-schedule"] }],
"delegations": [{ "id": "assistant", "from": "content-write", "to": "agent", "capabilities": ["content-schedule"], "maxDuration": "1 h" }],
"featureFlags": [{ "id": "scheduling", "gates": ["content-schedule"], "default": "off" }]
```

- A **contract** names the capabilities a call needs in `auth.requires` (on any scheme).
- A **plan** names the capabilities it entitles; a capability marked `core` is entitled on every plan.
- A **role** confers capabilities. A `platform` role is the platform's own (operators, services, the anonymous visitor): what the specification lists is what it confers. A `tenant` role is one a tenant starts with: the role is tenant data the tenant may change, and the list is where it starts. `holders` says who may hold it: `person`, `service`, `agent`, `team`, `anonymous`, `external` (a party that proves itself by signature or provisioning token).
- A **grant** confers capabilities that holders of the `issuer` role issue to holders of the `grantee` role, in one tenant when `perTenant`, for at most `maxDuration`.
- A **token scope** bounds what a call with a token carrying it may use; a **delegation** passes capabilities `from` a role, token scope, grant or other delegation `to` an agent, service or person.
- A **feature flag** gates capabilities per tenant: while it is off for a tenant (`default` when the tenant has no setting, off unless stated), nobody in the tenant may use them.

A call is admitted when all of these hold for every capability it requires: the tenant's plan entitles it (or it is core), no flag gating it is off for the tenant, the principal holds it (through its roles, its teams' roles or a live grant for this tenant), and, under a delegation, the delegation and the token's scopes pass it on and the delegator holds it.

|---|---|
| `capability.required` | With `system.generation`, every contract that is not local requires at least one capability (`auth.requires`). A `requires` that is not a non-empty list of names is `contract.auth-structured`. |
| `capability.unknown` | Every capability a contract requires, a plan entitles, a role or grant confers, a delegation or token scope passes on and a flag gates is a capability. |
| `capability.unreachable` | Every capability is conferred by some role or grant, and is core or entitled by some plan; otherwise nobody could ever use it. |
| `delegation.exceeds` | A delegation passes on only capabilities its `from` holds, and a grant confers only capabilities its issuer role holds. |
| `capability.duration` | A grant's or delegation's `maxDuration` is a positive duration. |

### Target contracts

A contract with `realisation: "target"` (WG-4968) is **specified but not yet implemented**: the contract, its types and its claims are the target, and nothing serves it. A generator emits its types and a trait method without an implementation, and **no route** for it, whatever its `bffRoute` or `binding` says; it is not counted as served. It may name `implementedBy`, the component that will implement it, and states a `ref` like any contract. It is held to no more than a generated contract (types that resolve), and less than a hole: no `H-` ref, no postcondition is demanded. Changing `realisation` to `generated` or `derived` is what implementing it means.

A target is not a served contract, so no derivation loads or commits through one (`derivation.load`, `derivation.commit`), no facade is lowered onto one (`contract.facade-route`: only served contracts count), and a target takes no `derivation` (`derivation.kind`).

### Supplied inputs

A served contract takes some inputs from the body and others from the request itself. `binding.suppliedBy` (WG-4968) is `{<input>: "route" | "session"}`, as in `"binding": {"suppliedBy": {"tenant": "route", "context": "session"}}`: the input comes from the request address (a path parameter, or the host a router resolved to a tenant) or from the signed-in session (the context), and **never from the body**. A generated route reads it from where it says, leaves it out of the body type, and refuses a body that carries it. Rules:

| Code | Rule |
|---|---|
| `contract.supplied-by` | `suppliedBy` is an object from names of declared inputs of the contract to `route` or `session`. |
| `form.supplied-input` | No field of a form fills an input its contract has supplied by the request, and no argument of the form (or of its `then` call) gives it. |
| `action.supplied-input` | No argument of an action (or of its `then` call) gives an input its contract has supplied by the request. |

A form or action does not need to fill a supplied input: `form.input-uncovered` and `action.argument-missing` leave it out.

## Cross-cutting constructs

Requirements repeat a few patterns: who may do what, what an input must meet, how long records are kept, how often a caller may act, how a call is retried, and what an act leaves in an audit log. Six entity kinds state them as structure, so they are checked and a generator can build code from them (`src/core/constructs.js`). Each kind has its own section and every one is optional; a specification that uses none is unchanged.

Several constructs name their target by one of a few reference properties, of which **exactly one** is set (`<kind>.target` otherwise). Durations are `"<decimal> <unit>"` with `ns`, `us`, `ms`, `s`, `min`, `h` or `d`, and positive (`"100 ms"`, `"400 d"`).

**Expressions** in a construct are the [expression language](#expression-language) of guards. Their references are checked against what is in scope (`<kind>.expr-reference`) and their types against the declared types (`<kind>.expr-type`), by the type classes of `src/core/codegen-model.js`: `bool`; number (the integer types, `f64`, `timestamp`, `duration`); string (`string`, `uuid`, an enum); `bytes`; `json`; struct; list; `option<T>` has the class of `T`, and an id or scalar type the class of its representation. A `json` value takes part only in `==` and `!=`, with another `json` value or `null`, and a path into it (`request.params.page`) is refused. A field whose type does not resolve (free text) has no known class and satisfies every rule. `!`, `&&`, `||` and `=>` take booleans; `-`, `*`, `/`, `%`, `<`, `<=`, `>`, `>=` take numbers; `+` takes two numbers or two strings; `==` and `!=` compare two values of one class or a value with `null`. An expression that does not parse is `<kind>.expr-syntax`. The principal is `principal.id`, `principal.tenant` and `principal.role`, all strings. An expression is checked only once its construct's target is known.

**policy** (`policies`): `{id, name?, description?, subject: {principal, role?}, contract | transition, resource?, condition?, effect: "allow"|"deny", source?}`. The subject is a principal kind (`member`, `operator`, `service`, ...) and, optionally, a role. The action is a contract call or a transition. The condition is a boolean over `request.<input>` (contract) or `event.<field>` (the transition's trigger event), `record.<field>` (with a `resource`) and the principal. A request is refused when a matching policy denies it; otherwise permitted when a matching policy allows it; otherwise the contract's new `policyDefault` (`deny` or `allow`) decides, and for a transition the default is deny.

**validation** (`validations`): `{id, description?, contract + input | record + field, rule, <parameters of the rule>, message, source?}`. `rule` is one of a fixed set, each with its parameters and nothing else: `required` (none), `maxLength` (`maxLength`, a positive integer, and `unit`: `characters` or `bytes`; on a string, bytes or a list), `pattern` (`pattern`, a regular expression the whole value matches; on a string), `range` (`min`, `max` or both; on a number), `oneOf` (`values`, non-empty, of the target's class), `custom` (`expr`, a boolean over `value`, the target, and `request.<input>` or `record.<field>`). `message` is what a refusal says.

**retention** (`retentions`): `{id, description?, record, keepFor | until, then: "delete"|"anonymise"|"archive", fields?, archiveTo?, source?}`. Keep each record for a duration from its creation, or until an event, then delete it, clear the listed `fields` (anonymise), or move it to the `archiveTo` component (archive). A record has at most one retention. It is the structured form of the record's prose `retention`, and it does not replace `erasure`, which says what a principal's deletion does; the record erasure rule (`record-erasure-point`) counts a retention that deletes the record or anonymises every personal field as the record's erasure point.

**quota** (`quotas`): `{id, description?, scope: "tenant"|"principal"|"source-address", contract | event, limit, window, onExceed: "refuse"|"queue"|"throttle", error?, heldBy?, source?}`. At most `limit` calls of the contract, or occurrences of the event, per scope in each `window`. A quota that refuses calls of a contract names the contract error the refusal is in `error`; `heldBy` is the component that keeps the counters.

**retry** (`retries`): `{id, description?, contract | event, attempts, backoff: {kind: "fixed"|"exponential", base, cap?}, idempotencyKey?, timeout?, source?}`. At most `attempts` attempts, the first included; the wait before the second attempt is `base`, and each later wait is the same (fixed) or doubles up to `cap` (exponential). `idempotencyKey` is the input of the contract, or payload field of the event, that identifies a repeat; `timeout` bounds one attempt.

**audit** (`audits`): `{id, description?, contract | transition | event, record, capture: [{field, from}], immutability: "append-only"|"chained-hash", chainField?, source?}`. Whenever the contract is called, the transition fires or the event occurs, a record of kind `record` is written: each captured `field` gets the value of `from`, an expression over `request.<input>` and `response.<output>` (contract) or `event.<field>` (transition or event), the principal and `time` (a number), of the field's class. Entries are never changed or removed; with `chained-hash` each holds the hash of the entry before it in `chainField`, a bytes or string field of the record that is not captured.

**Requirements realised by constructs.** A claim of kind `requirement` may list the constructs that realise it in `realisedBy`. A `construction` requirement is satisfied by a claim whose `models` names it **or** by at least one construct in `realisedBy`; otherwise `requirement.construction-unmodelled`.

**Consistency rules** always apply and are errors:

| Code | Rule |
|---|---|
| `policy.target`, `quota.target`, `retry.target`, `audit.target`, `validation.target` | Exactly one target property is set; a contract validation takes `input`, a record validation `field`. |
| `policy.expr-syntax`, `policy.expr-reference`, `policy.expr-type` | The condition parses, reads only what is in scope, and is a boolean of well-typed parts. |
| `validation.target-unknown` | The input or field is named and is declared by the contract or record. |
| `validation.param` | The rule's parameters are present and valid (a positive integer `maxLength`, a `pattern`, `min` or `max`, non-empty `values`, an `expr`), and no parameter of another rule is set. |
| `validation.target-type` | The rule fits the target's class (length, pattern, range), and every `oneOf` value is of that class. |
| `validation.pattern` | `pattern` is a regular expression. |
| `validation.range` | `min` is not greater than `max`. |
| `validation.expr-syntax`, `validation.expr-reference`, `validation.expr-type` | A custom rule's expression parses, is in scope and is a well-typed boolean. |
| `retention.period` | Exactly one of `keepFor` and `until`. |
| `retention.duration` | `keepFor` is a duration. |
| `retention.fields` | An anonymising retention lists `fields`; no other retention does. |
| `retention.field-unknown` | Every anonymised field is a field of the record. |
| `retention.duplicate` | A record has at most one retention. |
| `retention.archive-target` | Only an archiving retention names `archiveTo`. |
| `quota.limit`, `quota.window` | `limit` is a positive integer, `window` a duration. |
| `quota.error-missing`, `quota.error-unknown`, `quota.error-misplaced` | A quota refusing calls of a contract names one of the contract's errors; no other quota names an error. |
| `retry.attempts` | `attempts` is a positive integer. |
| `retry.duration` | `backoff.base`, `backoff.cap` and `timeout` are durations. |
| `retry.backoff` | Only an exponential backoff has a `cap`, and it is at least the `base`. |
| `retry.idempotency-key-unknown` | The idempotency key is an input of the contract or a payload field of the event. |
| `audit.capture` | `capture` is not empty and captures no field twice. |
| `audit.field-unknown` | Every captured field is a field of the record. |
| `audit.expr-syntax`, `audit.expr-reference`, `audit.expr-type` | Every `from` parses, is in scope, and is of its field's class (or `null` for an optional field). |
| `audit.chain-field` | A `chained-hash` audit names a `chainField`: a bytes or string field of the record, not captured; no other audit names one. |
| `claim.realised-by-not-requirement` | Only a requirement has `realisedBy`. |

**Readiness rules** (switch-gated like the others in `READINESS_RULES`: errors when `system.generation` is set, listed by the `readiness` command otherwise):

| Code | Rule |
|---|---|
| `ready.policy-default-missing` | A contract that policies govern states `policyDefault`. |
| `ready.policy-transition-model-level` | A policy's transition belongs to an implementation-level behavior, the only kind generated. |
| `ready.validation-unit-missing` | A `maxLength` validation states its `unit`. |
| `ready.retention-missing` | Every record with a personal or credential field has a retention. |
| `ready.retention-archive-target-missing` | An archiving retention names `archiveTo`. |
| `ready.quota-held-by-missing` | Every quota names `heldBy`. |
| `ready.retry-idempotency-missing` | A retry of an event, or of a contract that is not `idempotent`, names an `idempotencyKey`. |
| `ready.retry-timeout-missing` | Every retry states `timeout`. |
| `ready.audit-field-unfilled` | An audit fills every required field of its record: by a capture, or as the record's key (assigned by the store) or the chain field. |

### Pooled quotas

A `quota` limits one tenant (or principal, or source address). A **quota pool** (`quotaPools`, WG-5278) shares limits across a group of tenants, such as the clients of one reseller, and its meaning runs in Exegra's model, so claims about it are decided by simulation and exhaustive exploration instead of a hand-written trace.

```jsonc
"quotas": [ { "id": "q-automation-runs", "scope": "tenant", "event": "automation-run", "limit": 10, "window": "1 d", "onExceed": "throttle", "heldBy": "limit-store" } ],
"quotaPools": [
  { "id": "reseller-pool", "name": "Reseller pool", "groupedBy": "reseller", "heldBy": "limit-store", "window": "1 d", "windowEnd": "day-closed",
    "limits": [
      { "name": "runs", "kind": "rate", "quota": "q-automation-runs" },
      { "name": "storage", "kind": "level", "perMember": 10, "unit": "GB", "usage": "storage-changed" }
    ],
    "overShare": { "consecutive": 3 },
    "throttle": { "to": "fair-share", "release": 2 },
    "exemption": { "name": "burst eligibility", "setBy": "reseller-admin", "capability": "burst-eligibility-grant",
                   "event": "burst-eligibility-set", "effective": "same-window", "retroactive": false } }
],
"scenarios": [ { "id": "burst-exploration", "behaviors": [], "pools": ["reseller-pool"], "steps": [ ... ], "faults": [ ... ] } ]
```

| Property | Meaning |
|---|---|
| `memberClass`, `groupedBy` | Which tenants may be members (a tenant class; omitted, any) and what makes one pool of them (text: the reseller whose clients they are). |
| `heldBy` | The component that keeps the counters, the limit store. A pooled quota's own `heldBy` must be the same (`pool.held-by`). |
| `window`, `windowEnd` | The window usage is counted in (a duration), and the event that closes it (a day boundary). |
| `limits[]` | Each pooled limit: a `name` (a lower-case word), `kind` (`rate`: counted per window and reset at its end; `level`: a standing amount that usage raises or lowers), what each member contributes (`quota`, a per-tenant quota whose limit is the contribution, or `perMember`), `unit`, and `usage`, the event that uses it (payload `member` and `amount`; defaults to the event the quota counts). |
| `overShare.consecutive` | N: a member whose usage is over its fair share at the end of N consecutive windows is throttled, headroom or not, unless exempt. |
| `throttle` | `to`: `fair-share` (a throttled member may use up to its share) or `refuse` (it may only lower a level); `release`: the throttle lifts after that many consecutive windows ending at or under the share, or `"never"`. Required, so a specification cannot leave the release unsaid. |
| `exemption` | Set for a member by holders of `setBy` (with `capability`, which that role must confer) through `event` (payload `member`); `effective` `same-window` applies it from the window it is set in, that window's end included, `next-window` from the next; `retroactive: true` lifts a throttle in force, and by default it never applies to windows already throttled. |
| `modelMembers` | How many members the model runs, 1 to 4 (default 2); usage payloads name them `m1`, `m2`, ... |

**Meaning.** A member's fair share is its contribution, and the pool's capacity is the sum of the contributions. Composing with quotas this way means a per-tenant quota keeps saying what one tenant is entitled to, and the pool says that the entitlements are shared. A scenario lists the pools it runs in `pools` (a scenario may run pools and no behavior). Each pool runs as one machine per pooled limit and modelled member, `<pool>-<limit>-m<k>`, with subject `heldBy`, states `normal` and `throttled`, and variables `usage`, `day` (the window index), `overDays`, `underDays`, `throttledOn` (the window the throttle in force began, -1 none), `burstSetOn` and `burstFrom` (the window the exemption was set in and the first it applies to, -1 none), `admitted` and `refused`. `poolMachines` in `src/core/pools.js` derives them; `simulationInput` adds them after the scenario's behaviors, so the engines, the trace check and `exegra prove` run them unchanged.

- **Usage** of member `m<k>`: admitted in `normal` when it lowers the amount or the pool's total use plus it is within capacity (headroom); in `throttled`, only within the fair share and the capacity (`fair-share`) or only when it lowers the amount (`refuse`). Otherwise refused, changing only `refused`.
- **Window end**: the window ended over the share when `usage` exceeds it. In `normal`, a member whose over count reaches N is throttled, unless `burstFrom` is set and not after this window; in `throttled`, the throttle lifts when the under count reaches the release. A rate's usage resets and the window index advances.
- **Exemption set** for `m<k>`, the first time only: `burstSetOn` is this window and `burstFrom` this window or the next; retroactive, it also lifts the throttle in force.

Claims read the machines like any other: "a burst-eligible client is never throttled for a day on or after the day its eligibility was set" is the state invariant `reseller-pool-runs-m1.throttledOn < 0 || reseller-pool-runs-m1.burstSetOn < 0 || reseller-pool-runs-m1.throttledOn < reseller-pool-runs-m1.burstSetOn`. With the usage and eligibility events of a scenario as `inject-event` faults, exploration covers every combination of them; the claim holds with `effective: same-window`, and with `next-window` the explorer returns the run where eligibility is set on the day the third over-share day ends. Validation checks that a claim reads only variables the machines have, from pools every listed scenario runs (`expr.reference`).

| Code | Checks |
|---|---|
| `pool.limits` | At least one pooled limit; each has a lower-case name, and no two share one. |
| `pool.limit-contribution` | Exactly one of `quota` and `perMember`; `perMember` is positive. |
| `pool.quota-scope`, `pool.quota-window`, `pool.limit-kind` | A pooled quota is counted per tenant, over the pool's window, and is a rate. |
| `pool.held-by` | A pooled quota's counters are held by the pool's component. |
| `pool.usage-event`, `pool.event-payload` | Each limit has a usage event with payload fields `member` and `amount`; the exemption event has `member`. |
| `pool.window`, `pool.over-share`, `pool.release` | The window is a duration; the over-share count is a positive integer; the release is a positive integer or `never`. |
| `pool.model-members` | 1 to 4 modelled members. |
| `pool.exemption-capability` | The role that sets the exemption confers the capability it needs. |
| `pool.machine-id` | No entity has the id of a machine the pool runs as. |
| `scenario.empty` | A scenario runs at least one behavior or pool. |

The machines are not entities: renaming a pool or a limit does not rewrite claim expressions that name its machines (validation then reports them as `expr.reference`), and the inspector and simulator panel show only declared behaviors. `tests/fixtures/pooled-quotas/harbourline.jsonc` is Harbourline BR-12; `tests/core/pooled-quotas.test.js` explores it, seeds wrong rules, and breaks each validation rule once.

## User interface

A specification can state its pages and its user journeys precisely enough for a generator to build the frontend kernel (state, messages, effects, routes and transitions, wired to the backend's contracts) and end-to-end browser tests from them (`src/core/ui.js`). Six entity kinds, each in its own section and all optional. The kernel stays an Elm-style pure function, `update(state, message) -> {state, effects}`; drawing stays in hand-written renderers that a screen names. Field checks are the [validation constructs](#cross-cutting-constructs) on the inputs a form fills, and who may act is the policies on the contract an action calls: neither is restated here.

**screen** (`screens`): `{id, name, route, query?, viewModel?, kind?, title?, auth?, local?, description?}`. `route` is a path pattern: `"/"`, or one or more `/segment` where a segment is a literal (letters, digits, `.`, `_`, `~`, `-`) or `:param`; no parameter twice, no trailing `/`. A **catch-all** route, `"*"` or `"*name"`, answers every path no other screen answers (the not-found page); `name` is a route parameter holding the path that was opened. At most one screen is the catch-all; it has no address of its own, so nothing navigates to it and a journey reaches it with `gotoPath`. `local: [{name, type}]` declares **screen-local values**: state the screen holds besides its view model, empty until an action places a call's output there (`action.result`); expressions on the screen read them as `local.<name>`, and the renderer draws them. `query` lists optional query-string parameters (`q` of `/search?q=kiln`). Route and query parameters are strings. `viewModel` is the contract whose outputs are the screen's data; the kernel calls it with the route and query parameters as inputs of the same names. `kind` names the hand-written renderer that draws it. `auth` is `none`, `session` (any signed-in principal) or `role:<role>`.

**form** (`forms`): `{id, screen, contract, fields: [{name, input, label?, control, options?, optionsFrom?, derive?, until?, transform?, initial?, normalize?}], arguments?, then?, submitLabel, onSuccess, onError}`. Submitting calls `contract`; each field fills one of its inputs with a control (`text`, `textarea`, `password`, `checkbox`, `select`, `radio`, `date`, `number`) whose value class fits the input (a checkbox a boolean, a number control a number, a date a string or a number, the others a string). `label` and `submitLabel` are accessible names. A `select` or a `radio` (a group of radio buttons, such as colour swatches) lists `options: [{value, label}]` or takes them from the view model with `optionsFrom: {path, value?, label?}`: `path` is a path into the screen's view model (as `forEach`) that reaches a list; for a list of a declared struct, `value` and `label` name the fields that give each option's value (of the control's class) and label (a string); for a list of strings each item is its own value and label, and `value` and `label` are left out. **Derived fields:** `derive` is an expression over the other fields (`form.<field>`, each of its input's class) and the screen's scope that fills the field whenever what it reads changes; `until: "edited"` stops deriving once the person has edited the field (left out: always derived); `transform: "slug"` turns the derived string into an address segment (Unicode NFKD, combining marks removed, lower case, every run of characters other than `a-z0-9` replaced by `-`, `-` trimmed at both ends, cut to 80 characters, a trailing `-` trimmed again). A slug derived from the title until the slug is edited is `{name: "slug", derive: "form.title", transform: "slug", until: "edited"}`. `arguments` fills the inputs no field does: input -> expression (below). `onSuccess: {navigate?: {screen, params?, path?}, toast?, view?}` and `onError: {show: "inline"|"toast", prefix?, announce?}`; inline shows field errors on their fields. **Initial values:** `initial` fills a field when the form opens, from the view model. `{path}` reaches a value of the control's class (a number is shown in a text control), or a list of texts that `join` (the separator) puts together for a text control. `{path, where: {field, equals}, value}` reaches a list of structs and takes `value`, a field of the item, from the first item whose `field` equals the expression `equals` (over the screen's scope, such as `route.slug`); nothing found leaves the control's own initial value. An always-derived field has no initial value. **Normalization:** `normalize: "trim"` removes white space at both ends of the value of a text, textarea or password control before it is sent and before the outcome reads it. **A second call:** `then: {contract, arguments?}` calls a second contract when the first succeeds, before `onSuccess`; its arguments are expressions over `response.<output>` of the first call, `form.<field>` and the screen's scope, and the outcome reads the outputs of both calls (the second's where both have one). **View-model overlay:** `onSuccess.view` maps outputs of the view model of the screen the success opens (`navigate.screen`, else this screen) to expressions over the outcome's scope; those values hold until that view model is read again, such as the version a save moved the record to. While the form has unsaved changes, a view model read again keeps the values of these outputs it had, so a save still names the version the editing started from and a change made elsewhere meanwhile is refused as a conflict. **Refusal wording:** `onError.prefix` is text put before the message of a refusal shown as a toast, and `onError.announce` is what is announced when a refusal is only about fields. The wording of refusals as a whole is the `errorMessage` entity, below.

**action** (`actions`): `{id, screen, label, contract, form?, forEach?, arguments?, confirm?, confirmAnnounce?, alsoOn?, optimistic?, onSuccess?, onError?}`. `confirmAnnounce` is what is announced when the first press asks for the confirmation. **Also offered elsewhere:** `alsoOn: {auth}` offers the action on every other screen whose authentication is `auth` (a screen that states none counts as `none`), such as a sign-out in a page's header. Such an action reads only `principal` and `response.<output>` of its call, so it is not per-row, does not keep a result and reads no form. `onSuccess.view` and `onError.prefix` and `announce` are as on a form. A button whose accessible name is `label`; pressing it calls `contract` with `arguments` (input -> expression). `confirm` asks for a second press with that text first; its button's accessible name is that text. `optimistic` shows the success before the reply and undoes it on a refusal. **Results kept on the screen:** `result: {into, output}` places the call's `output` in the screen-local value `into` of the action's screen (of the same type) and the page stays where it is: an action with a `result` does not navigate. The editor's Preview tab, which calls the Markdown preview and shows its blocks, is such an action. **Reading a form:** `form` names a form of the same screen; the action's `arguments` and navigation expressions may then also read `form.<field>`, the values being edited, typed as in the form (the editor's Preview sends the body being edited). Without `form`, `form.<field>` on an action is not in scope. **Per-row actions:** `forEach` is a path into the view model (an output, then struct fields) that reaches a `list<S>` of a declared struct `S`; the action is repeated once per row, `item.<field>` is that row in its expressions, and `${item.<field>}` in `label` and `confirm` is filled in with the row's value, so each row's button has its own accessible name (`"Unpublish ${item.title}"`). **Visibility:** an action is shown only when the policies on its contract may permit the current principal: the kernel evaluates the policy decision of the contract (a matching deny refuses, else a matching allow permits, else `policyDefault`) with `request.<input>` bound to the action's arguments and `principal` to the signed-in principal; a condition that reads `record.<field>` cannot be decided on the page and counts as matching, so the action is shown and the server's decision is final, arriving through `onError`.

**Request encoding** (`encode` on a contract input, `inputs[].encode`) says how a page's request turns the value it holds into what the endpoint takes, in this order: `trim: true` removes white space at both ends; `split: "<separator>"` turns the text into the list of its trimmed, non-empty parts; `as: "number"` turns the text into a number (not together with `split`); `empty: "null"` sends an empty value (an empty text, an empty list or `false`) as `null`, and `empty: "omit"` leaves it out of the request, which only an optional input allows. `trim`, `split` and `as` read a text input. An `encode` with no key, or a key that is not one of these, is refused.

**errorMessage** (`errorMessages`): `{id, on: "check"|"error", kinds?, text, fallback?, field?, appliesTo?, description?}` words a refusal. `on: "check"` words a failed check of the reply, by its rule kind (`kinds`, such as `required` or `constraint`); `on: "error"` words an error code of the reply when no failed check explains it, and `kinds` lists the codes, each an error one of the contracts the forms or actions it applies to call (of any contract, when `appliesTo` is left out) lists in `errors`. `text` is filled in with `${check.detail}` (the detail as sent) and `${check.statement}` (the detail without the bracketed reference at its end) on a check, and with `${error.message}` on an error; `fallback` is the text used when the filled-in text is empty. `field`, on a check only, shows the message on the form field the check names (`name`: the `object.field` the check names) or on the field whose name starts the check's name (`prefix`: `title` for `title_length`); left out, the message is shown on the form as a whole. `appliesTo` lists the forms and actions it words; left out, all of them. A message with no `kinds` words every other check or error of its `on`. For a form or action and a kind, the message that applies is the first of: one that applies to it and lists the kind, one that applies to it without kinds, one for all that lists the kind, and the default. A specification that has a form or an action needs a default refusal message, `{on: "error", text: "${error.message}", fallback: ...}` with neither `kinds` nor `appliesTo` (`ready.error-message-default-missing`). Two messages that word the same kinds for the same forms and actions are refused.

**Expressions** in `arguments` and `navigate.params` use the [expression language](#expression-language), typed like the constructs' expressions: they read `route.<param>` (route and query parameters, strings), `query.<param>` (the screen's query parameters alone), `view.<output>` (outputs of the screen's view-model contract), `local.<name>` (screen-local values), `item.<field>` (the row of a per-row action) and `principal.id|tenant|role`; the outcome of a call (`navigate.params`, `navigate.path`, the toast) may also read `response.<output>` of the call and, on a form, `form.<field>` (the submitted value of a field, of its input's class). An argument is of its input's class (or `null` for an optional input); a route parameter is a string or a number. A navigation gives every route parameter of its target screen and nothing else but its query parameters. `navigate.path` is an expression of a string: the address opened when it is a same-site absolute path (it starts with `/` and not `//`), the screen being the fallback; signing in and following `?next=` is `{path: "query.next", screen: "screen-desk"}`.

**Toasts** fill placeholders: `${<scope>.<name>}` for every scope the outcome may read, and for `response` and `view` also `${<scope>.<output>.<field>...}` through struct fields (as a view-model path). Each placeholder reaches a value that can be shown as text: not a list, a struct or bytes. `"Signed in as ${response.name}."`

**liveBinding** (`liveBindings`): `{id, screen, event, refresh, when?}`. While the screen is open, each occurrence of `event` (published by the backend) refreshes its view model: `whole`, or a path into it: an output of the view-model contract, then fields of its struct types (through `list<T>` and `option<T>`). `when` refreshes only when a condition holds: an expression of a boolean over `event.<payload field>` and the screen's scope; `{value, in}`, where `in` is a view-model path that reaches a list and `value` an expression of the class of its items, holding when the value is one of them; or `{any: [condition]}` / `{all: [condition]}`, some or every one of a non-empty list. A notice that concerns an object the open view depends on is `when: {value: "event.object", in: "view.depends-on"}` (where the view-model contract has an output `view` whose struct has a field `depends-on`); the expression language has no membership operator, so membership is this form.

**uiScenario** (`uiScenarios`): `{id, name, verifies?: [requirement], browsers?: [name], viewport?: {width, height}, steps}`. A user journey a generator turns into a browser test. `browsers` names separate sessions (a separate cookie jar each); the journey starts in the first. Each step is an object with exactly one key:

An **element** is `{role, name | namePattern, level?, within?}`: a WAI-ARIA role, the accessible name exactly or as a regular expression, a heading `level` (1 to 6, headings only), and `within`, the element it is inside (an element whose name may be left out). Elements are addressed this way only; the format has no CSS selector anywhere, and a step with any other key is refused.

Steps that act:

| Step | Value |
|---|---|
| `goto` | `{screen, params?, host?}`: open the screen's route with these parameter values (every route parameter, optionally query parameters), on `host` (a tenant's host name and port) when given. |
| `gotoPath` | `{path, host?}`: open a raw path, such as an address no screen answers. |
| `reload`, `back` | `{}` (or `true`) |
| `click`, `focus` | an element |
| `clickAction` | `{action, item?, confirm?}`: press an action's button; for a per-row action `item` gives the row fields its label (and with `confirm: true` its confirmation) reads, which resolves the button's name. `confirm: true` also presses the confirmation. |
| `fill` | `{form, field, value}`, or an element (role `textbox`, `searchbox`, `combobox` or `spinbutton`) and `value` |
| `submit` | `{form}`: press the form's submit button. |
| `press` | a key, such as `Enter` or `Control+End` |
| `switchBrowser` | one of `browsers` |
| `goOffline`, `goOnline` | `{}` (or `true`) |
| `setViewport` | `{width, height}` |
| `emulate` | `{colorScheme?: light, dark or no-preference, reducedMotion?: reduce or no-preference, touch?, mobile?}`, at least one |
| `setCookie` | `{name, value, host, attributes?}`: put a cookie into the current browser, such as a session replayed against another host. |
| `apiCall` | `{method, path, host?, headers?, body?, as? or anonymous?, expectStatus?, expectJson?, expectBodyIncludes?, expectBodyExcludes?, capture?}`: a request outside the page, with the current browser's cookies, another browser's (`as`), or none (`anonymous: true`). `expectJson` maps a path in the JSON reply (`failed.0.rule`) to its value; `capture` maps a value name to such a path. |

Steps that expect (each takes an optional `timeoutMs`, a positive integer, where it waits):

| Step | Value |
|---|---|
| `expectText`, `expectNoText` | `{text or pattern, within?}`: the text is (is not) on the page. |
| `expectTitle` | `{text or pattern}`: the document title. |
| `expectScreen` | a screen id, or `{screen, params?}`: the address is that screen's route (with those parameters). |
| `expectRole` | an element and `state?`: `visible` (default), `hidden`, `enabled`, `disabled`, `focused`, `checked` or `unchecked`. |
| `expectCount` | an element (its name may be left out) and `count`: how many match. |
| `expectAttribute` | an element (or none: the document element), `attribute` and `value` or `pattern`. On an element: `aria-*`, `data-*`, `value` (a control's current value), `href`, `lang`, `dir`; on the document element: `data-*` (such as `data-accent`, `data-scheme`), `lang`, `dir`. |
| `expectStatus` | the HTTP status of the last navigation, 100 to 599 |
| `waitFor` | `{event}`: until the page has received the event. |
| `expectNoEvent` | `{event, forMs}`: the page receives no such event for that long. |
| `axeScan` | `{}`: an automated accessibility scan finds no violation. |
| `logScan` | `{forbid: [regular expression]}`: no service log line matches any. |
| `expectLog` | `{service, event, fields?, timeoutMs?}`: a line of the service's log for the logged event appears (the step waits for it, since logs are written asynchronously), holding each member of `fields` with that value; see [Telemetry](#telemetry). |
| `expectNoOverflow` | `{}`: the page does not scroll sideways. |
| `expectBeside` | `{a, b, side}` (two elements; side `left`, `right`, `above`, `below`): a lies wholly on that side of b. |
| `expectCookie` | `{name, absent?, attributes?: {secure?, httpOnly?, sameSite?: Strict, Lax or None, path?, hostPrefix?}}` in the current browser |

Steps that remember:

| Step | Value |
|---|---|
| `mark` | a name: the generator sets a marker of that name on the page's `window`. |
| `expectNoReload` | a marker name: the marker set by an earlier `mark` in this browser is still there, so the document was not loaded again. |
| `recordRequests` | a name: from here on, the current browser's requests and WebSocket connections are recorded in a log of that name. |
| `expectRequests` | `{log, to, only?, atLeast?, fromWorker?}`: `to` is a regular expression over the URL; `only`: every recorded request matches it; `atLeast`: at least so many do; `fromWorker`: every matching one was made by a worker, not the page's main thread. |
| `expectNoRequest` | `{log, path}`: no recorded request URL matches the pattern. |
| `capture` | `{name, from: "cookie", cookie}`, `{name, from: "header", header}`, `{name, from: "text", element}` or `{name, from: "attribute", element, attribute}`: remember a cookie's value, a header of the last response, or an element's text or attribute. |

A value captured by `capture` or by `apiCall.capture` is used in any string of a later step as `${name}` (in a value, a header, a path, a pattern, `logScan.forbid`, a cookie value); in a pattern it stands for its literal text. Captured values are shared by the journey's browsers; markers and request logs belong to the browser that set them.

**Client-side machines.** An implementation-level behavior whose subject is a component of category `client` (the page kernel's own machine) is held to exactly the machine rules of any implementation-level behavior ([Types, contract details and generation readiness](#types-contract-details-and-generation-readiness)); nothing exempts or rejects it.

**Timer delays read at run time.** A timer effect of an implementation-level machine may read its delay at run time: `after: {expr, simulate}`. `expr` is an expression of a number over the machine's variables, `time` and the triggering event's payload (a heartbeat interval the server announced and a transition stored in `heartbeatMs` is `{expr: "heartbeatMs", simulate: 10000}`); generated code evaluates it when the timer is set. A simulated run has no such value, so `simulate` (a number, a duration or a distribution, as any `after`) is the delay the simulator and every simulation-based check use. `refines` compares a timer's events and payloads with the model's; a delay is compared only when the model transition states a number, and then against the simulated delay. A model-level machine states its delays outright. Errors: `effect.after` (shape, model level, missing `simulate`, not a number), `expr.syntax` and `expr.reference` (as every machine expression); `ready.event-field-undeclared` covers the payload fields `expr` reads.

**Consistency rules** always apply and are errors. References to screens, contracts, events and claims in properties (`screen.viewModel`, `form.screen`, `form.contract`, `action.screen`, `action.contract`, `onSuccess.navigate.screen`, `liveBinding.screen`, `liveBinding.event`, `uiScenario.verifies`) are checked by the parser as every reference is (`ref.unresolved`, `ref.kind`).

| Code | Rule |
|---|---|
| `screen.route` | The route is a well-formed path pattern; query parameters are names, none repeating a parameter. |
| `screen.route-duplicate` | No two screens answer the same route (parameter names aside). |
| `route.ambiguous` | No two screens have routes that tie: both non-catch-all, the same number of segments, agreeing at every position (equal literals, or a parameter on either side), and the same number of literal segments. Routes of one shape are `screen.route-duplicate` instead. |
| `screen.catch-all-duplicate` | At most one screen is the catch-all. |
| `screen.local` | Screen-local values have names, none twice, and types that are built in or declared. |
| `screen.auth` | `auth` is `none`, `session` or `role:<role>`. |
| `screen.kind` | The renderer name is not empty. |
| `screen.view-model-input` | Every required input of the view-model contract is a route or query parameter. |
| `form.field-unknown` | Every field fills an input of the form's contract. |
| `form.field-duplicate` | No two fields share a name or fill one input; no input is filled by a field and an argument. |
| `form.input-uncovered` | Every required input of the contract is filled by a field or an argument. |
| `form.options` | A select or radio lists options or takes them from the view model, exactly one of the two; no other control has either. |
| `form.options-from` | `optionsFrom.path` reaches a list in the screen's view model; over structs, `value` and `label` are fields of it, of the control's class and a string; over scalars, items fit the control and `value` and `label` are left out. |
| `form.derive` | `until` is `edited` and `transform` is `slug` (on a string field), each only on a derived field; derived fields do not derive from one another in a cycle. |
| `form.control-type` | The control fits the class of its input. |
| `form.label-empty`, `action.label-empty` | Accessible names (field and option labels, submit labels, action labels) are not empty. |
| `form.argument-unknown`, `action.argument-unknown` | Every argument names an input of the contract. |
| `action.argument-missing` | Every required input of the action's contract has an argument. |
| `action.for-each` | `forEach` is a path into the screen's view model that reaches a list of a declared struct. |
| `action.label-template` | The label and confirmation use only `${item.<field>}`, with fields of the rows, and only on a per-row action. |
| `form.navigate-params`, `action.navigate-params` | A navigation gives exactly the target's route parameters (query parameters optional), and does not target the catch-all screen. |
| `form.toast-template`, `action.toast-template` | Every toast placeholder reads a name in scope that can be shown as text. |
| `action.form` | `form` is a form of the action's screen. |
| `action.result` | `result` is `{into, output}`: a screen-local value of the action's screen and an output of its contract of the same type; the action does not also navigate. |
| `form.expr-syntax`, `form.expr-reference`, `form.expr-type`, `action.expr-syntax`, `action.expr-reference`, `action.expr-type` | Arguments, navigation parameters and addresses, and derivations parse, read only what is in scope, and are of the right class. |
| `liveBinding.duplicate` | One event refreshes a screen through at most one binding. |
| `liveBinding.refresh` | `refresh` is `whole` or a path into the screen's view model. |
| `liveBinding.when` | A condition is an expression, `{value, in}` with `in` a view-model path reaching a list, or a non-empty `any` / `all`. |
| `liveBinding.expr-syntax`, `liveBinding.expr-reference`, `liveBinding.expr-type` | Conditions parse, read only the event's payload and the screen's scope, are booleans, and a membership value is of the class of the list's items. |
| `uiScenario.browsers` | Browser names are non-empty and distinct. |
| `uiScenario.viewport` | Viewports (the journey's and `setViewport`'s) have positive integer width and height. |
| `uiScenario.verifies-not-requirement` | A journey verifies requirements only. |
| `uiScenario.step` | A step has exactly one key of the table above, and its value has the shape given, with nothing else. |
| `uiScenario.step-reference` | Steps name existing screens, forms, fields of those forms, actions, events, and browsers of the journey (`switchBrowser`, `apiCall.as`). |
| `uiScenario.goto-params` | `goto` gives every route parameter of the screen, string or number values, nothing else but query parameters, and does not go to the catch-all screen. |
| `uiScenario.role` | A role is a WAI-ARIA role. |
| `uiScenario.name-empty` | An accessible name is not empty. |
| `uiScenario.status` | `expectStatus` (also an API call's) is an integer from 100 to 599. |
| `uiScenario.pattern` | Every pattern (`namePattern`, `pattern`, `to`, `path`, `logScan.forbid`) is a regular expression. |
| `uiScenario.level` | A heading level is on a heading and 1 to 6. |
| `uiScenario.attribute` | An expected or captured attribute is one the step may read (above). |
| `uiScenario.timeout` | `timeoutMs` and `forMs` are positive integers. |
| `uiScenario.host` | A host is a host name with an optional port. |
| `uiScenario.path` | A path (`gotoPath`, `apiCall`, a cookie's) is absolute, without spaces or a fragment. |
| `uiScenario.json-path` | A path into a JSON reply is names and indexes joined by `.`. |
| `uiScenario.capture-undefined` | Every `${name}` was captured by an earlier step. |
| `uiScenario.capture-duplicate` | A value name is captured once. |
| `uiScenario.mark-undefined` | `expectNoReload` names a marker set earlier in the same browser. |
| `uiScenario.log-undefined` | `expectRequests` and `expectNoRequest` name a log started earlier in the same browser. |
| `uiScenario.action-item` | `clickAction` gives a per-row action the row fields its label (and confirmation) read, gives no row to any other action, and confirms only an action with a confirmation. |
| `contract.encode` | `encode` has only `trim`, `split`, `as` and `empty`, and says something; `trim`, `split` and `as` read a text input, `split` is a non-empty separator and is not combined with `as`, and `empty` is given only for an optional input. |
| `form.initial` | `initial` is `{path}` (or `{path, join}`) and its path reaches a value of a class the control edits (a number for a text control); `join` applies only to a list of texts in a text control; an always-derived field has no initial value. |
| `form.initial-where` | With `where`, the path reaches a list of structs; `where` is `{field, equals}` with `field` a field of the item and `equals` of its class; `value` is a field of the item that the control edits; `join` does not apply. |
| `form.normalize` | `normalize` is on a text, textarea or password control only. |
| `form.then` | `then` is `{contract, arguments?}`, and nothing else; its arguments are checked as the form's arguments, over the outcome's scope. |
| `form.view-overlay`, `action.view-overlay` | `onSuccess.view` is output -> expression, each output of the view model of the screen the success opens, each expression of that output's class; that screen names a view-model contract. |
| `form.on-error`, `action.on-error` | `onError.prefix` and `onError.announce`, when given, are not empty. |
| `action.confirm-announce` | `confirmAnnounce` is given with `confirm`, and is not empty. |
| `action.also-on` | `alsoOn` is `{auth}` with an authentication of `none`, `session` or `role:<role>`; the action has no `forEach`, `form` or `result`; its arguments, navigation and toast read nothing of one screen (`route`, `query`, `view`, `local`, `item`, `form`). |
| `errorMessage.kinds` | `kinds`, when given, is a non-empty list of distinct names; on an error message, each kind is an error that a contract its forms and actions call (or any contract, when `appliesTo` is left out) lists in `errors`. |
| `errorMessage.field` | `field` is given only on a message on a check. |
| `errorMessage.template` | `text` and `fallback`, when given, are not empty and use only the placeholders of their message: `${check.detail}` and `${check.statement}` on a check, `${error.message}` on an error. |
| `errorMessage.applies-to` | `appliesTo`, when given, is a non-empty list naming each form or action once. |
| `errorMessage.duplicate` | No two messages word the same thing for the same forms and actions: the same `on`, overlapping `kinds` (or both without `kinds`), and overlapping `appliesTo` (or both without it). |
| `uiScenario.log-event` | `expectLog` names an event that is logged, by the service it names. |
| `uiScenario.log-field` | The members `expectLog` expects are the line's `tenant` (when the event logs one) and the names its allowlisted fields are written as. |

**Readiness rules** (switch-gated, in `READINESS_RULES`):

| Code | Rule |
|---|---|
| `ready.screen-view-model-missing` | Every screen names its view-model contract. |
| `ready.screen-kind-missing` | Every screen names its renderer. |
| `ready.form-field-label-missing` | Every form field has a label. |
| `ready.action-on-success-missing`, `ready.action-on-error-missing` | Every action says what happens on success and where a refusal is shown. |
| `ready.error-message-default-missing` | When there is a form or an action, some `errorMessage` has `on: "error"` with neither `kinds` nor `appliesTo`: the default wording of every refusal. |

The third set of constructs (catch-all, options from the view model, derived fields, screen-local results, filtered refreshes, templated toasts, run-time timer delays) adds no readiness rule: each is complete once it is consistent, and a generator needs nothing more from it. The fourth set (request encoding, initial values, a second call, view-model overlays, refusal wording) adds one, `ready.error-message-default-missing`, the rule that a specification with forms or actions states a default refusal message.

A contract a form or action uses that some policy names must state `policyDefault`: that is `ready.policy-default-missing`, the construct rule, which already covers every contract policies govern, so it is not reported twice.

## Telemetry

Generated code writes a structured log line for each domain event it logs, and end-to-end journeys read those
lines (`expectLog`). Module `src/core/telemetry.js` (`checkTelemetryConsistency`, `telemetryReadiness`, which is
in `READINESS_RULES`); `expectLog` is checked with the other journey steps in `src/core/ui-steps.js`.

**Services and the line format.** `system.telemetry: {format?: "json-lines", services: [{id, component?, log}]}`.
A service is a process that writes a log: `id` is the name written on every line, `component` the component it
runs, `log` the path of its log file relative to the deployment's working directory (such as
`var/logs/backend.jsonl`), which tests read. Every line is one JSON object with, in order, `ts` (milliseconds
since the Unix epoch), `level` (`debug`, `info`, `warn`, `error`), `service`, `event` (the log name),
`correlation` (when known: the id that follows one request through every service) and `tenant` (when the event
names one), then the event's allowlisted fields. These six names are reserved.

**Sensitive data.** A type declares `sensitive: "secret" | "password" | "token" | "personal"`, and so does a
struct field or an event payload field. A type is sensitive when it is marked, when a field of a struct is
(transitively), and `list<T>` / `option<T>` of a sensitive `T`. Sensitive data is never logged.

**Logging per event.** An event states `logging`:

```jsonc
{"id": "record-updated", "domain": true, "payload": [...],
 "logging": {"logged": true, "service": "backend", "level": "info", "name": "record.updated",
             "tenant": "tenant", "fields": [{"field": "object"}, {"field": "record", "as": "id"}]}}
{"id": "page-pinged", "logging": {"logged": false, "reason": "A heartbeat; it says nothing about the domain."}}
```

Logging is an allowlist: the line holds the tenant field (written as `tenant`) and the listed payload fields
(each written under `as`, by default its own name), never the rest of the payload. `name` is the line's `event`
member and defaults to the event id. `event.domain: true` marks a fact the running system records (a domain
event); any event may state its logging, a domain event must (readiness). A logged domain event is emitted by
the running system even when no modelled behavior emits it, so it is not reported as `gap.unused-event`. A generator writes one typed logging
function per logged event, taking exactly the correlation, the tenant and the allowlisted fields, and calls it
where the event is emitted.

| Code | Rule |
|---|---|
| `telemetry.service` | A service id is lower-case letters, digits and `-`, declared once; its `log` is a relative path without `..`. |
| `event.logging-shape` | `logging` is `{logged: true, service, level, name?, tenant?, fields}` or `{logged: false, reason}`, nothing else; a logged field is `{field, as?}`. |
| `event.logging-service` | A logged event names a service of `system.telemetry`. |
| `event.logging-name` | The log name is dotted lower-case words (`record.updated`), and one service logs one event under a name. |
| `event.logging-field-unknown` | Every logged field, and the tenant field, is a payload field of the event. |
| `event.logging-field-sensitive` | No logged field (nor the tenant field) is marked sensitive or of a sensitive type. |
| `event.logging-field-type` | A logged field is a scalar: a boolean, a number, a string (ids, enums and uuids included), or an option of one. |
| `event.logging-field-reserved` | A field is written under a lower-case name that is not one of the six every line holds, not twice, and the tenant field is not logged again. |
| `ready.event-logging-missing` | With `system.generation`, every event with `domain: true` states its logging. |

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

Guards, effect values and claim invariants use a small language in `src/core/expr.js`. No host-language code is evaluated anywhere, and specifications cannot contain executable JavaScript. A language that the users of the specified system write is a different construct, described as data ([Languages](#languages)), and so is the body language of [functions](#functions).

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

A behavior's effect is `{ "set": "<variable>", "to": <literal or expression string> }` or `{ "emit": "<event>", "after": <ticks>, "payload": { ... } }`. String values in `to` and `payload` are expressions; other JSON values are literals. Transitions are tried in declaration order. See [simulation.md](simulation.md). What every machine construct means, which Lean definition is normative for it, and the declarative implementation-level properties (`realisation`, `storage.durability`, `level`, `repr`, `storedIn`, `storage`, `delivery`, `elapsed`, `to`, `transaction`, `otherwise`, `ignores`) with their readiness rules are in [semantics.md](semantics.md).

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

`hash.js` (through the Lean kernel, `formal/Exegra/Hash.lean`, with theorems that declaration order, key order and presentation do not change the hash) normalizes the model (entities sorted by id, object keys sorted, locations and layout excluded; array order kept because it can be meaningful) and hashes it with cyrb53, rendered as 14 hex digits. It identifies revisions and detects change. It is not cryptographic. Two texts differing only in comments, whitespace, key order or top-level declaration order have the same hash.

Not implemented: schema migration. The `exegra` version is checked, but no `exegra migrate` command exists although the error message mentions one. This is recorded in the self-specification (component `parser`).

## Contract events

An event may be a request, a response or an error of a contract at a boundary, so that a simulated trace is checked, and reads, like a request log.

| Property | On | Meaning |
|---|---|---|
| `contract` | event | The id of a contract. An unknown id is a reference error. |
| `role` | event | `request`, `response` or `error`; required when `contract` is set, and not allowed without it. |
| `correlation` | event | The name of a payload field that pairs a response or error with its request (the request must carry a field of that name). |
| `binding` | contract | `{protocol?, method?, path?, operation?, case?}`; the first four only label a request in the request log, `case` is the contract's wire case ([Wire naming and json](#wire-naming-and-json)). |
| `optional` | contract input or output | `true` when a request may leave the input out. |

Field and type strings (`string`, `number`, `boolean`, `null`, literals such as `'a' | 'b'` or `true`, unions with `|`, arrays such as `string[]`) are read by `src/core/type-expr.js`; any other type text (`Operation[]`, `{text, hash}`) is opaque and accepts every value.

`validate` reports, with the position of the event: a missing role (`event.role-missing`), a role or correlation without a contract, a request payload field that is not an input (`event.contract-field`), an input that is not optional and missing (`event.contract-missing`), a field type that is not assignable to the contract's (`event.contract-type`), a response field that is not an output (an output typed `{ok: true, hash}` contributes the keys `ok` and `hash`), an error without a `code` field or whose literal codes are not among the contract's errors (`event.error-code`; an error named `a / b` declares both), and a correlation field that is not a payload field (`event.correlation`). The trace check and the request log are described in [simulation.md](simulation.md#contract-events-in-a-trace).
