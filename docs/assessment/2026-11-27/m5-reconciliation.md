# M5 reconciliation: extracted facts against declared facts (WG-5696)

What the static extractor reads from the code, how it compares with what the specification declared, and what changed in the specification because of it. Static extraction establishes static structure only: nothing here says how the code behaves when it runs.

Files this document rests on:

- the extractor: `tools/extract.js` (identity `exegra-static-extractor`, version 1), its surface `tools/surface.js`, the fact file `specs/exegra/extracted/facts.json`;
- the core's reading of it: `src/core/extraction.js`;
- the independent recomputation: `docs/assessment/2026-11-27/scripts/m5-audit-recompute.mjs` (shares no code with Exegra: own regular expressions, `jsonc-parser` on the specification text, `fs`);
- the comparison script: `docs/assessment/2026-11-27/scripts/m5-reconcile-compare.mjs` (Exegra's side of the same comparison).

## 1. The audit's discrepancy set, reproduced

The audit (multiscale.md, section 5.4) reported, from the import graph of the files that components claim (`src/`, `cli/` and `tools/`; 237 module entries; 349 import edges by regular expression) against the declared relationships of any kind, compared pair for pair:

| figure | audit |
|---|---|
| component pairs that import with no declared relationship | 9 |
| of the pairs that import, one with only the reverse declared (`generation-readiness -> validator`) | 1 |
| declared pairs with no import in that direction | 140 (70 involving an external or file component) |

The independent recomputation, run on the tree of the commit that records the audit (`ada1363`, `--root` that tree):

| figure | recomputed at `ada1363` |
|---|---|
| import edges | 345 |
| undeclared pairs | 10, of which 1 has only the reverse declared (so 9 plus 1) |
| declared pairs with no import | 140, of which 70 involve an external or unimplemented component |

That reproduces the audit's three figures exactly (the audit's 349 edges are 345 here: the audit counted edges, this counts those between claimed files; the pair figures are the audit's).

## 2. The same recomputation on the current tree, and Exegra's extraction on the same input

The current tree is `ms-stack` plus M5's new files; the specification is the one before M5 changed it (`git show HEAD:specs/exegra/spec.jsonc`), so the comparison is of the audit's method on today's code and yesterday's declarations.

| figure | `ada1363` (audit tree) | current tree, declarations before M5 |
|---|---|---|
| import pairs | 192 | 209 |
| declared pairs | 322 | 346 |
| undeclared pairs | 10 (9 plus 1 reversed) | 12 (11 plus 1 reversed) |
| declared pairs with no import | 140 | 149 (76 involving an external or unimplemented component) |

Exegra's extraction, lifted the way the audit lifted (JavaScript files of `src/`, `cli/`, `tools/`, owning component of each file, ordered pairs, declared pairs of any kind), on the same two inputs gives the same sets: 209 import pairs, 346 declared pairs, 12 undeclared, 1 reversed, 149 declared without import. The three lists (undeclared pairs, reversed pair, declared-without-import pairs) are equal as sets, element for element (checked by diffing the JSON the two scripts print).

### Differences from the audit, each named

Undeclared pairs, 10 to 12:

- `spec-guard -> workspace-service` (`tools/spec-guard.js` imports `tools/spec-manifest.js`): the spec guard component arrived with the front door (commit `587233c`, "Add a PreToolUse guard that keeps agents out of spec files"; component specified in `e551b38`).
- `verification-pipeline -> queries` (`tools/traceability.js` imports `moduleDeclarations` from `src/core/query.js`): M1's module elements (commit `3306fdc`, "Make elements recursive").

Declared pairs with no import, 140 to 149 (+12, -3):

- added by `3306fdc` (M1): `composition-root -> browser-platform`, `composition-root -> browser-storage`, `composition-root -> transactions`, `scene-renderer -> composition-root`, `visual-interaction -> scene-renderer`, `browser-user -> shell`, `shell -> browser-user`, `agent-cli -> nodejs-runtime`, `lean-call-boundary -> javascript-runtime`. The composition root became its own element, so the relationships `visual-interaction` held to the browser platform, the browser storage and the transactions moved to it: that is also the three pairs that left the list (`visual-interaction -> browser-platform`, `-> browser-storage`, `-> transactions`). These are runtime wiring and callbacks, which an import graph cannot see;
- added by `e551b38` (front door): `spec-guard -> filesystem`, `ai-coding-agent -> spec-guard`;
- added by `1c0b944` (WG-5684, claim verdicts): `lean-call-boundary -> claim-verdict`.

Declared pairs rose from 322 to 346 by those same commits. The drift the audit named, in both directions, is real and is exactly what the assumption `relationships-match-imports` could not follow.

## 3. After M5

Inside the extraction surface a static dependency is derived from the code. The declared ones were retired (section 4), so the audit's comparison of declarations against imports now has a different shape:

| figure | before M5 | after M5 |
|---|---|---|
| declared static dependencies (class static) between components of the surface | 33 | 0 |
| extracted relationships between module elements | | 502 (from 711 import facts in 233 files) |
| undeclared import pairs, by the audit's method | 12 | 37 |
| declared pairs with no import | 149 | 143 (76 involving an external or unimplemented component) |

The 37 are the 12 of section 2 plus 25 pairs that M5 removed from the declarations because the extracted facts carry them (22 formerly declared as `imports` or `depends-on` and 3 new: the imports of `src/core/extraction.js` by `claim-strength`, `transactions` and `verification-pipeline`, written by this change). They are no longer discrepancies, since the extracted fact is the dependency; an extracted dependency with no declared counterpart gives no diagnostic. The 143 remaining declared pairs without an import are declared runtime wiring, relationships to external components and planned components, and data and subscription relationships, none of which static extraction can see. They are not flagged.

Reconciliation on the current tree (`node cli/exegra.js reconcile --project exegra`): no warnings; one information note that extraction found 155 imports of 44 specifiers outside the surface (packages, builtins, the standard library) for which no element stands. The evaluated claim `extraction-reconciles-with-declarations` is verified.

## 4. Retired relationships and their coverage

Every retired relationship was checked, before it was removed, for an extracted relationship from a module of its source component (or a descendant) to a module of its target (or a descendant). All 29 are covered; none is reported lost. The operations are `m5-ops/03-retire-declared-imports.json` (the 22 relationships of kind `imports`) and `m5-ops/04-retire-declared-static-in-surface.json` (7 `depends-on` relationships that the Lean and JavaScript facts also carry, and the reclassification below).

| retired relationship | kind | from -> to | covering extracted facts | sources |
|---|---|---|---|---|
| validator-calls-queries | imports | validator -> queries | 3 extracted relationship(s), e.g. `extracted:imports:src/core/validate.js=>src/core/interactions.js` | 3 file edge(s) |
| explorer-calls-projection-system | imports | explorer -> projection-system | 1 extracted relationship(s), e.g. `extracted:imports:src/ui/explorer.js=>src/core/projections.js` | 1 file edge(s) |
| dialogs-calls-transactions | imports | dialogs -> transactions | 1 extracted relationship(s), e.g. `extracted:imports:src/ui/dialogs.js=>src/core/operations.js` | 1 file edge(s) |
| toolbar-calls-dom-helpers | imports | toolbar -> dom-helpers | 1 extracted relationship(s), e.g. `extracted:imports:src/ui/toolbar.js=>src/ui/dom.js` | 1 file edge(s) |
| shell-calls-dom-helpers | imports | shell -> dom-helpers | 1 extracted relationship(s), e.g. `extracted:imports:src/ui/shell.js=>src/ui/dom.js` | 1 file edge(s) |
| explorer-calls-dom-helpers | imports | explorer -> dom-helpers | 1 extracted relationship(s), e.g. `extracted:imports:src/ui/explorer.js=>src/ui/dom.js` | 1 file edge(s) |
| activity-panels-calls-dom-helpers | imports | activity-panels -> dom-helpers | 1 extracted relationship(s), e.g. `extracted:imports:src/ui/activity.js=>src/ui/dom.js` | 1 file edge(s) |
| overlay-calls-dom-helpers | imports | overlay -> dom-helpers | 1 extracted relationship(s), e.g. `extracted:imports:src/ui/overlay.js=>src/ui/dom.js` | 1 file edge(s) |
| inspector-calls-dom-helpers | imports | inspector -> dom-helpers | 1 extracted relationship(s), e.g. `extracted:imports:src/ui/inspector.js=>src/ui/dom.js` | 1 file edge(s) |
| property-controls-calls-dom-helpers | imports | property-controls -> dom-helpers | 1 extracted relationship(s), e.g. `extracted:imports:src/ui/property-controls.js=>src/ui/dom.js` | 1 file edge(s) |
| dialogs-calls-dom-helpers | imports | dialogs -> dom-helpers | 1 extracted relationship(s), e.g. `extracted:imports:src/ui/dialogs.js=>src/ui/dom.js` | 1 file edge(s) |
| source-editor-calls-dom-helpers | imports | source-editor -> dom-helpers | 1 extracted relationship(s), e.g. `extracted:imports:src/ui/source-editor.js=>src/ui/dom.js` | 1 file edge(s) |
| simulator-panel-calls-dom-helpers | imports | simulator-panel -> dom-helpers | 2 extracted relationship(s), e.g. `extracted:imports:src/ui/sim-panel.js=>src/ui/dom.js` | 2 file edge(s) |
| verification-panel-calls-dom-helpers | imports | verification-panel -> dom-helpers | 1 extracted relationship(s), e.g. `extracted:imports:src/ui/verification-panel.js=>src/ui/dom.js` | 1 file edge(s) |
| realisation-panel-calls-dom-helpers | imports | realisation-panel -> dom-helpers | 1 extracted relationship(s), e.g. `extracted:imports:src/ui/realisation-panel.js=>src/ui/dom.js` | 1 file edge(s) |
| responsive-layout-calls-dom-helpers | imports | responsive-layout -> dom-helpers | 1 extracted relationship(s), e.g. `extracted:imports:src/ui/layout.js=>src/ui/dom.js` | 1 file edge(s) |
| shell-calls-claim-method-registry | imports | shell -> claim-method-registry | 1 extracted relationship(s), e.g. `extracted:imports:src/ui/shell.js=>src/core/claim-methods.js` | 1 file edge(s) |
| register-importer-calls-markdown-importer | imports | register-importer -> markdown-importer | 1 extracted relationship(s), e.g. `extracted:imports:tools/import-register.js=>tools/import-markdown.js` | 1 file edge(s) |
| reader-surface-calls-dom-helpers | imports | reader-surface -> dom-helpers | 1 extracted relationship(s), e.g. `extracted:imports:src/ui/reader.js=>src/ui/dom.js` | 1 file edge(s) |
| reader-pages-calls-queries | imports | reader-pages -> queries | 1 extracted relationship(s), e.g. `extracted:imports:src/core/reader.js=>src/core/own.js` | 1 file edge(s) |
| agent-cli-calls-claim-method-registry | imports | agent-cli -> claim-method-registry | 2 extracted relationship(s), e.g. `extracted:imports:cli/admit.js=>src/core/claim-methods.js` | 2 file edge(s) |
| change-impact-calls-stable-serialization | imports | change-impact -> stable-serialization | 1 extracted relationship(s), e.g. `extracted:imports:src/core/impact.js=>src/core/stable-json.js` | 1 file edge(s) |
| lts-foundation-depends-on-exhaustive-explorer | depends-on | lts-foundation -> exhaustive-explorer | 1 extracted relationship(s), e.g. `extracted:imports:formal/Exegra/Core/=>formal/Exegra/Search.lean` | 1 file edge(s) |
| claim-evaluator-depends-on-fault-model | depends-on | claim-evaluator -> fault-model | 1 extracted relationship(s), e.g. `extracted:imports:src/core/claims.js=>src/core/fault-model.js` | 1 file edge(s) |
| proof-export-depends-on-formal-semantics | depends-on | proof-export -> formal-semantics | 1 extracted relationship(s), e.g. `extracted:imports:formal/Exegra/Prove.lean=>formal/Exegra/Json.lean` | 1 file edge(s) |
| proof-export-depends-on-exhaustive-explorer | depends-on | proof-export -> exhaustive-explorer | 1 extracted relationship(s), e.g. `extracted:imports:formal/Exegra/Prove.lean=>formal/Exegra/Explore.lean` | 1 file edge(s) |
| exhaustive-explorer-depends-on-formal-semantics | depends-on | exhaustive-explorer -> formal-semantics | 1 extracted relationship(s), e.g. `extracted:imports:formal/Exegra/Explore.lean=>formal/Exegra/Semantics.lean` | 1 file edge(s) |
| resource-model-depends-on-formal-semantics | depends-on | resource-model -> formal-semantics | 1 extracted relationship(s), e.g. `extracted:imports:formal/Exegra/Format2.lean=>formal/Exegra/Semantics.lean` | 1 file edge(s) |
| integrity-rules-depends-on-formal-semantics | depends-on | integrity-rules -> formal-semantics | 1 extracted relationship(s), e.g. `extracted:imports:formal/Exegra/Integrity.lean=>formal/Exegra/Json.lean` | 1 file edge(s) |

Declared static dependencies inside the surface that extraction did not find (unwitnessed), reclassified instead of removed, because each states a real relationship that is not an import (operations file 04):

| relationship | was | now | why |
|---|---|---|---|
| shell-depends-on-stylesheets | depends-on | reads | `index.html` loads the stylesheet; no JavaScript import |
| exhaustive-explorer-depends-on-fault-model | depends-on | reads | the explorer reads the scenario's fault model at run time |
| simulation-engine-depends-on-formal-semantics | depends-on | exercises | the engine is checked against the formal semantics |
| workload-model-depends-on-formal-semantics | depends-on | reads | the workload is defined in Lean first (planned) |

Module ownership repairs (operations files 01 and 02), made because the extracted imports showed the old claims were not a function from files to elements once `formal/` and `engine/` joined the surface:

- every Lean and Rust source belongs to exactly one module element (`traceability` reports no multiple owners and no unclaimed file); the directory claims `formal/`, `formal/Exegra/Api/` and `engine/` were replaced by the files no other element claims;
- a new component `formal-root` owns `formal/Exegra.lean`, `formal/Main.lean` and `formal/Exegra/Api.lean`: files that import every other Lean module and that nothing imports, which as parts of `formal-semantics` and `lean-call-boundary` made cycles that did not exist;
- `engine/exegra-engine/src/{v2,random,workload}.rs` moved from `resource-model` and `workload-model` to `rust-engine-oracle`, which owns the crate they import (as part of semantic-core they made a static dependency of the semantic core on tooling, and `core-independent-of-ui` was violated by it). `resource-model` is now `lean` rather than `mixed`.

## 5. What extraction found that the declarations never showed

Two structural claims are violated by facts, not by a change of the claims:

- `core-dependencies-acyclic` and `core-static-dependencies-acyclic`: the static dependencies among the components of the semantic core form cycles. The strongly connected sets of the static graph (extracted plus declared static):
  - `formal-semantics`, `resource-model`, `workload-model` (`Impl/Semantics.lean` imports `Format2.lean`, which imports `Semantics.lean` and `Workload.lean`);
  - `verdict-boundary`, `metric-claims`, `integrity-rules`, `validator`, `generation-readiness`, `simulation-contract`, `fault-model`, `exhaustive-explorer`, `proof-export`, `lean-call-boundary`, `parser` (for example `validate.js` imports `access.js` and `readiness.js` of `generation-readiness`, whose `readiness.js` imports `readiness-machines.js` of `validator`; `sim-input.js` and `fault-model.js` import each other; `Api/Engine.lean` imports `Prove.lean` and `Temporal.lean`);
  - `property-controls` and `dialogs` in the interface (known as an unknown on both components since before).
  They were `verified` over the declared relationships. They stay violated, with their counterexample recorded, and `npm run verify` lists them in `--expect-violated` with the reason in `docs/verification.md`, until ownership or imports change. Nothing weakens them.

`core-independent-of-ui` is verified over 314 declared and 502 extracted relationships, and says so in its scope.

## 6. The assumption became a check

`relationships-match-imports` (cited by 14 claims, not 11: three more were added since the audit) is removed. In its place:

- the evaluated claim `extraction-reconciles-with-declarations` (method `extraction-reconciled`, decided by the model and the facts: no declared static dependency inside the surface is redundant, unwitnessed, reversed or of another kind than extraction finds, and every extracted file belongs to a module element); its scope says static imports only;
- the assumption `static-extractor-sound` (trusted: the extractor reports exactly the static imports of the files it reads; tested against a corpus in `tests/core/extract.test.js`, not provable in Lean);
- the assumption `extracted-facts-current` (checked by `verify` through the import scan, `tools/import-scan.js`: the digest of every file of the surface against the fact file; and the file-system imports no extracted element stands for, as WG-5684 did: `src/core/derivation-cache.js` importing `node:fs` still has no declared relationship to `filesystem`, so the claims that rest on it are undecided when `verify` records that, as before).

The 14 claims cite both assumptions (`m5-ops/05-assumption-becomes-check.json`). WG-5684's claim `import-scan-checks-relationships` is kept, rewritten to state what the scan checks now.

## 7. Provenance surfaces

- Derived interactions carry `summary.provenance`, the mix of their witnesses (declared, extracted, observed). In the regenerated goldens (`tests/fixtures/abstraction/`) the module-level and component-level interactions show `extracted` counts.
- Every structural claim result has `basis`: counts by provenance of the relationships the claim reads, and `declared-only`, `extracted`, `observed` or `extracted+observed`. When extracted or observed relationships are read, the scope text ends with: "The relationships it reads are N declared, M extracted. Extracted relationships are static imports only: they say which files name which, never that the code runs that way."
- Claim strength reports the same in `details.basis` and `details.witnesses`, and its grounding text.

## 8. Observed facts

`node tools/observe.js <recording.json> --id <id> --out <file>` turns a recorded session (the traffic recorder's `{seq, id, payload}` stream) into observed facts that name the recording (id, source, digest, event count). `node cli/exegra.js reconcile --observed <file>` reports observed interactions with no declared relationship and declared runtime interactions the recording does not show as "not observed". The committed fixture `tests/fixtures/recordings/live-session.json` (5 events) gives two observed interactions (`persistence-client -> session` by `project-files-read`, `session -> persistence-client` by `read-intent`), and 37 declared runtime interactions not observed in it. No live recording is kept in the repository; the fixture stands for one.

## 9. Propagation and I4

`tests/core/extraction-propagation.test.js` runs a fixture repository (`tests/fixtures/extraction/`): adding an import between modules of two subsystems adds one extracted relationship, one witness at the module, component and subsystem cuts (internal to the one block at the system cut), flips `a-not-b-subsystems` and `a-not-b-components` to violated with the extracted witness as the counterexample, and `rederive` through the footprints equals `deriveModel` from scratch at every cut; retargeting moves the interaction between blocks; removing restores every cut to its first derivation. `tests/core/extract.test.js` checks that touching one file changes only that file's facts and that the committed fact file describes the tree.

