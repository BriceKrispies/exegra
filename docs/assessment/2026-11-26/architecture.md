# Architecture and computational scalability: assessment

Team: software architecture and computational scalability. I read the source only: Lean is not installed and `src/engine/lean/` is not built, so nothing that loads the Lean core was run. File and line references are to the repository at HEAD (02d8f00).

## 1. Verdict

- The Lean core is real, but narrow. It is the authority for exactly three things: structural model derivation (16 diagnostic codes), the semantic hash, and the operational semantics of the *engine input*.
- Everything between the spec and those three, and everything after them, is defined only in JavaScript. That covers lowering the spec to engine input, about 75+ well-formedness error rules, all structural, trace, evidence and metric claim verdicts, integrity-rule meaning, admission and transactions.
- The JS layer is about 20k lines of verdict-relevant code, against 624 lines of Lean shell.
- There is no dependency graph from guarantees to the artifacts they rest on. Recorded results (tests and Lean theorem checks) are keyed only by id or name.
- The Lean kernel, the JSON boundary, the number handling and the store can be kept and evolved. The *verdict layer* (claims, validation, lowering, admission, evidence records) has to be rebuilt as Lean definitions with a provenance and dependency model. Porting the current JS files one by one, as WG-4785 plans, will not by itself give change impact.

## 2. Fundamental limitations

### 2.1 Spec-to-semantics lowering is defined only in JS (BLOCKS-OBJECTIVE, ARGUED)
- The Lean theorems are about `runAnyValue` on an *engine input* (`formal/Exegra/Api.lean:83-90`, `Properties.lean`).
- The map from a specification to that input is written only in JS:
  - `src/core/sim-input.js` (`simulationInput` :124, `simulationInputV2` :394, `evalTypeOf` :38, which decides integer typing, timestamp→i64 and duration→u64);
  - `src/core/pools.js` (`poolMachines` :118 synthesizes whole state machines for quota pools);
  - `src/core/distributions.js` (BigInt quantile tables, lowering of distributions);
  - `src/core/fault-model.js` (`retryDelay` :146).
- So "the semantics of a spec" is Lean ∘ (1044 lines of JS). Pools and the int/option typing of variables have no Lean definition at all.
- The spec itself says so: claim `core-logic-in-lean` names "engine-input derivation WG-4800" (`spec.jsonc:17665`).
- Counterexample: in the spec, a quota-pool machine's variables and transitions come from `poolMachines`. No Lean theorem mentions pools, so a safety claim over a pool machine is a theorem about JS output.

### 2.2 Well-formedness is mostly JS-only (BLOCKS-OBJECTIVE, DEMONSTRATED)
- `Model.lean` emits 16 codes: `id.*`, `property.*`, `ref.*`, `schema.*`, `spec.*`, `entity.type`.
- `validate.js` alone emits at least 75 distinct error codes through `report('error', …)` (127 call sites). It also delegates to `function.js`, `language.js`, `type-shapes.js`, `layers.js`, `ui.js`, `data-model.js`, `integrity.js` and others: about 9.5k lines for product, language and type checks.
- Examples with no Lean counterpart: `component.parent-cycle` (`validate.js:73`) and `expr.reference` (`validate.js:110-135`). `grep` finds neither in `formal/`.
- These errors decide whether a transaction is accepted (`project.js:184`, `errorCount`), so they are on the verdict path.
- `language-eval.js:1-5` says outright: "Not mirrored in Lean". It follows a third, external kernel (`crates/kernel/src/expr.rs`).

### 2.3 Claim verdicts are JS-only (BLOCKS-OBJECTIVE, DEMONSTRATED)
- `src/core/claims.js` decides every status except `proved`:
  - structural (`acyclic` :852, `reachable` :713, `onlyVia` :733, `noRelationship` :674);
  - single-trace (`traceInvariant` :1228, `tracePrecedes` :1353, `traceNever` :1402, `traceEventually` :1414);
  - evidence (`evaluateEvidenceClaim` :515), metric, refinement and data-model checks.
- `claims.js` consumes a Lean trace, but evaluates the claim over it with the JS `expr.js` evaluator (`evalBool` :1191).
- `Temporal.lean` redefines the same forms over all runs. It is a *second* definition, and its vacuity policy differs.
- Counterexample (ARGUED from source): take `eventually {occurs: {event: E}}` where E is delivered only by the scenario script.
  - JS returns `inconclusive` (`claims.js:1420-1426`, which filters `source.kind !== 'scenario'`).
  - Lean `Matcher.hit` (`Temporal.lean:~52`) counts any delivery, so `tcheck` gives `holds`.
  - The same claim gets two meanings depending on which tool evaluates it.

### 2.4 Integrity-rule meaning is defined by the JS parser and the JS fact export (LIMITS, ARGUED)
- At edit and admission time, `integrity.js` evaluates the rules (`evaluateIntegrity` :723, `newErrorViolations`). Its Lean twin (`Integrity.lean`) runs only offline (`tools/prove-integrity.js`, the native `exegra-lean integrity`). It is not registered at the wasm boundary: `Api.lean:22` has only `Engine.entries ++ ModelPort.entries`.
- The Lean proof `holds_of_eval` is about the facts that `integrity-export.js:70-84` chose (a JS closure over the properties it reads) and about a formula produced by JS `parseRule`.
- No theorem links the exported facts to the model. A rule "proved" in Lean therefore rests on the JS parser and exporter.

### 2.5 No guarantee→artifact dependency graph, and stale results stay valid (BLOCKS-OBJECTIVE, DEMONSTRATED)
- Test results: `results.json` maps evidence id → `{outcome, ranAt, obtained}`. It has no tree stamp, no `ref`, no spec hash and no file digests.
- `collectEvidence` (`claims.js:483-497`) reads `recorded.results[e.id]` without comparing `e.data.ref`.
- Counterexample: `admit --ops '[{"type":"SetProperty","id":"ev-X","path":["ref"],"value":"tests/core/unrelated.test.js"}]'`.
  - Both the before and after snapshots use the same `data.recorded` (`commands.js:1010, 1025`).
  - The claim stays `supported` with "Exegra holds a recorded result of executing ev-X: pass".
  - `guaranteeChanges` (`admit.js:318`) looks only at claim `statement`/`evaluate`, rules, retentions and copies, never at evidence. So no reason is raised, and the change is **admitted**.
- In the repo today, `results.json` was last written at 177614f. Since then, `spec.jsonc`, `vite.config.js`, `README.md` and a test changed (`git diff --stat`), and every recorded pass still counts.
- Theorem results: `recorded.theorems` is keyed by theorem *name* (it holds `checkedAt` but no hash of the statement or of `formal/`).
  - `leanTheoremChecks` (`commands.js:171-181`) keeps the prior records when Lean is unavailable or `EXEGRA_NO_LEAN=1`.
  - The claim is then shown as `proved`, and its explanation says "the Lean kernel accepted its proof again" (`claims.js:415`).
  - Weakening the statement of `Exegra.runInput_terminates` in `formal/` leaves the claim `proved` on any machine without Lean.
- `tools/tree-stamp.js` is one monolithic SHA-256 over every tracked file, so it gives all-or-nothing reuse, not invalidation per guarantee. It also covers `results.json` and `spec.jsonc` themselves, so any edit invalidates every reusable outcome.

### 2.6 Admission sees only spec deltas (BLOCKS-OBJECTIVE, ARGUED)
- `admit` takes spec operations only (`commands.js:994-1050`). A change to code, Lean, a dependency or an assumption is not an input.
- The verdict is a status diff (`CLAIM_RANK`, `admit.js:20`) under the *same* recorded evidence, not a re-establishment of the affected guarantees.
- `admit.guarantee-weakened` for a changed claim statement can be acknowledged (`admit.js:322`, `--accept`).

### 2.7 "Verified" from author-entered declarations (LIMITS, DEMONSTRATED)
- `implementationLanguage` (`claims.js:812-835`) checks the *declared* `implementation.language` ("The declaration is not compared with the files").
- Setting `claim-evaluator.implementation.language = "lean"` would turn part of `core-logic-in-lean` green.
- The tag that selects the kernel (`verdict-kernel`) is also hand-assigned. It is missing from `validator`, `integrity-rules`, `claim-strength`, `parser`, `hash-binding`, `simulation-engine`, `generation-readiness` and `spec-layers` (all checked by listing the spec's components). Yet all of them decide errors, admission reasons or what reaches Lean.

### 2.8 Scalability (LIMITS, ARGUED; not measured here)
- Each commit runs:
  - a full JSON re-encoding of the 1.25 MB, 25k-line text (`parse.js:75-105`, with `{"o":[…]}` wrappers);
  - a full Lean `model.derive`, whose parser is a List-based `partial def` (`Json.lean:32-182`) and whose reference resolution is `List.find?`, O(refs × entities) (`Model.lean:946-966`; about 2,067 entities in the self-spec);
  - full `validateModel`;
  - `evaluateIntegrity` twice (before and after, `integrity.js:811-814`).
- `admit` additionally runs `evaluateClaims` twice: every scenario through Lean, and every metric claim N times.
- The docs report about 450 ms parse+validate per edit (`docs/integrity-rules.md:370`) and "no incremental parsing" (`docs/decisions.md:9`).
- The disk cache (177614f, `derivation-cache.js`) is keyed by SHA-256 of the *whole text* plus all of `src/core` and `src/engine/lean`. Any edit, or any edit to any core file, is a full miss. It speeds up repeated CLI runs, not edits.
- The cache key omits `node_modules/jsonc-parser`, which `parse.js` uses for syntax errors and locations. Upgrading it without changing `package.json`'s version gives stale hits (MINOR).

### 2.9 Partial JSON parser on the boundary (MINOR, ARGUED)
- `Json.parse` is `partial` (`Json.lean:32-182`), so it is opaque to proofs.
- `implRunAny_eq_parse_call` (`Api.lean:92`) is `rfl` *through* it. The theorems hold for every `Value` but say nothing about text→Value.
- The shell also rewrites values on the way back: `-0`, infinities and lone surrogates are replaced with U+FFFD (`parse.js:58-66, 214-217`).

## 3. Overclaims

1. **"Outside the verdict path".** `trusted-js-shell` (`spec.jsonc:14732-14733`) and `docs/verification.md:122` say the JS outside the `verdict-kernel` tag decides no claim status. But:
   - `validate.js`/`analyze.js` decide transaction acceptance;
   - `integrity.js` decides `admit.new-violation` (non-acknowledgeable);
   - `claim-strength.js` produces admission reasons;
   - `parse.js`, through `CLAIM_METHODS`, decides what is a valid method.
   None of these carries the tag.
2. **`core-logic-in-lean` undercounts.** It reports the gap as a few named components (WG-4800/4801/4802). The real gap is every JS rule above, about 20k lines across about 50 files (counted in §2.2–2.4).
3. **`proved` displayed from a stale record**, "the Lean kernel accepted its proof again" (§2.5).
4. **`supported`** reads "Exegra holds a recorded result of executing …" when the result may predate the current ref, code or spec (§2.5).
5. **`parse.js:5-9`** says "The model itself is derived by the verified kernel in Lean". Only a structural parse is derived there. The model the rest of Exegra reads is the JS object rebuilt from Lean's reply plus JS values (`valueAt`).
6. **`claim-method eventually`** with `expr` means "true in the final configuration" (`claims.js:1429-1436`; `Temporal.lean` header). That is not the temporal-logic "eventually". The name overstates what is checked (minor).

## 4. What to preserve

- **The single call boundary** `Exegra.Api.handle` with the registry (`Api.lean`, `lean.js`). It is name-agnostic, errors are values, and `registry_names_nodup` holds. This is the right shape for making Lean the sole authority: every new semantic function becomes a registered entry.
- **The Impl/definition split with refinement theorems** (`Impl.runAnyValue_eq`, `call_engine_run_spec`). It is the correct pattern for "the code that runs is the definition".
- **Exact decimal→double conversion** (`Number.lean:5-8`, `Num.ofDecimal`) and the bit-specified distribution lowering (`distributions.js:1-6`). That lowering is deterministic and portable, so it can be ported to Lean.
- **`derive_refs_resolve`, the semantic hash and `semanticHash_presentation`.** They give a sound identity for spec content.
- **Integrity-rule reflection** (`Sat`/`eval_iff`/`Least`/`least_eq_table`/`refutes_sound`). The mathematics is sound. What is missing is that it is not the evaluator that runs.
- **The SQLite store's per-entity rows** with `hash` and `refs` columns (`tools/spec-store.js:1-20`). It is the natural substrate for a fine-grained dependency graph and incremental derivation.
- **The honesty discipline of `claims.js`**: scope strings, `inconclusive` for vacuous checks, and `supported` kept distinct from `verified`. Keep it as the presentation of Lean verdicts.
- **The Rust engine as a differential oracle** (`tools/differential.js`). It is a duplicate, correctly placed outside the authority.

## 5. Architectural decisions that block the objective, and what should replace them

| Decision | Why it blocks | Replacement |
|---|---|---|
| Lean theorems target engine input; the spec→input lowering is JS (`sim-input.js`, `pools.js`) | No guarantee is ever about the *spec* | `model.lower : Model → Except Diag Input` in Lean, registered at the boundary; JS only serializes |
| Well-formedness = Lean structural + JS semantic rules | Class 1 has no single definition | One `WellFormed : Model → Prop` with a decidable checker in Lean, emitting all codes; JS keeps only text locations |
| Claim verdicts computed in JS over Lean traces | Classes 3, 4 and 8 have two definitions with different vacuity rules | One Lean `ClaimSem` per method (single trace = the explorer with bound 1, same `Form`); JS renders |
| Results keyed by evidence id / theorem name, with no provenance | No invalidation is possible | A content-addressed `Result {guarantee, inputs: {specEntityHashes, fileDigests, theoremStmtHash, toolVersion}, outcome}`; valid iff every input digest matches |
| Monolithic `treeStamp` and a whole-text cache key | O(spec) per edit; all-or-nothing reuse | A dependency DAG: entity → derived facts → claims → evidence/theorems → files (traceability already gives entity→files); invalidate by reachability |
| `admit` diffs statuses under fixed evidence and takes only spec ops | Change impact is impossible for code, Lean or assumptions | `admit` takes a change set over *all* artifacts, computes the invalidated guarantee set from the DAG, and requires re-establishment (or explicit downgrade to `stale`) |
| `verdict-kernel` tag and `implementation.language` are hand-declared | Self-certification | Derive "in Lean" from the boundary: a verdict is Lean-authoritative iff it is a registered Lean function's output; check it by the absence of JS evaluators on the verdict path (an import-graph check) |

## 6. Highest-leverage foundational changes (in dependency order)

1. **Provenance-stamped results** (independent of Lean).
   - Add `inputs` digests to every recorded result: for tests, the ref, the files the test imports transitively and the spec-entity hashes of the claim and its subjects; for theorems, the hash of the statement and a hash of `formal/`.
   - Add a status `stale`, which is never `supported` or `proved`.
   - *Done when*: the §2.5 counterexamples (an evidence ref swap via `admit`, and a weakened theorem with `EXEGRA_NO_LEAN=1`) both yield `stale` in a test.
2. **The lowering in Lean.**
   - Port `sim-input.js`, `pools.js`, `distributions.js` and `retryDelay` to `Exegra/Lower.lean`, registered as `model.lower`.
   - JS `simulationInput` becomes a call.
   - *Done when*: there is a theorem `call "engine.runSpec" m = runAnyValue (lower m)`, a differential test of the old JS lowering against Lean on every scenario of every spec under `specs/`, and `sim-input.js` is deleted.
3. **One claim semantics.**
   - Define `ClaimSem` in Lean for the structural, trace and evidence-aggregation methods.
   - Make single-trace evaluation the explorer restricted to the scripted order, sharing `Form`/`Matcher` and one vacuity policy.
   - *Done when*: `claims.js` contains no verdict logic (only formatting), and a theorem `singleTrace_verdict_le_explore` holds (a single-trace `holds` never contradicts an explorer `counterexample` on the same run).
4. **Well-formedness in Lean.**
   - Move the `validate.js` error rules to a decidable `WellFormed` in Lean, and integrity evaluation to `Integrity.eval` on the boundary.
   - Facts are exported by Lean from the model, not by JS.
   - *Done when*: the set of diagnostic codes in `validate.js` with severity `error` is empty, and `Integrity.lean` has a lemma that the exported facts are the model restricted to the rule's read set.
5. **Dependency DAG and incremental derivation.**
   - Build on the store's per-entity rows: per-entity derivation in Lean (entities are independent apart from ref resolution and vocabulary), a reverse index entity→claims→results, and `admit` over a change set of files and spec.
   - *Done when*: changing one entity re-derives O(affected) entities, `admit` names exactly the invalidated guarantees for a code-only change, and a benchmark shows sublinear edit cost on a 10× self-spec.

## 7. Predictions about other teams' conclusions

- **The formal-semantics team will likely over-credit Lean.** `Api.lean`'s `rfl` and refinement theorems are real, and `engine.js`/`parse.js` headers say "verified kernel". Expect them to conclude "simulation is proved". The theorems are about engine input; spec→input (pools, typing, distributions) is unverified JS.
- **The claims and evidence team may review `claims.js` statuses as the semantics** and miss that `recorded.results`/`theorems` carry no provenance. Then `supported` and `proved` look sound when they are only sound *at the time recorded*.
- **Someone will cite `core-logic-in-lean` as an honest, bounded gap list.** It is honest in spirit, but bounded by a hand-assigned tag that excludes validation, integrity, claim strength and the product-language checkers.
- **The integrity team may treat `holds_of_eval` proofs as about the spec.** They are about JS-exported facts and a JS-parsed formula. And the evaluator that runs during edits is JS.
- **The scalability team, or others, may credit the 177614f disk cache as incremental verification.** It is a whole-text memo with no dependency structure.
- **The Rust-engine team may call the Rust/Lean differential "independent agreement implies correctness".** Both consume the same JS-produced input, so a lowering bug is invisible to the differential.
