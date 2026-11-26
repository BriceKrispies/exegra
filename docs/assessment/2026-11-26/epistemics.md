# Epistemics: claim statuses, evidence and status inflation

Team: adversarial correctness and epistemic integrity. Read-only. Lean is not installed, so `analyzeSpec` cannot run. Demonstrations call the pure modules directly: `src/core/claims.js` with a hand-built model (its `semanticHash` string skips the Lean call), `cli/commands.js`, `cli/outcomes.js`, `cli/admit.js`, and real `node --test` runs. The scripts are in `scratchpad/epi/` (`inflate.mjs`, `pages-mutants.mjs`, `demo.test.js`).

## 1. Verdict

The status machinery for *model-evaluated* claims can be evolved. The structural and trace verdicts, vacuity-is-inconclusive, mandatory negatives and the Lean-facts rule are sound ideas worth keeping. The *evidence* side has to be redesigned:
- `supported` is a single flag that one pass of any test, or one author-written string, can raise.
- Nothing binds a result to the tree, to the test it ran or to what the claim's prose says.
- Skips can be recorded as passes, and stale passes and stale Lean facts are carried forward on purpose.
- `admit` treats a fall to `not-evaluated` as no regression.

134 of 248 claims are `supported` and 154 rest on an assumption that the specification itself says is false. So most of the positive statuses do not mean what their labels say.

## 2. Status rules and fundamental defects

### Status derivation (exact rules)
- **proved**: method is `lean-theorem` and the recorded facts in `results.json.theorems[thm]` say found, kind theorem, kernel ok, standard axioms only, and every `about` constant is a definition named in the statement (`claims.js:370-408`). Evidence can only lower it to `violated`. An empty `about` is allowed.
- **verified**: a structural method finds no counterexample on the *declared* graph and the selection is not vacuous. A trace method needs: holds on the listed scenarios, not vacuous, ≥1 negative, and every negative violates (`claims.js:1017-1119`). A `refines` check needs at least one non-stutter match (`:992`). A `fail` or `supports:false` evidence item turns it into `violated` (`:287-322`).
- **supported**: external-evidence or a declared external method. No evidence item contradicts, and *at least one* of these holds: a test with a recorded `pass`, a Concordance pass, or **any non-test evidence item at all** (`claims.js:537-546`). An external tool's `recorded.claims[id].outcome=='pass'` also gives supported (`:252-271`).
- **model-holds**: metric-bound, statistical (`:456`).
- **violated**: a counterexample, a recorded `fail`, `supports:false`, or Lean refusing the theorem.
- **inconclusive**: vacuous, or no negative, or an error. For evidence claims: test items only, none recorded (`:548`).
- **not-evaluated**: no method, unknown method, no evidence, or no Lean record (`:241, 274, 376, 517`).

### D1. Skipped and TODO tests are recorded as passes. BLOCKS-OBJECTIVE, DEMONSTRATED
- `countPassingTests` (`cli/commands.js:520-531`) counts every top-level `ok` line without `# SKIP`.
- A `describe` whose only test skips prints `ok N - suite` with no SKIP marker. A `{todo}` test prints `ok N - ... # TODO`, which is also not filtered.
- Real run on `epi/demo.test.js` with `--test-name-pattern="inner real check"`: the only matching test skipped, the TAP was `ok 1 - suite whose only test is skipped`, `countPassingTests` returned **1**, and so `runTestReference` returns **pass**.
- On the reuse path, `nodeOutcome` (`cli/outcomes.js:88`) calls it `skipped` only if *every* matched test skipped. Pattern `trivially|real check` therefore gives `pass` while the real check skipped. Pattern `publishes` (a `todo` test) gives `pass`.
- The fresh path and the reuse path disagree for the same reference.
- Real exposure: whole-file references to files with self-skipping tests. `ev-formal-differential` (formal-semantics.test.js), `ev-formal-explore`, `ev-integrity-lean`, `ev-lean-theorem-method` (the Lean part is `skip: noLean`), `ev-engines-agree` (native binary `t.skip`). Each records `pass` as long as one non-gated test in its file passes. `lean-theorem-method-refuses-unsound-proofs` can be `supported` without Lean ever having been shown a `sorry`.

### D2. Stale results are kept on purpose and never detected. BLOCKS-OBJECTIVE, DEMONSTRATED (in committed data)
- `mergeRecordedResults` (`commands.js:546-549`) keeps the *prior* outcome when the run is `skipped`. `results.json` entries carry no tree stamp, no ref, no test-file hash and no list of matched titles.
- Demo: prior `{ev-x: pass @2026-11-19}`, then ev-x is re-pointed at a test that skips. The merge keeps `pass @2026-11-19`.
- Committed: `ev-readiness-shipped-projects` has a `pass` with ranAt **2026-11-19**, while every other entry is from 2026-11-25. Its test is `skip: strataLinked ? false : ...` (`tests/core/readiness-machines.test.js:146`), and `specs/strata` is absent. Its assertion is about `specs/exegra/spec.jsonc`, which changed many times after Nov 19, yet `implementation-machine-readiness-rules` still counts it.
- The tree stamp (`tools/tree-stamp.js`) is used only to decide whether `.outcomes/*.json` can be reused *inside* verify. `exegra claims`, `generate`, the UI and `admit` all read `results.json` with no freshness check.
- `generated/claims-report.md` (hash `1525dce…`, 248 claims) predates the last 4 commits. It omits `pages-site-published-from-main` entirely, and `results.json` has no `ev-pages-*` entry.

### D3. Lean facts are trusted forever, keyed only by theorem name. BLOCKS-OBJECTIVE, DEMONSTRATED (code path)
- `leanTheoremChecks` (`commands.js:171-182`) returns the *prior* `theorems` unchanged when Lean is unavailable, and returns them **silently** under `EXEGRA_NO_LEAN=1`.
- A record has no hash of the Lean sources and no statement text. So replacing a proof with `sorry` and running `verify` in this very container (no Lean) keeps all 14 claims `proved`.
- `inflate.mjs` claim `lean-stale` shows `proved` from facts alone. Anyone who can write `results.json` can mint `proved`.

### D4. No link between a claim's prose and what is checked. BLOCKS-OBJECTIVE, DEMONSTRATED
Output of `inflate.mjs` (real `evaluateClaims`):
```
pages-like     supported  recorded result of ev-yaml-regex: pass
p-equals-np    supported  recorded result of ev-unrelated (tests/core/expr.test.js): pass
doc-only       supported  Document "ev-doc" (illustrative://no-such-report) is author-entered only
half-tested    supported  ev-a: pass. Test evidence "ev-b" has no recorded result.
lean-no-about  proved     "Nat.add_comm" ... claim names no implementation constant
```
- No rule relates `statement`, `kind`, `subjects` or the test's subject. Validation checks only the characters of a ref (`validate.js:640-647`). Any passing test makes "P = NP" supported.
- One document string makes a production-latency claim supported.
- "A and B", with only A tested, is supported. This happens for real: `product-layers-expressions` is supported while `ev-layers-expressions-drift-strata` (the Strata part, a skipped test) has no result (claims-report.md:6439).
- `proved` with an empty `about` is still labelled *"Proved in Lean: a kernel-checked theorem about the code"* (`claim-methods.js:20`).
- A real Lean example: the statement of `model-derivation-total` says "always returns". The theorem is `∃ out, call "model.derive" v = .ok out := ⟨_, rfl⟩` (`formal/Exegra/Api.lean:97`). That is a definitional unfolding of the wrapper. Termination and absence of traps are trusted-base assumptions, not part of the theorem.
- Refs are regexes over test names (`--test-name-pattern`, `compilePattern`). `.` is an allowed character. A renamed or deleted test silently re-binds to any other test whose title contains the pattern.

### D5. A `verified` structural claim that is false of the code. LIMITS, DEMONSTRATED
- `core-independent-of-ui` says no core component depends on "…the file system…", and its status is **Verified**.
- `derivation-cache` (parent `semantic-core`, spec.jsonc:2741) has the responsibility "Store each entry in one file under the cache directory…", and `src/core/derivation-cache.js` reaches `node:fs`.
- No `derivation-cache → filesystem` relationship is declared. The green status rests on the unchecked assumption `relationships-match-imports`. An import scan is feasible (the rationale at spec:14653 says one was run once, by hand), but it is not wired in.

### D6. Assumptions are never weighed, even when known false. BLOCKS-OBJECTIVE, ARGUED + data
- `recorded-results-reflect-current-code` (spec:14666) has the rationale "staleness is not detected", and `recorded-results-file` lists it as an unknown.
- 154 claims cite this assumption and are still `supported`. Assumptions are listed but have no effect on status (`claims.js:232`).
- The repository's own data falsifies this one (D2). It is *checkable*, yet it is treated as an axiom.

### D7. Circular self-verification. LIMITS, ARGUED
- Claims about the evaluator (15 claims name `claim-evaluator`) get their status from that same JS evaluator, through tests that call it.
- `own-behavioral-claims-falsifiable` ("every behavioral claim … is verified") could be decided over the model, yet it is `external-evidence`. A test runs `claims.js` on spec.jsonc, then `claims.js` marks the claim about itself `supported`.
- `core-logic-in-lean` admits that the claim evaluator is not in Lean, and `--expect-violated` suppresses that admission (D8). No independent checker exists for the status rules. Nothing in the repo calls this "independent", but `supported` is shown with the same tone class as external confirmation.

### D8. `--expect-violated` and `admit` normalise regressions. BLOCKS-OBJECTIVE, DEMONSTRATED
- The expectation is matched by claim id only (`commands.js:639, 708`). Any *new* counterexample of `core-logic-in-lean` (for example a new JS verdict-kernel component) or of `edits-only-via-transactions` passes `npm run verify`. The id list is hard-coded in `package.json:25`.
- `verify` fails only on validation errors, failed evidence and unexpected `violated`. A claim falling to `inconclusive` or `not-evaluated` passes.
- `admit`: `CLAIM_RANK` leaves out `not-evaluated` (`admit.js:20`). Demo with `compare()`: supported→not-evaluated, proved→not-evaluated, and a removed verified claim all give verdict **admitted** with 0 reasons.
- Editing an existing claim's `statement` (stronger) or its `evaluate` (weaker selector, `transitive:false`) without a status change is invisible to admit.
- A new external-evidence claim with a milestone and one `document` item is admitted as `supported` (`admit.js:211`).

### Case study: `pages-site-published-from-main`
- **Kind/method mismatch.** The kind is `structural` and the method is `external-evidence`. The statement is a temporal and operational universal ("every push to main publishes … only after … validates").
- **The prose is internally inconsistent.** If validation fails, the push does not publish, so "every push publishes" is false by the workflow's own design.
- **The prose is false of the workflow as written.** The top-level `concurrency: {group: pages, cancel-in-progress: false}` makes GitHub *cancel the already-pending run* when a third push arrives. With pushes A, B, C in quick succession, B is never built or published. The same happens with `[skip ci]` pushes, a disabled workflow, or Pages not being enabled (the "one-time setup" is not an assumption of the claim, `assumptions: []`).
- **The evidence cannot fail for the relevant defects** (`pages-mutants.mjs`, the test's regexes copied verbatim). Each of these mutants of `pages.yml` still makes all three assertions **PASS**:
  - `if: false` on the deploy job
  - `validate … || true`
  - `paths: [does-not-exist/**]` added under `push`
  - `needs: build` removed
  - `if: false` on the build job
- **Status today.** It is `inconclusive` (no results). After the next `npm run verify` it becomes `supported`, which AGENTS.md step 3 accepts as done.

**What would prevent this systemically** (folded into §6):
1. *Evidence must be falsifiable.* External-evidence claims declare evidence negatives: mutations of the subject artifact that the referenced test must fail, run by `verify` in a scratch tree. The rule Exegra already applies to traces and integrity rules ("a check that cannot fail is not verified") extends to tests.
2. *Evidence declares what it can establish.* For example `static-config`, `unit-behavior`, `runtime-observation`, `operational-record`. The claim kind/modality fixes the required class: a "every push publishes" claim needs `operational-record` evidence (deployment run ids per push) to be `supported`. With only static evidence it caps at a weaker, distinctly named status such as `configured`.
3. *Claims are split into atomic conjuncts.* Each conjunct has its own evidence, and the status is the meet over conjuncts, so "A and B with B untested" is not supported.
4. *Kind/method consistency is validated.* A `structural` claim whose statement quantifies over runs or time is a validation error.

## 3. Overclaims
- The `proved` label "a kernel-checked theorem about the code" also applies with an empty `about`, and to stale facts (D3, D4).
- `supported` has the label "Supported by external evidence" and an `ok-external` tone, yet it covers a placeholder document string. The docs admit this (claims-and-evidence.md, Evidence), but the status and its tone do not.
- claims-report.md says "Verified means checked … against this model revision". `supported` rows rest on results from other revisions (D2).
- AGENTS.md: "never marked positive without evidence". Evidence here can be a skipped test (D1), a stale pass (D2) or any unrelated test (D4).
- `core-independent-of-ui` is shown green `verified` while false of the code (D5).
- The doc table says "A Node test reference that matches no test … is recorded as a fail". A match whose every test skipped inside a describe is recorded as a **pass** (D1).

## 4. Preserve
- `evaluateOne`'s monotonicity: evidence can only worsen a model verdict (`claims.js:287-322`). This is the right lattice direction.
- Vacuity and negative rules for trace claims (`:1083-1119`), and refines requiring a non-stutter match. These are a genuine falsifiability discipline; extend them to evidence.
- The Lean facts rule (axiom whitelist, refusal of `sorryAx`/`ofReduceBool`, `about`-in-statement). The fix is to bind the facts to sources, not to change the rule.
- `tree-stamp.js` (content-addressed, covers untracked and generated files) and the stale checks in `outcomes.js` (complete, before==after==current). This is the right primitive; it only needs to reach `results.json` and evaluation.
- External methods are never `verified`, metric claims are never `verified`, and the explanation says which parts were executed. Honest wording to keep.
- `claim-strength.js`, which separates check strength and grounding from status.

## 5. Architectural decisions that prevent the objective
1. **Status is a function of an untimed results file.** Replace it with results keyed by (evidence id, ref, tree stamp or stamp of the subject files, test-file hash, exact executed test ids, pass/skip counts). Evaluation must take the current stamp and produce `stale` (never positive) on any mismatch.
2. **A single `supported` bucket for heterogeneous evidence.** Replace it with an evidence lattice by class (§2 case study). Author-entered items give `asserted`, never `supported`.
3. **Assumptions are inert annotations.** Replace them with assumptions that have a status (checked / unchecked / known-violated). A claim whose assumption is known-violated or checkable-but-unchecked cannot reach a positive status. `relationships-match-imports` and `recorded-results-reflect-current-code` are both mechanically checkable.
4. **Prose statement and check are decoupled.** For model methods, generate the canonical statement from `evaluate` and show it next to the author's prose. For `lean-theorem`, pin the theorem's type (its hash) in the claim, so a changed statement fails verify until the pin is re-reviewed. Make `about` mandatory for the "about the code" label.
5. **Known violations whitelisted by id; `not-evaluated` unranked.** Replace them with expected counterexample fingerprints, and treat any downgrade or removal as a regression that needs explicit acknowledgement.

## 6. Highest-leverage changes, in dependency order
1. **Exact, skip-aware test execution.** Refs name exact test ids. `pass` requires ≥1 executed leaf test with no skip and no todo, and every matched leaf passing. Describe lines are ignored, and the fresh and reuse paths share one function. A skip records `skipped` and *erases* the prior result. *Done when:* `epi/demo.test.js` patterns `inner real check`, `trivially|real check` and `publishes` all record not-pass on both paths, and a test in `tests/core/outcome-reuse.test.js` asserts this.
2. **Bind results to the tree.** `results.json` entries carry the tree stamp (or per-evidence subject stamp), and theorem records carry the hash of the `formal/**/*.lean` sources and the theorem type. `evaluateClaims` takes `currentStamp` and returns `stale` on mismatch. Missing Lean gives `not-evaluated`, not prior facts. *Done when:* editing any byte of a referenced test (or replacing a proof by `sorry`) and running `exegra claims` without re-running verify turns the claim `stale`/`not-evaluated`; the committed `ev-readiness-shipped-projects` entry is reported stale.
3. **Evidence negatives (mutation-backed evidence).** External-evidence claims declare `negatives: [{patch, mustFail: evidenceId}]`, which verify applies in a temporary worktree. A claim with no killing negative caps at `inconclusive`, mirroring trace claims. *Done when:* `pages-site-published-from-main` with the five mutants of `pages-mutants.mjs` declared is *inconclusive* until its test is strengthened to kill them.
4. **Evidence classes and atomic conjuncts.** Add `establishes` on evidence and `requires` per claim modality, and validate kind against modality. Non-test items give `asserted`. *Done when:* `inflate.mjs` yields `asserted` for `doc-only`, `inconclusive` for `half-tested`, and a validation error for the pages claim (temporal statement, static evidence).
5. **Regression gating.** Admit ranks `not-evaluated` and removals as regressions. Statement or `evaluate` edits of existing claims need acknowledgement. `--expect-violated` takes counterexample fingerprints and fails on a changed set. Wire an import scan into a checked claim. *Done when:* the `compare()` demo of §2 D8 is rejected, and adding an undeclared `src/core → node:fs` import turns `core-independent-of-ui` violated (today `derivation-cache` already should).

## 7. Predictions about other teams
- **Lean/formal teams** will audit theorem statements and find them sound, then conclude that "14 proved" is trustworthy. They will miss that `proved` is decided from a JSON file kept across Lean-less runs, with no source hash (D3). Their soundness findings hold for the *last tree on which Lean ran*, not for HEAD.
- **Simulation/trace teams** will praise mandatory negatives and stop there. They may not notice that 134 of the positive statuses never touch the model at all and rest on D1/D2-weak evidence.
- **Architecture teams** will take `core-independent-of-ui` (verified) as established independence. It is false of the code (D5).
- **Tooling/CI teams** will read the tree-stamp machinery as "results are bound to the tree". It binds only `.outcomes` reuse inside one verify run, not `results.json` or what `claims`/`generate`/`admit` read.
- Most teams will treat `npm run verify` passing as a gate. It cannot fail on downgrades to `inconclusive`/`not-evaluated` or on new counterexamples of the two whitelisted claims (D8).

## Cross-challenge

### C1. "Fixing evidence bookkeeping in JS is wasted work." Partly conceded; mostly rebutted.
A status is a function `status : Claim × Facts × CurrentArtifacts → Status`. The objective puts the *function* in Lean. It cannot put the *facts* in Lean: running a test, reading a file, hashing a tree or invoking `lake` are observations of an untrusted world. They are oracle inputs and belong to the trusted base.

A Lean decision layer fed today's `results.json` would decide soundly from stale, skip-inflated facts. Its outputs would be exactly as wrong as the current JS outputs, with a theorem attached. So fact provenance is a **precondition** of the Lean milestone, not polishing that the milestone replaces.

The line, change by change:

| Fix | Side | Why |
|---|---|---|
| Status lattice, meet/join, "stale/asserted never positive", "evidence only worsens", the regression order used by admit | **Semantics → Lean** | It decides what a claim means. Write it once in Lean with theorems (for example `positive s → ∀ f ∈ basis s, fresh f`), not as a further JS revision of `evaluateEvidenceClaim`. **Concession:** improving the JS lattice in `claims.js`/`admit.js` is wasted; only a stopgap one-line `not-evaluated` ranking in admit is justified. |
| Freshness predicate `fresh f ≡ f.stamp = stamp(deps f)` | Semantics → Lean | It is part of the lattice. |
| Computing stamps, the dependency map of a fact (traceability), recording provenance | Tooling, outside Lean | IO. It is trusted, so keep it small and test it. |
| Skip-aware, exact test references (TAP/JUnit/Playwright adapters) | Tooling, outside Lean | It produces facts. This is a real bug today (D1); about 20 lines; not deferrable, because a Lean layer would consume its wrong output. |
| lean-theorem binding (template elaboration, defeq, hypothesis telescope, `implemented_by`/`extern` scan) | **Lean meta code** | It must run inside Lean's elaborator. JS only transports the verdict and its hashes. |
| Fact schema `{kind, subject, stamp, deps, producer, executedIds, skipped}` | Interface; define in Lean | It is the type of the decision function's input, so it is the contract the JS producers must meet. |

Order: (1) the fact schema and lattice as a Lean type and function, with theorems; (2) the JS fact producers fixed to emit that schema (skip-aware, stamped); (3) delete the JS status rules. Steps 1 and 2 can proceed in parallel. None of step 2 is thrown away by the port.

### C2. The lean-theorem binding rule
1. **The claim carries the expected statement.**
   - For methods with a template, the expected Lean type is generated from `evaluate` (for example state-invariant gives `∀ cfg ∈ Reachable spec sc b, Holds expr cfg`).
   - Free-form claims carry `expect: "<Lean term>"`. A human reviews that prose and `expect` agree, and its elaborated hash is **pinned** in the claim. A changed hash is a statement edit that admit must acknowledge.
2. **The check, in Lean meta code.** Elaborate `expect` in a fixed environment (the library plus declared `open`s) to get `T`. Require `isDefEq (← inferType thm) T` at **reducible** transparency, i.e. `example : T := @thm` with unfolding limited to reducibles. Default transparency would also be sound, but makes "same statement" hard for a reviewer to predict. Keep the axiom whitelist. Reject when any constant in `T`'s closure that the claim is about carries `@[implemented_by]`/`@[extern]`, or is `opaque`/compiled from `partial` (lean.md L1.3). Record `hash(T)`, `hash(formal/**)` and the Lean version; a mismatch at read time gives `stale`.
3. **Vacuous hypotheses are handled by a witness obligation.** `forallTelescope` splits `T` into data binders `xs`, Prop binders `hs` and conclusion `C`. The rule then mechanically generates `Wit(T) := ∃ xs, h₁ ∧ … ∧ hₙ`. The claim must name a second theorem whose type is defeq to `Wit(T)`, checked the same way. Stronger and preferred for grounding: a witness instantiated at Exegra's own spec (`Hyps exegraSpec`, by `decide`), which shows the hypotheses hold where the claim is used, not merely somewhere.
4. **Decidability.** "The hypotheses are satisfiable" is not decidable in general. Hypotheses are arbitrary propositions; for example `h : Halts p` or an open conjecture can be encoded, so no procedure decides whether a witness exists. It is not even semi-decidable when the `hᵢ` themselves are undecidable. So satisfiability cannot be an automatic check, only a proof obligation the author discharges.
5. **Honest status without a witness:** `proved-under {hypotheses-satisfiable}`. The theorem is proved as an implication, the open assumption is named, and it never displays as `proved`. The same mechanism covers trusted-base and environment assumptions (C3).

Conclusion-side vacuity (`True ∨ P`, tautologies) is excluded by item 1. The type must equal the template or the pinned `expect`, so a free-form theorem cannot substitute.

### C3. A minimal lattice in which no status overstates its basis
A status is a tuple **(strength, subject, open assumptions A, freshness)**, not a single word. Each component answers a distinction the brief requires.

**Strength** (a chain plus a bottom group). Each item names the distinction it encodes:
- `refuted`. A fresh counterexample or contradicting fact. **Distinction:** violation is a fact.
- `undecided(reason)`. Covers today's not-evaluated and inconclusive, including a check that cannot fail (no killing negative). **Distinction:** absence of a counterexample ≠ proof.
- `asserted`. Author-entered documents or reviews only. Equal to `undecided` for establishment; it exists so the UI can say "someone wrote this". **Distinction:** declared ≠ true.
- `instance-checked(n, subject)`. Passes on n listed runs, tests or traces, with ≥1 killing negative or evidence mutant. A statistical result is the same status with `(N, β, conf)` attached. **Distinction:** passing test ≠ universal guarantee.
- `explored(bound)`. Exhaustive within a stated bound. Ordered by bound inclusion. **Distinction:** bounded exhaustive ≠ unbounded proof.
- `proved`. A Lean theorem whose type matches the template or the pinned `expect` (C2). **Distinction:** universal.

Order: `refuted < {undecided, asserted} < instance-checked < explored(b) < proved`.

**Subject** ∈ {`model`, `implementation`, `reality`}. **Distinctions:** satisfiable/model ≠ implemented; verified simulator ≠ empirically accurate (class 8 needs `reality`).
- A structural check over declared relationships is `proved, subject=model`.
- A claim about code built from it is `subject=implementation` only under the open assumption `relationships-match-imports`, which then appears in A.
- Strength never carries across subjects: no rule turns `model` into `implementation` except discharging a named refinement or conformance assumption.

**Open assumptions A**: unwitnessed hypotheses, environment and fairness assumptions, and checkable-but-unchecked assumptions such as `recorded-results-reflect-current-code`. The trusted computing base is listed once globally and is not repeated in A. **Distinction:** assumption ≠ fact.

**Freshness** ∈ {fresh, stale}. **Distinction:** valid now vs needs re-verification (the change-impact requirement).

**Derivation rules:**
1. Strength comes only from fresh facts of the matching kind: a document gives `asserted`; a test or trace with a killing negative gives `instance-checked`; the explorer gives `explored`; a C2-bound theorem gives `proved`. Anything else gives `undecided`.
2. Conjunctive claims take the meet over conjuncts: minimum strength, union of A, intersection of subjects. An untested conjunct caps the claim at `undecided`.
3. Any fresh contradicting fact gives `refuted`. Evidence only worsens.
4. Any fact in the basis with a mismatched stamp makes the whole tuple `stale(previous)`, which is never positive. A stale refutation stays blocking (`refuted, stale`), so staleness never improves a status.
5. If an assumption in A is itself refuted, the claim becomes `undecided(assumption-refuted)`. It does not become `refuted`, because the claim may still be true.
6. **Display rule:** positive tone only for `proved ∧ A = ∅ ∧ fresh`. Every other positive strength is printed with its qualifiers ("explored to b, model, under {a₁}").
7. **Regression order** for admit and verify: s ≤ s' iff strength ≤, A ⊇ A', same subject, and s' is fresh. Any move that is down, incomparable, or a removal counts as a regression and needs acknowledgement. A whitelisted violation is matched by counterexample fingerprint, not by claim id.

Mapping from today's statuses:
- `verified` (structural) becomes `proved, model`.
- `verified` (trace) becomes `instance-checked(model)`.
- `supported` (test) becomes `instance-checked(implementation)` only with a killing mutant (§6.3), otherwise `undecided`.
- `supported` (document) becomes `asserted`.
- `model-holds` becomes `instance-checked(model, N, conf)`.
- Today's `proved` with an empty `about` becomes `undecided`.
