# Candidate decompositions of `semantic-core`: what each improves or worsens

Source: `semantic-core-candidates.json` in this folder, the output of

```sh
node cli/exegra.js decompose --project exegra --scope semantic-core --file tests/fixtures/decomposition/semantic-core-audit.json
```

on the current self-specification (semantic hash `15d8986c18c903`, declared and extracted facts; the figures were re-taken on the merged specification, where they differ from the first run). `semantic-core-audit-declared.json` is the same with `--provenance declared --source declared`, the declared-relationship base of the audit. The command was run twice and the two outputs are byte-identical; the specification was not written by it.

Valid is not meaningful. Every figure below is a measurement of structure. None of them accepts, ranks or recommends a candidate, and no candidate here is called better on a score. What each candidate gains on one measure it gives up on another, and which trade a person wants is their judgement, not something these figures decide.

## What was generated

43 candidates over the 48 children of `semantic-core` (47 components and the module element `module:src/core/types.js` that the component declares itself). The audit groupings list 34 of them and place the other 14 in `simulation` (`rest`), as the audit placed its planned components:

| Source | Candidates | Validity (V1 to V7) |
|---|---|---|
| given: the audit's first grouping (`audit-first`) | 1 | valid |
| given: the audit's second grouping (`audit-second`) | 1 | valid |
| refinements (split, merge, move) read off those two | 37 | valid |
| contract-bounded regions (`semantic-core-contract-regions`) | 1 | valid |
| declared hierarchy (`semantic-core-declared`, 48 single-element blocks) | 1 | invalid, V3 |
| module directories (`semantic-core-directories`) | 1 | invalid, V3 |
| condensation of dependency cycles (`semantic-core-cycles-condensed`) | 1 | invalid, V3 |

The three invalid ones fail V3 with the same witnesses, which are a fact about the specification and not about the grouping: `claim-evaluator` and `simulation-engine` each declare a port, and the boundary of each has an outgoing `invokes` typed by a contract (`run-scenario`, `trace-v2`) that no declared port covers (`interface.undeclared-boundary` on `claim-evaluator-calls-simulation-engine` and `simulation-engine-calls-performance-metrics`). A grouping that keeps either of them inside a block with its callee, as the audit groupings and the contract regions do, does not have that boundary, so V3 does not apply to it. An invalid candidate has no measurements.

No connector exists among the children (`connectors` generated nothing), and `refinement` of the declared base generated nothing (its blocks are single elements); it generated 37 from the audit groupings instead.

V6 does not apply to any of them: no block of any candidate is an element that declares abstract behaviour. The reports say so and give the reason; V6 is not passed silently. V7 holds for all valid candidates: the boundaries between their blocks carry no contract that its events fail to type. The six hops from outside the scope into the core that declare a contract and whose events are untyped (`session-calls-transactions`, `source-editor-submits-edits-transactions`, `composition-root-submits-edits-transactions`, `session-calls-claim-evaluator`, `session-calls-simulation-engine`, `agent-cli-calls-simulation-engine`) are the boundary of `semantic-core` itself. Every candidate has them unchanged, so they are listed in each report (`conditions[V7].detail.outside`) and decided by none.

## Measurements of the three that differ most

| Measure | `audit-first` | `audit-second` | `semantic-core-contract-regions` |
|---|---|---|---|
| Blocks | 5 (1, 11, 24, 6, 6 members) | 5 (1, 11, 24, 5, 7 members) | 2 (1 module element and 47 members) |
| Facts internal to a block | 241 | 242 | 422 |
| Facts crossing blocks (boundary size) | 181 | 180 | 0 |
| Cohesion (internal over internal plus crossing) | 0.571 | 0.573 | 1.000 |
| Ordered block pairs with a crossing fact | 16 of 20 | 15 of 20 | 0 |
| Dependency cycles among blocks (static, runtime, together) | 1, 1, 1 (4, 5, 5 blocks) | 1, 1, 1 (4, 5, 5 blocks) | 0, 0, 0 |
| Witnesses on the back edges of dependency cycles | 37 | 28 | 0 |
| Interface groups, over all blocks; largest | 45; 12 | 44; 12 | 14; 14 |
| Crossing facts typed by a contract | 2 of 181 (0.011) | 2 of 180 (0.011) | no crossing facts |
| Redundant declared facts on a boundary | 0 | 0 | 0 |
| Opaque grain elements | 6 | 6 | 6 |
| Boundary fact provenance | 58 declared, 123 extracted | 58 declared, 122 extracted | none |

### `audit-first` against `audit-second`

`audit-second` differs from `audit-first` in the sizes of `verdicts` (6 to 5 members) and `well-formedness` (6 to 7): one child sits in the other block. The other three blocks are the same size. Against `audit-first` it:

- improves the boundary by one fact (181 to 180), one block pair (16 to 15), and the witnesses on the back edges of the dependency cycle (37 to 28), with cohesion 0.571 to 0.573;
- worsens nothing on the figures above;
- leaves the cycle in place: both groupings keep one dependency cycle through `model-kernel`, `simulation`, `verdicts` and `well-formedness`, and, since the specification declares `decomposition-evaluator-calls-transactions` (the evaluator is a child the groupings place in `simulation`, and `transactions` is `editing`), `editing` as well, so neither is acyclic. The static-class cycle is still the four blocks; the witness that brings `editing` into the dependency and runtime cycles is that one back edge from `simulation` to `editing`. All back edges are in each report's `evidence.cycles`.

Neither reaches the contract coverage of a boundary worth speaking of: two crossing facts in about 180 are typed by a contract.

### The contract regions

`semantic-core-contract-regions` has no crossing facts and no cycles because it is two blocks, one of them the 47 other children. Its cohesion of 1 and its boundary of 0 follow from there being one block; they say the partition is trivial, not that the core is cohesive. It improves boundary size, coupling and cycles to zero and worsens the one thing the other two do: it does not separate anything. Its largest interface is 14 groups against 11 in the audit groupings, because one block now holds every boundary toward the rest of the system.

## Refinements

The 37 refinements are one split, merge or move of an audit grouping each. They are valid. Two read off the table show the shape of the trade:

| Measure | `audit-second` | `audit-second~move-proof-export-to-simulation` | `audit-first~merge-editing-model-kernel-simulation-verdicts-well-formedness` |
|---|---|---|---|
| Blocks | 5 | 5 | 1 |
| Largest block | 24 | 25 | 48 |
| Crossing facts | 180 | 167 | 0 |
| Cohesion | 0.573 | 0.604 | 1.000 |
| Back-edge witnesses | 28 | 21 | 0 |
| Dependency cycles among blocks | 1 | 1 | 0 |

Moving `proof-export` into `simulation` reduces the boundary by 13 facts and the back-edge witnesses by 7, makes `simulation` one member larger, and leaves the cycle. Merging the five blocks of the cycle removes it, because the cycle is inside the merged block, at the price of one block of all 48 children and no boundary inside the core at all; that is the same trade as the contract regions make.

## What these measurements do not say

- That any candidate is the right architecture. The cycle among the large blocks is present in both audit groupings and is removed only by merging the blocks it runs through.
- That a smaller boundary is better. It is smaller where blocks are larger.
- That the declared single-element hierarchy is worse: it is invalid under V3 for a reason unrelated to its shape, so it has no measurements to compare.

Figures taken on the declared base alone (`semantic-core-audit-declared.json`) are 41 internal and 58 crossing dependency-class facts for both audit groupings. The audit's 46 and 53 were counted on an older specification; `tests/core/decomposition.test.js` reproduces them on the audit-time facts (`tests/fixtures/decomposition/audit-semantic-core.json`).
