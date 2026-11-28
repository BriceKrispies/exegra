# Multiscale M3: the semantic abstraction engine, recorded evidence

WG-5694. What the abstraction engine (`src/core/abstraction.js`, `src/core/footprints.js`) reports on Exegra's own
specification at the commit that introduced it, and the measurements its acceptance asks to record. The design is
described in [model-and-format.md](../../model-and-format.md#elements-hierarchies-facets-and-cuts) ("The derived
model at a cut") and [claims-and-evidence.md](../../claims-and-evidence.md#claims-stated-at-a-cut). Open work is in
Workgraph (WG-5709 integrity rules over derived facts, WG-5710 Lean proofs, WG-5695 views that adopt a cut).

## Derived models of the five cuts

Measured with `node cli/exegra.js derive --project exegra --cut <id>`; the outputs are the goldens in
`tests/fixtures/abstraction/`, and `tests/core/abstraction.test.js` compares them with a lift recomputed from the
raw relationships and component parents (the audit's appendix A method).

| Cut | Blocks | of which implicit | Derived interactions (per kind) | Relationships internal to a block |
|---|---|---|---|---|
| `l0` | 15 | 0 | 18 | 320 |
| `l1` | 21 | 0 | 73 | 181 |
| `persistence-expanded` | 29 | 0 | 93 | 166 |
| `semantic-core-expanded` | 63 | 0 | 221 | 80 |
| `module-level` | 346 | 74 | 362 | 0 |

At `module-level` every component with declared modules is opened; its relationships stay on it as an implicit
block, which is why every one of the 362 relationships is a derived interaction there and none is internal.

The seven invariants I1-I7 hold on every declared cut, with kinds as declared and coarsened to the top kinds,
and functoriality over the 12 comparable pairs of declared cuts (`l1 <= l0`, `persistence-expanded <= l1, l0`,
`semantic-core-expanded <= l1, l0`, `module-level <=` each logical cut, and the three runtime cuts): the claims
`abstraction-witness-completeness` through `abstraction-determinism` are verified by the model. The property
checks over generated specifications found one fault while they were written, in the ordering of a V4
diagnostic's entities (determinism), which is fixed.

## Port and interface reconciliation

Every declared port of the self-specification, at `module-level` (each port's owner is a block there):

| Port | Owner | Declares | Matched by derived boundary groups |
|---|---|---|---|
| `transactions-apply-in` | transactions | provides apply-transaction | `in:invokes:apply-transaction`, `in:submits-edits:apply-transaction` |
| `claims-evaluate-in` | claim-evaluator | provides evaluate-claims | `in:invokes:evaluate-claims` |
| `simulation-run-in` | simulation-engine | provides run-scenario | `in:invokes:run-scenario` |
| `projection-scene-in` | projection-system | provides project-scene | `in:invokes:project-scene` |
| `session-apply-out` | session | requires apply-transaction | `out:invokes:apply-transaction` |
| `session-write-out` | session | requires write-file | `out:invokes:write-file` |
| `session-claims-out` | session | requires evaluate-claims | `out:invokes:evaluate-claims` |
| `session-project-out` | session | requires project-scene | `out:invokes:project-scene` |
| `session-run-out` | session | requires run-scenario | `out:invokes:run-scenario` |
| `client-write-out` | persistence-client | requires write-file | `out:invokes:write-file` |
| `plugin-write-in` | dev-server-plugin | provides write-file | `in:invokes:write-file` |
| `plugin-write-out` | dev-server-plugin | requires write-file | `out:invokes:write-file` |
| `workspace-write-in` | workspace-service | provides write-file | `in:invokes:write-file` |
| `cli-command-in` | agent-cli | provides agent-command | `in:invokes:agent-command` |
| `cli-apply-out` | agent-cli | requires apply-transaction | `out:submits-edits:apply-transaction` |

No port is unrealised. Six typed boundary groups are not covered by a declared port of their block (V3
encapsulation, reported as `interface.undeclared-boundary` in the derived model, not as validation warnings):

- `agent-cli` invokes `evaluate-claims` and `run-scenario` without declaring requires ports for them;
- `claim-evaluator` invokes `run-scenario` without a requires port;
- `persistence-client` receives the session's `write-file` invocation without a provides port (it declares only
  `client-write-out`);
- `projection-system` projects `project-scene` onto the scene renderer without a port;
- `simulation-engine` invokes `trace-v2` (planned) without a port.

**Contract realisation paths.** `write-file` runs `session -> persistence-client -> dev-server-plugin ->
workspace-service`. Only the middle hop is typed (`write-file-request` and its answers). The first hop carries the
session's intents (`write-intent`, `read-intent`, ...) and the last, in-process hop the `ws-*` events, none of
which belongs to the contract: both are flagged. Every other contract's hops are untyped or unmodelled (no
behavior exchanges events along them), which is where V7 conformance work starts.

## The restated `core-independent-of-ui`

| Form | Targets | Verdict |
|---|---|---|
| Hand-written (before), leaves | 12 listed elements, 59 components | verified |
| Restated at `l1`, `{outside: semantic-core, except: [jsonc-parser-library, javascript-runtime]}` | 18 blocks, 65 components | verified |

The restated targets include every old one and add the markdown specification source, the external test runner,
the SQLite engine, the composition root, the browser user and the Node.js runtime. The JSONC parser library and the
JavaScript runtime are excepted with their reasons, because the core depends on them on purpose.

## Footprints and incremental re-derivation

`tests/core/abstraction.test.js` applies 200 seeded edits to the self-specification's relationships and
components (kind, target, description, additions, deletions, and component placements, which are structural).
After each, the five cuts are re-derived from the edit's affected set and compared with a full derivation, the
recomputed interactions are checked to be exactly those whose witnesses before or after hold the edited
relationship, and the graph claims are re-evaluated only when their footprint is touched and compared with a full
evaluation. While the check was written it caught two footprints narrower than what the results read (a scope
sentence counting every relationship of the filtered kinds, and a level scope counting every derived interaction);
both footprints were widened to what is read.

## Per-edit latency

Measured on the self-specification on the development machine (Windows, Node 24), median of 20 edits, each a
`SetProperty` on one relationship's description through `Project.apply`, followed by projecting the structural
view with `semantic-core` and `application` collapsed and evaluating the eight graph claims:

| | `Project.apply` (validation gate) | structural scene | graph claims |
|---|---|---|---|
| Before (ms-stack, without the engine) | 696 ms | 0.8 ms | 2.1 ms |
| After | 694 ms | 3.1 ms | 3.9 ms |

The validation gate is unchanged within noise: the engine adds two linear checks to it (port connections and
realisation maps). The scene costs more because it derives the model of its cut (memoised per model and cut), and
the claims because `core-independent-of-ui` is now evaluated at `l1`. Deriving all five cuts after an edit takes
19.2 ms in full and 11.5 ms from the footprints (mean of 50 edits); the remainder is the per-block interface
comparison and the model-wide diagnostics, which are recomputed in full.
