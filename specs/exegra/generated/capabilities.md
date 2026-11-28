# Capability matrix

Generated from the specification by `exegra generate`; do not edit. A claim belongs to a class through its
`guaranteeClass`. It is listed as established only when Lean shows it established: proved, fresh, and with no
open assumption (formal/Exegra/Verdict.lean, `shownEstablished`). Every other claim of the class is listed with
its status.

| Class | Established | Not established |
|---|---|---|
| 1. Well-formedness | none | none |
| 2. Consistency | none | none |
| 3. Safety | none | none |
| 4. Liveness | none | none |
| 5. Compositionality | none | none |
| 6. Refinement | none | none |
| 7. Implementation conformance | none | none |
| 8. Simulation fidelity | none | none |
| Change impact | none | `admit-refuses-theorem-weakening` (supported), `admit-takes-change-sets` (supported), `change-impact-remarks-dependents` (supported), `impact-changed-claim-remarked` (proved), `impact-direct-dependency-remarked` (proved), `impact-proof-only-not-weakened` (proved), `impact-statement-change-weakens` (proved), `verify-reruns-only-impacted-evidence` (supported) |

## Counts

| What | Count |
|---|---|
| Components | 116 |
| Relationships | 354 |
| Behaviors | 43 |
| Scenarios | 36 |
| Claims | 462 |
| Claims shown established | 5 |
| Claims inconclusive | 20 |
| Claims not-evaluated | 41 |
| Claims proved | 123 |
| Claims supported | 221 |
| Claims verified | 57 |
