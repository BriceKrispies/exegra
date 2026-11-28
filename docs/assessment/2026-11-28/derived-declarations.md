# Derived declarations of the self-specification (WG-5705)

What the self-specification declared by hand although the model can compute it, what was moved, and the checks
that show nothing changed. The per-claim record is [derived-declarations.json](derived-declarations.json).

## Test evidence, now carried by the tests

- **Before:** 827 `evidence` entities, every one of kind `test` and supporting, almost all saying only "this claim is
  backed by this test". No declared evidence was a measurement, review, document or contradicting evidence.
- **Now:** each test names the claims it evidences with a marker comment (`// @evidence <claim> ...`, or with a
  title pattern after `#` for generated titles, docs/claims-and-evidence.md). `exegra extract` records the markers in
  `specs/exegra/extracted/facts.json`, and the model derives one evidence entity per marked claim and reference.
  The markers reproduce the declared references exactly: 502 markers above a test with that literal title, 290 with
  the declared pattern, 35 for whole files. Two declared pairs were duplicates, so 827 declarations became 825
  derived evidence entities. Each declaration's `description` stayed with the test, as a comment above its marker.
- **Status comparison:** all 486 claims evaluated with the recorded results, before (declared evidence) and after
  (derived evidence, the recorded results re-keyed to the derived ids of the same claim and reference): no status
  differs.
- **Validation** reports a marker naming no claim, a marker it cannot read, a declared test evidence that duplicates
  a derived one, and a tested claim with no subjects (this replaces the integrity rule
  `tested-claims-name-subjects`, which ranged over declared test evidence and became vacuous).

## Claim subjects that repeated the claim's parameters

A claim that declares no subjects now takes the entities its evaluation parameters name (`claimSubjects`,
src/core/query.js). Eight structural claims named their subjects in their parameters as well; five declared exactly
the derived set and lost the declaration (tests/fixtures/derived-declarations/claim-subjects.json records each
declaration and the derived value at removal time). Three kept theirs because the derived value differs:
`storage-has-owner` declares six of the seven storage components its selector selects, and the two
`semantic-core` acyclicity claims declare the subsystem where the selector selects its descendants.

## Static dependencies

`exegra reconcile` reports no declared static dependency inside the extraction surface: they were already derived
from the extracted imports (WG-5696), so nothing was left to remove.

## Size

| | Bytes of spec.jsonc and parts |
|---|---|
| At the start of WG-5740 (eab205e) | 1,640,995 |
| Before the removal (with this task's new claims) | 1,670,338 |
| After removing the declared test evidence | 1,349,372 |
| Final | 1,350,888 |
