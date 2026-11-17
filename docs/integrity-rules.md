# Integrity rules

Validation catches broken references and schema errors one value at a time. It does not catch a
contradiction between entities: an entity whose basis is a superseded decision, a decision that
closes a gap whose `resolvedBy` names another decision, a proposed entity with no source. Claim
selectors pick components only, so claims cannot say these things either. An **integrity rule**
can. It is a declarative rule over the whole specification. Exegra evaluates it on every edit, and
an edit that adds a violation of an `error` rule is refused. Each result is evidence: a rule that
holds can be proved in Lean, and a rule that is violated comes with concrete counterexamples, which
Lean can refute it from.

## Declaring a rule

`integrityRule` is a built-in kind of the meta-model, declared in the `integrityRules` section. It
is not project vocabulary.

```jsonc
"integrityRules": [
  { "id": "closes-agrees-with-resolved-by", "severity": "error",
    "statement": "Every entity a decision closes names that decision as its resolver.",
    "rule": "forall d : decision, forall x in d.closes, x.resolvedBy == d",
    "basis": ["dec-01"] }
]
```

| Property | Meaning |
|---|---|
| `statement` | The rule in plain words (required). |
| `severity` | `error`: an edit may not add a violation. `warning`: violations are only reported (required). |
| `rule` | The formula (required). |
| `rationale`, `basis` | Why the rule exists, and the entities it rests on (any kind). |

## The rule language

The language is small, first-order and decidable over the finite specification. It has no
recursion and no arithmetic, so every rule evaluates in finite time. `src/core/integrity.js`
implements it, and `formal/Exegra/Integrity.lean` gives its meaning (`Sat`).

```
formula := quant | or ('=>' formula)?                    -- => is right-associative
quant   := ('forall' | 'exists') x (':' kinds | 'in' term) ('where' formula)? ',' formula
or      := and ('||' and)*          and := unary ('&&' unary)*
unary   := '!' unary | quant | '(' formula ')' | 'true' | 'false' | 'nonempty' term
         | term ('==' | '!=' | 'in' | 'not in') term
kinds   := '*' | kind ('|' kind)*
term    := 'kindof' term | x ('.' property)* | literal | '[' literal (',' literal)* ']'
literal := "string" | 'string' | number | true | false
```

- **A term denotes a finite set of values.** A variable is one value. `x.p` is the value or values
  of property `p` of the entity whose id `x` is: a list property gives its items, and an absent
  property gives nothing. Because a reference is an id, `d.closes.resolvedBy` follows references
  through lists. `kindof x` is the kind of the entity `x`. A value that is not an entity id has no
  properties and no kind.
- **Comparisons:** `a == b` is set equality, so an absent property equals nothing but the empty set.
  `a != b` is its negation. `a in b` holds when `a` is non-empty and every value of `a` is in `b`.
  `nonempty a` holds when `a` has a value.
- **Quantifiers** range over every entity (`*`), the entities of some kinds (`decision|gap`), or the
  values of a term (`in e.basis`). `where` filters the range: `forall x ... where F, B` means that `B`
  holds for every `x` for which `F` holds, and `exists x ... where F, B` means that some `x` satisfies
  both.
- Values are typed: `"1"`, `1` and `true` differ. Entity ids that a rule writes as literals are not
  references, so a rename does not rewrite them.

Validation reports a rule that does not parse, an unbound variable, an undeclared kind and a
property that no kind declares as the error `integrity.invalid`. A misspelt kind or property would
otherwise make the rule hold vacuously.

### The five rules of the decision register

These rules come from a converted specification's decision register. They are written in
`tests/fixtures/integrity/spec.jsonc`.

```
no-basis-on-superseded:
  forall e : * where e.status != "superseded", forall b in e.basis,
    !(kindof b == "decision" && b.status == "superseded")
closes-agrees-with-resolved-by:
  forall d : decision, forall x in d.closes, x.resolvedBy == d
resolved-by-is-closed-or-narrowed:
  forall x : *, forall d in x.resolvedBy, x in d.closes || x in d.narrows
proposed-has-source:
  forall e : * where e.origin == "proposed" && kindof e not in ["designArea"],
    nonempty e.basis || nonempty e.encodes
resolution-revisited:
  forall e : *, forall b in e.basis where nonempty b.resolvedBy && b.resolvedBy != e,
    b.resolvedBy in e.basis
```

The last rule says that an entity resting on a resolved item was revisited after the resolution.
The resolver itself is excluded: a decision's basis normally holds the gaps it resolves, and that
is not staleness. The fixture holds exactly this case: `dec-1` rests on `g-1`, and `g-1` is resolved
by `dec-1`.

## Results

`evaluateIntegrity(model)` evaluates every rule once per model; validation and the ratchet share the
result. Each rule is one of:

- `holds`, with `instances`: the number of bodies evaluated under the rule's leading universal
  quantifiers (after their filters);
- `violated`, with every **counterexample**: an assignment of the leading universal quantifiers
  that passes their filters and makes the body false, as variable bindings with entity ids, kinds
  and lines;
- `invalid`, with the problem.

A rule whose leading quantifier ranges over nothing is **vacuous**. It holds, because there is
nothing to check, and validation reports it as the warning `integrity.vacuous`. This is the same
principle claims follow: vacuity is not verification.

`validate` reports every current violation as a diagnostic `integrity.violated`. The diagnostic has
the rule's severity and sits at the first entity the counterexample names. These diagnostics are
left out of `analyzeSpec`'s `errorCount`, which counts the errors that block a transaction:
violations are governed by the ratchet instead. `exegra validate` still counts them, so it fails
while an error rule is violated.

## Enforcement on edit: the ratchet

`Project.apply` evaluates the rules on the model before and after the transaction. If the result
has a violation of an `error` rule that the project did not have before, the transaction is
refused with code `integrity.violated` and one diagnostic per new counterexample, and nothing
changes. A violation is identified by its rule and its bindings. Therefore:

- an edit unrelated to an existing violation is accepted, so a project that already has violations
  stays editable;
- an edit that adds a counterexample is refused, even when the rule was violated already;
- an edit that fixes a violation is accepted;
- a new `error` rule that is already violated cannot be added, because all its violations are new.
  Add it as a `warning`, then promote it: promotion keeps the existing violations and stops new
  ones;
- `warning` rules never block.

Undo, redo and reload are not checked. They restore or adopt text that was valid before.

## Proof and refutation in Lean

`exegra prove-integrity [<ruleId>] [--rules <file>] [--max-witnesses N]` decides each rule three ways
and reports `holds`, `violated` or `incomplete`. It needs Lake.

1. **Export** (`src/core/integrity-export.js`). The export holds only what the rule touches: the
   entities it can reach and the properties it reads. A rule over `*` reaches every entity; a rule
   over some kinds reaches those kinds, closed under the references of the properties it reads.
   Every id, kind, property name and literal is interned to a natural number, so the kernel
   compares numbers, which it evaluates natively, and never strings. The entities form a balanced
   binary search tree keyed by id. The intern table is written beside the proof file as
   `<rule>.values.json`.
2. **Differential.** `exegra-lean integrity` runs the compiled Lean checker (`eval`, `cex`) on the
   exported facts. Its verdict and its set of witnesses must equal the JavaScript evaluator's;
   otherwise the rule is `incomplete` and nothing is claimed.
3. **Proof.** The tool writes `formal/generated/integrity/<rule>.lean` and `lake env lean` checks it.
   - `facts_search_tree : facts.bst none none = true`. With `Facts.find_complete`, this means that
     following a reference finds exactly the entity with that id.
   - For a rule that holds: `theorem holds : Sat facts [] rule := holds_of_eval (by decide +kernel)`.
     This is a **proof by reflection**. `eval` is a Bool checker defined by structural recursion, and
     `eval_iff` proves `eval u env φ = true ↔ Sat u env φ` for every formula. The kernel then only
     evaluates `eval facts [] rule` to `true`.
   - For a violated rule: one `theorem violated_<n> : ¬ Sat facts [] rule := violated_of_refutes w (by
     decide +kernel)` per witness `w`, up to `--max-witnesses` (default 10). `refutes` checks one
     witness only: each value is in its quantifier's range, passes its filter, and the body is false.
     `refutes_sound` proves that such a witness makes the rule false. A refutation is therefore
     established from the concrete counterexample, without re-deciding the whole rule.

**Why this is sound.** `decide +kernel` has the kernel evaluate the Bool checker, so no compiled
code is trusted. `native_decide` would add `Lean.ofReduceBool` and trust the Lean compiler; it is
not used. `prove-integrity` reads `#print axioms` for every theorem and reports the rule
`incomplete` unless each depends on `propext`, `Classical.choice` and `Quot.sound` only. The
general theorems (`eval_iff`, `refutes_sound`, `Facts.find_complete`) are pinned to those axioms
with `#guard_msgs` in `Integrity.lean`. What is not proved is that the exported facts are the
specification: the export is JavaScript, and the differential step checks that the Lean checker
and the evaluator agree on it.

**Why reflection, and not `decide` on the formula directly.** The meaning `Sat` quantifies over
membership in the facts, which has no `Decidable` instance the kernel can reduce efficiently. A
direct `decide` would also compare strings, which the kernel unfolds character by character. The
reflective checker over interned numbers and a search tree keeps the kernel's work close to one
pass over the exported entities, with logarithmic reference lookups.

## Commands

| Command | Does |
|---|---|
| `exegra integrity [<ruleId>] [--rules <file>] [--limit N]` | Evaluates the rules: status, instances, vacuity, counterexamples (the first `--limit`, default 20) and time. Fails with `integrity.violated` when an error rule is violated or a rule is invalid. |
| `exegra prove-integrity [<ruleId>] [--rules <file>] [--max-witnesses N]` | Proves or refutes in Lean, as above. Fails with `integrity.incomplete` when a rule could not be decided. |

`--rules <file>` adds rules from a JSON array of `integrityRule` entities to the model in memory,
without the ratchet. Use it to try rules on a specification that cannot or should not be edited.

## Scale

Measured on a linked specification of about 14,450 entities (5.7 MB). The five rules above were
given with `--rules`:

| | Time |
|---|---|
| Evaluating all five rules (JavaScript) | about 27 ms per edit, on top of about 450 ms to parse and validate the text |
| Lean checker, per rule (`exegra-lean integrity`) | 0.1 to 0.2 s |
| Lean proof check, per rule over `*` (elaboration of the facts, the search-tree theorem, `holds` or the refutations) | 7 to 29 s |
| Lean proof check, a rule over one kind (20 entities) | about 1 s |

The kernel's time grows roughly linearly with the number of exported entities.
