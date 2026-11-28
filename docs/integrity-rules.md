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
arithmetic, and its only recursion is through derived relations (below), which range over finite
candidate tuples, so every rule evaluates in finite time. `src/core/integrity.js`
implements it, and `formal/Exegra/Integrity.lean` gives its meaning (`Sat`).

```
formula := quant | or ('=>' formula)?                    -- => is right-associative
quant   := ('forall' | 'exists') x (':' kinds | 'in' term) ('where' formula)? ',' formula
or      := and ('||' and)*          and := unary ('&&' unary)*
unary   := '!' unary | quant | '(' formula ')' | 'true' | 'false' | 'nonempty' term
         | rel '(' (term (',' term)*)? ')'            -- a derived relation (below)
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

## Derived relations

A first-order rule cannot say "no module reaches itself": reaching is the transitive closure of
`uses`, and the closure has no bound the rule could unfold to. A **derived relation** can. It is
an entity of the built-in kind `integrityRelation`, declared in the `integrityRelations` section,
and rules and other relations use it as an atom.

```jsonc
"integrityRelations": [
  { "id": "reaches", "statement": "Module a reaches module b through one or more uses.",
    "params": [{ "name": "a", "kinds": ["module"] }, { "name": "b", "kinds": ["module"] }],
    "clauses": ["b in a.uses", "exists m in a.uses, reaches(m, b)"] }
],
"integrityRules": [
  { "id": "uses-acyclic", "severity": "error", "statement": "No module reaches itself.",
    "rule": "forall m : module, !reaches(m, m)" }
]
```

| Property | Meaning |
|---|---|
| `statement` | What a tuple of the relation means, in plain words (required). |
| `params` | The parameters, in order (required). Each has a `name` and `kinds`: a list of entity kinds, or `"*"` for every entity. |
| `clauses` | Formulas of the rule language (required). Each is one way a tuple is in the relation. Their free variables must be parameters. A parameter a clause does not mention ranges over its whole domain. |
| `rationale`, `basis` | As for rules. |

Relation ids follow the id rules of every entity, and must not be a keyword of the rule language.
`tests/fixtures/integrity/relations.jsonc` has reachability, a pair of mutually recursive relations
(`odd-path`, `even-path`) and stratified negation (`stale-dep` negates `live`).

### Syntax and meaning of an atom

```
unary := ... | rel '(' (term (',' term)*)? ')'
```

`rel(t1, ..., tn)` holds when there is a choice of one value from each `ti`, each a finite set of
values as every term is, such that the tuple of those values is in the relation. So
`reaches(m.uses, b)` holds when some module `m` uses reaches `b`, and an atom with an argument that
has no value is false. The number of arguments must equal the number of parameters.

### The meaning of a relation: its least model

The **candidate tuples** of a relation are the product of its parameter domains: for
`reaches`, every pair of modules. The relation is the **least** set of candidate tuples that is
closed under its clauses: whenever a candidate tuple satisfies one of the clauses, it is in the
relation. On a cycle `a -> b -> a`, `reaches` holds `(a, a)`, `(a, b)`, `(b, a)`, `(b, b)` and
nothing else.

The least model exists only when a relation's clauses use their own relation, and the relations
recursive with it, positively. Relations are therefore **stratified**:

1. The dependency graph has an edge from each relation to every relation its clauses name.
2. Its strongly connected components, in topological order, are the strata: every relation a
   stratum uses is in it or in an earlier stratum.
3. Within a stratum, every atom of a relation of that stratum must occur **positively**. Polarity
   flips under `!`, on the left side of `=>`, and in the `where` filter of a `forall` (which is
   the left side of an implication). The filter of an `exists` does not flip it. A quantifier's
   domain is a term, and terms contain no atoms.
4. An atom of a lower stratum may occur with any polarity. `stale-dep(a) :- exists b : module,
   reaches(a, b) && !live(b)` is allowed, because `live` is computed first.

Each stratum is the least model of its clauses with the lower strata fixed. Rules have no
stratum: they may use any relation with any polarity.

### Diagnostics

Each problem is an error on the relation. It makes the relation invalid, with every relation that
uses it, every relation in its cycle, and every rule that uses any of them. The rule's diagnostic
carries the same code.

| Code | Problem |
|---|---|
| `integrity.relation-unstratified` | Recursion through negation: an atom of the relation's stratum occurs negatively. |
| `integrity.relation-arity` | An atom has a different number of arguments than the relation has parameters (in a clause or a rule). |
| `integrity.relation-unknown` | An atom names no relation (in a clause or a rule). |
| `integrity.relation-unbound` | A clause has a free variable that is not a parameter. |
| `integrity.relation-kind` | A parameter's kind does not exist, or its `kinds` is neither `"*"` nor a list of kinds. |
| `integrity.relation-syntax` | A clause does not parse. |
| `integrity.relation-params` | A parameter has no name, a name that is a keyword, or a duplicate name; or the relation id is a keyword. |
| `integrity.relation-size` | The relation has more than 100,000 candidate tuples. |

An undeclared kind or property in a clause is reported with the rule codes `integrity.kind` and
`integrity.property`, on the relation.

### Evaluation

`relationTables(model)` in `src/core/integrity.js` computes the strata lowest first. Within a
stratum it starts from empty tables and, pass after pass, adds every candidate tuple that is not
yet in its relation and satisfies one of its clauses, until a pass adds nothing. Since the
stratum's own atoms occur only positively, every tuple added is in the least model, and the final
tables are closed under the clauses, so they are the least model. Each pass but the last adds a
tuple, so evaluation ends. Only the strata of the relations the rules use, directly or through
other relations, are computed; each stratum at most once per model, so validation and the ratchet
share them, and a relation no rule uses costs nothing. The cost is that of naive evaluation: every candidate tuple, through
the general formula evaluator, on every pass (WG-5267).

### Proof in Lean

`formal/Exegra/Integrity.lean` defines the meaning and proves the checker computes it.

- `Formula.atom r ts` is the atom. `Sat u I env φ` takes an interpretation `I : Nat → List Nat →
  Prop` of the relations; `eval u T env φ` takes a Bool table, and `eval_iff` relates them.
- A `Program` is a list of strata, each a list of `Rel` (an id, one domain per parameter, the
  clauses with the parameters as variables `0 .. n-1`).
- **Meaning.** `Least u prog` is defined stratum by stratum without mentioning the checker. A tuple
  is in a relation of a stratum iff it is in that relation in **every** interpretation that agrees
  with the lower strata and is closed under the stratum's clauses (`LeastS`, `ClosedS`, `Agree`).
- **Checker.** `solve u prog []` iterates each stratum's clauses from empty tables over the
  candidate tuples (`stepS`: a row is the candidates that satisfy a clause under the previous
  iterate) until a step changes nothing. It runs on fuel (the number of candidate
  tuples plus two); running out returns `none`, a failure that makes a proof impossible, never a
  wrong table.
- **Stratification.** `wf prog` checks, per stratum, that ids are distinct and new, that every
  clause is positive in the stratum's own relations (`posF`, with the polarity rules above), and that
  every atom names a relation of the stratum or below with its arity. A proof file decides it with
  `decide +kernel`; nothing is trusted from JavaScript.
- **Theorem.** `least_eq_table : wf prog = true → solve u prog [] = some T → ∀ r vs, Least u prog
  r vs ↔ look T r vs = true`. Its halves are `stratum_closed` (the fixpoint table is closed under
  the clauses) and `stratum_le_closed` (every iterate lies in every closed interpretation that agrees
  with the lower strata). The second rests on `sat_mono`: a formula in which the atoms of a set of
  relations occur only with polarity `p` is monotone (`p = true`) or antitone in them.
- `holds_of_eval` and `violated_of_refutes` conclude `Sat u (Least u prog) [] φ` and its negation.

A proof file states, besides `facts_search_tree`:

```lean
def prog : Program := ...      -- the relations the rule uses, in stratum order ([] when none)
def table : Table := ...       -- their tables, exported from the JavaScript evaluator
theorem prog_wf : wf prog = true := by decide +kernel
theorem prog_solved : solve facts prog [] = some table := by decide +kernel
theorem holds : Sat facts (Least facts prog) [] rule := holds_of_eval prog_wf prog_solved (by decide +kernel)
```

The export includes the entities of the parameter domains and of what the clauses read. The
differential step of `prove-integrity` also requires that `exegra-lean integrity` finds the
program stratified and solved and that its tables equal the JavaScript tables. Every theorem above
is pinned to `propext`, `Classical.choice` and `Quot.sound` (`sat_mono` to `propext`) with
`#guard_msgs`.

### Comparison with Nemo

`tests/proofs/integrity-nemo.test.js` compares the JavaScript tables with
[Nemo](https://github.com/knowsys/nemo), an independent Datalog engine. It translates the
relations of the fixture, and of seeded random programs over random graphs, to Nemo rules. The
programs use closures of edges in three recursive forms, a mutually recursive pair, and negation of
lower strata. The relations `nmo` derives must equal the tables. Entities and property values go
to Nemo as CSV facts of typed keys, read with `format = (string, ...)`. A clause becomes one rule
per disjunct of its disjunctive normal form, and each parameter is bound by the facts of its kinds.
The translation covers atoms, negated atoms, `x in y.p`, `y.p == literal` on a single-valued
property, and `exists` over a property or a kind. A relation outside that fragment is not
compared, and the test prints which. The test is skipped with the reason when `nmo` is absent
(`EXEGRA_NEMO`, or `%LOCALAPPDATA%\exegra\tools\nemo-0.10.1\nmo.exe`).

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
   When the rule, or a clause of a relation it uses, takes `kindof`, the export also includes the
   entity whose id equals an exported entity's kind, if there is one: a kind is a value, and a term
   may follow it (`forall k in kindof n, nonempty k.tag`).
   Every id, kind, property name and literal is interned to a natural number, so the kernel
   compares numbers, which it evaluates natively, and never strings. The entities form a balanced
   binary search tree keyed by id. The intern table is written beside the proof file as
   `<rule>.values.json`.
2. **Differential.** `exegra-lean integrity` runs the compiled Lean checker (`eval`, `cex`) on the
   exported facts. Its verdict and its set of witnesses must equal the JavaScript evaluator's, and
   for a rule that uses derived relations the program must be stratified and solved with the same
   tables; otherwise the rule is `incomplete` and nothing is claimed.
3. **Proof.** The tool writes `formal/generated/integrity/<rule>.lean` and `lake env lean` checks it.
   - `facts_search_tree : facts.bst none none = true`. With `Facts.find_complete`, this means that
     following a reference finds exactly the entity with that id.
   - `prog_wf` and `prog_solved`: the derived relations the rule uses (`prog`, empty when it uses
     none) are stratified, and the checker's fixpoint is `table` (see Derived relations).
   - For a rule that holds: `theorem holds : Sat facts (Least facts prog) [] rule := holds_of_eval
     prog_wf prog_solved (by decide +kernel)`. This is a **proof by reflection**. `eval` is a Bool
     checker defined by structural recursion, and `eval_iff` proves `eval u T env φ = true ↔ Sat u
     (toI T) env φ` for every formula; `least_eq_table` turns the table into the least-model
     meaning. The kernel then only evaluates `eval facts (look table) [] rule` to `true`.
   - For a violated rule: one `theorem violated_<n> : ¬ Sat facts (Least facts prog) [] rule :=
     violated_of_refutes w prog_wf prog_solved (by decide +kernel)` per witness `w`, up to `--max-witnesses` (default 10). `refutes` checks one
     witness only: each value is in its quantifier's range, passes its filter, and the body is false.
     `refutes_sound` proves that such a witness makes the rule false. A refutation is therefore
     established from the concrete counterexample, without re-deciding the whole rule.

**Limits.** Each Lean process (`exegra-lean integrity` and the check of the proof file) runs
under a time limit, `--timeout <seconds>` (default 300). A rule whose relations have more than
`--max-candidates` candidate tuples in total over the exported facts (default 500) is not sent to
the kernel. Either way the rule is `incomplete`, with the reason ("too large to prove in the
kernel", or the process that ran out of time), and nothing is claimed; the JavaScript result stands
unproved. The kernel evaluates the fixpoint iteration of `solve` by reduction, and its work grows
with the candidate tuples times the iterations times the table sizes. Measured on a chain of
modules with the `reaches` relation: 196 candidates in 9 s, 400 candidates in 46 s.
The proof file is checked by running `lean` directly in the environment `lake env` prints, so the
time limit stops the process doing the work.

**Why this is sound.** `decide +kernel` has the kernel evaluate the Bool checker, so no compiled
code is trusted. `native_decide` would add `Lean.ofReduceBool` and trust the Lean compiler; it is
not used. `prove-integrity` reads `#print axioms` for every theorem and reports the rule
`incomplete` unless each depends on `propext`, `Classical.choice` and `Quot.sound` only. The
general theorems (`eval_iff`, `refutes_sound`, `Facts.find_complete`, and those of derived
relations) are pinned to those axioms
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
| `exegra prove-integrity [<ruleId>] [--rules <file>] [--max-witnesses N] [--timeout S] [--max-candidates N]` | Proves or refutes in Lean, as above, within the limits above. Fails with `integrity.incomplete` when a rule could not be decided. |

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
