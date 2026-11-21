# Coverage

Exegra measures how much of a specification its own scenarios and examples exercise, in two places where the
specification states behavior that generated code must reproduce: the transitions and guards of the machines that
ship, and the branches of functions. Both are computed by checking the model and running Exegra's own engine and
evaluator; nothing is estimated. Line and region coverage of generated or hand-written code, and mutation testing, are
measured by the repositories that hold that code (WG-4965).

## Machines: `exegra cover-machines`

```
node cli/exegra.js cover-machines [<behaviorId>] [--bound N] [--max-runs N] [--write <dir>] --project <name>
```

**What is covered.** Every implementation-level behavior (`level: "implementation"`) whose realisation is `shipped`
(`src/core/realisation.js`: declared, or by default the subject's implementation is not `not-implemented`) is
measured. Its items are:

- each transition that is not `faultOnly`;
- for each transition with a guard, two **guard outcomes**: *true* (the transition fires) and *false* (the event is
  delivered to the machine in the transition's source state, the transition is considered and its guard does not
  hold).

A transition marked `otherwise` has no guard, so it has only its transition item.

**Read from traces.** The command runs every scenario that lists the machine and reads its trace
(`src/core/machine-coverage.js`, `exercisedItems`): a fired transition covers its item and its guard's true outcome;
the guarded transitions of the same state and event declared before it were tried and were false (the declaration
order rule of [semantics](semantics.md)); an event ignored with reason `guard-false` had every considered guard false.

**The search.** For each item the scenarios leave out, a bounded breadth-first search runs the machine alone through
sequences of actions. An action is either the delivery of an input event, one time unit after the previous action, or
a wait:

- *Input events* are the events the machine's transitions react to, except those the machine emits itself (an `emit`
  or a timer), which arrive through its own effects.
- *Payloads* are representative values of each payload field's declared type: the values scenarios already deliver
  for that field, the literals of the guards on that event and their neighbours (n - 1, n, n + 1) for a number, both
  values of a bool, the values of an enum, and `null` for an optional field. An instanced machine is searched as one
  instance: every key field holds the same value, and routes by key are added for the input events that carry the key.
- *Waits* go past each time threshold of an expression that reads `time` (a literal n gives a wait of n + 1), or to the
  moment the next pending thing (a timer, a delayed event) happens.

Each delivery is one engine run (`src/core/engine.js`) of the whole sequence; a run that does not end quiescent is
discarded. States are deduplicated: first in a coarse round with the first payload of each event, where states differ
only by the machines' states, the variables the guards read and which events are pending; then with the full state
(variables, a timestamp variable as its age, pending events at their relative time) and the first payload, three, and
all. The search stops when every item is covered, or at the bound on actions (`--bound`, default 12) or on engine runs
per machine (`--max-runs`, default 5000, half for the coarse round).

**Generated scenarios.** Of the runs that covered something new, a greedy cover (largest gain first, shortest on a
tie) is kept, each named `cover-<machine>-<n>`. `--write <dir>` writes them to `<dir>/ops.json` as `CreateEntity`
operations of kind `scenario`, tagged `generated-coverage` (`tags`), with a description of what each exercises.
Apply them with `exegra apply --file <dir>/ops.json`; the differentials then run them like any other scenario. Once
applied, the command finds them as scenarios and generates nothing more for those items.

**The finding.** A transition that no scenario and no searched sequence reaches is
`machine.transition-unreachable`, a warning, or an error when `system.generation` is set (the command then fails). The
message says which of three things holds:

- its source state is entered by no transition from the initial state, guards aside, so nothing can reach it;
- the search exhausted every state it could reach with the offered events and payloads;
- the search stopped at its bound (of actions or of runs): it is unreachable *within that bound*, and a larger bound
  may still reach it.

A guard outcome nothing reaches is listed among the open items of the table, not as a finding: the false outcome of
the last guard of a group whose guards are complementary cannot happen, and saying so is the point.

**Output.** `summary` (transitions and guard outcomes covered/total, and how many by the scenarios alone),
`table` (one row per machine: transitions, guards, generated scenarios, open items), `machines` (every item and what
covered it, the generated scenarios, the bounds and whether the search was complete) and `findings`.

The negative fixture is `tests/fixtures/machine-coverage/spec.jsonc`: a door with a state nothing enters.

## Functions: `exegra cover-functions`

```
node cli/exegra.js cover-functions [<functionId>] [--branches] --project <name>
```

Exegra evaluates every example of every function (`src/core/function.js`). With the branch recorder attached
(`withBranchRecorder`), the evaluator reports each branch it takes; `src/core/function-coverage.js` lists every branch
point of each function's lets and body and marks it covered when some example takes it:

| Branch point | Branches |
|---|---|
| `if c then a else b` | `then`, `else` |
| `match e { ... }` | each arm, `_` included |
| `try call f(...)` | the value passes on (`ok`), the error propagates (`err`, only when `f` can fail) |
| `fail(...)` | taken |

A branch taken through a call from another function's example counts. The report gives, per function, branches
covered/total, the examples and how many fail, and each uncovered branch with where it is (`body` or `let <name>`,
line and column in that text, and the text at that point). `--branches` lists every branch.

**Informational only.** There is no readiness rule for uncovered branches: one that asked for every branch to be taken
would push a specification toward one example per branch. The examples are checked by evaluating every one of them
(an example whose result differs is an error); this report says what they exercise. `system.generation.functionBranches`
is no longer used and is accepted so that a specification that sets it still validates.
