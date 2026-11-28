// Declarative registry of claim evaluation methods. This is data: the validator
// checks `claim.evaluate` against it, the evaluator dispatches on it, and the
// inspector describes methods from it. A method that is not listed here is
// "unsupported": the claim stays explicitly not-evaluated.
//
// Parameter types: selector | string | strings | boolean | expr | ids:<kind> | matcher | negatives
//
// A selector picks components. It is a string id, an array of ids, or an object
// whose present fields must all match:
//   { ids, category, kind, tag, facet, trustZone, within, outside, except, all }
// A component nested (at any depth) inside a selected subsystem is also selected.
// facet names a declared facet or a tag (a tag is an implicit facet); it selects the facet's members.
// outside: X selects the complement of X: every component that is not X, not inside X and not an ancestor of X.
// except: [{id, reason}] removes those elements (and what they contain) from the selection; each needs a reason.
//
// The graph methods (no-relationship, reachable, only-via, acyclic) may state a level: `cut` names a declared cut,
// and the claim is evaluated on the derived model of that cut under the transfer rules (claims.js, "Claims stated
// at a cut"; src/core/abstraction.js).
//
// A matcher picks trace occurrences: { event: <event id> } or { transition: <transition id> }.
//
// A negative is [{ scenario: <one of the claim's scenarios>, faults: [<fault id>, ...] }]: that scenario run with
// its own faults plus these, which must violate the claim. A trace claim is verified only when it holds on its
// scenarios and each negative, at least one, violates it (claims.js).

export const CLAIM_STATUSES = /** @type {const} */ ({
  proved: { label: 'Proved in Lean: a kernel-checked theorem about the code', tone: 'ok-proof' },
  verified: { label: 'Verified within the stated model and assumptions', tone: 'ok' },
  supported: { label: 'Supported by external evidence', tone: 'ok-external' },
  violated: { label: 'Violated', tone: 'bad' },
  inconclusive: { label: 'Inconclusive', tone: 'warn' },
  'model-holds': { label: 'Holds in the model (parameters assumed)', tone: 'ok-model' },
  asserted: { label: 'Asserted by an author: written down, not established by anything Exegra checked', tone: 'warn' },
  'not-evaluated': { label: 'Not evaluated', tone: 'none' },
});

/** The conformance stages, weakest first, with what each establishes. */
function CONFORMANCE_STAGES_DATA() {
  return /** @type {[string, string][]} */ ([
    ['structural', 'Structural conformance: the code has the parts the specification names (declared modules exist, every source file is claimed, realisation roots resolve). Rests on test evidence; at most checked on instances.'],
    ['interface', 'Interface conformance: the code accepts and produces the shapes the specification declares (contracts, payload and record types, telemetry line formats). Rests on test evidence; at most checked on instances.'],
    ['transition', 'Transition conformance: from each specified state, the code reacts to each event as the transition the specification declares (scenarios generated from the machines, run against the code). Rests on test evidence; at most checked on instances.'],
    ['trace', 'Trace conformance: a run of the code, driven by a scenario, produces the specified behaviour (the trace of a claim checked against what the code did). Rests on test evidence; at most checked on instances.'],
    ['runtime-monitor', 'Runtime-monitor conformance: a stream recorded from the running code replays through the specification without a divergence. Rests on test evidence; at most checked on instances.'],
    ['verified-refinement', 'Verified refinement: a Lean theorem states that the implementation refines the specification. Proved, subject implementation, when the Lean gate accepts the theorem.'],
  ]);
}

/** The conformance stages, weakest first. */
export const CONFORMANCE_STAGES = CONFORMANCE_STAGES_DATA().map(([stage]) => stage);

/** The stage a conformance method checks, or null. @param {string|null|undefined} method */
export function conformanceStage(method) {
  return typeof method === 'string' && method.startsWith('conformance-') && CONFORMANCE_STAGES.includes(method.slice(12)) ? method.slice(12) : null;
}

export const CLAIM_METHODS = {
  'no-relationship': {
    kinds: ['structural'],
    doc: 'No relationship (optionally: no transitive path) leads from any `from` component to any `to` component.',
    params: {
      cut: { type: 'ids:cut', doc: 'The level the claim is stated at: a declared cut. The claim is evaluated on the derived model of that cut (blocks and lifted interactions with witnesses), and its verdict transfers to the base only by the transfer rules (absence exactly; a coarse path only when a chain between members witnesses it; acyclicity as a statement about blocks). Naming an element hidden inside a block of the cut, or selecting part of a block, is not expressible at that level.' },
      from: { type: 'selector', required: true },
      to: { type: 'selector', required: true },
      kinds: { type: 'strings', doc: 'Relationship kinds considered. Default: every kind.' },
      classes: { type: 'strings', doc: 'Dependency classes of the relationship kinds followed (static, runtime, none), as well as `kinds`: a relationship must pass both. A legacy kind has the class of the kind it behaves as.' },
      transitive: { type: 'boolean', doc: 'Also forbid multi-hop paths.' },
      where: { type: 'edge-filter', doc: 'Only relationships whose property has one of the values, e.g. {"property": "layer", "values": ["current", "target"]}.' },
    },
  },
  reachable: {
    kinds: ['structural'],
    doc: 'Every `from` component reaches at least one `to` component along directed relationships.',
    params: {
      cut: { type: 'ids:cut', doc: 'The level the claim is stated at: a declared cut. The claim is evaluated on the derived model of that cut (blocks and lifted interactions with witnesses), and its verdict transfers to the base only by the transfer rules (absence exactly; a coarse path only when a chain between members witnesses it; acyclicity as a statement about blocks). Naming an element hidden inside a block of the cut, or selecting part of a block, is not expressible at that level.' },
      from: { type: 'selector', required: true },
      to: { type: 'selector', required: true },
      kinds: { type: 'strings', doc: 'Relationship kinds followed. Default: every kind.' },
      classes: { type: 'strings', doc: 'Dependency classes of the relationship kinds followed (static, runtime, none), as well as `kinds`: a relationship must pass both. A legacy kind has the class of the kind it behaves as.' },
      where: { type: 'edge-filter', doc: 'Only relationships whose property has one of the values, e.g. {"property": "layer", "values": ["current", "target"]}.' },
    },
  },
  'only-via': {
    kinds: ['structural'],
    doc: 'Every directed path from a `from` component to a `to` component passes through a `via` component.',
    params: {
      cut: { type: 'ids:cut', doc: 'The level the claim is stated at: a declared cut. The claim is evaluated on the derived model of that cut (blocks and lifted interactions with witnesses), and its verdict transfers to the base only by the transfer rules (absence exactly; a coarse path only when a chain between members witnesses it; acyclicity as a statement about blocks). Naming an element hidden inside a block of the cut, or selecting part of a block, is not expressible at that level.' },
      from: { type: 'selector', required: true },
      to: { type: 'selector', required: true },
      via: { type: 'selector', required: true },
      kinds: { type: 'strings' },
      classes: { type: 'strings', doc: 'Dependency classes of the relationship kinds followed (static, runtime, none), as well as `kinds`: a relationship must pass both. A legacy kind has the class of the kind it behaves as.' },
      where: { type: 'edge-filter', doc: 'Only relationships whose property has one of the values, e.g. {"property": "layer", "values": ["current", "target"]}.' },
    },
  },
  'has-port': {
    kinds: ['structural'],
    doc: 'Every selected component declares a port matching the given direction / contract / name.',
    params: {
      select: { type: 'selector', required: true },
      direction: { type: 'string' },
      contract: { type: 'ids:contract' },
      name: { type: 'string' },
    },
  },
  'property-defined': {
    kinds: ['structural'],
    doc: 'Every selected component has a non-empty value for the property (dot path allowed).',
    params: {
      select: { type: 'selector', required: true },
      property: { type: 'string', required: true },
    },
  },
  acyclic: {
    kinds: ['structural'],
    doc: 'The directed graph of the given relationship kinds has no cycle (stated at a cut: the blocks form no cycle).',
    params: {
      cut: { type: 'ids:cut', doc: 'The level the claim is stated at: a declared cut. The claim is evaluated on the derived model of that cut (blocks and lifted interactions with witnesses), and its verdict transfers to the base only by the transfer rules (absence exactly; a coarse path only when a chain between members witnesses it; acyclicity as a statement about blocks). Naming an element hidden inside a block of the cut, or selecting part of a block, is not expressible at that level.' },
      kinds: { type: 'strings', doc: 'Default: kinds flagged as dependencies.' },
      classes: { type: 'strings', doc: 'Dependency classes of the relationship kinds followed (static, runtime, none), as well as `kinds`: a relationship must pass both. A legacy kind has the class of the kind it behaves as.' },
      where: { type: 'edge-filter', doc: 'Only relationships whose property has one of the values, e.g. {"property": "layer", "values": ["current", "target"]}.' },
      within: { type: 'selector' },
    },
  },
  'data-model': {
    kinds: ['structural'],
    doc: 'The data rules hold on the records and copies of the model (src/core/data-model.js): erasure-point, record-erasure-point, no-principal-in-shared, party-by-id, freshness-bound, holder-reaches-owner. Inconclusive when a listed rule has nothing to check.',
    params: {
      rules: { type: 'strings', doc: 'Rules to check. Default: all six.' },
      records: { type: 'ids:record', doc: 'Only these records and the copies of them.' },
    },
  },
  'state-invariant': {
    kinds: ['invariant'],
    doc: 'The expression holds in the initial configuration and after every step of each listed scenario. A trace-level check, not a proof over all executions.',
    params: {
      scenarios: { type: 'ids:scenario', required: true },
      negatives: { type: 'negatives', doc: 'Runs that must violate the claim: [{scenario, faults}], one of the listed scenarios with extra faults. Verified needs at least one, and every one must violate the claim.' },
      expr: { type: 'expr', required: true },
      theorem: { type: 'string', doc: 'A Lean theorem (in formal/, checked by lake build Exegra) stating the invariant for the calculus system of the scenario, as `exegra prove --module` writes it; when Lean accepts it with the standard axioms only, the claim reads proved.' },
      about: { type: 'strings', doc: 'The Lean constants the statement of the theorem must mention (with `theorem`).' },
    },
  },
  precedes: {
    kinds: ['temporal'],
    doc: 'In each listed scenario, every occurrence of `then` has an earlier occurrence of `first`.',
    params: {
      scenarios: { type: 'ids:scenario', required: true },
      negatives: { type: 'negatives', doc: 'Runs that must violate the claim: [{scenario, faults}], one of the listed scenarios with extra faults. Verified needs at least one, and every one must violate the claim.' },
      first: { type: 'matcher', required: true },
      then: { type: 'matcher', required: true },
    },
  },
  eventually: {
    kinds: ['temporal'],
    doc: 'In each listed scenario, `occurs` happens at least once (or `expr` holds in the final configuration).',
    params: {
      scenarios: { type: 'ids:scenario', required: true },
      negatives: { type: 'negatives', doc: 'Runs that must violate the claim: [{scenario, faults}], one of the listed scenarios with extra faults. Verified needs at least one, and every one must violate the claim.' },
      occurs: { type: 'matcher' },
      expr: { type: 'expr' },
    },
  },
  never: {
    kinds: ['temporal'],
    doc: 'In each listed scenario, `occurs` never happens.',
    params: {
      scenarios: { type: 'ids:scenario', required: true },
      negatives: { type: 'negatives', doc: 'Runs that must violate the claim: [{scenario, faults}], one of the listed scenarios with extra faults. Verified needs at least one, and every one must violate the claim.' },
      occurs: { type: 'matcher', required: true },
    },
  },
  liveness: {
    kinds: ['temporal'],
    doc: 'Over the infinite runs of each listed scenario in the behaviour calculus (a run that ends stutters in its last state), the state predicate `expr` holds infinitely often (`form` "GF") or from some point on forever (`form` "FG"), on every run that is weakly fair to the transitions the fairness assumptions the claim cites name. Decided only by `exegra prove` (a ranking proof, a lasso counterexample, incomplete or not supported); a trace check never decides it, so the claim stays not evaluated in the live view (docs/simulation.md, "Liveness").',
    params: {
      scenarios: { type: 'ids:scenario', required: true },
      form: { type: 'string', required: true, doc: '"GF" (always eventually) or "FG" (eventually always).' },
      expr: { type: 'expr', required: true },
    },
  },
  'metric-bound': {
    kinds: ['measured'],
    doc: 'A measured output of seeded format-2 runs (response time, outcomes, throughput, false positives, transitions, utilisation, queue length, waiting time) meets a bound (op and bound: exact binomial test over the runs) or agrees with an analytic value (approx: sign-test interval of the median). Model results only: model-holds, violated or inconclusive with N, k and the confidence; never verified or supported (docs/simulation.md, "Claims over metrics").',
    params: {
      scenarios: { type: 'ids:scenario', required: true },
      metric: { type: 'any', required: true, doc: '{kind, of, statistic, outcomes?}.' },
      op: { type: 'string', doc: '<=, <, >= or >.' },
      bound: { type: 'string', doc: 'The bound, a duration ("30 ms") or an exact decimal.' },
      approx: { type: 'any', doc: '{value, tolerance} instead of op and bound.' },
      fraction: { type: 'string', doc: 'Fraction of runs that must satisfy the bound. Default 0.95.' },
      confidence: { type: 'string', doc: 'Default 0.95.' },
      runs: { type: 'any', doc: 'N, fixed before the runs. Default 59.' },
      seed: { type: 'string', doc: 'Base seed of the runs.' },
      asOf: { type: 'string', doc: 'The date the evaluation is made for (recorded in the result).' },
      negatives: { type: 'negatives', doc: 'Runs that must fail: [{scenario, faults}].' },
      controlNegatives: { type: 'negatives', doc: "Runs that must hold: a twin's faults on a control scenario." },
    },
  },
  refines: {
    kinds: ['temporal'],
    doc: 'The implementation behavior refines the model behavior it names in `refines`, through its `refinement` mapping: in the trace of each scenario that runs it (or of each listed scenario), every initial configuration of the behavior maps to the model\'s initial configuration, and every transition it fires maps either to the transition the model would fire from the mapped configuration on the same event (same from and to under the state mapping, guard true and first in declaration order, effects giving the mapped post-variables, the same emitted events) or to a stutter that changes no mapped state or variable and emits nothing. Violated with the first failing step; a check of these traces, not of all executions (docs/claims-and-evidence.md, "Refinement").',
    params: {
      behavior: { type: 'ids:behavior', required: true, doc: 'The implementation behavior (one id); it declares `refines` and `refinement`.' },
      scenarios: { type: 'ids:scenario', doc: 'The scenarios whose traces are checked. Default: every scenario that runs the behavior.' },
    },
  },
  'refines-composition': {
    kinds: ['temporal'],
    doc: 'The declared abstraction `behavior` (a behavior with `abstracts`) is refined by the composition of its members: in each listed scenario (default: every scenario that runs it, else every scenario that runs all its members) the run with the abstraction and the run with its members (with `finest`, members of member abstractions too) give the same boundary trace once the members\' internal events are hidden: the same events, kinds and payloads at times related by the time scale, the same outcome and the same final configuration of every machine outside the region. The runs are the Lean engine\'s and the comparison is decided in Lean (engine.refineBoundary). Violated with the first boundary counterexample; verified with a step correspondence and strength conservative; undecided when the strength is incomplete. Each negative (a listed scenario with extra faults, applied at whichever level has the transition) must break the refinement. A check of these runs, not of every interleaving (docs/composition.md).',
    params: {
      behavior: { type: 'ids:behavior', required: true, doc: 'The abstraction (one id).' },
      scenarios: { type: 'ids:scenario', doc: 'The driving scenarios. Default: every scenario that runs the abstraction, else every one that runs all its members.' },
      finest: { type: 'boolean', doc: 'Compare with the finest members (members of member abstractions expanded).' },
      negatives: { type: 'negatives', doc: 'Runs that must break the refinement: [{scenario, faults}].' },
    },
  },
  'environment-assumed': {
    kinds: ['structural', 'temporal'],
    doc: 'In the run of each listed scenario, every delivered event that no running machine reacts to and that an element the scenario omits would receive (an element with a behavior that consumes it, or whose declared interface lists it as an input) is covered by an environment assumption of the scenario\'s cut naming that element and event. Violated with the first unassumed delivery. Each negative ({scenario, without: [elements]}) drops the environment assumptions for those elements and must then report one (docs/composition.md, "Behavioural cuts").',
    params: {
      scenarios: { type: 'ids:scenario', required: true, doc: 'The scenarios checked.' },
      negatives: { type: 'any', doc: '[{scenario, without: [element]}]: the scenario without those environment assumptions must report an unassumed delivery.' },
    },
  },
  'order-independent': {
    kinds: ['invariant', 'temporal'],
    doc: 'Composition does not depend on the order in which a scenario lists its behaviors (invariant I2): each listed scenario (default: every scenario), and each negative run of the claims that list it, run with its behaviors reversed and in every rotation, gives every invariant and temporal claim that lists the scenario the same verdict as the scenario\'s own order. invariant_rename (formal/Exegra/Core/BehavRename.lean) proves the same of the calculus\'s relation; this checks the scheduler\'s runs (docs/composition.md, "Order independence").',
    params: {
      scenarios: { type: 'ids:scenario', doc: 'The scenarios checked. Default: every scenario.' },
    },
  },
  transfers: {
    kinds: ['temporal', 'invariant'],
    doc: 'The preservation rules applied to `claim` and the declared abstraction `abstraction` give the outcome `expect` (transferred, the default, or not-transferred): a safety claim (never, precedes, state-invariant) over the abstraction\'s boundary alphabet that holds where the abstraction runs transfers down to its members when the refinement check certifies the abstraction; a liveness claim (eventually, liveness) never transfers without a declared fairness hypothesis; anything else is not transferred, with the reason (docs/composition.md, "Claim transfer").',
    params: {
      claim: { type: 'ids:claim', required: true, doc: 'The claim established at the abstraction\'s level.' },
      abstraction: { type: 'ids:behavior', required: true, doc: 'The declared abstraction.' },
      expect: { type: 'string', doc: 'transferred (default) or not-transferred.' },
    },
  },
  'alternatives-reconciled': {
    kinds: ['structural'],
    doc: 'No element has alternative machines: two behaviors of one subject that consume a common event either run together in some scenario or are related by a declared abstraction (one a member, at any depth, of the other) or by refines. Violated with the pairs (docs/composition.md, "One behaviour per element per level").',
    params: {
      subjects: { type: 'ids:component', doc: 'The elements checked. Default: every element.' },
    },
  },
  'interfaces-closed': {
    kinds: ['structural'],
    doc: 'Every event belongs to an interface (declared by an element or port, inferred from a behavior that consumes or emits it, or the element producedBy names), every cross-element state read crosses a declared interface that exports it, and every declared interface lists its members\' boundary events (docs/composition.md, "Interfaces"). Violated with the faults.',
    params: {},
  },
  'lean-theorem': {
    kinds: ['structural', 'invariant', 'temporal', 'requirement'],
    doc: 'A theorem of the Lean core (formal/) states the claim. Lean checks it (tools/lean-theorems.js, recorded by exegra verify): the theorem exists, the kernel accepts its proof again, it depends on no axiom beyond propext, Classical.choice and Quot.sound (no sorry, no native_decide, no axiom of our own), and each named implementation constant occurs in its statement. Proved when all hold; violated when Lean refuses; not evaluated without a recorded check.',
    params: {
      theorem: { type: 'string', required: true, doc: 'The fully qualified theorem name, e.g. Exegra.runInput_terminates.' },
      about: { type: 'strings', doc: 'Implementation constants (compiled definitions) the statement must mention, e.g. Exegra.runInput.' },
      supersedes: { type: 'string', doc: 'A theorem of type `new statement → old statement`: when the statement of the theorem changes, admit accepts the change as a strengthening, not a weakening, only if this theorem passes the Lean gate (exegra admit, reason admit.theorem-weakened).' },
    },
  },
  'implementation-language': {
    kinds: ['structural'],
    doc: 'Every selected component that is implemented (implementation.status other than not-implemented) records implementation.language equal to `language`. Violated with the components that are not, listed with progress; inconclusive when nothing is selected or a selected component records no language.',
    params: {
      select: { type: 'selector', required: true },
      language: { type: 'string', required: true },
      exclude: { type: 'selector', doc: 'Components left out (exactly these: a subsystem named here does not take its children with it).' },
      plannedBy: { type: 'string', doc: 'The Workgraph task that ports the rest, named in the result.' },
    },
  },
  'abstraction-well-formed': {
    kinds: ['structural'],
    doc: 'The abstraction structure is well formed: every listed hierarchy (default: logical and every declared one) is laminar and acyclic, with every element under at most one parent and every module element under exactly one element, and every listed cut (default: every declared cut) is an antichain that covers every element of its hierarchy, so its abstraction map sends each element at or below it to exactly one block. Violated with the offending elements; decided by the model.',
    params: {
      hierarchies: { type: 'strings', doc: 'The hierarchy ids checked (logical is the one component.parent declares). Default: every hierarchy.' },
      cuts: { type: 'ids:cut', doc: 'The cuts checked. Default: every declared cut.' },
    },
  },
  'abstraction-invariants': {
    kinds: ['structural'],
    doc: 'The derived models of the listed cuts (default: every declared cut), with kinds as declared and coarsened to the top kinds, satisfy the listed invariants of an abstraction (default: all; src/core/abstraction.js, abstractionInvariants): witness-completeness (I1), boundary-accounting (I2), recoverability (I3), interfaces-from-boundaries (I4), functoriality over every comparable pair of the listed cuts (I5), kind-preservation (I6) and determinism (I7). Each is recomputed from the relationships independently of how the derived model is assembled. Violated with the faults; decided by the model.',
    params: {
      cuts: { type: 'ids:cut', doc: 'The cuts checked. Default: every declared cut.' },
      invariants: { type: 'strings', doc: 'The invariants checked, by name. Default: all seven.' },
    },
  },
  'extraction-reconciled': {
    kinds: ['structural'],
    doc: 'The declared relationships agree with the facts extracted from the implementation (tools/extract.js, read as data with provenance extracted): inside the extraction surface no declared static dependency is redundant (the extracted fact carries the edge), unwitnessed, reversed or of another kind, and every extracted file belongs to a module element. An extracted dependency with no declared counterpart is not a discrepancy, since the extracted fact is the dependency. Static structure only: runtime wiring stays declared and is not compared. Violated with the discrepancies; decided by the model and the facts.',
    params: {},
  },
  // Staged conformance of the implementation to the specification (WG-5685, criterion 11;
  // docs/claims-and-evidence.md, "Conformance stages"). Each stage is a method whose result names its stage. The
  // first five rest on executed test evidence and give at most checkedOnInstances; verified-refinement rests on a
  // Lean theorem and gives proved, with subject implementation.
  ...Object.fromEntries(CONFORMANCE_STAGES_DATA().map(([stage, doc]) => [`conformance-${stage}`, stage === 'verified-refinement'
    ? { kinds: ['structural', 'invariant', 'temporal', 'requirement'], doc, params: {
      theorem: { type: 'string', required: true, doc: 'The Lean theorem stating that the implementation refines its specification, e.g. one built on Exegra.Core.LTS.Simulates.' },
      about: { type: 'strings', doc: 'Implementation constants (compiled definitions) the statement must mention.' },
    } }
    : { kinds: ['structural', 'invariant', 'temporal', 'requirement'], doc, params: {} }])),
  'external-evidence': {
    kinds: ['measured', 'structural', 'invariant', 'temporal'],
    doc: 'The model cannot establish this claim. Its status comes only from evidence entities and recorded results of executing them.',
    params: {},
  },
};
