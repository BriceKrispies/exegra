// Declarative registry of claim evaluation methods. This is data: the validator
// checks `claim.evaluate` against it, the evaluator dispatches on it, and the
// inspector describes methods from it. A method that is not listed here is
// "unsupported": the claim stays explicitly not-evaluated.
//
// Parameter types: selector | string | strings | boolean | expr | ids:<kind> | matcher | negatives
//
// A selector picks components. It is a string id, an array of ids, or an object
// whose present fields must all match:
//   { ids, category, kind, tag, trustZone, within, all }
// A component nested (at any depth) inside a selected subsystem is also selected.
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
  'not-evaluated': { label: 'Not evaluated', tone: 'none' },
});

export const CLAIM_METHODS = {
  'no-relationship': {
    kinds: ['structural'],
    doc: 'No relationship (optionally: no transitive path) leads from any `from` component to any `to` component.',
    params: {
      from: { type: 'selector', required: true },
      to: { type: 'selector', required: true },
      kinds: { type: 'strings', doc: 'Relationship kinds considered. Default: every kind.' },
      transitive: { type: 'boolean', doc: 'Also forbid multi-hop paths.' },
      where: { type: 'edge-filter', doc: 'Only relationships whose property has one of the values, e.g. {"property": "layer", "values": ["current", "target"]}.' },
    },
  },
  reachable: {
    kinds: ['structural'],
    doc: 'Every `from` component reaches at least one `to` component along directed relationships.',
    params: {
      from: { type: 'selector', required: true },
      to: { type: 'selector', required: true },
      kinds: { type: 'strings', doc: 'Relationship kinds followed. Default: every kind.' },
      where: { type: 'edge-filter', doc: 'Only relationships whose property has one of the values, e.g. {"property": "layer", "values": ["current", "target"]}.' },
    },
  },
  'only-via': {
    kinds: ['structural'],
    doc: 'Every directed path from a `from` component to a `to` component passes through a `via` component.',
    params: {
      from: { type: 'selector', required: true },
      to: { type: 'selector', required: true },
      via: { type: 'selector', required: true },
      kinds: { type: 'strings' },
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
    doc: 'The directed graph of the given relationship kinds has no cycle.',
    params: {
      kinds: { type: 'strings', doc: 'Default: kinds flagged as dependencies.' },
      where: { type: 'edge-filter', doc: 'Only relationships whose property has one of the values, e.g. {"property": "layer", "values": ["current", "target"]}.' },
      within: { type: 'selector' },
    },
  },
  'data-model': {
    kinds: ['structural'],
    doc: 'The data rules hold on the records and copies of the model (src/core/data-model.js): erasure-point, no-principal-in-shared, party-by-id, freshness-bound, holder-reaches-owner. Inconclusive when a listed rule has nothing to check.',
    params: {
      rules: { type: 'strings', doc: 'Rules to check. Default: all five.' },
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
  'lean-theorem': {
    kinds: ['structural', 'invariant', 'temporal', 'requirement'],
    doc: 'A theorem of the Lean core (formal/) states the claim. Lean checks it (tools/lean-theorems.js, recorded by exegra verify): the theorem exists, the kernel accepts its proof again, it depends on no axiom beyond propext, Classical.choice and Quot.sound (no sorry, no native_decide, no axiom of our own), and each named implementation constant occurs in its statement. Proved when all hold; violated when Lean refuses; not evaluated without a recorded check.',
    params: {
      theorem: { type: 'string', required: true, doc: 'The fully qualified theorem name, e.g. Exegra.runInput_terminates.' },
      about: { type: 'strings', doc: 'Implementation constants (compiled definitions) the statement must mention, e.g. Exegra.runInput.' },
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
  'external-evidence': {
    kinds: ['measured', 'structural', 'invariant', 'temporal'],
    doc: 'The model cannot establish this claim. Its status comes only from evidence entities and recorded results of executing them.',
    params: {},
  },
};
