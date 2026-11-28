// The metric-bound claim method (format 2, WG-4715; docs/simulation.md, "Claims over metrics"):
// run each scenario once per run seed in metrics mode, take one statistic per run from the trace's
// measured outputs, decide by the exact binomial test (op and bound) or the sign-test interval
// (approx), and turn the scenarios and the negatives into facts from which Lean decides the status
// (model-holds, violated or inconclusive, never verified or supported). The engine is passed in as a
// function from engine-input text to trace, so this module runs on the WebAssembly engine, the
// native binary or the Lean executable alike.

import { decideStatuses } from './verdict.js';
import { evaluateRuns, parseRational, rat, runSeed, underpowered } from './metric-stats.js';

/** @typedef {import('./metric-stats.js').Rational} Rational */
/** @typedef {import('./metric-stats.js').RunStatistic} RunStatistic */
/** @typedef {(inputText: string) => any} EngineRun */

/**
 * The quantile key of a statistic `p<q>` as the engine reports it: `p90` → `"0.9"`, `p99` →
 * `"0.99"`, `p99.9` → `"0.999"`, `p5` → `"0.05"`.
 * @param {string} st
 */
export function quantileKey(st) {
  const m = /^p(\d+)(?:\.(\d+))?$/.exec(st);
  if (!m) return st;
  const digits = (m[1].padStart(2, '0') + (m[2] ?? '')).replace(/0+$/, '');
  return digits === '100' ? '1' : `0.${digits}`;
}

/**
 * The statistic of one run: from `trace.metrics`, for a metric `{kind, of, statistic}` with kind
 * `utilisation` (statistic `ratio` or `max`), `queue-length` (`ratio`, `mean` or `max`) or
 * `waiting-time` (`mean`, `count`, `max` or `p<q>` with `q` among the input's quantiles).
 * @param {any} trace @param {{kind: string, of: string, statistic: string}} metric
 * @returns {RunStatistic}
 */
export function runStatistic(trace, metric) {
  const seed = String(trace.seed);
  const truncated = trace.truncated === true;
  if (['response-time', 'outcomes', 'throughput', 'false-positives'].includes(metric.kind)) return requestStatistic(trace, metric, seed, truncated);
  if (metric.kind === 'transitions') {
    const c = trace.metrics?.transitions?.[metric.of];
    if (c === undefined) throw new Error(`The run measured no transition "${metric.of}" (write it as <behavior>.<transition>).`);
    return { seed, truncated, value: rat(BigInt(c)) };
  }
  const r = trace.metrics?.resources?.[metric.of];
  if (!r) throw new Error(`The run measured no resource "${metric.of}".`);
  const st = metric.statistic;
  if (metric.kind === 'utilisation') {
    if (st === 'ratio') return { seed, truncated, value: r.utilisation.capacityTime ? rat(BigInt(r.utilisation.busy), BigInt(r.utilisation.capacityTime)) : null };
    if (st === 'max') return { seed, truncated, value: rat(BigInt(r.utilisation.max)) };
  }
  if (metric.kind === 'queue-length') {
    if (st === 'ratio' || st === 'mean') return { seed, truncated, value: r.queueLength.window ? rat(BigInt(r.queueLength.integral), BigInt(r.queueLength.window)) : null };
    if (st === 'max') return { seed, truncated, value: rat(BigInt(r.queueLength.max)) };
  }
  if (metric.kind === 'waiting-time') {
    const w = r.waitingTime;
    const n = w.count;
    if (st === 'count') return { seed, truncated, value: rat(BigInt(n)), samples: n };
    if (st === 'max') return { seed, truncated, samples: n, infinite: w.infinite, value: w.infinite ? 'inf' : w.max === null ? null : rat(BigInt(w.max)) };
    if (st === 'mean') {
      return { seed, truncated, samples: n, infinite: w.infinite, underpowered: underpowered({ statistic: 'mean', n }),
        value: w.infinite || !n ? null : rat(BigInt(w.sum), BigInt(n)) };
    }
    const m = /^p(.+)$/.exec(st);
    if (m) {
      const key = quantileKey(st);
      const q = w.quantiles[key] ?? w.quantiles[m[1]];
      if (!q) throw new Error(`The run did not measure quantile ${key}; add it to the input's metrics.quantiles.`);
      return { seed, truncated, samples: n, infinite: w.infinite, underpowered: underpowered({ statistic: st, n }),
        value: q.empty ? null : q.infinite ? 'inf' : rat(BigInt(q.value)) };
    }
  }
  throw new Error(`Statistic "${st}" is not available for metric kind "${metric.kind}".`);
}

/**
 * The statistic of one run for a request-class metric (docs/simulation.md, "Request lifecycle"):
 * `response-time` (`mean`, `max`, `count` or `p<q>` over every measured request, +∞ for one that
 * did not end `ok`), `outcomes` (`ratio` or `count` of the measured requests with an outcome in
 * `metric.outcomes`, default `ok`), `throughput` (`ratio`: ok requests per second of the window;
 * `count`), `false-positives` (`ratio`: refused among the measured legitimate requests; `count`).
 * @param {any} trace @param {{kind: string, of: string, statistic: string, outcomes?: string[]}} metric
 * @param {string} seed @param {boolean} truncated
 * @returns {RunStatistic}
 */
function requestStatistic(trace, metric, seed, truncated) {
  const c = trace.metrics?.requests?.[metric.of];
  if (!c) throw new Error(`The run measured no request class "${metric.of}".`);
  const st = metric.statistic;
  const n = c.measured;
  // Starts refused as duplicates (a key equal to that of an unended request) make n depend on the system even for
  // an open workload, so a run with any is never left out as underpowered (metric-stats.js, evaluateRuns).
  const duplicates = typeof c.duplicate === 'number' ? c.duplicate : 0;
  if (metric.kind === 'response-time') {
    const w = c.responseTime;
    if (st === 'count') return { seed, truncated, value: rat(BigInt(n)), samples: n };
    if (st === 'max') return { seed, truncated, samples: n, infinite: w.infinite, value: w.infinite ? 'inf' : w.max === null ? null : rat(BigInt(w.max)) };
    if (st === 'mean') {
      return { seed, truncated, samples: n, infinite: w.infinite, underpowered: underpowered({ statistic: 'mean', n }), duplicates,
        value: w.infinite || !n ? null : rat(BigInt(w.sum), BigInt(n)) };
    }
    const m = /^p(.+)$/.exec(st);
    if (m) {
      const key = quantileKey(st);
      const q = w.quantiles[key] ?? w.quantiles[m[1]];
      if (!q) throw new Error(`The run did not measure quantile ${key}; add it to the input's metrics.quantiles.`);
      return { seed, truncated, samples: n, infinite: w.infinite, underpowered: underpowered({ statistic: st, n }), duplicates,
        value: q.empty ? null : q.infinite ? 'inf' : rat(BigInt(q.value)) };
    }
  }
  if (metric.kind === 'outcomes') {
    const set = metric.outcomes ?? ['ok'];
    const k = set.reduce((a, o) => a + (o === 'censored' ? c.outcomes.censored : (c.outcomes[o] ?? 0)), 0);
    if (st === 'count') return { seed, truncated, value: rat(BigInt(k)), samples: n };
    if (st === 'ratio') return { seed, truncated, samples: n, value: n ? rat(BigInt(k), BigInt(n)) : null };
  }
  if (metric.kind === 'throughput') {
    if (st === 'count') return { seed, truncated, value: rat(BigInt(c.outcomes.ok)) };
    const per = { s: 1n, ms: 1000n, us: 1000000n, ns: 1000000000n }[/** @type {string} */ (trace.timeUnit)];
    if (per === undefined) throw new Error(`Throughput needs a time unit with a rate, not "${trace.timeUnit}".`);
    if (st === 'ratio') return { seed, truncated, value: c.window ? rat(BigInt(c.outcomes.ok) * per, BigInt(c.window)) : null };
  }
  if (metric.kind === 'false-positives') {
    const l = c.legitimate;
    if (st === 'count') return { seed, truncated, value: rat(BigInt(l.refused)) };
    if (st === 'ratio') return { seed, truncated, samples: l.measured, value: l.measured ? rat(BigInt(l.refused), BigInt(l.measured)) : null };
  }
  throw new Error(`Statistic "${st}" is not available for metric kind "${metric.kind}".`);
}

/**
 * Whether the metric's request class is open-started in this engine input (docs/simulation.md, "Request
 * lifecycle"): every start entry of the class comes from an open workload, so its sample count depends only on
 * the arrivals. Decided from the declarations, conservatively: the class's named workload is open; or, with no
 * workload named, at least one open workload issues the start event and nothing else can put it in the queue (no
 * closed or population workload issues it, no behavior emits it or names it as a `then`, no scenario step and no
 * fault injects it). Anything else, a metric that is not over a request class included, is not open-started, and
 * an underpowered run of it then counts as not satisfying the bound.
 * @param {any} input a version-2 engine input
 * @param {{kind?: string, of?: string}} metric
 * @returns {boolean}
 */
export function openStartedClass(input, metric) {
  if (!['response-time', 'outcomes', 'throughput', 'false-positives'].includes(String(metric?.kind))) return false;
  const cls = (Array.isArray(input?.requests) ? input.requests : []).find((/** @type {any} */ c) => c?.id === metric.of);
  const event = cls?.start?.event;
  if (typeof event !== 'string') return false;
  const workloads = Array.isArray(input?.workloads) ? input.workloads : [];
  if (typeof cls.start.workload === 'string') {
    const w = workloads.find((/** @type {any} */ x) => x?.id === cls.start.workload);
    return w?.kind === 'open';
  }
  /** @param {any} w */
  const issues = (w) => (w?.kind === 'population' ? w?.start?.event === event : w?.event === event);
  const issuing = workloads.filter(issues);
  if (!issuing.length || issuing.some((/** @type {any} */ w) => w.kind !== 'open')) return false;
  /** Whether any object under `v` has `emit` or `then` equal to the event. @param {any} v @returns {boolean} */
  const emits = (v) => {
    if (Array.isArray(v)) return v.some(emits);
    if (!v || typeof v !== 'object') return false;
    if (v.emit === event || v.then === event || v.then?.event === event) return true;
    return Object.values(v).some(emits);
  };
  if (emits(input.behaviors)) return false;
  if ((Array.isArray(input?.scenario?.steps) ? input.scenario.steps : []).some((/** @type {any} */ s) => s?.event === event)) return false;
  if ((Array.isArray(input?.faults) ? input.faults : []).some((/** @type {any} */ f) => f?.kind === 'inject-event' && f?.event === event)) return false;
  return true;
}

/**
 * Run one scenario input N times with the run seeds of the base seed and evaluate the statistic. Whether the
 * class is open-started is computed from the input (openStartedClass) unless the claim states it.
 * @param {EngineRun} run
 * @param {any} input a version-2 engine input
 * @param {{metric: any, op?: string, bound?: any, approx?: {value: any, tolerance: any},
 *   runs: number, fraction: any, confidence: any, seed: string, openStarted?: boolean}} claim
 */
export function evaluateScenario(run, input, claim) {
  /** @type {RunStatistic[]} */
  const stats = [];
  for (let r = 0; r < claim.runs; r++) {
    const seeded = { ...input, scenario: { ...input.scenario, seed: runSeed(claim.seed, r), output: 'metrics' } };
    const trace = run(JSON.stringify(seeded));
    stats.push(runStatistic(trace, claim.metric));
  }
  const spec = {
    op: claim.op,
    bound: claim.bound === undefined ? undefined : parseRational(claim.bound),
    approx: claim.approx ? { value: parseRational(claim.approx.value), tolerance: parseRational(claim.approx.tolerance) } : undefined,
    fraction: parseRational(claim.fraction ?? '0.95'),
    confidence: parseRational(claim.confidence ?? '0.95'),
    openStarted: typeof claim.openStarted === 'boolean' ? claim.openStarted : openStartedClass(input, claim.metric),
  };
  return { ...evaluateRuns(stats, spec), openStarted: spec.openStarted, seeds: stats.map((s) => s.seed), statistics: stats };
}

/**
 * Evaluate a metric-bound claim: run every scenario, negative and control negative and test each. The claim's
 * status is not decided here: it is decided in Lean from the facts these results make (metricVerdictInput), the
 * claim holding only when every scenario holds, every negative fails and every control negative holds.
 * @param {EngineRun} run
 * @param {{scenarios: any[], negatives?: any[], controlNegatives?: any[]}} inputs engine inputs
 * @param {Parameters<typeof evaluateScenario>[2]} claim
 */
export function evaluateMetricClaim(run, inputs, claim) {
  const scenarios = inputs.scenarios.map((i) => evaluateScenario(run, i, claim));
  const negatives = (inputs.negatives ?? []).map((i) => evaluateScenario(run, i, claim));
  const controlNegatives = (inputs.controlNegatives ?? []).map((i) => evaluateScenario(run, i, claim));
  return { scope: 'model only; parameters as stated', runs: claim.runs, fraction: String(claim.fraction ?? '0.95'), confidence: String(claim.confidence ?? '0.95'), scenarios, negatives, controlNegatives };
}

/**
 * The facts a metric claim's results make, for the Lean verdict (src/core/verdict.js): the claim is the
 * conjunction of one part per scenario (its statistical test passed, failed or could not decide), per negative
 * (passed when the negative fails, as it must; undecided otherwise) and per control negative (passed when it
 * holds). The first part is named after the claim, so that facts about the claim as a whole can target it.
 * @param {{scenarios: {verdict: string}[], negatives: {verdict: string}[], controlNegatives: {verdict: string}[]}} result
 * @param {string} claimId @param {string[]} [assumptions] @param {string} [stamp] the model's semantic hash
 * @returns {{claim: import('./verdict.js').VerdictClaim, facts: import('./verdict.js').Fact[], parts: {id: string, role: string, index: number}[]}}
 */
export function metricVerdictInput(result, claimId, assumptions = [], stamp = 'model') {
  /** @type {{id: string, role: string, index: number, outcome: import('./verdict.js').FactOutcome}[]} */
  const parts = [];
  const outcome = (/** @type {string} */ v, /** @type {string} */ wanted) => (v === wanted ? 'pass' : v === 'fails' && wanted === 'holds' ? 'fail' : 'undecided');
  result.scenarios.forEach((s, i) => parts.push({ id: i === 0 ? claimId : `${claimId}#scenario-${i}`, role: 'scenario', index: i, outcome: outcome(s.verdict, 'holds') }));
  result.negatives.forEach((s, i) => parts.push({ id: `${claimId}#negative-${i}`, role: 'negative', index: i, outcome: s.verdict === 'fails' ? 'pass' : 'undecided' }));
  result.controlNegatives.forEach((s, i) => parts.push({ id: `${claimId}#control-${i}`, role: 'control', index: i, outcome: s.verdict === 'holds' ? 'pass' : 'undecided' }));
  if (!parts.length) parts.push({ id: claimId, role: 'scenario', index: 0, outcome: 'undecided' });
  return {
    claim: { all: parts.map((p) => ({ part: p.id, subject: /** @type {const} */ ('model'), assumptions })) },
    facts: parts.map((p) => ({ kind: /** @type {const} */ ('statistical'), subject: /** @type {const} */ ('model'), target: { part: p.id }, stamps: { recorded: stamp, current: stamp }, outcome: p.outcome })),
    parts: parts.map(({ id, role, index }) => ({ id, role, index })),
  };
}

/**
 * The Lean verdict of a metric claim's results on their own (no evidence, no assumptions): what the fixtures check.
 * @param {Parameters<typeof metricVerdictInput>[0]} result
 */
export function metricVerdict(result) {
  const input = metricVerdictInput(result, 'metric-claim');
  return decideStatuses([{ claim: input.claim, facts: input.facts }])[0];
}
