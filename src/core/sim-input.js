// The engine input: everything the simulation engine reads for one scenario run, as a plain
// JSON document, and nothing else. It holds no JSONC, meta-model, layout or validation state, so
// an engine in any language can run from it alone. Pure; no I/O.
// Format "exegra-sim-input", version 2; see docs/simulation.md, "Engine input and trace format".
// A scenario that uses a construct of format 2 (workloads, a seed or horizon, instances, resource,
// timer or link effects) derives its times in its `timeUnit` (simulationInputV2; docs/simulation.md,
// "Specification-level form"); any other scenario counts time in logical ticks (unit `tick`), with
// every number as the scenario gives it. Format 1 no longer exists (WG-5681).

import { lowerDistribution, unitExponentialTable } from './distributions.js';
import { unsharedText } from './codegen-model.js';

import { retryDelay } from './fault-model.js';
import { poolMachines } from './pools.js';

/** @typedef {import('./types.js').Model} Model */

/**
 * @typedef {{id:string, from:string, to:string, on:string, guard:string|null, effects:any[], faultOnly:boolean}} InputTransition
 * @typedef {{id:string, subject:string, initial:string, types?:Record<string, string>, variables:{name:string, initial:any}[], states:string[], transitions:InputTransition[]}} InputBehavior
 * @typedef {{id:string, kind:string, event?:string, transition?:string, occurrence?:number, by?:number, at?:number, payload?:Record<string, any>}} InputFault
 * @typedef {{format:'exegra-sim-input', version:2, time?:{unit:string, perSecond:number|null},
 *   scenario:{id:string, steps:{at:number, event:string, payload:Record<string, any>}[], faults:string[], stepLimit:number},
 *   behaviors:InputBehavior[], events:{id:string}[], faults:InputFault[]}} SimulationInput
 */

export const SIM_INPUT_FORMAT = 'exegra-sim-input';

const INT_TYPES = ['u8', 'u16', 'u32', 'u64', 'i32', 'i64'];

/**
 * The type a declared type name stands for in evaluation (WG-4902, docs/semantics.md, "Numbers"):
 * an integer type name, `option`, or the name itself (which the engines treat as untyped). A
 * timestamp is an `i64` and a duration a `u64` (milliseconds, as generated code holds them); a
 * declared id or scalar type is its representation.
 * @param {Model} model @param {any} name @param {number} [depth]
 * @returns {string|undefined}
 */
export function evalTypeOf(model, name, depth = 0) {
  if (typeof name !== 'string') return undefined;
  const t = unsharedText(name);
  if (INT_TYPES.includes(t)) return t;
  if (t === 'timestamp') return 'i64';
  if (t === 'duration') return 'u64';
  if (/^option\s*</.test(t)) return 'option';
  const decl = model.entities.get(t);
  if (decl && decl.kind === 'type' && depth < 8) {
    const d = /** @type {any} */ (decl.data);
    if ((d.kind === 'id' || d.kind === 'scalar') && typeof d.repr === 'string') return evalTypeOf(model, d.repr, depth + 1);
  }
  return t;
}

/**
 * The declared types of the references an implementation-level behavior's expressions read, by
 * dotted path (`types` of a behavior in the engine input, WG-4902): `time` (an `i64`), each
 * variable with a `repr`, and `event.<field>` for each payload field of the events it receives
 * (`option` for an optional field). A field that two received events declare with different
 * types is left out. A model-level behavior has none: its numbers are untyped doubles.
 * @param {Model} model @param {string} bid
 * @returns {Record<string, string>}
 */
export function behaviorTypes(model, bid) {
  const b = model.entities.get(bid);
  /** @type {Record<string, string>} */
  const out = {};
  if (!b || b.kind !== 'behavior' || /** @type {any} */ (b.data).level !== 'implementation') return out;
  out.time = 'i64';
  for (const v of Array.isArray(b.data.variables) ? b.data.variables : []) {
    const t = evalTypeOf(model, v?.repr);
    if (typeof v?.name === 'string' && t !== undefined) out[v.name] = t;
  }
  /** @type {Set<string>} */
  const conflicting = new Set();
  const received = new Set((model.byKind.transition ?? []).filter((t) => t.owner === bid).map((t) => t.data.on));
  for (const eid of received) {
    const ev = model.entities.get(eid);
    const payload = ev && ev.kind === 'event' && Array.isArray(/** @type {any} */ (ev.data).payload) ? /** @type {any} */ (ev.data).payload : [];
    for (const f of payload) {
      if (typeof f?.name !== 'string') continue;
      const t = f.optional === true ? 'option' : evalTypeOf(model, f.type);
      if (t === undefined) continue;
      const key = `event.${f.name}`;
      if (key in out && out[key] !== t) conflicting.add(key);
      else out[key] = t;
    }
  }
  for (const k of conflicting) delete out[k];
  return out;
}
/** The engine input format's version: 2 (format 1 is gone, WG-5681). */
export const SIM_INPUT_VERSION = 2;

/** Fields of an effect the engine reads. */
const EFFECT_KEYS = ['set', 'to', 'emit', 'after', 'payload'];
/** Fields of a fault the engine reads (besides its id). */
const FAULT_KEYS = ['kind', 'event', 'transition', 'occurrence', 'by', 'at', 'payload'];

/** @param {any} o @param {string} k */
const hasOwn = (o, k) => Object.prototype.hasOwnProperty.call(o, k);

/** JSON copy of a value: plain data only. @template T @param {T} v @returns {T} */
function copy(v) {
  return v === undefined ? v : JSON.parse(JSON.stringify(v));
}

/** @param {any} fx */
function inputEffect(fx) {
  if (!fx || typeof fx !== 'object' || Array.isArray(fx)) return copy(fx);
  /** @type {Record<string, any>} */
  const out = {};
  // An emit's `to` names a receiver outside the model (implementation level, declarative): not engine input.
  for (const k of EFFECT_KEYS) if (hasOwn(fx, k) && fx[k] !== undefined && !(k === 'to' && hasOwn(fx, 'emit'))) out[k] = copy(fx[k]);
  return out;
}

/**
 * Derive the engine input for one scenario run. `faults`, when given, replaces the scenario's
 * own fault list, as `runScenario(model, id, {faults})` (engine.js) does. Throws for a scenario,
 * behavior, event or fault that does not exist, before any engine runs.
 * @param {Model} model
 * @param {string} scenarioId
 * @param {string[]} [faults]
 * @returns {SimulationInput}
 */
export function simulationInput(model, scenarioId, faults) {
  const scenario = model.entities.get(scenarioId);
  if (!scenario || scenario.kind !== 'scenario') throw new Error(`"${scenarioId}" is not a scenario in this model.`);
  const sdata = scenario.data;
  const behaviorIds = Array.isArray(sdata.behaviors) ? sdata.behaviors.slice() : [];

  const allTransitions = model.byKind.transition ?? [];
  /** @type {InputBehavior[]} */
  const behaviors = behaviorIds.map((/** @type {string} */ bid) => {
    const b = model.entities.get(bid);
    if (!b || b.kind !== 'behavior') throw new Error(`Scenario "${scenarioId}" lists "${bid}", which is not a behavior.`);
    const types = behaviorTypes(model, bid);
    return {
      id: bid,
      subject: b.data.subject,
      initial: b.data.initial,
      ...(Object.keys(types).length ? { types } : {}),
      variables: (Array.isArray(b.data.variables) ? b.data.variables : []).map((/** @type {any} */ v) => ({ name: v.name, initial: copy(v.initial) })),
      states: (model.byKind.state ?? []).filter((s) => s.owner === bid).map((s) => s.id),
      transitions: allTransitions.filter((t) => t.owner === bid).map((t) => ({
        id: t.id,
        from: t.data.from,
        to: t.data.to,
        on: t.data.on,
        guard: typeof t.data.guard === 'string' ? t.data.guard : null,
        effects: (Array.isArray(t.data.effects) ? t.data.effects : []).map(inputEffect),
        faultOnly: t.data.faultOnly === true,
      })),
    };
  });

  // A quota pool the scenario lists runs as the machines its meaning derives (src/core/pools.js), after the
  // scenario's behaviors.
  for (const pid of Array.isArray(sdata.pools) ? sdata.pools : []) {
    const p = model.entities.get(pid);
    if (!p || p.kind !== 'quotaPool') throw new Error(`Scenario "${scenarioId}" lists "${pid}", which is not a quota pool.`);
    behaviors.push(...poolMachines(model, pid));
  }

  const faultIds = [...new Set(faults ?? sdata.faults ?? [])];
  /** @type {InputFault[]} */
  const faultDecls = faultIds.map((id) => {
    const f = model.entities.get(/** @type {string} */ (id));
    if (!f || f.kind !== 'fault') throw new Error(`"${id}" is not a fault in this model.`);
    /** @type {Record<string, any>} */
    const out = { id };
    for (const k of FAULT_KEYS) if (hasOwn(f.data, k) && f.data[k] !== undefined) out[k] = copy(f.data[k]);
    return /** @type {InputFault} */ (out);
  });

  const steps = (Array.isArray(sdata.steps) ? sdata.steps : []).map((/** @type {any} */ st, /** @type {number} */ i) => {
    const ev = model.entities.get(st.event);
    if (!ev || ev.kind !== 'event') throw new Error(`Scenario "${scenarioId}" step ${i} delivers "${st.event}", which is not an event.`);
    return { at: st.at, event: st.event, payload: copy(st.payload ?? {}) };
  });
  for (const f of faultDecls) {
    if (f.kind !== 'inject-event') continue;
    const ev = model.entities.get(/** @type {string} */ (f.event));
    if (!ev || ev.kind !== 'event') throw new Error(`Fault "${f.id}" injects "${f.event}", which is not an event.`);
  }

  /** The fields every version-2 input shares, before units and format-2 constructs. */
  const v1 = {
    format: SIM_INPUT_FORMAT,
    version: SIM_INPUT_VERSION,
    scenario: { id: scenarioId, steps, faults: faultIds, stepLimit: sdata.maxSteps ?? 1000 },
    behaviors,
    events: (model.byKind.event ?? []).map((e) => ({ id: e.id })),
    faults: faultDecls,
  };
  if (needsTimedInput(model, sdata) || faultDecls.some((f) => FORMAT2_FAULTS.includes(/** @type {string} */ (f.kind)))) return simulationInputV2(model, scenarioId, v1);
  // A scenario with no format-2 construct counts time in logical ticks: every number as it is.
  return /** @type {SimulationInput} */ ({ ...v1, version: SIM_INPUT_VERSION, time: { unit: 'tick', perSecond: null } });
}

/**
 * The fault kinds only format 2 has (WG-4903): a scenario with one of them derives version 2.
 * Each acts as the runtime would: duplicate-event delivers and queues a copy `by` later, lose-event
 * drops, retry-event delays by the retry backoff after `attempts` failures (docs/semantics.md).
 */
export const FORMAT2_FAULTS = ['duplicate-event', 'lose-event', 'retry-event'];

// ---------------------------------------------------------------------------
// Format 2 (docs/simulation.md, "Specification-level form")
// ---------------------------------------------------------------------------

export const SIM_INPUT_VERSION_2 = 2;

/** Base units per second of each time unit. */
const PER_SECOND = /** @type {Record<string, bigint|null>} */ ({ tick: null, s: 1n, ms: 1000n, us: 1000000n, ns: 1000000000n });
/** Nanoseconds per duration unit. */
const NS = /** @type {Record<string, bigint>} */ ({ ns: 1n, us: 1000n, ms: 1000000n, s: 1000000000n, min: 60000000000n, h: 3600000000000n });
/** Bytes per size unit. */
const BYTES = /** @type {Record<string, bigint>} */ ({ B: 1n, kB: 1000n, MB: 1000000n, GB: 1000000000n, KiB: 1024n, MiB: 1048576n, GiB: 1073741824n });
/** Bytes per second of each bandwidth unit, as [num, den]. */
const BANDWIDTH = /** @type {Record<string, [bigint, bigint]>} */ ({
  'bit/s': [1n, 8n], 'kbit/s': [1000n, 8n], 'Mbit/s': [1000000n, 8n], 'Gbit/s': [1000000000n, 8n],
  'B/s': [1n, 1n], 'kB/s': [1000n, 1n], 'MB/s': [1000000n, 1n], 'GB/s': [1000000000n, 1n],
});
const RATE_PER = /** @type {Record<string, bigint>} */ ({ s: 1n, min: 60n, h: 3600n });

/** @param {bigint} a @param {bigint} b @returns {bigint} */
const gcdBig = (a, b) => (b === 0n ? a : gcdBig(b, a % b));

/** An exact decimal as [num, den]. @param {string} s @param {string} what */
function decimal(s, what) {
  const m = /^(\d+)(?:\.(\d+))?$/.exec(s);
  if (!m) throw new Error(`${what}: "${s}" is not an exact non-negative decimal.`);
  const frac = m[2] ?? '';
  return [BigInt(m[1] + frac), 10n ** BigInt(frac.length)];
}

/**
 * A duration `"<decimal> <unit>"` in whole base units of `unit`. A bare number is already in base
 * units.
 * @param {any} v @param {string} unit @param {string} what
 * @returns {number}
 */
export function durationIn(v, unit, what) {
  if (typeof v === 'number' && Number.isInteger(v) && v >= 0) return v;
  const m = typeof v === 'string' ? /^(\S+)\s*(ns|us|ms|s|min|h)$/.exec(v.trim()) : null;
  if (!m) throw new Error(`${what}: "${v}" is not a duration ("<decimal> <unit>", unit ns, us, ms, s, min or h).`);
  const [n, d] = decimal(m[1], what);
  if (unit === 'tick') throw new Error(`${what}: unit tick has no duration; "${v}" needs a time unit.`);
  const num = n * NS[m[2]];
  const den = d * NS[unit];
  if (num % den !== 0n) throw new Error(`${what}: "${v}" is not a whole number of ${unit}.`);
  const x = num / den;
  if (x >= 2n ** 53n) throw new Error(`${what}: "${v}" is 2^53 base units or more.`);
  return Number(x);
}

/** A rate `"<decimal>/<s|min|h>"` as an exact `{num, den}` per second. @param {any} v @param {string} what */
export function rateOf(v, what) {
  if (v && typeof v === 'object' && 'num' in v) return v;
  const m = typeof v === 'string' ? /^(\S+)\s*\/\s*(s|min|h)$/.exec(v.trim()) : null;
  if (!m) throw new Error(`${what}: "${v}" is not a rate ("<decimal>/s", "/min" or "/h").`);
  const [n, d] = decimal(m[1], what);
  const den = d * RATE_PER[m[2]];
  const g = gcdBig(n, den) || 1n;
  return { num: Number(n / g), den: Number(den / g) };
}

/** A size `"<decimal> <unit>"` in bytes. @param {any} v @param {string} what */
function sizeOf(v, what) {
  if (typeof v === 'number') return v;
  const m = typeof v === 'string' ? /^(\S+)\s*(B|kB|MB|GB|KiB|MiB|GiB)$/.exec(v.trim()) : null;
  if (!m) throw new Error(`${what}: "${v}" is not a size.`);
  const [n, d] = decimal(m[1], what);
  const x = n * BYTES[m[2]];
  if (x % d !== 0n) throw new Error(`${what}: "${v}" is not a whole number of bytes.`);
  return Number(x / d);
}

/** A bandwidth `"<decimal> <unit>"` in whole bytes per second (rounded down). @param {any} v @param {string} what */
function bandwidthOf(v, what) {
  if (typeof v === 'number') return v;
  const m = typeof v === 'string' ? /^(\S+)\s*(bit\/s|kbit\/s|Mbit\/s|Gbit\/s|B\/s|kB\/s|MB\/s|GB\/s)$/.exec(v.trim()) : null;
  if (!m) throw new Error(`${what}: "${v}" is not a bandwidth.`);
  const [n, d] = decimal(m[1], what);
  const [a, b] = BANDWIDTH[m[2]];
  return Number((n * a) / (d * b));
}

/**
 * A distribution as written in a specification, lowered to the engine's integer form: a duration
 * (fixed), `{constant}`, `{uniform: {lo, hi}}`, `{exponential: {mean}}`, `{lognormal: {median,
 * p99 | sigma}}`, `{empirical: {samples} | {quantiles}}`, with durations in any unit; or an engine
 * distribution (`{kind}`) as it is.
 * @param {any} d @param {string} unit @param {string} what
 */
export function lowerSpecDistribution(d, unit, what) {
  if (d === undefined || d === null) return undefined;
  if (typeof d === 'number' || typeof d === 'string') return { kind: 'fixed', value: durationIn(d, unit, what) };
  if (typeof d !== 'object' || 'kind' in d) return d;
  const dur = (/** @type {any} */ x) => String(durationIn(x, unit, what));
  if ('constant' in d) return lowerDistribution({ constant: dur(d.constant) }, what);
  if ('uniform' in d) return lowerDistribution({ uniform: { lo: dur(d.uniform.lo), hi: dur(d.uniform.hi) } }, what);
  if ('exponential' in d) return lowerDistribution({ exponential: { mean: dur(d.exponential.mean) } }, what);
  if ('lognormal' in d) {
    const l = d.lognormal;
    return lowerDistribution({ lognormal: { median: dur(l.median), ...(l.p99 !== undefined ? { p99: dur(l.p99) } : { sigma: l.sigma }) } }, what);
  }
  if ('empirical' in d) {
    const e = d.empirical;
    return lowerDistribution({ empirical: e.samples ? { samples: e.samples.map(dur) } : { quantiles: e.quantiles.map((/** @type {any[]} */ [p, x]) => [p, dur(x)]) } }, what);
  }
  throw new Error(`${what}: unknown distribution.`);
}

/** Effects that only format 2 has. */
const V2_EFFECTS = ['use', 'acquire', 'release', 'timer', 'cancel', 'via'];

/**
 * Whether a scenario needs the timed version-2 input (simulationInputV2: times in base units of its
 * `timeUnit`, instances, resources, workloads): it names workloads, a seed or a horizon, or one of its
 * behaviors has instances or one of the effects only that input has. Every other scenario derives a
 * version-2 input that counts time in logical ticks (format 1 is gone, WG-5681).
 * @param {Model} model @param {any} sdata
 */
export function needsTimedInput(model, sdata) {
  if ((Array.isArray(sdata.workloads) && sdata.workloads.length) || sdata.seed !== undefined || sdata.horizon !== undefined) return true;
  for (const fid of Array.isArray(sdata.faults) ? sdata.faults : []) if (FORMAT2_FAULTS.includes(model.entities.get(fid)?.data?.kind)) return true;
  for (const bid of sdata.behaviors ?? []) {
    const b = model.entities.get(bid);
    if (b?.data?.instances) return true;
    for (const t of (model.byKind.transition ?? []).filter((x) => x.owner === bid)) {
      for (const fx of t.data.effects ?? []) if (fx && typeof fx === 'object' && V2_EFFECTS.some((k) => k in fx)) return true;
    }
  }
  return false;
}

/**
 * The time unit an implementation-level machine's bare numbers are in (WG-4902, docs/semantics.md,
 * "Time"): the unit of the scenarios that run it. A timed scenario's unit is its `timeUnit`, by default
 * `us`; a tick-counted scenario that names a `timeUnit` has that unit, and one that names none constrains
 * nothing. With no constraining scenario the unit is `ms`, the unit of generated code's clock. When the
 * scenarios disagree, `units` lists every unit found and `unit` is the first.
 * @param {Model} model @param {string} bid
 * @returns {{unit: string, units: string[], scenarios: string[]}}
 */
export function machineTimeUnit(model, bid) {
  /** @type {string[]} */
  const units = [];
  /** @type {string[]} */
  const scenarios = [];
  for (const s of model.byKind.scenario ?? []) {
    const d = /** @type {any} */ (s.data);
    if (!Array.isArray(d.behaviors) || !d.behaviors.includes(bid)) continue;
    const u = typeof d.timeUnit === 'string' ? d.timeUnit : needsTimedInput(model, d) ? 'us' : undefined;
    if (u === undefined) continue;
    scenarios.push(s.id);
    if (!units.includes(u)) units.push(u);
  }
  return { unit: units[0] ?? 'ms', units, scenarios };
}

/** Nanoseconds per unit of a scenario clock. */
export const UNIT_NS = Object.freeze({ ns: 1, us: 1000, ms: 1000000, s: 1000000000 });

/** The instances the engine reads: `storedIn` is implementation-level and declarative. @param {any} inst */
function engineInstances(inst) {
  const out = copy(inst);
  if (out && typeof out === 'object') delete out.storedIn;
  return out;
}

/** @param {any} fx @param {string} unit @param {string} what */
function effectV2(fx, unit, what) {
  if (!fx || typeof fx !== 'object' || Array.isArray(fx)) return copy(fx);
  const out = copy(fx);
  for (const k of ['source', 'note', 'description']) delete out[k];
  if ('emit' in out && !('timer' in out)) delete out.to;
  if ('demand' in out) out.demand = lowerSpecDistribution(out.demand, unit, `${what}.demand`);
  if ('emit' in out && !('timer' in out) && 'after' in out) out.after = lowerSpecDistribution(out.after, unit, `${what}.after`);
  // A delay read at run time ({expr, simulate}) is simulated with its simulate delay.
  if ('timer' in out && 'after' in out) out.after = lowerSpecDistribution(out.after && typeof out.after === 'object' && 'expr' in out.after ? out.after.simulate : out.after, unit, `${what}.after`);
  if ('size' in out && typeof out.size === 'object') out.size = lowerSpecDistribution(out.size, unit, `${what}.size`);
  else if ('size' in out && typeof out.size === 'string' && /^\S+\s*(B|kB|MB|GB|KiB|MiB|GiB)$/.test(out.size)) out.size = sizeOf(out.size, `${what}.size`);
  if ('to' in out && out.to && typeof out.to === 'object' && 'sample' in out.to) out.to = { sample: lowerSpecDistribution(out.to.sample, unit, `${what}.to.sample`) };
  return out;
}

/**
 * The version-2 engine input of a scenario (docs/simulation.md, "Specification-level form"): the
 * shared fields with times in whole base units of the scenario's `timeUnit` (default `us`),
 * behaviors with their instances and format-2 effects, the routes, resources, links, workloads and
 * request classes the model declares, the scenario's seed, horizon, warm-up and stop time, and
 * distributions lowered to integer tables (`src/core/distributions.js`). Throws on a malformed
 * unit, rate or distribution, before any engine runs.
 * @param {Model} model @param {string} scenarioId @param {any} v1 the fields every version-2 input of the scenario shares
 * @returns {any}
 */
export function simulationInputV2(model, scenarioId, v1) {
  const sdata = /** @type {any} */ (model.entities.get(scenarioId)).data;
  const unit = typeof sdata.timeUnit === 'string' ? sdata.timeUnit : 'us';
  if (!(unit in PER_SECOND)) throw new Error(`Scenario "${scenarioId}": unknown time unit "${unit}".`);
  const ps = PER_SECOND[unit];
  const dur = (/** @type {any} */ v, /** @type {string} */ what) => durationIn(v, unit, what);
  const opt = (/** @type {any} */ v, /** @type {string} */ what) => (v === undefined || v === null ? null : dur(v, what));
  const behaviors = v1.behaviors.map((/** @type {any} */ b) => {
    const e = /** @type {any} */ (model.entities.get(b.id));
    return {
      ...b,
      ...(e.data.instances ? { instances: engineInstances(e.data.instances) } : {}),
      transitions: b.transitions.map((/** @type {any} */ t) => {
        const te = /** @type {any} */ (model.entities.get(t.id));
        return { ...t, effects: (Array.isArray(te?.data?.effects) ? te.data.effects : []).map((/** @type {any} */ fx, /** @type {number} */ k) => effectV2(fx, unit, `${t.id}.effects[${k}]`)) };
      }),
    };
  });
  const horizon = opt(sdata.horizon, `${scenarioId}.horizon`);
  const resources = (model.byKind.resource ?? []).map((r) => {
    const d = /** @type {any} */ (r.data);
    return {
      id: r.id, kind: d.kind ?? 'pool', capacity: d.capacity, discipline: d.discipline ?? 'fifo', queueBound: d.queueBound ?? null,
      overflow: d.overflow ?? 'refuse',
      demandFactor: d.demandFactor?.usl
        ? { usl: { alpha: ratPair(d.demandFactor.usl.alpha), beta: ratPair(d.demandFactor.usl.beta) } }
        : (d.demandFactor ?? null),
      classes: (Array.isArray(d.classes) ? d.classes : []).map((/** @type {any} */ c) => ({
        id: c.id, priority: c.priority ?? 0, reserved: c.reserved ?? 0, limit: c.limit ?? null, queueBound: c.queueBound ?? null,
        maxWait: opt(c.maxWait, `${r.id}.${c.id}.maxWait`),
      })),
    };
  });
  const links = (model.byKind.link ?? []).map((l) => {
    const d = /** @type {any} */ (l.data);
    return {
      id: l.id, from: d.from, to: d.to, latency: lowerSpecDistribution(d.latency, unit, `${l.id}.latency`) ?? { kind: 'fixed', value: 0 },
      bandwidth: d.bandwidth === undefined ? null : bandwidthOf(d.bandwidth, `${l.id}.bandwidth`),
      queueBound: d.queueBound ?? null, ordered: d.ordered === true, fanout: d.fanout === true,
    };
  });
  const wanted = Array.isArray(sdata.workloads) ? sdata.workloads : [];
  const workloads = wanted.map((/** @type {string} */ wid) => {
    const w = model.entities.get(wid);
    if (!w || w.kind !== 'workload') throw new Error(`Scenario "${scenarioId}" names "${wid}", which is not a workload.`);
    const d = /** @type {any} */ (w.data);
    /** @type {any} */
    const out = { id: wid, kind: d.kind ?? 'open' };
    for (const k of ['event', 'legitimate', 'maxArrivals', 'requestField', 'clientField', 'addressField', 'reply', 'population', 'behavior', 'count'])
      if (d[k] !== undefined) out[k] = copy(d[k]);
    if (d.payload) out.payload = Object.fromEntries(Object.entries(d.payload).map(([k, v]) => [k, v && typeof v === 'object' && 'sample' in /** @type {any} */ (v)
      ? { sample: lowerSpecDistribution(/** @type {any} */ (v).sample, unit, `${wid}.payload.${k}`) } : copy(v)]));
    if (out.kind === 'open') {
      out.process = d.process ?? 'poisson';
      out.phases = Array.isArray(d.phases)
        ? d.phases.map((/** @type {any} */ p, /** @type {number} */ i) => ({ from: dur(p.from, `${wid}.phases[${i}].from`), until: dur(p.until, `${wid}.phases[${i}].until`),
          rate: p.rate && typeof p.rate === 'object' && 'from' in p.rate ? { from: rateOf(p.rate.from, wid), to: rateOf(p.rate.to, wid) } : rateOf(p.rate, wid) }))
        : [{ from: 0, until: horizon ?? 0, rate: rateOf(d.rate, `${wid}.rate`) }];
      if (d.repeat !== undefined) out.repeat = dur(d.repeat, `${wid}.repeat`);
      if (d.batch !== undefined) out.batch = lowerSpecDistribution(d.batch, 'tick', `${wid}.batch`);
      if (d.clients) {
        out.clients = { count: d.clients.count, ...(d.clients.pick ? { pick: d.clients.pick } : {}) };
        if (d.clients.addresses) out.clients.addresses = { groupSize: lowerSpecDistribution(d.clients.addresses.groupSize, 'tick', `${wid}.groupSize`) };
      }
    } else if (out.kind === 'closed') {
      if (d.think !== undefined) out.think = lowerSpecDistribution(d.think, unit, `${wid}.think`);
      if (d.start !== undefined) out.start = lowerSpecDistribution(d.start, unit, `${wid}.start`);
      if (d.timeout !== undefined) out.timeout = dur(d.timeout, `${wid}.timeout`);
    } else if (out.kind === 'population') {
      out.start = { event: d.start?.event, ...(d.start?.at !== undefined ? { at: lowerSpecDistribution(d.start.at, unit, `${wid}.start.at`) } : {}) };
    }
    return out;
  });
  const requests = (model.byKind.requestClass ?? []).map((c) => ({ id: c.id, start: copy(/** @type {any} */ (c.data).start), key: /** @type {any} */ (c.data).key, ends: copy(/** @type {any} */ (c.data).ends ?? []) }));
  const faults = v1.faults.map((/** @type {any} */ f) => {
    const e = /** @type {any} */ (model.entities.get(f.id)).data;
    const out = { ...f };
    if (out.by !== undefined) out.by = dur(out.by, `${f.id}.by`);
    // A duplicate's second delivery comes `by` later (default at once); a retry is delayed by the
    // runtime's backoff after `attempts` failed dispatches (fault-model.js, retryDelay).
    if (out.kind === 'duplicate-event' && out.by === undefined) out.by = 0;
    if (out.kind === 'retry-event') out.by = retryDelay(model, e.attempts, unit);
    if (out.at !== undefined) out.at = dur(out.at, `${f.id}.at`);
    for (const k of ['resource', 'class', 'capacity', 'limit', 'num', 'den', 'behavior', 'effect']) if (e[k] !== undefined) out[k] = copy(e[k]);
    if (e.demand !== undefined) out.demand = lowerSpecDistribution(e.demand, unit, `${f.id}.demand`);
    if (e.window) out.window = { at: dur(e.window.at, `${f.id}.window.at`), ...(e.window.until !== undefined ? { until: dur(e.window.until, `${f.id}.window.until`) } : {}) };
    return out;
  });
  /** @type {any} */
  const input = {
    format: SIM_INPUT_FORMAT,
    version: SIM_INPUT_VERSION_2,
    time: { unit, perSecond: ps === null ? null : Number(ps) },
    scenario: {
      ...v1.scenario,
      steps: v1.scenario.steps.map((/** @type {any} */ st, /** @type {number} */ i) => ({ ...st, at: dur(st.at, `${scenarioId}.steps[${i}].at`) })),
      seed: sdata.seed === undefined ? null : String(sdata.seed),
      horizon, warmup: opt(sdata.warmup, `${scenarioId}.warmup`), stopAt: opt(sdata.stopAt, `${scenarioId}.stopAt`),
      output: sdata.output ?? 'trace',
    },
    behaviors,
    events: v1.events,
    faults,
    routes: copy(Array.isArray(sdata.routes) ? sdata.routes : []),
    resources,
    links,
    workloads,
    requests,
  };
  if (sdata.metrics) input.metrics = copy(sdata.metrics);
  if (workloads.some((/** @type {any} */ w) => w.process === 'poisson')) input.unitExponential = unitExponentialTable();
  return input;
}

/** A USL parameter as `[num, den]` from an exact decimal or a pair. @param {any} v */
function ratPair(v) {
  if (Array.isArray(v)) return v;
  const [n, d] = decimal(String(v), 'demandFactor');
  const g = gcdBig(n, d) || 1n;
  return [Number(n / g), Number(d / g)];
}
