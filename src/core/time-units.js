// Time units and declared types as validation, readiness and the claim methods read them: the unit a
// scenario counts time in, the unit an implementation-level machine's bare numbers are in, durations in
// base units, and the evaluation type of a declared type name. The lowering of a scenario to its engine
// input is not here: it is in Lean (formal/Exegra/Lower.lean, Exegra.Lower.engineInput, WG-5683), called
// through src/core/engine.js (engineInput); these helpers follow the same rules (docs/simulation.md,
// "Specification-level form") for the diagnostics that run before any engine does. Pure; no I/O.

import { unsharedText } from './codegen-model.js';

/** @typedef {import('./types.js').Model} Model */

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
 * The fault kinds only the timed input has (WG-4903): a scenario with one of them counts time in its
 * `timeUnit`.
 */
export const FORMAT2_FAULTS = ['duplicate-event', 'lose-event', 'retry-event'];

/** Effects that only the timed input has. */
const V2_EFFECTS = ['use', 'acquire', 'release', 'timer', 'cancel', 'via'];

/** Nanoseconds per duration unit. */
const NS = /** @type {Record<string, bigint>} */ ({ ns: 1n, us: 1000n, ms: 1000000n, s: 1000000000n, min: 60000000000n, h: 3600000000000n });

/** An exact decimal as [num, den]. @param {string} s @param {string} what */
function decimal(s, what) {
  const m = /^(\d+)(?:\.(\d+))?$/.exec(s);
  if (!m) throw new Error(`${what}: "${s}" is not an exact non-negative decimal.`);
  const frac = m[2] ?? '';
  return [BigInt(m[1] + frac), 10n ** BigInt(frac.length)];
}

/**
 * A duration `"<decimal> <unit>"` in whole base units of `unit`, as the lowering derives it. A bare
 * number is already in base units.
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

/**
 * Whether a scenario counts time in its `timeUnit` (the timed input): it names workloads, a seed or a
 * horizon, one of its faults is a duplicate, lose or retry fault, or one of its behaviors has instances
 * or one of the effects only that input has. Every other scenario counts time in logical ticks.
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
