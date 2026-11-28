// Shared by the queueing fixture tests: engine inputs written with `{lower: <family>}`
// distributions, lowered here, and twins as faults of the base input.

import { call, initLean } from '../../../src/core/lean.js';

/**
 * Lower `{lower: <family>}` distributions with the Lean lowering (Exegra.Lower.Dist, the registered
 * function "lower.tables") and add the unit exponential table.
 * @param {any} input
 */
export function lowerInput(input) {
  initLean();
  const out = structuredClone(input);
  /** @type {any[]} */
  const families = [];
  const collect = (/** @type {any} */ v) => {
    if (!v || typeof v !== 'object') return;
    if (Array.isArray(v)) { v.forEach(collect); return; }
    if (v.lower && Object.keys(v).length === 1) { families.push({ path: 'distribution', family: v.lower }); return; }
    for (const k of Object.keys(v)) collect(v[k]);
  };
  collect(out);
  const r = call('lower.tables', { families });
  if (!r.ok) throw new Error(r.error);
  const lowered = /** @type {any[]} */ (r.value.families);
  for (const l of lowered) if (l.error) throw new Error(l.error);
  let next = 0;
  const walk = (/** @type {any} */ v) => {
    if (!v || typeof v !== 'object') return v;
    if (Array.isArray(v)) return v.map(walk);
    if (v.lower && Object.keys(v).length === 1) return lowered[next++];
    for (const k of Object.keys(v)) v[k] = walk(v[k]);
    return v;
  };
  const result = walk(out);
  if (result.workloads?.some((/** @type {any} */ w) => w.process === 'poisson')) result.unitExponential = r.value.unitExponential;
  return result;
}

/** The base input with a twin's faults active. @param {any} base @param {string[]} faults */
export function withFaults(base, faults) {
  return { ...base, scenario: { ...base.scenario, faults: [...faults] } };
}

/** The base input with a list of changes. @param {any} base @param {{path: (string|number)[], value: any}[]} changes */
export function changed(base, changes) {
  const out = structuredClone(base);
  for (const { path: p, value } of changes) {
    let o = out;
    for (const k of p.slice(0, -1)) o = o[k];
    o[p[p.length - 1]] = structuredClone(value);
  }
  return out;
}
