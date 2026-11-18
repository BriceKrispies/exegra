// Shared by the queueing fixture tests: engine inputs written with `{lower: <family>}`
// distributions, lowered here, and twins as faults of the base input.

import { lowerDistribution, unitExponentialTable } from '../../../src/core/distributions.js';

/** Lower `{lower: <family>}` distributions and add the unit exponential table. @param {any} input */
export function lowerInput(input) {
  const out = structuredClone(input);
  const walk = (/** @type {any} */ v) => {
    if (!v || typeof v !== 'object') return v;
    if (Array.isArray(v)) return v.map(walk);
    if (v.lower && Object.keys(v).length === 1) return lowerDistribution(v.lower);
    for (const k of Object.keys(v)) v[k] = walk(v[k]);
    return v;
  };
  const lowered = walk(out);
  if (lowered.workloads?.some((/** @type {any} */ w) => w.process === 'poisson')) lowered.unitExponential = unitExponentialTable();
  return lowered;
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
