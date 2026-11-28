// Commands for behavioural composition along the hierarchy (docs/composition.md): interfaces, compose,
// refine, environment, order-check and transfer. Registered into the command table by cli/commands.js,
// which hands in its helpers (this module is imported by commands.js, so it cannot import them back).

import {
  interfaceReport, eventInterfaces, crossReads, alternativeMachines, compositeBehavior, checkAbstraction,
  describeCounterexample, scenarioCut, environmentReport, orderIndependence, transferClaim, abstractionOf,
  behaviorsAtLevels, inputWith,
} from '../src/core/composition.js';
import { runEngine } from '../src/core/engine.js';
import { checkTrace } from '../src/core/claims.js';

/** @typedef {import('../src/core/types.js').Model} Model */

/**
 * The verdict of every applicable invariant and temporal claim on a trace (checkTrace), by claim id.
 * @param {Model} model @param {any} trace @returns {Record<string, string>}
 */
export function traceVerdicts(model, trace) {
  /** @type {Record<string, string>} */
  const out = {};
  for (const c of checkTrace(model, trace)) {
    if (c.automatic) continue;
    const v = c.pending ? 'undecided' : c.holds ? 'holds' : 'violated';
    // A claim with several checks on one trace is violated when any is.
    out[c.claimId] = out[c.claimId] === 'violated' || v === 'violated' ? 'violated' : out[c.claimId] === 'undecided' || v === 'undecided' ? 'undecided' : v;
  }
  return out;
}

/**
 * Parse `--level a=members,b=abstract`.
 * @param {string|undefined} value @param {(code: string, message: string) => Error} usage
 * @returns {Record<string, 'abstract'|'members'|'finest'>}
 */
export function parseLevels(value, usage) {
  /** @type {Record<string, 'abstract'|'members'|'finest'>} */
  const out = {};
  for (const part of (value ?? '').split(',').map((s) => s.trim()).filter(Boolean)) {
    const [k, v] = part.split('=');
    if (!k || !['abstract', 'members', 'finest'].includes(v)) throw usage('invalid-argument', `--level takes <abstraction>=abstract|members|finest, comma-separated; got "${part}".`);
    out[k] = /** @type {any} */ (v);
  }
  return out;
}

/**
 * The faults of the negatives of every trace claim that lists a scenario, as extra fault sets (each with the
 * scenario's own faults).
 * @param {Model} model @param {string} sid
 */
function negativeFaultSets(model, sid) {
  const own = model.entities.get(sid)?.data.faults ?? [];
  /** @type {string[][]} */
  const sets = [];
  const seen = new Set();
  for (const c of model.byKind.claim ?? []) {
    const ev = c.data.evaluate;
    if (!ev || !Array.isArray(ev.negatives)) continue;
    for (const n of ev.negatives) {
      if (n?.scenario !== sid || !Array.isArray(n.faults)) continue;
      const set = [...new Set([...own, ...n.faults])];
      const key = set.join(',');
      if (!seen.has(key)) { seen.add(key); sets.push(set); }
    }
  }
  return sets;
}

/**
 * The order-independence check of one scenario: verdicts of its claims on its own run and on each of its
 * negatives' runs, under every order orderIndependence tries.
 * @param {Model} model @param {string} sid
 */
export function orderCheck(model, sid) {
  return orderIndependence(model, sid, (t) => traceVerdicts(model, t), { faultSets: negativeFaultSets(model, sid) });
}

/** @param {any} h the helpers of cli/commands.js */
export function compositionCommands(h) {
  const { loadProject, requireModel, requireEntity, usage, INLINE_OPTIONS, listValue, CliError } = h;
  return {
    interfaces: {
      usage: 'interfaces [<elementId>] [--events]',
      summary: 'The event interfaces of elements (docs/composition.md): per element its declared interface (inputs, outputs, exported observables), the interface inferred from its members\' behaviours (inputs, outputs, internal events, observables read from outside), whether they agree, and the cross-element state reads into it. --events lists, per event, the interfaces it belongs to. Also the same-subject alternative machines.',
      options: { events: { type: 'boolean' }, ...INLINE_OPTIONS },
      run: async (/** @type {any} */ ctx) => {
        const { project } = await loadProject(ctx);
        const model = requireModel(project);
        const id = ctx.positionals[0];
        if (id !== undefined) requireEntity(model, id, 'component');
        /** @type {any} */
        const result = { elements: interfaceReport(model, id) };
        if (id === undefined) {
          result.reads = crossReads(model);
          result.alternatives = alternativeMachines(model);
        }
        if (ctx.values.events === true) result.events = Object.fromEntries(eventInterfaces(model));
        return { result, semanticHash: project.semanticHash };
      },
    },

    compose: {
      usage: 'compose <elementId> --scenario <scenarioId> [--faults a,b] [--steps]',
      summary: 'The derived behaviour of an element in a scenario: the scenario\'s machines inside the element, composed with the rest on the engine, with the events internal to the element hidden; its boundary trace is the projection of the run, computed in Lean (exact strength). --steps adds the full trace.',
      options: { scenario: { type: 'string' }, faults: { type: 'string' }, steps: { type: 'boolean' }, ...INLINE_OPTIONS },
      run: async (/** @type {any} */ ctx) => {
        const { project } = await loadProject(ctx);
        const model = requireModel(project);
        const el = ctx.positionals[0];
        if (!el) throw usage('missing-argument', 'Missing argument <elementId>.');
        requireEntity(model, el, 'component');
        if (!ctx.values.scenario) throw usage('missing-argument', '--scenario is required.');
        requireEntity(model, ctx.values.scenario, 'scenario');
        const faults = ctx.values.faults === undefined ? undefined : listValue(ctx.values.faults);
        const r = compositeBehavior(model, el, ctx.values.scenario, { faults });
        const { trace, ...rest } = r;
        return { result: { ...rest, outcome: trace.outcome, stepCount: trace.steps.length, ...(ctx.values.steps === true ? { trace } : {}) }, semanticHash: project.semanticHash };
      },
    },

    refine: {
      usage: 'refine <abstractionId> [--scenarios a,b] [--finest] [--faults a,b]',
      summary: 'Check a declared abstraction (a behaviour with `abstracts`) against the composition of its members: each driving scenario runs with the region at the abstraction and at its members (--finest: members of member abstractions too), the members\' internal events hidden, and Lean compares the boundary traces (events, kinds, payloads, times under the time scale, outcome, and the final configuration of the machines outside the region). The result is a step correspondence per scenario (certificate) or the first boundary counterexample, with the strength: conservative (declared and refined on these runs) or incomplete (an opaque member, a fault left out, or nothing checked).',
      options: { scenarios: { type: 'string' }, finest: { type: 'boolean' }, faults: { type: 'string' }, ...INLINE_OPTIONS },
      run: async (/** @type {any} */ ctx) => {
        const { project } = await loadProject(ctx);
        const model = requireModel(project);
        const id = ctx.positionals[0];
        if (!id) throw usage('missing-argument', 'Missing argument <abstractionId>.');
        requireEntity(model, id, 'behavior');
        if (!abstractionOf(model, id)) throw new CliError('refine.not-an-abstraction', `Behavior "${id}" declares no abstraction ("abstracts": {members}).`);
        const r = checkAbstraction(model, id, {
          scenarios: ctx.values.scenarios === undefined ? undefined : listValue(ctx.values.scenarios),
          finest: ctx.values.finest === true,
          faults: ctx.values.faults === undefined ? undefined : listValue(ctx.values.faults),
        });
        return { result: { ...r, ...(r.counterexample ? { explanation: describeCounterexample(r.counterexample) } : {}) }, semanticHash: project.semanticHash };
      },
    },

    environment: {
      usage: 'environment [<scenarioId>] [--level a=members,...]',
      summary: 'A scenario\'s behavioural cut (the level of each region, declared or inferred) and its environment: every delivered event that no running machine reacts to and that an omitted element would receive, split into those an environment assumption covers and those it does not (scenario.environment-unassumed). Without a scenario: every scenario.',
      options: { level: { type: 'string' }, ...INLINE_OPTIONS },
      run: async (/** @type {any} */ ctx) => {
        const { project } = await loadProject(ctx);
        const model = requireModel(project);
        const ids = ctx.positionals[0] !== undefined ? [requireEntity(model, ctx.positionals[0], 'scenario').id] : (model.byKind.scenario ?? []).map((/** @type {any} */ s) => s.id);
        const levels = parseLevels(ctx.values.level, usage);
        const scenarios = ids.map((/** @type {string} */ sid) => {
          const at = Object.keys(levels).length ? behaviorsAtLevels(model, sid, levels) : null;
          const trace = runEngine(at ? inputWith(model, sid, at.behaviors, at.faults) : inputWith(model, sid, model.entities.get(sid).data.behaviors));
          const env = environmentReport(model, sid, trace, at?.behaviors);
          return { scenario: sid, cut: scenarioCut(model, sid), ...(at ? { atLevels: at } : {}), assumed: env.assumed, unassumed: env.unassumed };
        });
        return { result: { scenarios, unassumed: scenarios.reduce((n, s) => n + s.unassumed.length, 0) }, semanticHash: project.semanticHash };
      },
    },

    'order-check': {
      usage: 'order-check [<scenarioId>]',
      summary: 'Order independence of composition (invariant I2): run each scenario (and each negative run of its claims) with its behaviours listed reversed and in every rotation, and compare the verdict of every invariant and temporal claim that lists it, and the trace up to the order of behaviours. Without a scenario: every scenario.',
      options: { ...INLINE_OPTIONS },
      run: async (/** @type {any} */ ctx) => {
        const { project } = await loadProject(ctx);
        const model = requireModel(project);
        const ids = ctx.positionals[0] !== undefined ? [requireEntity(model, ctx.positionals[0], 'scenario').id] : (model.byKind.scenario ?? []).map((/** @type {any} */ s) => s.id);
        const scenarios = ids.map((/** @type {string} */ sid) => orderCheck(model, sid));
        return {
          result: {
            scenarios: scenarios.length, orders: scenarios.reduce((n, s) => n + s.orders, 0),
            verdictsIndependent: scenarios.every((s) => s.verdictsIndependent),
            traceDifferences: scenarios.filter((s) => s.traceDifferences).map((s) => ({ scenario: s.scenario, runs: s.traceDifferences })),
            differences: scenarios.filter((s) => !s.verdictsIndependent).map((s) => ({ scenario: s.scenario, differences: s.differences })),
            results: scenarios,
          },
          semanticHash: project.semanticHash,
        };
      },
    },

    transfer: {
      usage: 'transfer <claimId> --abstraction <behaviorId>',
      summary: 'Whether a claim established at a declared abstraction holds for its members, by the preservation rules (docs/composition.md, "Claim transfer"): safety over the boundary alphabet transfers down a refinement that the check certifies; liveness never transfers without a declared fairness hypothesis; anything else is not transferred, with the reason.',
      options: { abstraction: { type: 'string' }, ...INLINE_OPTIONS },
      run: async (/** @type {any} */ ctx) => {
        const { project } = await loadProject(ctx);
        const model = requireModel(project);
        const id = ctx.positionals[0];
        if (!id) throw usage('missing-argument', 'Missing argument <claimId>.');
        requireEntity(model, id, 'claim');
        if (!ctx.values.abstraction) throw usage('missing-argument', '--abstraction is required.');
        requireEntity(model, ctx.values.abstraction, 'behavior');
        return { result: transferClaim(model, id, ctx.values.abstraction), semanticHash: project.semanticHash };
      },
    },
  };
}
