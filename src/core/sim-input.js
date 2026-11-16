// The engine input: everything the simulation engine reads for one scenario run, as a plain
// JSON document, and nothing else. It holds no JSONC, meta-model, layout or validation state, so
// an engine in any language can run from it alone. Pure; no I/O.
// Format "exegra-sim-input", version 1; see docs/simulation.md, "Engine input and trace format".

/** @typedef {import('./types.js').Model} Model */

/**
 * @typedef {{id:string, from:string, to:string, on:string, guard:string|null, effects:any[], faultOnly:boolean}} InputTransition
 * @typedef {{id:string, subject:string, initial:string, variables:{name:string, initial:any}[], states:string[], transitions:InputTransition[]}} InputBehavior
 * @typedef {{id:string, kind:string, event?:string, transition?:string, occurrence?:number, by?:number, at?:number, payload?:Record<string, any>}} InputFault
 * @typedef {{format:'exegra-sim-input', version:1,
 *   scenario:{id:string, steps:{at:number, event:string, payload:Record<string, any>}[], faults:string[], stepLimit:number},
 *   behaviors:InputBehavior[], events:{id:string}[], faults:InputFault[]}} SimulationInput
 */

export const SIM_INPUT_FORMAT = 'exegra-sim-input';
export const SIM_INPUT_VERSION = 1;

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
  for (const k of EFFECT_KEYS) if (hasOwn(fx, k) && fx[k] !== undefined) out[k] = copy(fx[k]);
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
    return {
      id: bid,
      subject: b.data.subject,
      initial: b.data.initial,
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

  return {
    format: SIM_INPUT_FORMAT,
    version: SIM_INPUT_VERSION,
    scenario: { id: scenarioId, steps, faults: faultIds, stepLimit: sdata.maxSteps ?? 1000 },
    behaviors,
    events: (model.byKind.event ?? []).map((e) => ({ id: e.id })),
    faults: faultDecls,
  };
}
