// Fault models as specification entities, and which faults the generated runtime can produce.
//
import { durationIn, needsTimedInput } from './time-units.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */

/** @param {number} n @param {string} one @param {string} many */
const plural = (n, one, many) => `${n} ${n === 1 ? one : many}`;
/** @param {string[]} xs */
const list = (xs) => (xs.length <= 2 ? xs.join(' and ') : `${xs.slice(0, -1).join(', ')} and ${xs[xs.length - 1]}`);

// Fault models: how a claim result states the model it holds under, and the
// validation rules of the environment, failureMode and faultModel kinds.

/** The fault model a claim names, when it names one that exists. @param {Model} model @param {Entity} claim */
export function faultModelOf(model, claim) {
  const fm = typeof claim.data.faultModel === 'string' ? model.entities.get(claim.data.faultModel) : undefined;
  return fm && fm.kind === 'faultModel' ? fm : null;
}

/** @param {Model} model @param {any} b */
function boundText(model, b) {
  const names = (Array.isArray(b.modes) ? b.modes : []).map((/** @type {string} */ id) => model.entities.get(id)?.data.name ?? id);
  const what = `${b.scope ? `${b.scope}-scoped ` : ''}${names.length ? list(names) : 'failures'}`;
  return `at most ${b.maxConcurrent} ${what} at once`;
}

/** "Under fault model X (n failure modes; bounds: ...)." @param {Model} model @param {Entity} fm */
export function faultModelScope(model, fm) {
  const n = Array.isArray(fm.data.modes) ? fm.data.modes.length : 0;
  const bounds = (Array.isArray(fm.data.bounds) ? fm.data.bounds : []).filter((/** @type {any} */ b) => b && typeof b === 'object').map((/** @type {any} */ b) => boundText(model, b));
  return `Under fault model ${fm.data.name ?? fm.id} (${plural(n, 'failure mode', 'failure modes')}; bounds: ${bounds.length ? bounds.join('; ') : 'none declared'}).`;
}

/** What the listed scenarios actually inject of the fault model. @param {Model} model @param {Entity} fm @param {any} ev */
export function faultCoverage(model, fm, ev) {
  const modes = new Set(Array.isArray(fm.data.modes) ? fm.data.modes : []);
  const ids = Array.isArray(ev?.scenarios) ? ev.scenarios : [];
  const hit = new Set();
  for (const sid of ids) {
    const sc = model.entities.get(sid);
    for (const fid of Array.isArray(sc?.data.faults) ? sc.data.faults : []) {
      const r = model.entities.get(fid)?.data.realises;
      if (typeof r === 'string' && modes.has(r)) hit.add(r);
    }
  }
  return `The result holds under fault model "${fm.id}" only as far as the listed scenarios inject its failure modes: they inject ${hit.size} of its ${modes.size}; the rest were not exercised.`;
}


/**
 * Validation rules of the environment, failureMode and faultModel kinds, and of the scenarios
 * that name a fault model. Structure, enums and references are checked generically in parse.js.
 * @param {Model} model
 * @returns {Diagnostic[]}
 */
export function validateFaultModels(model) {
  /** @type {Diagnostic[]} */
  const out = [];
  /** @param {'error'|'warning'} severity @param {string} code @param {Entity} entity @param {string} message @param {(string|number)[]} [sub] */
  const report = (severity, code, entity, message, sub) => {
    out.push({ code, severity, message, entityId: entity.id, loc: entity.loc, path: sub ? [...entity.path, ...sub] : entity.path });
  };
  const get = (/** @type {string} */ id) => model.entities.get(id);
  const kind = (/** @type {string} */ k) => model.byKind[k] ?? [];
  const hasSource = (/** @type {any} */ o) => !!o && typeof o === 'object' && typeof o.source === 'string' && o.source !== '';
  for (const e of kind('environment')) {
    (Array.isArray(e.data.guarantees) ? e.data.guarantees : []).forEach((/** @type {any} */ g, /** @type {number} */ i) => {
      if (!g || typeof g !== 'object') return;
      if (!hasSource(g)) report('error', 'environment.guarantee-no-source', e, `Guarantee "${g.aspect ?? i}" names no source; say what justifies the value.`, ['guarantees', i]);
      if ('value' in g && typeof g.value !== 'number' && typeof g.value !== 'string') report('error', 'environment.guarantee-value', e, 'A guarantee "value" must be a number or a string.', ['guarantees', i, 'value']);
    });
  }
  for (const m of kind('failureMode')) {
    const rate = m.data.rate;
    if (!rate || typeof rate !== 'object') report('error', 'failure-mode.no-rate-source', m, `Failure mode "${m.id}" states no rate, so it has no rate source.`);
    else {
      if (!hasSource(rate)) report('error', 'failure-mode.no-rate-source', m, `The rate of failure mode "${m.id}" names no source.`, ['rate']);
      if (typeof rate.value === 'number' && rate.value < 0) report('error', 'failure-mode.value', m, 'A rate must not be negative.', ['rate', 'value']);
    }
    const d = m.data.duration;
    if (d && typeof d === 'object') {
      if (!hasSource(d)) report('error', 'failure-mode.no-duration-source', m, `The duration of failure mode "${m.id}" names no source.`, ['duration']);
      for (const k of ['typical', 'max']) if (typeof d[k] === 'number' && d[k] < 0) report('error', 'failure-mode.value', m, `Duration "${k}" must not be negative.`, ['duration', k]);
      if (typeof d.typical === 'number' && typeof d.max === 'number' && d.typical > d.max) report('error', 'failure-mode.value', m, 'Typical duration exceeds the maximum.', ['duration']);
    }
  }
  for (const fm of kind('faultModel')) {
    const modes = new Set(Array.isArray(fm.data.modes) ? fm.data.modes : []);
    (Array.isArray(fm.data.bounds) ? fm.data.bounds : []).forEach((/** @type {any} */ b, /** @type {number} */ i) => {
      if (!b || typeof b !== 'object') return;
      if (!hasSource(b)) report('error', 'fault-model.bound-no-source', fm, `Bound ${i + 1} of fault model "${fm.id}" names no source.`, ['bounds', i]);
      if (typeof b.maxConcurrent === 'number' && !(Number.isInteger(b.maxConcurrent) && b.maxConcurrent >= 0)) report('error', 'fault-model.bound-value', fm, '"maxConcurrent" must be a non-negative integer.', ['bounds', i, 'maxConcurrent']);
      (Array.isArray(b.modes) ? b.modes : []).forEach((/** @type {any} */ id, /** @type {number} */ j) => {
        if (typeof id === 'string' && !modes.has(id)) report('warning', 'fault-model.bound-mode-outside', fm, `Bound ${i + 1} limits "${id}", which is not one of the model's failure modes.`, ['bounds', i, 'modes', j]);
      });
    });
  }
  for (const s of kind('scenario')) {
    const fm = typeof s.data.faultModel === 'string' ? get(s.data.faultModel) : undefined;
    if (!fm || fm.kind !== 'faultModel') continue;
    const modes = new Set(Array.isArray(fm.data.modes) ? fm.data.modes : []);
    (Array.isArray(s.data.faults) ? s.data.faults : []).forEach((/** @type {any} */ fid, /** @type {number} */ i) => {
      const f = typeof fid === 'string' ? get(fid) : undefined;
      const realises = f && f.kind === 'fault' ? f.data.realises : undefined;
      if (typeof realises === 'string' && !modes.has(realises)) report('warning', 'scenario.fault-outside-model', s, `Fault "${fid}" realises failure mode "${realises}", which is not in fault model "${fm.id}".`, ['faults', i]);
    });
  }

  out.push(...faultRealisability(model));
  return out;
}

// ---------------------------------------------------------------------------
// Faults the runtime can produce (docs/semantics.md, "Faults the runtime can produce")
// ---------------------------------------------------------------------------

/** The runtime's own retry policy (crates/runtime RetryPolicy::default): 1 s, factor 2, at most 300 s. */
export const RUNTIME_RETRY = Object.freeze({ first: '1 s', factor: 2, max: '300 s' });

/**
 * The retry policy the generated runtime uses: system.generation.retry over the runtime's default.
 * @param {Model} model
 * @returns {{first:any, factor:number, max:any}}
 */
export function retryPolicy(model) {
  const r = /** @type {any} */ (model.system?.data?.generation)?.retry;
  const o = r && typeof r === 'object' ? r : {};
  return {
    first: o.first ?? RUNTIME_RETRY.first,
    factor: Number.isInteger(o.factor) && o.factor >= 1 ? o.factor : RUNTIME_RETRY.factor,
    max: o.max ?? RUNTIME_RETRY.max,
  };
}

/**
 * The delay, in whole base units of `unit`, after which an at-least-once message is delivered when
 * its first `attempts` dispatches failed: the sum of the waits after each failure, the k-th wait
 * being min(first * factor^(k-1), max), as RetryPolicy::delay computes it. Throws when a duration
 * of the policy is not a whole number of `unit` (or `unit` is tick).
 * @param {Model} model @param {number} attempts @param {string} unit
 * @returns {number}
 */
export function retryDelay(model, attempts, unit) {
  const p = retryPolicy(model);
  const first = durationIn(p.first, unit, 'system.generation.retry.first');
  const max = durationIn(p.max, unit, 'system.generation.retry.max');
  let wait = first;
  let total = 0;
  for (let k = 1; k <= attempts; k++) {
    if (k > 1) wait = Math.min(wait * p.factor, max);
    total += Math.min(wait, max);
  }
  return total;
}

/**
 * The first `n` delays retryDelay gives (attempts 1..n), for messages.
 * @param {Model} model @param {string} unit @param {number} n
 */
function retryDelays(model, unit, n) {
  return Array.from({ length: n }, (_, i) => retryDelay(model, i + 1, unit));
}

/**
 * Whether `by` (base units of `unit`) is a delay the runtime's backoff produces: retryDelay for some
 * number of failed attempts.
 * @param {Model} model @param {number} by @param {string} unit
 */
export function isRetryDelay(model, by, unit) {
  if (!(by > 0)) return false;
  for (let n = 1; n <= 100000; n++) {
    const d = retryDelay(model, n, unit);
    if (d === by) return true;
    if (d > by) return false;
  }
  return false;
}

/** The fault kinds that act on the deliveries of an event. */
const EVENT_FAULTS = ['drop-event', 'lose-event', 'delay-event', 'retry-event', 'duplicate-event', 'inject-event'];

/**
 * The time unit of a scenario's numbers: its timeUnit, `us` for a timed scenario that names none,
 * or undefined for a scenario in logical ticks.
 * @param {Model} model @param {any} sdata
 */
function scenarioUnit(model, sdata) {
  if (typeof sdata.timeUnit === 'string') return sdata.timeUnit;
  return needsTimedInput(model, sdata) ? 'us' : undefined;
}

/**
 * Why the runtime cannot produce `fault` in scenario `s`, or undefined when it can. The runtime
 * delivers a timer firing exactly once, at its deadline (it removes the timer and steps its event in
 * one transaction); an at-least-once message stays in its sender's outbox until a dispatch
 * succeeds, retried with backoff, and may be dispatched again when the sender stops between the
 * dispatch and recording it; an at-most-once message is dispatched once, and lost when the
 * dispatch fails or the sender stops between commit and dispatch. An event that declares no
 * delivery comes from outside the runtime (a person, a browser, another system), which may send it
 * late, twice or not at all. Generated code has no switch that turns a transition on or off.
 * @param {Model} model @param {import('./types.js').Entity} s @param {import('./types.js').Entity} fault
 * @param {Set<string>} timerEvents the events a timer of the scenario's behaviors fires, and every elapsed event
 * @returns {string|undefined}
 */
export function unrealisableReason(model, s, fault, timerEvents) {
  const get = (/** @type {any} */ id) => (typeof id === 'string' ? model.entities.get(id) : undefined);
  const k = fault.data.kind;
  if (k === 'enable-transition' || k === 'disable-transition') {
    const t = get(fault.data.transition);
    const owner = t && t.kind === 'transition' ? get(t.owner) : undefined;
    if (owner && owner.data.level === 'implementation') {
      return `${k} changes implementation-level machine "${owner.id}" itself; generated code has no switch that turns transition "${t?.id}" ${k === 'enable-transition' ? 'on' : 'off'}. Model the cause as a fault of the input the machine receives (lose-event, drop-event, delay-event, retry-event, duplicate-event or inject-event).`;
    }
    return undefined;
  }
  if (!EVENT_FAULTS.includes(k)) return undefined;
  const ev = get(fault.data.event);
  if (!ev || ev.kind !== 'event') return undefined;
  if (timerEvents.has(ev.id)) {
    if (k === 'inject-event') return `"${ev.id}" is fired by a timer${ev.data.elapsed === true ? ' (it stands for elapsed time)' : ''}; only the timer delivers it, so it cannot arrive from outside.`;
    return `"${ev.id}" is fired by a timer, and the runtime delivers a timer firing exactly once, at its deadline: it removes the timer and steps its event in one transaction, so a firing is never dropped, delayed or repeated.`;
  }
  const delivery = ev.data.delivery;
  const declared = delivery === 'at-least-once' || delivery === 'at-most-once' ? `declares delivery ${delivery}` : 'declares no delivery, so it comes from outside the runtime';
  const unit = scenarioUnit(model, s.data);
  switch (k) {
    case 'drop-event':
      if (delivery === 'at-least-once') return `"${ev.id}" is at-least-once: its sender's outbox keeps it until a dispatch succeeds, so it is never dropped; a failed dispatch only delays it by the backoff (use retry-event).`;
      return undefined;
    case 'lose-event':
      if (delivery !== 'at-most-once') return `lose-event is the loss of an at-most-once message between its sender's commit and dispatch; "${ev.id}" ${declared}.`;
      return undefined;
    case 'retry-event':
      if (delivery !== 'at-least-once') return `retry-event is the redelivery of an at-least-once message after failed dispatches; "${ev.id}" ${declared}.`;
      return undefined;
    case 'duplicate-event':
      if (delivery === 'at-most-once') return `"${ev.id}" is at-most-once: its outbox entry is claimed before it is dispatched, so it is never dispatched twice.`;
      return undefined;
    case 'delay-event': {
      if (delivery === 'at-most-once') return `"${ev.id}" is at-most-once: it is dispatched once, when due, and never deferred, so the runtime cannot deliver it late.`;
      if (delivery !== 'at-least-once') return undefined;
      if (unit === undefined || unit === 'tick') return `"${ev.id}" is at-least-once, which the runtime delays only by its retry backoff, a duration; scenario "${s.id}" counts logical ticks, so the delay cannot be one (give the scenario a timeUnit, or use retry-event).`;
      let by;
      try { by = durationIn(fault.data.by, unit, `${fault.id}.by`); } catch { return undefined; }
      let ok = false;
      let known = '';
      try {
        ok = isRetryDelay(model, by, unit);
        known = retryDelays(model, unit, 5).join(', ');
      } catch (e) {
        return `"${ev.id}" is at-least-once, which the runtime delays only by its retry backoff, and that backoff is not a whole number of ${unit} (${/** @type {Error} */ (e).message}).`;
      }
      if (!ok) return `"${ev.id}" is at-least-once: the runtime delays it only by its retry backoff, after one or more failed dispatches (${known}, ... ${unit}; system.generation.retry), not by ${by} ${unit}. Use retry-event with the number of failed attempts.`;
      return undefined;
    }
    default:
      return undefined;
  }
}

/**
 * The fault.unrealisable diagnostics: every fault of a scenario that runs an implementation-level
 * machine must be one the generated runtime can produce (unrealisableReason).
 * @param {Model} model
 * @returns {Diagnostic[]}
 */
export function faultRealisability(model) {
  /** @type {Diagnostic[]} */
  const out = [];
  const get = (/** @type {any} */ id) => (typeof id === 'string' ? model.entities.get(id) : undefined);
  const transitions = model.byKind.transition ?? [];
  const elapsed = (model.byKind.event ?? []).filter((e) => e.data.elapsed === true).map((e) => e.id);
  for (const s of model.byKind.scenario ?? []) {
    const bs = (Array.isArray(s.data.behaviors) ? s.data.behaviors : []).filter((/** @type {any} */ b) => typeof b === 'string');
    if (!bs.some((/** @type {string} */ b) => get(b)?.data.level === 'implementation')) continue;
    const owned = new Set(bs);
    /** @type {Set<string>} */
    const timerEvents = new Set(elapsed);
    for (const t of transitions) {
      if (!owned.has(/** @type {string} */ (t.owner))) continue;
      for (const fx of Array.isArray(t.data.effects) ? t.data.effects : []) if (fx && typeof fx === 'object' && 'timer' in fx && typeof fx.emit === 'string') timerEvents.add(fx.emit);
    }
    (Array.isArray(s.data.faults) ? s.data.faults : []).forEach((/** @type {any} */ fid, /** @type {number} */ i) => {
      const f = get(fid);
      if (!f || f.kind !== 'fault') return;
      const why = unrealisableReason(model, s, f, timerEvents);
      if (why) out.push({ code: 'fault.unrealisable', severity: 'error', message: `Scenario "${s.id}" runs implementation-level machines, but fault "${f.id}" (${f.data.kind}) is not something the runtime can do: ${why}`, entityId: s.id, loc: s.loc, path: [...s.path, 'faults', i] });
    });
  }
  return out;
}
