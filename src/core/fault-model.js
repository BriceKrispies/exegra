// Fault models as specification entities.
//
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

  return out;
}
