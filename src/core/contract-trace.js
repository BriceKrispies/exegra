// Contract events: events that are requests and responses of a contract at a boundary.
//
// An event may name a `contract`, a `role` (request, response, error) and, for a response or an error,
// a `correlation` field that pairs it with its request. This module holds what both the validator
// (static check of the declarations) and the simulator (check of a trace) need:
//   - the fields and error codes a contract allows for each role,
//   - checkContractEvents: the automatic checks of a simulated trace, read from the trace only,
//   - requestLog: the trace rendered as the lines of a request log.
// Pure and deterministic: reads a model and a trace, never changes them, and the engine is not involved.

import { parseType, valueFits, typeText, splitTop, valueText } from './type-expr.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./engine.js').Trace} Trace */
/** @typedef {{type:string|undefined, optional:boolean}} FieldDef */
/** @typedef {'request'|'response'|'error'} Role */

export const CHECK_ID = 'contract-conformance';
const CLAIM_ID = 'trace-contract-conformance';

/**
 * The fields a contract allows in the payload of an event with this role. A request carries the
 * inputs; a response carries the outputs. An output whose type is an object type such as
 * `{ok: true, hash}` contributes the keys of that object (its alternatives are merged by name).
 * An error is free-form apart from its `code`, so it has no field table.
 * @param {Entity} contract @param {Role} role
 * @returns {Map<string, FieldDef>}
 */
export function contractFields(contract, role) {
  /** @type {Map<string, FieldDef>} */
  const out = new Map();
  if (role === 'error') return out;
  const list = role === 'request' ? contract.data.inputs : contract.data.outputs;
  for (const f of Array.isArray(list) ? list : []) {
    if (!f || typeof f.name !== 'string') continue;
    const type = typeof f.type === 'string' ? f.type.trim() : undefined;
    if (role === 'response' && type && type.startsWith('{') && type.endsWith('}')) {
      for (const part of splitTop(type.slice(1, -1), ',')) {
        if (!part) continue;
        const i = part.indexOf(':');
        const key = (i < 0 ? part : part.slice(0, i)).trim();
        const t = i < 0 ? undefined : part.slice(i + 1).trim();
        const prev = out.get(key);
        out.set(key, { type: prev ? (prev.type && t ? `${prev.type} | ${t}` : undefined) : t, optional: true });
      }
    } else {
      out.set(f.name, { type, optional: f.optional === true || role === 'response' });
    }
  }
  return out;
}

/** The error codes a contract declares. An error named "a / b" declares both. @param {Entity} contract @returns {string[]} */
export function contractErrorCodes(contract) {
  const codes = [];
  for (const e of Array.isArray(contract.data.errors) ? contract.data.errors : []) {
    if (e && typeof e.name === 'string') codes.push(...e.name.split(' / ').map((/** @type {string} */ s) => s.trim()).filter(Boolean));
  }
  return codes;
}

/**
 * The contract and role of an event, when it is a contract event with a contract that exists.
 * @param {Model} model @param {string} eventId
 * @returns {{event: Entity, contract: Entity, role: Role|undefined}|null}
 */
export function contractEvent(model, eventId) {
  const event = model.entities.get(eventId);
  if (!event || event.kind !== 'event' || typeof event.data.contract !== 'string') return null;
  const contract = model.entities.get(event.data.contract);
  if (!contract || contract.kind !== 'contract') return null;
  const role = event.data.role === 'request' || event.data.role === 'response' || event.data.role === 'error' ? event.data.role : undefined;
  return { event, contract, role };
}

/** @param {unknown} a @param {unknown} b @returns {boolean} */
const same = (a, b) => JSON.stringify(a) === JSON.stringify(b);

/**
 * The automatic checks of contract events on a trace. One failed check per violation, carrying the step;
 * when the trace has contract events and none violates, one passing check. Nothing is returned for a
 * trace without contract events.
 * @param {Model} model @param {Trace} trace
 * @returns {{claimId: string, holds: boolean, automatic: true, check: string, stepIndex?: number, explanation: string}[]}
 */
export function checkContractEvents(model, trace) {
  const claimId = model.entities.get(CLAIM_ID)?.kind === 'claim' ? CLAIM_ID : CHECK_ID;
  /** @type {{claimId: string, holds: boolean, automatic: true, check: string, stepIndex?: number, explanation: string}[]} */
  const out = [];
  /** @type {Map<string, {step:number, payload:Record<string, any>, answered:boolean}[]>} */
  const requests = new Map();
  let seen = 0;
  /** @param {number} stepIndex @param {string} explanation */
  const bad = (stepIndex, explanation) => out.push({ claimId, holds: false, automatic: true, check: CHECK_ID, stepIndex, explanation });
  for (const step of trace.steps) {
    if (step.kind !== 'deliver') continue;
    const ce = contractEvent(model, step.event.id);
    if (!ce || !ce.role) continue;
    seen++;
    const { event, contract, role } = ce;
    const payload = step.event.payload ?? {};
    const where = `${event.id} (${role} of contract ${contract.id})`;
    const fields = contractFields(contract, role);
    if (role !== 'error') {
      for (const [k, v] of Object.entries(payload)) {
        const def = fields.get(k);
        if (!def) { bad(step.index, `${where}: payload field "${k}" is not ${role === 'request' ? 'an input' : 'an output'} of the contract.`); continue; }
        const type = parseType(def.type);
        if (!valueFits(v, type)) bad(step.index, `${where}: payload field "${k}" is ${valueText(v)}, which does not fit ${typeText(type)}.`);
      }
    }
    if (role === 'request') {
      for (const [k, def] of fields) if (!def.optional && !(k in payload)) bad(step.index, `${where}: required input "${k}" is missing.`);
      const list = requests.get(contract.id) ?? [];
      list.push({ step: step.index, payload, answered: false });
      requests.set(contract.id, list);
      continue;
    }
    if (role === 'error') {
      const codes = contractErrorCodes(contract);
      if (typeof payload.code !== 'string') bad(step.index, `${where}: an error needs a string "code".`);
      else if (!codes.includes(payload.code)) bad(step.index, `${where}: error code "${payload.code}" is not among the contract's errors (${codes.join(', ') || 'none declared'}).`);
    }
    const open = (requests.get(contract.id) ?? []).filter((r) => !r.answered);
    const corr = typeof event.data.correlation === 'string' ? event.data.correlation : null;
    const match = corr && payload[corr] !== undefined ? open.find((r) => same(r.payload[corr], payload[corr])) : open[0];
    if (!match) {
      bad(step.index, `${where}: answers no earlier unanswered request of contract ${contract.id}${corr && payload[corr] !== undefined ? ` with ${corr} = ${valueText(payload[corr])}` : ''}.`);
    } else match.answered = true;
  }
  if (seen && !out.length) out.push({ claimId, holds: true, automatic: true, check: CHECK_ID, explanation: `${seen} contract event${seen === 1 ? '' : 's'} fit their contracts and every response answers a request.` });
  return out;
}

/**
 * @typedef {Object} RequestLogEntry
 * @property {number} step     index of the trace step
 * @property {number} time     logical time of the step
 * @property {Role} role
 * @property {string} contract contract id
 * @property {string} event    event id
 * @property {boolean} lost    the step was dropped by a fault: the message never arrived
 * @property {string} text     one line, for example `→ POST /me/display-name {name: "Bob"}`
 */

/** @param {Record<string, any>} payload @returns {string} */
function payloadText(payload) {
  const parts = Object.entries(payload).map(([k, v]) => `${k}: ${valueText(v)}`);
  return parts.length ? `{${parts.join(', ')}}` : '';
}

/** What a request is called in the log: its contract's binding, else the event's name. @param {Entity} contract @param {Entity} event @returns {string} */
function requestLabel(contract, event) {
  const b = contract.data.binding;
  if (b && typeof b === 'object') {
    if (b.method && b.path) return `${b.method} ${b.path}`;
    if (b.operation) return String(b.operation);
    if (b.path) return String(b.path);
  }
  return typeof event.data.name === 'string' ? event.data.name : event.id;
}

/**
 * The trace as the lines of a request log: one entry per step whose event is a contract event with a
 * role. Delayed steps are left out (the same event is delivered later). Non-contract steps give nothing.
 * @param {Model} model @param {Trace} trace
 * @returns {RequestLogEntry[]}
 */
export function requestLog(model, trace) {
  /** @type {RequestLogEntry[]} */
  const out = [];
  for (const step of trace.steps) {
    if (step.kind === 'delay') continue;
    const ce = contractEvent(model, step.event.id);
    if (!ce || !ce.role) continue;
    const { event, contract, role } = ce;
    const payload = { ...(step.event.payload ?? {}) };
    let head;
    if (role === 'request') head = `→ ${requestLabel(contract, event)}`;
    else if (role === 'error') { head = `← refused ${typeof payload.code === 'string' ? payload.code : '?'}`; delete payload.code; }
    else head = '← ok';
    const rest = payloadText(payload);
    const line = rest ? `${head} ${rest}` : head;
    const lost = step.kind === 'drop';
    out.push({ step: step.index, time: step.time, role, contract: contract.id, event: event.id, lost, text: lost ? `✕ lost ${line}` : line });
  }
  return out;
}
