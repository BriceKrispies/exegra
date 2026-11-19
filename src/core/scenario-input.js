// Scenario input typing (scenario.input-type): every value a scenario feeds a machine must have the type its event
// declares. Step payloads and the payloads of inject-event faults are checked against the payload fields of the
// event they deliver: built-in representations (bool, the integers with their bounds, f64, string, bytes,
// timestamp, duration, uuid, json), declared id, scalar, enum and struct types, and list<T> and option<T>. A required
// field must be present, a field the event does not declare is refused, and an option or optional field may be
// absent or null. A type text that does not resolve (free text, or the type-expr forms `number`, `boolean`,
// `'a' | 'b'`) is checked with the loose rules of type-expr.js, which accept anything they cannot read.
// Pure: no I/O.

import { isBuiltinType } from './builtin-types.js';
import { parseType, valueFits, typeText } from './type-expr.js';
import { unsharedText } from './codegen-model.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */

const WRAPPER_RE = /^(list|option|set|shared)<(.+)>$/;
const UUID_RE = /^[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}$/;
const MAX_DEPTH = 8;

/** Inclusive integer bounds of the integer built-ins (as doubles; u64 and i64 are bounded by the exact powers of two). */
const INTEGER_RANGES = /** @type {Record<string, [number, number]>} */ ({
  u8: [0, 255], u16: [0, 65535], u32: [0, 4294967295], u64: [0, 2 ** 64], i32: [-2147483648, 2147483647], i64: [-(2 ** 63), 2 ** 63],
});

/** @param {unknown} v */
function show(v) {
  const s = JSON.stringify(v);
  if (s === undefined) return String(v);
  return s.length > 48 ? `${s.slice(0, 45)}...` : s;
}

/**
 * Why a value does not have a built-in representation, or null when it does.
 * @param {string} repr @param {unknown} v @returns {string|null}
 */
function builtinProblem(repr, v) {
  switch (repr) {
    case 'bool': return typeof v === 'boolean' ? null : 'is not a boolean';
    case 'f64': return typeof v === 'number' && Number.isFinite(v) ? null : 'is not a finite number';
    case 'string': return typeof v === 'string' ? null : 'is not a string';
    case 'bytes': return typeof v === 'string' || (Array.isArray(v) && v.every((x) => Number.isInteger(x) && x >= 0 && x <= 255)) ? null : 'is not bytes (a string or an array of 0..255)';
    case 'uuid': return typeof v === 'string' && UUID_RE.test(v) ? null : 'is not a uuid (8-4-4-4-12 hexadecimal digits)';
    case 'json': return v === undefined ? 'is missing' : null;
    case 'unit': return v === null ? null : 'is not the unit value null';
    case 'timestamp': case 'duration': return typeof v === 'number' && Number.isInteger(v) ? null : 'is not an integer';
    default: {
      const range = INTEGER_RANGES[repr];
      if (!range) return null;
      if (typeof v !== 'number' || !Number.isInteger(v)) return `is not an integer (${repr})`;
      return v >= range[0] && v <= range[1] ? null : `is outside the range of ${repr}`;
    }
  }
}

/**
 * Why a value does not have a type, or null when it does. `typeName` is a payload or struct field type text.
 * @param {Model} model @param {string} typeName @param {unknown} v @param {number} depth @returns {string|null}
 */
export function valueProblem(model, typeName, v, depth = 0) {
  const text = typeName.trim();
  const wrapped = WRAPPER_RE.exec(text);
  if (wrapped) {
    if (wrapped[1] === 'shared') return valueProblem(model, wrapped[2], v, depth);
    if (wrapped[1] === 'option') return v === null ? null : valueProblem(model, wrapped[2], v, depth);
    if (!Array.isArray(v)) return `is not a list (${text})`;
    for (let i = 0; i < v.length; i++) { const p = valueProblem(model, wrapped[2], v[i], depth); if (p) return `item ${i} ${p}`; }
    if (wrapped[1] === 'set') {
      const seen = new Set();
      for (let i = 0; i < v.length; i++) {
        const key = JSON.stringify(v[i]);
        if (seen.has(key)) return `repeats item ${i} (${text} holds distinct items)`;
        seen.add(key);
      }
    }
    return null;
  }
  if (isBuiltinType(text)) return builtinProblem(text, v);
  const t = model.entities.get(text);
  if (t?.kind === 'type') {
    const d = t.data;
    if (d.kind === 'enum') {
      const values = Array.isArray(d.values) ? d.values : [];
      return values.includes(v) ? null : `is not a value of enum ${text} (${values.join(', ')})`;
    }
    if (d.kind === 'struct') {
      if (depth >= MAX_DEPTH) return null;
      if (!v || typeof v !== 'object' || Array.isArray(v)) return `is not an object (${text})`;
      const fields = Array.isArray(d.fields) ? d.fields : [];
      const obj = /** @type {Record<string, unknown>} */ (v);
      for (const f of fields) {
        if (!f || typeof f.name !== 'string' || typeof f.type !== 'string') continue;
        const absent = !(f.name in obj) || obj[f.name] === undefined;
        if (absent || obj[f.name] === null) {
          if (f.optional === true || WRAPPER_RE.exec(unsharedText(f.type))?.[1] === 'option') continue;
          return `lacks the required field "${f.name}" of ${text}`;
        }
        const p = valueProblem(model, f.type, obj[f.name], depth + 1);
        if (p) return `field "${f.name}" ${p}`;
      }
      const known = new Set(fields.map((/** @type {any} */ f) => f?.name));
      for (const k of Object.keys(obj)) if (!known.has(k)) return `has the field "${k}", which ${text} does not declare`;
      return null;
    }
    // id and scalar: the representation
    if (typeof d.repr === 'string') {
      const p = builtinProblem(d.repr, v);
      return p ? `${p} (${text})` : null;
    }
    return null;
  }
  // The type does not resolve: the loose rules of type-expr.js.
  const atoms = parseType(text);
  return valueFits(v, atoms) ? null : `does not fit ${typeText(atoms)}`;
}

/**
 * Problems of one payload against the payload fields of an event.
 * @param {Model} model @param {any} event @param {any} payload @returns {{field?: string, message: string}[]}
 */
function payloadProblems(model, event, payload) {
  if (!Array.isArray(event.data.payload)) return [];
  if (payload === undefined) payload = {};
  if (!payload || typeof payload !== 'object' || Array.isArray(payload)) return [{ message: 'The payload must be an object.' }];
  /** @type {{field?: string, message: string}[]} */
  const out = [];
  const declared = new Set();
  for (const f of event.data.payload) {
    if (!f || typeof f.name !== 'string') continue;
    declared.add(f.name);
    const type = typeof f.type === 'string' ? f.type : '';
    const absent = !(f.name in payload) || payload[f.name] === undefined;
    if (absent || payload[f.name] === null) {
      if (!type || f.optional === true || WRAPPER_RE.exec(unsharedText(type))?.[1] === 'option' || type.trim() === 'json' || parseType(type).some((a) => a.k === 'null' || a.k === 'any')) continue;
      out.push({ field: f.name, message: `Payload field "${f.name}" (${type}) of event "${event.id}" is missing.` });
      continue;
    }
    if (!type) continue;
    const p = valueProblem(model, type, payload[f.name]);
    if (p) out.push({ field: f.name, message: `Payload field "${f.name}" of event "${event.id}" ${p}, but is ${show(payload[f.name])}; its type is ${type}.` });
  }
  for (const k of Object.keys(payload)) if (!declared.has(k)) out.push({ field: k, message: `Payload field "${k}" is not a field of event "${event.id}".` });
  return out;
}

/**
 * The scenario.input-type diagnostics of a model: an error under system.generation, a warning otherwise.
 * @param {Model} model @returns {Diagnostic[]}
 */
export function scenarioInputDiagnostics(model) {
  const severity = model.system.data.generation !== undefined ? 'error' : 'warning';
  /** @type {Diagnostic[]} */
  const out = [];
  /** @param {any} entity @param {(string|number)[]} sub @param {string} message */
  const report = (entity, sub, message) => out.push({ code: 'scenario.input-type', severity, message, entityId: entity.id, loc: entity.loc, path: [...entity.path, ...sub] });
  for (const s of model.byKind.scenario ?? []) {
    (Array.isArray(s.data.steps) ? s.data.steps : []).forEach((/** @type {any} */ st, /** @type {number} */ i) => {
      const ev = typeof st?.event === 'string' ? model.entities.get(st.event) : undefined;
      if (!ev || ev.kind !== 'event') return;
      for (const p of payloadProblems(model, ev, st.payload)) report(s, p.field !== undefined && st.payload && p.field in st.payload ? ['steps', i, 'payload', p.field] : ['steps', i, 'payload'], `Scenario "${s.id}" step ${i}: ${p.message}`);
    });
  }
  for (const f of model.byKind.fault ?? []) {
    if (f.data.kind !== 'inject-event' || typeof f.data.event !== 'string') continue;
    const ev = model.entities.get(f.data.event);
    if (!ev || ev.kind !== 'event') continue;
    for (const p of payloadProblems(model, ev, f.data.payload)) report(f, p.field !== undefined && f.data.payload && p.field in f.data.payload ? ['payload', p.field] : ['payload'], `Fault "${f.id}": ${p.message}`);
  }
  return out;
}
