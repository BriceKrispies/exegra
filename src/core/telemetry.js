// Telemetry: the structured log lines generated code writes for domain events. `system.telemetry` names the
// services that write a log and fixes the line format (JSON lines: ts, level, service, event, then correlation
// and tenant when known, then the event's allowlisted fields). Each event states its logging: logged by one
// service at one level with an allowlist of payload fields (and the names they are written under), or not
// logged, with a reason. Payloads are never logged whole, and a field marked sensitive (or of a sensitive type)
// is never logged. This module holds the consistency rules (errors, always on) and the readiness rule (with
// system.generation, every domain event states its logging). Pure and deterministic.
// docs/model-and-format.md, "Telemetry".

import { typeClass, parseTypeName } from './codegen-model.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */
/** @typedef {{code: string, severity: 'error', message: string, entityId: string}} Gap */

/** The members every log line has, in order; a logged field may not be written under one of these names. */
export const RECORD_FIELDS = Object.freeze(['ts', 'level', 'service', 'event', 'correlation', 'tenant']);
/** The levels of a log line. */
export const LOG_LEVELS = Object.freeze(['debug', 'info', 'warn', 'error']);
/** The kinds of sensitive data, none of which is ever logged. */
export const SENSITIVE_KINDS = Object.freeze(['secret', 'password', 'token', 'personal']);

const SERVICE_RE = /^[a-z][a-z0-9-]*$/;
const LOG_NAME_RE = /^[a-z][a-z0-9_]*(?:\.[a-z][a-z0-9_]*)*$/;
const FIELD_NAME_RE = /^[a-z][a-z0-9_-]*$/;
const WRAPPER_RE = /^(list|option|set|shared)<(.+)>$/;

/** @param {any} v */
const isObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);
/** @param {any} v @returns {any[]} */
const list = (v) => (Array.isArray(v) ? v : []);
/** @param {any} v */
const nonEmpty = (v) => typeof v === 'string' && v.trim() !== '';

/**
 * The services of system.telemetry, by id.
 * @param {Model} model @returns {Map<string, any>}
 */
export function telemetryServices(model) {
  const t = model.system?.data.telemetry;
  return new Map(list(isObj(t) ? t.services : undefined).filter((s) => isObj(s) && typeof s.id === 'string').map((s) => [s.id, s]));
}

/**
 * The kind of sensitive data a type holds, or undefined: a type marked sensitive, a struct with a sensitive
 * field or a union variant field, a map of such a value, or list<T> / set<T> / option<T> / shared<T> of such a type.
 * @param {Model} model @param {any} name @param {Set<string>} [seen]
 * @returns {string|undefined}
 */
export function typeSensitivity(model, name, seen = new Set()) {
  if (typeof name !== 'string') return undefined;
  const text = name.trim();
  const wrapped = WRAPPER_RE.exec(text);
  if (wrapped) return typeSensitivity(model, wrapped[2], seen);
  const parsed = parseTypeName(text);
  if (parsed.k === 'map') return typeSensitivity(model, parsed.value, seen) ?? typeSensitivity(model, parsed.key, seen);
  const t = model.entities.get(text);
  if (t?.kind !== 'type' || seen.has(t.id)) return undefined;
  seen.add(t.id);
  if (typeof t.data.sensitive === 'string') return t.data.sensitive;
  const fields = [...list(t.data.fields), ...list(t.data.variants).flatMap((v) => (isObj(v) ? list(v.fields) : []))];
  for (const f of fields) {
    if (!isObj(f)) continue;
    if (typeof f.sensitive === 'string') return f.sensitive;
    const inner = typeSensitivity(model, f.type, seen);
    if (inner) return inner;
  }
  return undefined;
}

/**
 * The payload field of an event by name.
 * @param {Entity} e @param {any} name
 */
const payloadField = (e, name) => list(e.data.payload).find((f) => isObj(f) && f.name === name);

/**
 * What an event's log line holds: the service, level, log name, the tenant field and the allowlisted fields
 * as {field, as} (as = the member name written), or null when the event is not logged.
 * @param {Entity} e
 * @returns {{service: string, level: string, name: string, tenant?: string, fields: {field: string, as: string}[]}|null}
 */
export function eventLogging(e) {
  const l = e.data.logging;
  if (!isObj(l) || l.logged !== true) return null;
  return {
    service: l.service,
    level: l.level,
    name: typeof l.name === 'string' ? l.name : e.id,
    ...(typeof l.tenant === 'string' ? { tenant: l.tenant } : {}),
    fields: list(l.fields).filter((f) => isObj(f) && typeof f.field === 'string').map((f) => ({ field: f.field, as: typeof f.as === 'string' ? f.as : f.field })),
  };
}

/**
 * The consistency rules of telemetry: the services, and each event's logging (shape, service, fields that
 * exist, are not sensitive, are scalars and are written under names of their own).
 * @param {Model} model @returns {Diagnostic[]}
 */
export function checkTelemetryConsistency(model) {
  /** @type {Diagnostic[]} */
  const out = [];
  /** @param {string} code @param {Entity} e @param {string} message @param {(string|number)[]} [sub] */
  const err = (code, e, message, sub = []) => out.push({ code, severity: 'error', message, entityId: e.id, loc: e.loc, path: [...e.path, ...sub] });

  const sys = model.system;
  const t = sys?.data.telemetry;
  if (sys && isObj(t)) {
    /** @type {Set<string>} */
    const seen = new Set();
    list(t.services).forEach((s, i) => {
      if (!isObj(s)) return;
      const at = ['telemetry', 'services', i];
      if (!(typeof s.id === 'string' && SERVICE_RE.test(s.id))) err('telemetry.service', sys, `Telemetry service ${i + 1} needs an id of lower-case letters, digits and -, starting with a letter; found ${JSON.stringify(s.id)}.`, [...at, 'id']);
      else if (seen.has(s.id)) err('telemetry.service', sys, `Telemetry service "${s.id}" is declared twice.`, [...at, 'id']);
      else seen.add(s.id);
      if (!(typeof s.log === 'string' && s.log.trim() !== '' && !s.log.startsWith('/') && !/^[A-Za-z]:/.test(s.log) && !s.log.split(/[\\/]/).includes('..'))) err('telemetry.service', sys, `Telemetry service ${JSON.stringify(s.id)} needs "log": the path of its log file, relative to the deployment's working directory (no "..").`, [...at, 'log']);
    });
  }
  const services = telemetryServices(model);

  /** service -> log name -> event id */
  /** @type {Map<string, Map<string, string>>} */
  const names = new Map();
  for (const e of model.byKind.event ?? []) {
    const l = e.data.logging;
    if (l === undefined) continue;
    const at = ['logging'];
    if (!isObj(l) || typeof l.logged !== 'boolean') { err('event.logging-shape', e, `The logging of event "${e.id}" is {logged: true, service, level, name?, tenant?, fields} or {logged: false, reason}.`, at); continue; }
    if (l.logged === false) {
      const extra = Object.keys(l).filter((k) => k !== 'logged' && k !== 'reason');
      if (extra.length) err('event.logging-shape', e, `Event "${e.id}" is not logged, so its logging takes only a reason; ${extra.join(', ')} ${extra.length > 1 ? 'do' : 'does'} not apply.`, at);
      if (!nonEmpty(l.reason)) err('event.logging-shape', e, `Event "${e.id}" is not logged and needs the "reason" why not.`, [...at, 'reason']);
      continue;
    }
    if (l.reason !== undefined) err('event.logging-shape', e, `Event "${e.id}" is logged, so its logging has no "reason".`, [...at, 'reason']);
    if (typeof l.service !== 'string') err('event.logging-shape', e, `Event "${e.id}" is logged and needs the "service" whose log holds it.`, at);
    else if (!services.has(l.service)) err('event.logging-service', e, `Event "${e.id}" is logged by service "${l.service}", which system.telemetry does not declare${services.size ? ` (declared: ${[...services.keys()].join(', ')})` : ' (it declares no services)'}.`, [...at, 'service']);
    if (!LOG_LEVELS.includes(l.level)) err('event.logging-shape', e, `Event "${e.id}" is logged and needs a "level": ${LOG_LEVELS.join(', ')}.`, [...at, 'level']);
    if (!Array.isArray(l.fields)) err('event.logging-shape', e, `Event "${e.id}" is logged and needs "fields", the allowlist of payload fields its line holds (possibly empty); a payload is never logged whole.`, at);
    const logName = typeof l.name === 'string' ? l.name : e.id;
    if (!LOG_NAME_RE.test(logName)) err('event.logging-name', e, `Event "${e.id}" is logged as ${JSON.stringify(logName)}; a log name is lower-case words of letters, digits and _, joined by dots, such as record.updated.`, [...at, l.name === undefined ? 'logged' : 'name']);
    else if (typeof l.service === 'string') {
      const byName = names.get(l.service) ?? new Map();
      names.set(l.service, byName);
      if (byName.has(logName)) err('event.logging-name', e, `Events "${byName.get(logName)}" and "${e.id}" are both logged by service "${l.service}" as "${logName}"; a log line names one event.`, [...at, 'name']);
      else byName.set(logName, e.id);
    }

    /** Checks one logged payload field. @param {any} name @param {(string|number)[]} where @param {string} what */
    const checkField = (name, where, what) => {
      const f = payloadField(e, name);
      if (!f) { err('event.logging-field-unknown', e, `The ${what} "${name}" of event "${e.id}" is not one of its payload fields${list(e.data.payload).length ? ` (${list(e.data.payload).filter(isObj).map((p) => p.name).join(', ')})` : ' (it has none)'}.`, where); return; }
      const sensitive = typeof f.sensitive === 'string' ? f.sensitive : typeSensitivity(model, f.type);
      if (sensitive) err('event.logging-field-sensitive', e, `The ${what} "${name}" of event "${e.id}" is ${typeof f.sensitive === 'string' ? 'marked' : `of type "${f.type}", which is`} sensitive (${sensitive}); sensitive data is never logged.`, where);
      const cls = typeClass(model, f.type);
      if (!['bool', 'number', 'string', 'any'].includes(cls)) err('event.logging-field-type', e, `The ${what} "${name}" of event "${e.id}" is a ${cls}; a log line holds only scalars (booleans, numbers and strings, or an option of one).`, where);
    };
    if (l.tenant !== undefined) {
      if (typeof l.tenant !== 'string') err('event.logging-shape', e, `The "tenant" of event "${e.id}"'s logging names the payload field holding the tenant.`, [...at, 'tenant']);
      else checkField(l.tenant, [...at, 'tenant'], 'tenant field');
    }
    /** @type {Set<string>} */
    const written = new Set();
    list(l.fields).forEach((x, i) => {
      const where = [...at, 'fields', i];
      if (!isObj(x) || typeof x.field !== 'string') { err('event.logging-shape', e, `Logged field ${i + 1} of event "${e.id}" is {field, as?}: a payload field and the name it is written under.`, where); return; }
      const extra = Object.keys(x).filter((k) => k !== 'field' && k !== 'as');
      if (extra.length) err('event.logging-shape', e, `Logged field "${x.field}" of event "${e.id}": ${extra.join(', ')} ${extra.length > 1 ? 'are' : 'is'} not part of it (field, as).`, where);
      checkField(x.field, [...where, 'field'], 'logged field');
      if (x.field === l.tenant) err('event.logging-field-reserved', e, `Field "${x.field}" of event "${e.id}" is already written as the line's tenant.`, where);
      const as = typeof x.as === 'string' ? x.as : x.field;
      if (!FIELD_NAME_RE.test(as)) err('event.logging-field-reserved', e, `Logged field "${x.field}" of event "${e.id}" is written as ${JSON.stringify(as)}; a member name is lower-case letters, digits, _ and -, starting with a letter.`, [...where, x.as === undefined ? 'field' : 'as']);
      else if (RECORD_FIELDS.includes(as)) err('event.logging-field-reserved', e, `Logged field "${x.field}" of event "${e.id}" would be written as "${as}", which every log line already holds (${RECORD_FIELDS.join(', ')}); give it another name with "as".`, [...where, x.as === undefined ? 'field' : 'as']);
      else if (written.has(as)) err('event.logging-field-reserved', e, `Two logged fields of event "${e.id}" are written as "${as}".`, [...where, x.as === undefined ? 'field' : 'as']);
      else written.add(as);
    });
  }
  return out;
}

/**
 * With system.generation, every domain event (an event with domain: true) states its logging: logged, or
 * not logged with a reason.
 * @param {Model} model @returns {Gap[]}
 */
export function telemetryReadiness(model) {
  /** @type {Gap[]} */
  const out = [];
  for (const e of model.byKind.event ?? []) {
    if (e.data.domain === true && e.data.logging === undefined) out.push({ code: 'ready.event-logging-missing', severity: 'error', message: `Domain event "${e.id}" does not state its logging: {logged: true, service, level, fields} or {logged: false, reason}.`, entityId: e.id });
  }
  return out;
}
