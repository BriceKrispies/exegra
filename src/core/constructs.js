// Cross-cutting constructs: the patterns requirements repeat, stated as entities a generator can build code
// from. policy (who may do what), validation (what a value must meet), retention (how long records are
// kept), quota (how often a scope may act), retry (how a call or emit is repeated) and audit (what an act
// writes to an append-only log). This module holds their consistency rules (errors, always on) and their
// readiness rules (codes ready.*, errors only when the specification sets system.generation; see
// readiness.js). Pure and deterministic. docs/model-and-format.md, "Cross-cutting constructs".

import { parseExpr, exprRefs } from './expr.js';
import { typeClass, exprClass } from './codegen-model.js';
import { recordFields, isErasableRecordField } from './data-model.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */
/** @typedef {import('./codegen-model.js').TypeClass} TypeClass */
/** @typedef {{code: string, severity: 'error', message: string, entityId: string}} Gap */

/** The entity kinds of the constructs, which a requirement's realisedBy may name. */
export const CONSTRUCT_KINDS = Object.freeze(['policy', 'validation', 'retention', 'quota', 'retry', 'audit']);

/** The attributes of the principal an expression may read, and their classes. */
const PRINCIPAL = new Map(/** @type {[string, TypeClass][]} */ ([['id', 'string'], ['tenant', 'string'], ['role', 'string']]));

const DURATION_RE = /^(\d+(?:\.\d+)?)\s*(ns|us|ms|s|min|h|d)$/;
const NS = { ns: 1, us: 1e3, ms: 1e6, s: 1e9, min: 6e10, h: 3.6e12, d: 8.64e13 };

/**
 * A duration "<decimal> <unit>" (units ns, us, ms, s, min, h, d) in nanoseconds, or null when the text is not
 * a positive duration.
 * @param {any} text @returns {number|null}
 */
export function durationNs(text) {
  const m = typeof text === 'string' ? DURATION_RE.exec(text.trim()) : null;
  if (!m) return null;
  const v = Number(m[1]) * NS[/** @type {keyof typeof NS} */ (m[2])];
  return v > 0 ? v : null;
}

/** @param {any} v */
const isObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);
/** @param {any} v @returns {any[]} */
const list = (v) => (Array.isArray(v) ? v : []);
/** @param {any} v */
const posInt = (v) => Number.isInteger(v) && v >= 1;

/**
 * Named, typed fields (contract inputs or outputs, event payload, record fields) as a map from name to class.
 * @param {Model} model @param {any} fields @returns {Map<string, TypeClass>}
 */
const fieldClasses = (model, fields) => new Map(list(fields).filter((f) => isObj(f) && typeof f.name === 'string').map((f) => [f.name, typeClass(model, f.type)]));

/**
 * The consistency rules of the six constructs, and that only a requirement names constructs in realisedBy.
 * @param {Model} model @returns {Diagnostic[]}
 */
export function checkConstructConsistency(model) {
  /** @type {Diagnostic[]} */
  const out = [];
  /** @param {string} code @param {Entity} e @param {string} message @param {(string|number)[]} [sub] */
  const err = (code, e, message, sub = []) => out.push({ code, severity: 'error', message, entityId: e.id, loc: e.loc, path: [...e.path, ...sub] });
  /** @param {any} id @param {string} kind @returns {Entity|undefined} */
  const get = (id, kind) => {
    const e = typeof id === 'string' ? model.entities.get(id) : undefined;
    return e && e.kind === kind ? e : undefined;
  };
  const kind = (/** @type {string} */ k) => model.byKind[k] ?? [];

  /**
   * Exactly one of the target properties is set. Returns the one that is, or undefined.
   * @param {Entity} e @param {string[]} props @returns {string|undefined}
   */
  const target = (e, props) => {
    const set = props.filter((p) => e.data[p] !== undefined);
    if (set.length === 1) return set[0];
    err(`${e.kind}.target`, e, `${e.kind[0].toUpperCase()}${e.kind.slice(1)} "${e.id}" must name exactly one of ${props.join(', ')}; it names ${set.length ? set.join(' and ') : 'none'}.`, set.length ? [set[1]] : []);
    return undefined;
  };

  /**
   * An expression of a construct: it parses, every reference is in scope, and it is of the wanted class.
   * `scope` maps a head (request, record, event, ...) to its fields; `singles` are one-word references.
   * @param {Entity} e @param {any} src @param {(string|number)[]} sub
   * @param {Map<string, Map<string, TypeClass>>} scope @param {Map<string, TypeClass>} singles
   * @param {(cls: TypeClass) => string|undefined} judge  a complaint about the result class, or undefined
   */
  const checkExpr = (e, src, sub, scope, singles, judge) => {
    const parsed = parseExpr(src);
    if (!parsed.ok) { err(`${e.kind}.expr-syntax`, e, `Expression "${src}": ${parsed.error.message} (at character ${parsed.error.pos + 1}).`, sub); return; }
    const heads = [...scope.keys(), ...singles.keys()].join(', ');
    let bad = false;
    for (const path of exprRefs(parsed.ast)) {
      const ok = path.length === 1 ? singles.has(path[0]) : path.length === 2 && !!scope.get(path[0])?.has(path[1]);
      if (!ok) { bad = true; err(`${e.kind}.expr-reference`, e, `Expression "${src}": "${path.join('.')}" is not in scope here (in scope: ${heads || 'nothing'}${scope.size ? ', each with its declared fields' : ''}).`, sub); }
    }
    if (bad) return;
    const r = exprClass(parsed.ast, (path) => (path.length === 1 ? singles.get(path[0]) : scope.get(path[0])?.get(path[1])) ?? 'any');
    const complaint = r.error ?? judge(r.cls);
    if (complaint) err(`${e.kind}.expr-type`, e, `Expression "${src}": ${complaint}.`, sub);
  };
  /** @param {TypeClass} cls */
  const boolean = (cls) => (cls === 'bool' || cls === 'any' ? undefined : `it is a ${cls}, and a condition must be a boolean`);

  // --- policy ---------------------------------------------------------------
  for (const p of kind('policy')) {
    const on = target(p, ['contract', 'transition']);
    // An expression is checked once its target is known: the target decides what is in scope.
    if (!on || typeof p.data.condition !== 'string') continue;
    /** @type {Map<string, Map<string, TypeClass>>} */
    const scope = new Map([['principal', PRINCIPAL]]);
    const contract = on === 'contract' ? get(p.data.contract, 'contract') : undefined;
    if (contract) scope.set('request', fieldClasses(model, contract.data.inputs));
    const transition = on === 'transition' ? get(p.data.transition, 'transition') : undefined;
    const ev = transition ? get(transition.data.on, 'event') : undefined;
    if (ev) scope.set('event', fieldClasses(model, ev.data.payload));
    const resource = get(p.data.resource, 'record');
    if (resource) scope.set('record', fieldClasses(model, resource.data.fields));
    checkExpr(p, p.data.condition, ['condition'], scope, new Map(), boolean);
  }

  // --- validation -------------------------------------------------------------
  /** @type {Record<string, string[]>} */
  const PARAMS = { required: [], maxLength: ['maxLength', 'unit'], pattern: ['pattern'], range: ['min', 'max'], oneOf: ['values'], custom: ['expr'] };
  const ALL_PARAMS = ['maxLength', 'unit', 'pattern', 'min', 'max', 'values', 'expr'];
  for (const v of kind('validation')) {
    const d = v.data;
    const on = target(v, ['contract', 'record']);
    /** @type {TypeClass|undefined} */
    let cls;
    /** @type {Map<string, Map<string, TypeClass>>} */
    const scope = new Map();
    if (on === 'contract') {
      if (d.field !== undefined) err('validation.target', v, `Validation "${v.id}" targets a contract input, so it takes "input", not "field".`, ['field']);
      const c = get(d.contract, 'contract');
      const inputs = c ? fieldClasses(model, c.data.inputs) : undefined;
      if (inputs) scope.set('request', inputs);
      if (typeof d.input !== 'string') err('validation.target-unknown', v, `Validation "${v.id}" targets contract "${d.contract}" but names no "input".`, ['contract']);
      else if (inputs && !inputs.has(d.input)) err('validation.target-unknown', v, `Contract "${d.contract}" has no input "${d.input}".`, ['input']);
      else cls = inputs?.get(d.input);
    } else if (on === 'record') {
      if (d.input !== undefined) err('validation.target', v, `Validation "${v.id}" targets a record field, so it takes "field", not "input".`, ['input']);
      const r = get(d.record, 'record');
      const fields = r ? fieldClasses(model, r.data.fields) : undefined;
      if (fields) scope.set('record', fields);
      if (typeof d.field !== 'string') err('validation.target-unknown', v, `Validation "${v.id}" targets record "${d.record}" but names no "field".`, ['record']);
      else if (fields && !fields.has(d.field)) err('validation.target-unknown', v, `Record "${d.record}" has no field "${d.field}".`, ['field']);
      else cls = fields?.get(d.field);
    }
    const rule = typeof d.rule === 'string' && Object.hasOwn(PARAMS, d.rule) ? d.rule : undefined;
    if (!rule) continue;
    for (const k of ALL_PARAMS) if (d[k] !== undefined && !PARAMS[rule].includes(k)) err('validation.param', v, `"${k}" does not belong to rule ${rule}.`, [k]);
    const known = cls !== undefined && cls !== 'any';
    if (rule === 'maxLength') {
      if (!posInt(d.maxLength)) err('validation.param', v, `Rule maxLength needs "maxLength", a positive integer.`, ['maxLength']);
      if (known && cls !== 'string' && cls !== 'bytes' && cls !== 'list') err('validation.target-type', v, `Rule maxLength applies to a string, bytes or a list; the target is a ${cls}.`, ['rule']);
    } else if (rule === 'pattern') {
      if (typeof d.pattern !== 'string') err('validation.param', v, 'Rule pattern needs "pattern", a regular expression.', ['pattern']);
      else {
        try { new RegExp(d.pattern, 'u'); } catch (e) { err('validation.pattern', v, `Pattern "${d.pattern}" is not a regular expression: ${/** @type {Error} */ (e).message}.`, ['pattern']); }
      }
      if (known && cls !== 'string') err('validation.target-type', v, `Rule pattern applies to a string; the target is a ${cls}.`, ['rule']);
    } else if (rule === 'range') {
      const hasMin = d.min !== undefined, hasMax = d.max !== undefined;
      if (!hasMin && !hasMax) err('validation.param', v, 'Rule range needs "min", "max" or both.', ['rule']);
      else if (hasMin && hasMax && typeof d.min === 'number' && typeof d.max === 'number' && d.min > d.max) err('validation.range', v, `The range of "${v.id}" is empty: min ${d.min} is greater than max ${d.max}.`, ['min']);
      if (known && cls !== 'number') err('validation.target-type', v, `Rule range applies to a number; the target is a ${cls}.`, ['rule']);
    } else if (rule === 'oneOf') {
      if (!Array.isArray(d.values) || !d.values.length) err('validation.param', v, 'Rule oneOf needs a non-empty "values".', ['values']);
      else if (known) {
        const js = cls === 'bool' ? 'boolean' : cls === 'number' ? 'number' : cls === 'string' ? 'string' : undefined;
        d.values.forEach((/** @type {any} */ x, /** @type {number} */ i) => {
          if (typeof x !== js) err('validation.target-type', v, `Value ${JSON.stringify(x)} of rule oneOf is not a ${cls}, the class of the target.`, ['values', i]);
        });
      }
    } else if (rule === 'custom') {
      if (typeof d.expr !== 'string') err('validation.param', v, 'Rule custom needs "expr", a boolean expression.', ['expr']);
      else if (on) checkExpr(v, d.expr, ['expr'], scope, new Map([['value', cls ?? 'any']]), boolean);
    }
  }

  // --- retention --------------------------------------------------------------
  /** @type {Map<string, string>} */
  const retained = new Map();
  for (const t of kind('retention')) {
    const d = t.data;
    if (typeof d.record === 'string') {
      const first = retained.get(d.record);
      if (first) err('retention.duplicate', t, `Record "${d.record}" already has retention "${first}"; a record has at most one.`, ['record']);
      else retained.set(d.record, t.id);
    }
    if ((d.keepFor === undefined) === (d.until === undefined)) err('retention.period', t, `Retention "${t.id}" must state exactly one of "keepFor" (a duration) and "until" (an event).`, d.keepFor === undefined ? ['record'] : ['until']);
    else if (d.keepFor !== undefined && durationNs(d.keepFor) === null) err('retention.duration', t, `"keepFor" of retention "${t.id}" is ${JSON.stringify(d.keepFor)}; a duration is "<decimal> <unit>" with ns, us, ms, s, min, h or d.`, ['keepFor']);
    if (d.then === 'anonymise' && !(Array.isArray(d.fields) && d.fields.length)) err('retention.fields', t, `Retention "${t.id}" anonymises, so it names the fields it clears in "fields".`, ['then']);
    if (d.then !== 'anonymise' && d.fields !== undefined) err('retention.fields', t, `Retention "${t.id}" does not anonymise, so it takes no "fields".`, ['fields']);
    const r = get(d.record, 'record');
    if (r) {
      const names = new Set(recordFields(r).map(({ field }) => field.name));
      list(d.fields).forEach((n, i) => { if (typeof n === 'string' && !names.has(n)) err('retention.field-unknown', t, `Record "${r.id}" has no field "${n}".`, ['fields', i]); });
    }
    if (d.archiveTo !== undefined && d.then !== 'archive') err('retention.archive-target', t, `Retention "${t.id}" does not archive, so it takes no "archiveTo".`, ['archiveTo']);
  }

  // --- quota --------------------------------------------------------------------
  for (const q of kind('quota')) {
    const d = q.data;
    const on = target(q, ['contract', 'event']);
    if (d.limit !== undefined && !posInt(d.limit)) err('quota.limit', q, `The limit of quota "${q.id}" must be a positive integer.`, ['limit']);
    if (d.window !== undefined && durationNs(d.window) === null) err('quota.window', q, `The window of quota "${q.id}" is ${JSON.stringify(d.window)}; a duration is "<decimal> <unit>" with ns, us, ms, s, min, h or d.`, ['window']);
    if (!on) continue;
    if (d.onExceed === 'refuse' && on === 'contract') {
      const c = get(d.contract, 'contract');
      if (typeof d.error !== 'string') err('quota.error-missing', q, `Quota "${q.id}" refuses calls of contract "${d.contract}", so it names the contract error the refusal is in "error".`, ['onExceed']);
      else if (c && !list(c.data.errors).some((x) => isObj(x) && x.name === d.error)) err('quota.error-unknown', q, `Contract "${c.id}" has no error "${d.error}".`, ['error']);
    } else if (d.error !== undefined) {
      err('quota.error-misplaced', q, `Quota "${q.id}" takes an "error" only when it refuses calls of a contract.`, ['error']);
    }
  }

  // --- retry --------------------------------------------------------------------
  for (const y of kind('retry')) {
    const d = y.data;
    const on = target(y, ['contract', 'event']);
    if (d.attempts !== undefined && !posInt(d.attempts)) err('retry.attempts', y, `The attempts of retry "${y.id}" must be a positive integer.`, ['attempts']);
    /** @type {[string, any, (string|number)[]][]} */
    const durations = [['backoff base', d.backoff?.base, ['backoff', 'base']], ['backoff cap', d.backoff?.cap, ['backoff', 'cap']], ['timeout', d.timeout, ['timeout']]];
    for (const [what, value, sub] of durations) {
      if (value !== undefined && durationNs(value) === null) err('retry.duration', y, `The ${what} of retry "${y.id}" is ${JSON.stringify(value)}; a duration is "<decimal> <unit>" with ns, us, ms, s, min, h or d.`, sub);
    }
    if (isObj(d.backoff) && d.backoff.cap !== undefined) {
      if (d.backoff.kind !== 'exponential') err('retry.backoff', y, `Retry "${y.id}" backs off by a fixed wait, which has no "cap".`, ['backoff', 'cap']);
      else {
        const base = durationNs(d.backoff.base), cap = durationNs(d.backoff.cap);
        if (base !== null && cap !== null && cap < base) err('retry.backoff', y, `The backoff cap of retry "${y.id}" (${d.backoff.cap}) is shorter than its base (${d.backoff.base}).`, ['backoff', 'cap']);
      }
    }
    if (typeof d.idempotencyKey === 'string') {
      const owner = on === 'contract' ? get(d.contract, 'contract') : on === 'event' ? get(d.event, 'event') : undefined;
      const names = owner ? fieldClasses(model, owner.kind === 'contract' ? owner.data.inputs : owner.data.payload) : undefined;
      if (names && !names.has(d.idempotencyKey)) err('retry.idempotency-key-unknown', y, `"${d.idempotencyKey}" is not ${owner?.kind === 'contract' ? 'an input of contract' : 'a payload field of event'} "${owner?.id}".`, ['idempotencyKey']);
    }
  }

  // --- audit --------------------------------------------------------------------
  for (const a of kind('audit')) {
    const d = a.data;
    const on = target(a, ['contract', 'transition', 'event']);
    /** @type {Map<string, Map<string, TypeClass>>} */
    const scope = new Map([['principal', PRINCIPAL]]);
    if (on === 'contract') {
      const c = get(d.contract, 'contract');
      if (c) { scope.set('request', fieldClasses(model, c.data.inputs)); scope.set('response', fieldClasses(model, c.data.outputs)); }
    } else if (on) {
      const t = on === 'transition' ? get(d.transition, 'transition') : undefined;
      const ev = on === 'event' ? get(d.event, 'event') : t ? get(t.data.on, 'event') : undefined;
      if (ev) scope.set('event', fieldClasses(model, ev.data.payload));
    }
    const singles = new Map(/** @type {[string, TypeClass][]} */ ([['time', 'number']]));
    const r = get(d.record, 'record');
    const fields = r ? new Map(recordFields(r).map(({ field }) => [field.name, field])) : undefined;
    const capture = list(d.capture);
    if (Array.isArray(d.capture) && !capture.length) err('audit.capture', a, `Audit "${a.id}" captures nothing; "capture" lists the fields it writes.`, ['capture']);
    /** @type {Set<string>} */
    const seen = new Set();
    capture.forEach((c, i) => {
      if (!isObj(c) || typeof c.field !== 'string') return;
      if (seen.has(c.field)) err('audit.capture', a, `Audit "${a.id}" captures field "${c.field}" twice.`, ['capture', i, 'field']);
      seen.add(c.field);
      const f = fields?.get(c.field);
      if (fields && !f) { err('audit.field-unknown', a, `Record "${r?.id}" has no field "${c.field}".`, ['capture', i, 'field']); return; }
      if (!on || typeof c.from !== 'string') return;
      const want = f ? typeClass(model, f.type) : 'any';
      checkExpr(a, c.from, ['capture', i, 'from'], scope, singles, (cls) => (
        cls === want || cls === 'any' || want === 'any' || (cls === 'null' && f?.optional === true) ? undefined : `it is a ${cls}, but field "${c.field}" is a ${want}`));
    });
    if (d.immutability === 'chained-hash') {
      if (typeof d.chainField !== 'string') err('audit.chain-field', a, `Audit "${a.id}" is chained by hash, so it names the field that holds the previous entry's hash in "chainField".`, ['immutability']);
      else if (fields) {
        const f = fields.get(d.chainField);
        const cls = f ? typeClass(model, f.type) : undefined;
        if (!f) err('audit.chain-field', a, `Record "${r?.id}" has no field "${d.chainField}".`, ['chainField']);
        else if (cls !== 'bytes' && cls !== 'string' && cls !== 'any') err('audit.chain-field', a, `Chain field "${d.chainField}" is a ${cls}; a hash is held in bytes or a string.`, ['chainField']);
        else if (seen.has(d.chainField)) err('audit.chain-field', a, `Chain field "${d.chainField}" is filled by the chain, so it is not captured.`, ['chainField']);
      }
    } else if (d.chainField !== undefined) {
      err('audit.chain-field', a, `Audit "${a.id}" is not chained by hash, so it takes no "chainField".`, ['chainField']);
    }
  }

  // --- requirements realised by constructs ------------------------------------
  for (const c of kind('claim')) {
    if (c.data.realisedBy !== undefined && c.data.kind !== 'requirement') err('claim.realised-by-not-requirement', c, `Claim "${c.id}" is a ${c.data.kind} claim; only a requirement is realised by constructs ("realisedBy").`, ['realisedBy']);
  }
  return out;
}

/**
 * The readiness rules of the constructs: what a generator needs beyond consistency.
 * @param {Model} model @returns {Gap[]}
 */
export function constructReadiness(model) {
  /** @type {Gap[]} */
  const out = [];
  /** @param {Entity} e @param {string} code @param {string} message */
  const gap = (e, code, message) => out.push({ code, severity: 'error', message, entityId: e.id });
  const kind = (/** @type {string} */ k) => model.byKind[k] ?? [];
  /** @param {any} id @param {string} k */
  const get = (id, k) => {
    const e = typeof id === 'string' ? model.entities.get(id) : undefined;
    return e && e.kind === k ? e : undefined;
  };

  // Policies: every contract they govern says what happens when none matches; a transition is generated
  // code only in an implementation-level machine.
  /** @type {Set<string>} */
  const governed = new Set();
  for (const p of kind('policy')) {
    const c = get(p.data.contract, 'contract');
    if (c && c.data.policyDefault === undefined && !governed.has(c.id)) gap(c, 'ready.policy-default-missing', `Contract "${c.id}" is governed by policies but does not say what they decide when none matches ("policyDefault": deny or allow).`);
    if (c) governed.add(c.id);
    const t = get(p.data.transition, 'transition');
    const b = t?.owner ? get(t.owner, 'behavior') : undefined;
    if (b && b.data.level !== 'implementation') gap(p, 'ready.policy-transition-model-level', `Policy "${p.id}" governs transition "${t?.id}" of behavior "${b.id}", which is a model-level machine; generated code exists only for an implementation-level one.`);
  }

  // Validations: a length says what it counts.
  for (const v of kind('validation')) {
    if (v.data.rule === 'maxLength' && v.data.unit === undefined) gap(v, 'ready.validation-unit-missing', `Validation "${v.id}" limits a length but does not say whether it counts characters or bytes ("unit").`);
  }

  // Retentions: every record with personal or credential fields has one; an archive names where it goes.
  const retained = new Set(kind('retention').map((t) => t.data.record));
  for (const r of kind('record')) {
    if (!retained.has(r.id) && recordFields(r).some(({ field }) => isErasableRecordField(field))) gap(r, 'ready.retention-missing', `Record "${r.id}" holds personal or credential fields but no retention says how long it is kept.`);
  }
  for (const t of kind('retention')) {
    if (t.data.then === 'archive' && t.data.archiveTo === undefined) gap(t, 'ready.retention-archive-target-missing', `Retention "${t.id}" archives but names no component in "archiveTo".`);
  }

  // Quotas: where the counters are kept.
  for (const q of kind('quota')) {
    if (q.data.heldBy === undefined) gap(q, 'ready.quota-held-by-missing', `Quota "${q.id}" does not name the component that keeps its counters ("heldBy").`);
  }

  // Retries: a repeat is harmless, and an attempt ends.
  for (const y of kind('retry')) {
    const c = get(y.data.contract, 'contract');
    const needsKey = y.data.event !== undefined || (c !== undefined && c.data.idempotent !== true);
    if (needsKey && y.data.idempotencyKey === undefined) gap(y, 'ready.retry-idempotency-missing', `Retry "${y.id}" repeats ${c ? `contract "${c.id}", which is not idempotent,` : `event "${y.data.event}"`} without an "idempotencyKey".`);
    if (y.data.timeout === undefined) gap(y, 'ready.retry-timeout-missing', `Retry "${y.id}" does not say how long one attempt may take ("timeout").`);
  }

  // Audits: every required field of the record written is filled, except its key (assigned by the store)
  // and the chain field (filled by the chain).
  for (const a of kind('audit')) {
    const r = get(a.data.record, 'record');
    if (!r) continue;
    const filled = new Set([...list(a.data.capture).map((c) => c?.field), ...list(r.data.key), a.data.chainField]);
    for (const { field } of recordFields(r)) {
      if (field.optional !== true && !filled.has(field.name)) gap(a, 'ready.audit-field-unfilled', `Audit "${a.id}" writes record "${r.id}" but captures nothing for its required field "${field.name}".`);
    }
  }
  return out;
}
