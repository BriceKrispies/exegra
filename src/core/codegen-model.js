// What a code generator needs to know about data and interfaces, and the consistency rules over it (errors,
// always on): declared types, record constraints and schema versions, requirement realisation. Pure and
// deterministic. The readiness rules, which are errors only when the specification sets `system.generation`,
// are in readiness.js.

import { BUILTIN_TYPES, WIRE_CASES, isBuiltinType } from './builtin-types.js';
import { recordFields } from './data-model.js';
import { splitTop } from './type-expr.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */

const WRAPPER_RE = /^(list|option|set|shared)<(.+)>$/;
const MAP_RE = /^map<(.+)>$/;

/**
 * A type text read as list<T>, set<T>, option<T>, shared<T>, map<K, V> or a plain name. A map has exactly two top-level
 * arguments (split outside angle brackets, so map<K, map<K2, V>> is a map of maps); map<string> and map<a, b, c>
 * are plain names, which do not resolve. A set<T> is a JSON array of distinct items, in order. A shared<T> is a
 * sharing hint (Arc<T> in Rust), identical to T on the wire.
 * @param {any} name
 * @returns {{k: 'list', of: string}|{k: 'set', of: string}|{k: 'option', of: string}|{k: 'shared', of: string}|{k: 'map', key: string, value: string}|{k: 'name', name: string}}
 */
export function parseTypeName(name) {
  const text = typeof name === 'string' ? name.trim() : '';
  const wrapped = WRAPPER_RE.exec(text);
  if (wrapped) {
    const of = wrapped[2].trim();
    if (wrapped[1] === 'shared') return { k: 'shared', of };
    return wrapped[1] === 'list' ? { k: 'list', of } : wrapped[1] === 'set' ? { k: 'set', of } : { k: 'option', of };
  }
  const map = MAP_RE.exec(text);
  if (map) {
    const args = splitTop(map[1], ',');
    if (args.length === 2 && args[0] && args[1]) return { k: 'map', key: args[0], value: args[1] };
  }
  return { k: 'name', name: text };
}

/**
 * The type text a shared<T> hint wraps, with every hint removed: shared<shared<T>> is T. A sharing hint is
 * identical to T on the wire, so a reader that looks at the shape of a value uses this.
 * @param {string} name @returns {string}
 */
export function unsharedText(name) {
  let text = name.trim();
  for (let m = /^shared<(.+)>$/.exec(text); m; m = /^shared<(.+)>$/.exec(text)) text = m[1].trim();
  return text;
}

/**
 * A type name resolves when it is a built-in, the id of a `type` entity, list<T> / set<T> / option<T> / shared<T> of
 * a resolving T, or map<K, V> of a resolving K and V.
 * @param {Model} model @param {any} name
 * @returns {boolean}
 */
export function typeResolves(model, name) {
  if (typeof name !== 'string') return false;
  const p = parseTypeName(name);
  if (p.k === 'list' || p.k === 'set' || p.k === 'option' || p.k === 'shared') return typeResolves(model, p.of);
  if (p.k === 'map') return typeResolves(model, p.key) && typeResolves(model, p.value);
  const text = p.name;
  if (isBuiltinType(text)) return true;
  return model.entities.get(text)?.kind === 'type';
}

/**
 * What an expression can do with a value of a type: the class of the type. `any` is a type text that does not
 * resolve (free text such as principal-id), about which nothing is known, so nothing about it is refused. `json`
 * is any JSON value: it is compared only with == and != (with another json value or null), and has no fields. A
 * union and a map have the same opaque class.
 * @typedef {'bool'|'number'|'string'|'bytes'|'struct'|'list'|'json'|'null'|'any'} TypeClass
 */

const NUMBER_TYPES = ['u8', 'u16', 'u32', 'u64', 'i32', 'i64', 'f64', 'timestamp', 'duration'];

/**
 * The class of a type name: bool; number (the integers, f64, timestamp, duration); string (string, uuid, an enum);
 * bytes; json; struct; list (list<T> and set<T>); option<T> and shared<T> are the class of T. An id or scalar type has the class of its representation.
 * @param {Model} model @param {any} name
 * @returns {TypeClass}
 */
export function typeClass(model, name) {
  if (typeof name !== 'string') return 'any';
  const p = parseTypeName(name);
  if (p.k === 'map') return 'json';
  if (p.k === 'list' || p.k === 'set') return 'list';
  if (p.k === 'option' || p.k === 'shared') return typeClass(model, p.of);
  const text = p.name;
  if (text === 'bool') return 'bool';
  if (NUMBER_TYPES.includes(text)) return 'number';
  if (text === 'string' || text === 'uuid') return 'string';
  if (text === 'bytes') return 'bytes';
  if (text === 'json') return 'json';
  if (text === 'unit') return 'null';
  const t = model.entities.get(text);
  if (t?.kind !== 'type') return 'any';
  if (t.data.kind === 'enum') return 'string';
  if (t.data.kind === 'struct') return 'struct';
  if (t.data.kind === 'union') return 'json';
  return isBuiltinType(t.data.repr) ? typeClass(model, t.data.repr) : 'any';
}

/**
 * The structure of a type, for typing and evaluating function bodies (WG-4933, src/core/function.js), where the
 * class of typeClass is too coarse: a struct's fields and a union's variants must be known. Ids and scalars keep
 * their id and representation, enums their values. A set<T> has the structure of list<T>, marked set: true.
 * @typedef {{k: 'prim', name: string} | {k: 'enum', id: string, values: string[]} | {k: 'alias', id: string, repr: string}
 *   | {k: 'struct', id: string, fields: {name: string, type: TypeStructure, optional: boolean}[]}
 *   | {k: 'union', id: string, encoding: {tag: string, tagField?: string, contentField?: string, variantCase?: string}, variants: {name: string, newtype: boolean, tuple?: boolean, fields: {name: string, type: TypeStructure, optional: boolean}[]}[]}
 *   | {k: 'list', of: TypeStructure, set?: boolean} | {k: 'option', of: TypeStructure} | {k: 'map', key: TypeStructure, value: TypeStructure}} TypeStructure
 */

/**
 * The structure of a type name, or undefined when it does not resolve. Struct fields and union variants are
 * resolved lazily (getters), so recursive types such as an expression union are fine.
 * @param {Model} model @param {any} name
 * @returns {TypeStructure|undefined}
 */
export function typeStructure(model, name) {
  if (typeof name !== 'string' || !typeResolves(model, name)) return undefined;
  const p = parseTypeName(name);
  if (p.k === 'list') return { k: 'list', of: /** @type {TypeStructure} */ (typeStructure(model, p.of)) };
  // A set holds and types as a list; set: true lets the debug rule of format write it as Rust writes a BTreeSet.
  if (p.k === 'set') return { k: 'list', of: /** @type {TypeStructure} */ (typeStructure(model, p.of)), set: true };
  if (p.k === 'option') return { k: 'option', of: /** @type {TypeStructure} */ (typeStructure(model, p.of)) };
  // shared<T> is a sharing hint (WG-4960): its structure is T's.
  if (p.k === 'shared') return typeStructure(model, p.of);
  if (p.k === 'map') return { k: 'map', key: /** @type {TypeStructure} */ (typeStructure(model, p.key)), value: /** @type {TypeStructure} */ (typeStructure(model, p.value)) };
  if (isBuiltinType(p.name)) return { k: 'prim', name: p.name };
  const t = /** @type {Entity} */ (model.entities.get(p.name));
  const d = t.data;
  /** @param {any} fs */
  const fieldsOf = (fs) => (Array.isArray(fs) ? fs : []).filter(isObj).map((/** @type {any} */ f) => ({
    name: String(f.name),
    get type() { return /** @type {TypeStructure} */ (typeStructure(model, f.type) ?? { k: 'prim', name: 'json' }); },
    optional: f.optional === true,
  }));
  if (d.kind === 'enum') return { k: 'enum', id: t.id, values: (Array.isArray(d.values) ? d.values : []).filter((/** @type {any} */ v) => typeof v === 'string') };
  if (d.kind === 'struct') return { k: 'struct', id: t.id, get fields() { return fieldsOf(d.fields); } };
  if (d.kind === 'union') {
    return {
      k: 'union', id: t.id,
      get encoding() {
        const e = isObj(d.encoding) ? d.encoding : {};
        return { tag: typeof e.tag === 'string' ? e.tag : 'external', tagField: e.tagField, contentField: e.contentField, variantCase: e.variantCase };
      },
      get variants() { return (Array.isArray(d.variants) ? d.variants : []).filter(isObj).map((/** @type {any} */ v) => ({ name: String(v.name), newtype: v.newtype === true, tuple: v.tuple === true, fields: fieldsOf(v.fields) })); },
    };
  }
  return { k: 'alias', id: t.id, repr: typeof d.repr === 'string' ? d.repr : 'json' };
}

/**
 * The class of an expression whose references have the classes `refClass` gives, and the first type error in
 * it. The rules are those evalExpr applies when it runs: !, &&, || and => take booleans; -, *, /, %, <, <=, >
 * and >= take numbers; + takes two numbers or two strings; == and != take two values of one class, or null.
 * A json value therefore takes part only in == and != (no ordering, no arithmetic, no concatenation).
 * A reference of class any satisfies every rule.
 * @param {import('./expr.js').Ast} ast @param {(path: string[]) => TypeClass} refClass
 * @returns {{cls: TypeClass, error?: string}}
 */
export function exprClass(ast, refClass) {
  /** @type {string|undefined} */
  let error;
  /** @param {TypeClass} c @param {TypeClass} want @param {string} op */
  const need = (c, want, op) => {
    if (c !== want && c !== 'any' && error === undefined) error = `operator "${op}" needs a ${want === 'bool' ? 'boolean' : want}, not a ${c}`;
  };
  /** @param {import('./expr.js').Ast} n @returns {TypeClass} */
  const walk = (n) => {
    if (n.t === 'lit') return n.v === null ? 'null' : typeof n.v === 'boolean' ? 'bool' : typeof n.v === 'number' ? 'number' : 'string';
    if (n.t === 'ref') return refClass(n.path);
    if (n.t === 'un') {
      const a = walk(n.a);
      if (n.op === '!') { need(a, 'bool', '!'); return 'bool'; }
      need(a, 'number', '-');
      return 'number';
    }
    const a = walk(n.a), b = walk(n.b);
    if (['&&', '||', '=>'].includes(n.op)) { need(a, 'bool', n.op); need(b, 'bool', n.op); return 'bool'; }
    if (n.op === '==' || n.op === '!=') {
      if (a !== b && a !== 'any' && b !== 'any' && a !== 'null' && b !== 'null' && error === undefined) error = `operator "${n.op}" compares a ${a} with a ${b}`;
      return 'bool';
    }
    if (n.op === '+' && (a === 'string' || b === 'string')) {
      need(a, 'string', '+'); need(b, 'string', '+');
      return 'string';
    }
    need(a, 'number', n.op); need(b, 'number', n.op);
    return ['<', '<=', '>', '>='].includes(n.op) ? 'bool' : 'number';
  };
  const cls = walk(ast);
  return error === undefined ? { cls } : { cls, error };
}

/** @param {any} v */
const isObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);

/**
 * The consistency rules of types, records and requirement realisation.
 * @param {Model} model @returns {Diagnostic[]}
 */
export function checkCodegenConsistency(model) {
  /** @type {Diagnostic[]} */
  const out = [];
  /** @param {string} code @param {Entity} e @param {string} message @param {(string|number)[]} [sub] */
  const err = (code, e, message, sub = []) => out.push({ code, severity: 'error', message, entityId: e.id, loc: e.loc, path: [...e.path, ...sub] });

  for (const t of model.byKind.type ?? []) {
    const d = t.data;
    if (isBuiltinType(t.id)) err('type.shadows-builtin', t, `Type "${t.id}" has the name of a built-in representation type (${BUILTIN_TYPES.join(', ')}).`, ['id']);
    if (d.kind === 'id' || d.kind === 'scalar') {
      if (typeof d.repr !== 'string') err('type.repr-missing', t, `Type "${t.id}" is ${d.kind === 'id' ? 'an id' : 'a scalar'} and needs a "repr", one of ${BUILTIN_TYPES.join(', ')}.`, ['kind']);
      else if (!isBuiltinType(d.repr)) err('type.repr-not-builtin', t, `Type "${t.id}" has representation "${d.repr}", which is not a built-in type (${BUILTIN_TYPES.join(', ')}).`, ['repr']);
      else if (d.repr === 'unit') err('type.repr-not-builtin', t, `Type "${t.id}" is represented as unit, which holds no value; an id or scalar is represented by a built-in type that does.`, ['repr']);
      else if (d.repr === 'json') err('type.repr-json', t, `Type "${t.id}" is ${d.kind === 'id' ? 'an id' : 'a scalar'} represented as json; an id or scalar has a representation of a single kind, so use json directly where any JSON value is meant.`, ['repr']);
    } else if (d.kind === 'enum') {
      if (!Array.isArray(d.values) || !d.values.length) err('type.values-missing', t, `Type "${t.id}" is an enum and needs a non-empty "values".`, ['kind']);
    } else if (d.kind === 'struct') {
      const fields = Array.isArray(d.fields) ? d.fields : [];
      if (!fields.length) err('type.fields-missing', t, `Type "${t.id}" is a struct and needs "fields".`, ['kind']);
      fields.forEach((/** @type {any} */ f, /** @type {number} */ i) => {
        if (isObj(f) && !typeResolves(model, f.type)) err('type.field-unresolved', t, `Field "${f.name}" of struct "${t.id}" has type "${f.type}", which is neither built-in nor a declared type.`, ['fields', i, 'type']);
      });
    }
  }

  for (const r of model.byKind.record ?? []) {
    const fields = recordFields(r);
    const names = new Set(fields.map(({ field }) => field.name));
    for (const { field, index } of fields) {
      if (field.onDelete !== undefined && field.refersTo === undefined) err('record.on-delete-without-refers-to', r, `Field "${field.name}" of record "${r.id}" has "onDelete" but no "refersTo".`, ['fields', index, 'onDelete']);
      if (field.onDelete === 'set-null' && field.optional !== true) err('record.set-null-required', r, `Field "${field.name}" of record "${r.id}" is "set-null" on delete, so it must be "optional": true.`, ['fields', index, 'onDelete']);
    }
    (Array.isArray(r.data.unique) ? r.data.unique : []).forEach((/** @type {any} */ set, /** @type {number} */ i) => {
      (Array.isArray(set) ? set : []).forEach((/** @type {any} */ n, /** @type {number} */ j) => {
        if (typeof n === 'string' && !names.has(n)) err('record.unique-field', r, `Unique set ${i + 1} of record "${r.id}" names "${n}", which is not one of its fields.`, ['unique', i, j]);
      });
    });
    (Array.isArray(r.data.indexes) ? r.data.indexes : []).forEach((/** @type {any} */ ix, /** @type {number} */ i) => {
      (isObj(ix) && Array.isArray(ix.fields) ? ix.fields : []).forEach((/** @type {any} */ n, /** @type {number} */ j) => {
        if (typeof n === 'string' && !names.has(n)) err('record.index-field', r, `Index "${ix.name}" of record "${r.id}" names "${n}", which is not one of its fields.`, ['indexes', i, 'fields', j]);
      });
    });
    const version = r.data.schemaVersion;
    if (version !== undefined && !(Number.isInteger(version) && version >= 1)) err('record.schema-version', r, `The schema version of record "${r.id}" must be an integer of at least 1.`, ['schemaVersion']);
    if (Array.isArray(r.data.changes)) {
      const versions = r.data.changes.map((/** @type {any} */ c) => (isObj(c) ? c.version : undefined));
      const top = Number.isInteger(version) ? version : 0;
      const want = Array.from({ length: top }, (_, i) => i + 1);
      const ok = versions.length === want.length && want.every((v, i) => versions[i] === v);
      if (!ok) err('record.changes-version', r, `The changes of record "${r.id}" must list versions 1 to its schema version (${top || 'not set'}) in order without gaps; found ${versions.length ? versions.join(', ') : 'none'}.`, ['changes']);
    }
  }

  // A requirement that generated code guarantees is checked by some claim over the model, or realised by at
  // least one cross-cutting construct (constructs.js) that generated code is built from.
  for (const c of model.byKind.claim ?? []) {
    if (c.data.kind !== 'requirement' || c.data.realisation !== 'construction') continue;
    const modelled = (model.byKind.claim ?? []).some((m) => (Array.isArray(m.data.models) ? m.data.models : [m.data.models]).includes(c.id));
    const realised = Array.isArray(c.data.realisedBy) && c.data.realisedBy.length > 0;
    if (!modelled && !realised) err('requirement.construction-unmodelled', c, `Requirement "${c.id}" is realised by construction, but no claim has "models" naming it and it names no construct in "realisedBy".`, ['realisation']);
  }
  out.push(...checkWireConsistency(model));
  return out;
}

/** The failures a serving runtime reports itself, which an error body maps to error kinds (system.generation.errorBody.runtime). */
export const RUNTIME_FAILURES = Object.freeze(['unauthenticated', 'forbidden', 'invalid-request', 'timeout', 'unavailable', 'internal']);

/** @param {any} v */
const isStatus = (v) => Number.isInteger(v) && v >= 400 && v <= 599;

/**
 * The status an error of a contract travels with: its own `status`, the status of its `kind`, or the defaults of
 * system.generation (`errorKind`, then `errorStatus`). Undefined when none applies.
 * @param {Model} model @param {any} error @returns {number|undefined}
 */
export function errorStatus(model, error) {
  const g = isObj(model.system.data.generation) ? model.system.data.generation : {};
  const kinds = isObj(g.errorKinds) ? g.errorKinds : {};
  if (isObj(error) && isStatus(error.status)) return error.status;
  const kind = isObj(error) && typeof error.kind === 'string' ? error.kind : g.errorKind;
  if (typeof kind === 'string' && Object.hasOwn(kinds, kind) && isStatus(kinds[kind])) return kinds[kind];
  return isStatus(g.errorStatus) ? g.errorStatus : undefined;
}

/**
 * The rules of contract errors on the wire: error statuses and kinds and the error body
 * (system.generation.errorKinds, errorStatus, errorKind, errorBody; contract errors[].status and errors[].kind).
 * @param {Model} model @returns {Diagnostic[]}
 */
function checkWireConsistency(model) {
  /** @type {Diagnostic[]} */
  const out = [];
  /** @param {string} code @param {Entity} e @param {string} message @param {(string|number)[]} [sub] */
  const err = (code, e, message, sub = []) => out.push({ code, severity: 'error', message, entityId: e.id, loc: e.loc, path: [...e.path, ...sub] });
  const sys = model.system;
  const g = isObj(sys.data.generation) ? sys.data.generation : {};
  const at = (/** @type {(string|number)[]} */ ...sub) => ['generation', ...sub];

  // Error kinds: a name per kind of failure, each with one HTTP status.
  /** @type {Record<string, number>} */
  const kinds = Object.create(null);
  if (g.errorKinds !== undefined) {
    if (!isObj(g.errorKinds)) err('generation.error-kinds', sys, 'system.generation.errorKinds must map each error kind to its HTTP status.', at('errorKinds'));
    else {
      for (const [k, v] of Object.entries(g.errorKinds)) {
        if (isStatus(v)) kinds[k] = v;
        else err('generation.error-kinds', sys, `Error kind "${k}" has status ${JSON.stringify(v)}; a status is an integer from 400 to 599.`, at('errorKinds', k));
      }
    }
  }
  const kindNames = Object.keys(kinds);
  if (g.errorStatus !== undefined && !isStatus(g.errorStatus)) err('generation.error-status', sys, `system.generation.errorStatus is ${JSON.stringify(g.errorStatus)}; a status is an integer from 400 to 599.`, at('errorStatus'));
  if (g.errorKind !== undefined && !(typeof g.errorKind === 'string' && g.errorKind in kinds)) err('generation.error-status', sys, `system.generation.errorKind is ${JSON.stringify(g.errorKind)}, which is not one of the error kinds (${kindNames.join(', ') || 'none declared'}).`, at('errorKind'));
  if (g.errorKind !== undefined && g.errorStatus !== undefined) err('generation.error-status', sys, 'system.generation states both errorKind and errorStatus; the default of an error is one or the other.', at('errorStatus'));

  // The error body: a struct type whose code field holds the kind, with the message and correlation fields
  // named, every other field optional, and every runtime failure mapped to a kind.
  const body = g.errorBody;
  if (body !== undefined && isObj(body)) {
    if (!kindNames.length) err('generation.error-body-kinds', sys, 'system.generation.errorBody needs errorKinds: the code of a body is the kind of its failure.', at('errorBody'));
    const t = typeof body.type === 'string' ? model.entities.get(body.type) : undefined;
    if (t && t.kind === 'type' && t.data.kind !== 'struct') err('generation.error-body-type', sys, `The error body type "${body.type}" is ${t.data.kind === 'enum' ? 'an enum' : `a ${t.data.kind}`}; it must be a struct.`, at('errorBody', 'type'));
    const fields = t?.kind === 'type' && t.data.kind === 'struct' && Array.isArray(t.data.fields) ? t.data.fields.filter(isObj) : null;
    if (fields) {
      /** @type {[string, string][]} */
      const roles = [['code', 'the kind of the failure'], ['message', 'a message safe to show the caller'], ['correlation', "the caller's correlation id"]];
      /** @type {Set<string>} */
      const named = new Set();
      for (const [role, what] of roles) {
        const name = body[role];
        if (name === undefined) {
          if (role !== 'correlation') err('generation.error-body-field', sys, `system.generation.errorBody names no "${role}" field: the field of "${body.type}" that holds ${what}.`, at('errorBody'));
          continue;
        }
        const f = fields.find((/** @type {any} */ x) => x.name === name);
        if (!f) { err('generation.error-body-field', sys, `The error body "${role}" is "${name}", which is not a field of "${body.type}".`, at('errorBody', role)); continue; }
        named.add(f.name);
        if (f.optional === true) err('generation.error-body-field', sys, `Field "${f.name}" of "${body.type}" holds ${what} and must not be optional.`, at('errorBody', role));
        if (role === 'code') {
          const ct = typeof f.type === 'string' ? model.entities.get(f.type) : undefined;
          if (ct?.kind !== 'type' || ct.data.kind !== 'enum') err('generation.error-body-field', sys, `Field "${f.name}" of "${body.type}" holds the kind of a failure, so its type must be an enum; it is "${f.type}".`, at('errorBody', role));
          else {
            const values = Array.isArray(ct.data.values) ? ct.data.values : [];
            const missing = kindNames.filter((k) => !values.includes(k));
            if (missing.length) err('generation.error-body-code', sys, `The code field of the error body has type "${ct.id}", whose values lack the error kind${missing.length > 1 ? 's' : ''} ${missing.map((k) => `"${k}"`).join(', ')}.`, at('errorBody', role));
          }
        } else if (f.type !== 'string') err('generation.error-body-field', sys, `Field "${f.name}" of "${body.type}" holds ${what}, so its type must be string; it is "${f.type}".`, at('errorBody', role));
      }
      for (const f of fields) {
        if (!named.has(f.name) && f.optional !== true) err('generation.error-body-type', sys, `Field "${f.name}" of the error body type "${body.type}" is neither its code, message nor correlation, so it must be optional: a body made for a runtime failure leaves it out.`, at('errorBody', 'type'));
      }
    }
    const runtime = isObj(body.runtime) ? body.runtime : {};
    if (body.runtime !== undefined && !isObj(body.runtime)) err('generation.error-body-runtime', sys, 'system.generation.errorBody.runtime must map each runtime failure to an error kind.', at('errorBody', 'runtime'));
    for (const failure of RUNTIME_FAILURES) {
      const kind = runtime[failure];
      if (kind === undefined) err('generation.error-body-runtime', sys, `system.generation.errorBody.runtime does not say which error kind the runtime failure "${failure}" is answered with.`, at('errorBody', 'runtime'));
      else if (!(typeof kind === 'string' && kind in kinds)) err('generation.error-body-runtime', sys, `The runtime failure "${failure}" is answered with error kind ${JSON.stringify(kind)}, which is not one of the error kinds (${kindNames.join(', ') || 'none declared'}).`, at('errorBody', 'runtime', failure));
    }
    for (const key of Object.keys(runtime)) {
      if (!RUNTIME_FAILURES.includes(key)) err('generation.error-body-runtime', sys, `"${key}" is not a runtime failure; they are ${RUNTIME_FAILURES.join(', ')}.`, at('errorBody', 'runtime', key));
    }
  }

  // Contracts: each error states a status or a kind, not both.
  for (const c of model.byKind.contract ?? []) {
    (Array.isArray(c.data.errors) ? c.data.errors : []).forEach((/** @type {any} */ e, /** @type {number} */ i) => {
      if (!isObj(e)) return;
      if (e.status !== undefined && !isStatus(e.status)) err('contract.error-status', c, `The error "${e.name}" of contract "${c.id}" has status ${JSON.stringify(e.status)}; a status is an integer from 400 to 599.`, ['errors', i, 'status']);
      if (e.kind !== undefined && !(typeof e.kind === 'string' && e.kind in kinds)) err('contract.error-kind-unknown', c, `The error "${e.name}" of contract "${c.id}" has kind ${JSON.stringify(e.kind)}, which is not one of the error kinds of system.generation.errorKinds (${kindNames.join(', ') || 'none declared'}).`, ['errors', i, 'kind']);
      if (e.status !== undefined && e.kind !== undefined) err('contract.error-status-kind', c, `The error "${e.name}" of contract "${c.id}" states both a status and a kind; its status is the one of its kind, so state one.`, ['errors', i]);
    });
  }
  return out;
}
