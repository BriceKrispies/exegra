// The rules of union types, their wire encoding, id and scalar constraints, map keys and recursion (WG-4925).
// Errors, always on, like the other consistency rules of types (codegen-model.js). Pure and deterministic.
//
//   type.union-variants  a union has variants, each named once, with fields named once; a newtype variant has one field;
//                        a tuple variant has two or more fields, none optional, and is not also a newtype
//   type.union-field     the type of a variant field resolves
//   type.encoding        tag, tagField, contentField and variantCase agree with each other and with the variants (an
//                        internal tag writes no newtype or tuple variant)
//   type.map-key         a map key is string, an integer built-in, or an id or scalar over one
//   type.recursion       a struct does not contain itself through struct fields alone
//   type.constraints     pattern, minLength, maxLength only on an id or scalar whose representation takes them

import { parseTypeName, typeResolves, unsharedText } from './codegen-model.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */

export const INTEGER_TYPES = Object.freeze(['u8', 'u16', 'u32', 'u64', 'i32', 'i64']);
/** How the variant names of a union are written on the wire; the names as written when none is given. */
export const VARIANT_CASES = Object.freeze(['PascalCase', 'snake_case', 'kebab-case']);
/** How a union is tagged on the wire (serde's forms); external is the default. */
export const UNION_TAGS = Object.freeze(['external', 'internal', 'adjacent']);

/** @param {any} v */
const isObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);

/** @param {any} kind */
const kindText = (kind) => (kind === undefined ? 'of no kind' : `${/^[aeiou]/.test(kind) ? 'an' : 'a'} ${kind}`);

/**
 * The name a variant has on the wire: its words (split at - _ spaces and lower-to-upper changes) written in the
 * case; `undefined` keeps the name as written.
 * @param {string} name @param {string|undefined} variantCase
 * @returns {string}
 */
export function variantWireName(name, variantCase) {
  if (variantCase === undefined) return name;
  const words = name
    .replace(/([a-z0-9])([A-Z])/g, '$1 $2')
    .replace(/([A-Z]+)([A-Z][a-z])/g, '$1 $2')
    .split(/[\s_-]+/)
    .filter(Boolean)
    .map((w) => w.toLowerCase());
  if (variantCase === 'snake_case') return words.join('_');
  if (variantCase === 'kebab-case') return words.join('-');
  return words.map((w) => w[0].toUpperCase() + w.slice(1)).join('');
}

/**
 * Whether a type text may be the key of a map<K, V>.
 * @param {Model} model @param {string} text
 */
function isMapKey(model, text) {
  const key = unsharedText(text);
  if (key === 'string' || INTEGER_TYPES.includes(key)) return true;
  const t = model.entities.get(key);
  return t?.kind === 'type' && (t.data.kind === 'id' || t.data.kind === 'scalar') && (t.data.repr === 'string' || INTEGER_TYPES.includes(t.data.repr));
}

/**
 * The map keys in a type text that resolve but cannot be keys. A key that does not resolve is the readiness
 * rules' business, so it is not reported twice.
 * @param {Model} model @param {any} text
 * @returns {string[]}
 */
function badMapKeys(model, text) {
  const p = parseTypeName(text);
  if (p.k === 'list' || p.k === 'set' || p.k === 'option' || p.k === 'shared') return badMapKeys(model, p.of);
  if (p.k === 'name') return [];
  return [...(typeResolves(model, p.key) && !isMapKey(model, p.key) ? [p.key] : []), ...badMapKeys(model, p.key), ...badMapKeys(model, p.value)];
}

/** @param {string} pattern */
function regexCompiles(pattern) {
  try { new RegExp(pattern, 'u'); return true; } catch { return false; }
}

/**
 * The structs a struct holds directly: through a field whose type is a struct's name (or shared<that name>, which
 * holds it as T does), not through list, set, option, map or a union, whose values may be empty or absent.
 * @param {Model} model @param {Entity} t @returns {string[]}
 */
function directStructs(model, t) {
  return (Array.isArray(t.data.fields) ? t.data.fields : [])
    .map((/** @type {any} */ f) => (isObj(f) && typeof f.type === 'string' ? unsharedText(f.type) : ''))
    .filter((/** @type {string} */ n) => model.entities.get(n)?.kind === 'type' && model.entities.get(n)?.data.kind === 'struct');
}

/** @param {Model} model @param {Entity} t @param {(code: string, message: string, sub?: (string|number)[]) => void} err */
function checkUnion(model, t, err) {
  const d = t.data;
  const enc = isObj(d.encoding) ? d.encoding : {};
  const tag = enc.tag ?? 'external';
  const an = tag === 'internal' ? 'an' : 'a';
  const variants = Array.isArray(d.variants) ? d.variants : [];
  if (!variants.length) err('type.union-variants', `Type "${t.id}" is a union and needs a non-empty "variants".`, ['variants']);
  /** @type {Set<string>} */
  const seen = new Set();
  /** @type {Map<string, string>} */
  const wire = new Map();
  variants.forEach((/** @type {any} */ v, /** @type {number} */ i) => {
    const at = ['variants', i];
    if (!isObj(v) || typeof v.name !== 'string' || !v.name.trim()) { err('type.union-variants', `Variant ${i + 1} of union "${t.id}" needs a "name".`, [...at, 'name']); return; }
    if (seen.has(v.name)) err('type.union-variants', `Union "${t.id}" has the variant "${v.name}" twice.`, [...at, 'name']);
    seen.add(v.name);
    const w = variantWireName(v.name, enc.variantCase);
    const first = wire.get(w);
    if (first !== undefined && first !== v.name) err('type.union-variants', `Variants "${first}" and "${v.name}" of union "${t.id}" are both written "${w}" on the wire.`, [...at, 'name']);
    wire.set(w, first ?? v.name);
    const fields = Array.isArray(v.fields) ? v.fields : [];
    /** @type {Set<string>} */
    const names = new Set();
    fields.forEach((/** @type {any} */ f, /** @type {number} */ j) => {
      if (!isObj(f) || typeof f.name !== 'string') { err('type.union-field', `Field ${j + 1} of variant "${v.name}" of union "${t.id}" needs a "name" and a "type".`, [...at, 'fields', j]); return; }
      if (names.has(f.name)) err('type.union-variants', `Variant "${v.name}" of union "${t.id}" has the field "${f.name}" twice.`, [...at, 'fields', j, 'name']);
      names.add(f.name);
      if (!typeResolves(model, f.type)) err('type.union-field', `Field "${f.name}" of variant "${v.name}" of union "${t.id}" has ${f.type === undefined ? 'no type' : `type "${f.type}", which is neither built-in nor a declared type`}.`, [...at, 'fields', j, 'type']);
    });
    if (v.newtype === true && fields.length !== 1) err('type.union-variants', `Variant "${v.name}" of union "${t.id}" is a newtype and needs exactly one field; it has ${fields.length}.`, [...at, 'newtype']);
    if (v.tuple === true) {
      if (v.newtype === true) err('type.union-variants', `Variant "${v.name}" of union "${t.id}" is both a newtype and a tuple; a variant with one positional field is a newtype, with two or more a tuple.`, [...at, 'tuple']);
      else if (fields.length < 2) err('type.union-variants', `Variant "${v.name}" of union "${t.id}" is a tuple and needs two or more fields; it has ${fields.length}${fields.length === 1 ? ', so it is a newtype' : ''}.`, [...at, 'tuple']);
      fields.forEach((/** @type {any} */ f, /** @type {number} */ j) => {
        if (isObj(f) && f.optional === true) err('type.union-variants', `Field "${f.name}" of tuple variant "${v.name}" of union "${t.id}" is optional; a positional field is always written, so use option<T> for one that may be null.`, [...at, 'fields', j, 'optional']);
      });
    }
    if (tag === 'internal' && v.tuple === true) err('type.encoding', `Variant "${v.name}" of union "${t.id}" is a tuple, which an internally tagged union cannot write; internal tagging needs struct-like or unit variants.`, [...at, 'tuple']);
    if (tag === 'internal' && v.newtype === true) err('type.encoding', `Variant "${v.name}" of union "${t.id}" is a newtype, which an internally tagged union cannot write; internal tagging needs struct-like or unit variants.`, [...at, 'newtype']);
    if (tag === 'internal' && typeof enc.tagField === 'string' && names.has(enc.tagField)) err('type.encoding', `Variant "${v.name}" of union "${t.id}" has a field named "${enc.tagField}", which is the tag field of its internal encoding.`, [...at, 'fields']);
  });
  if (d.encoding === undefined) return;
  const at = ['encoding'];
  if (!isObj(d.encoding)) { err('type.encoding', `The "encoding" of union "${t.id}" is {tag, tagField?, contentField?, variantCase?}.`, at); return; }
  if (enc.tag !== undefined && !UNION_TAGS.includes(enc.tag)) err('type.encoding', `The tag of union "${t.id}" is "${enc.tag}"; it is one of ${UNION_TAGS.join(', ')}.`, [...at, 'tag']);
  if (enc.variantCase !== undefined && !VARIANT_CASES.includes(enc.variantCase)) err('type.encoding', `The variantCase of union "${t.id}" is "${enc.variantCase}"; it is one of ${VARIANT_CASES.join(', ')}.`, [...at, 'variantCase']);
  if (enc.tagField !== undefined && tag === 'external') err('type.encoding', `Union "${t.id}" has a tagField but an external tag; a tagField belongs to an internal or adjacent encoding.`, [...at, 'tagField']);
  if (enc.contentField !== undefined && tag !== 'adjacent') err('type.encoding', `Union "${t.id}" has a contentField but ${an} ${tag} tag; a contentField belongs to an adjacent encoding.`, [...at, 'contentField']);
  if ((tag === 'internal' || tag === 'adjacent') && !(typeof enc.tagField === 'string' && enc.tagField)) err('type.encoding', `Union "${t.id}" has ${an} ${tag} tag and needs a tagField.`, [...at, 'tag']);
  if (tag === 'adjacent' && !(typeof enc.contentField === 'string' && enc.contentField)) err('type.encoding', `Union "${t.id}" has an adjacent tag and needs a contentField.`, [...at, 'tag']);
  if (tag === 'adjacent' && enc.tagField !== undefined && enc.tagField === enc.contentField) err('type.encoding', `The tagField and contentField of union "${t.id}" are both "${enc.tagField}".`, [...at, 'contentField']);
}

/** @param {Entity} t @param {(code: string, message: string, sub?: (string|number)[]) => void} err */
function checkConstraints(t, err) {
  const d = t.data;
  const c = d.constraints;
  const at = ['constraints'];
  if (d.kind !== 'id' && d.kind !== 'scalar') { err('type.constraints', `Type "${t.id}" is ${kindText(d.kind)} and has "constraints"; only an id or scalar type takes them.`, at); return; }
  if (!isObj(c)) { err('type.constraints', `The "constraints" of type "${t.id}" are {pattern?, minLength?, maxLength?}.`, at); return; }
  const repr = d.repr === undefined ? 'nothing' : `"${d.repr}"`;
  for (const k of Object.keys(c)) if (!['pattern', 'minLength', 'maxLength'].includes(k)) err('type.constraints', `Type "${t.id}" has the constraint "${k}"; the constraints are pattern, minLength and maxLength.`, [...at, k]);
  if (c.pattern !== undefined) {
    if (typeof c.pattern !== 'string' || !regexCompiles(c.pattern)) err('type.constraints', `The pattern of type "${t.id}" is not a valid regular expression.`, [...at, 'pattern']);
    else if (d.repr !== 'string') err('type.constraints', `Type "${t.id}" has a pattern but is represented as ${repr}; a pattern needs a string.`, [...at, 'pattern']);
  }
  for (const k of ['minLength', 'maxLength']) {
    if (c[k] === undefined) continue;
    if (!Number.isInteger(c[k]) || c[k] < 0) err('type.constraints', `The ${k} of type "${t.id}" must be a non-negative integer.`, [...at, k]);
    else if (d.repr !== 'string' && d.repr !== 'bytes') err('type.constraints', `Type "${t.id}" has a ${k} but is represented as ${repr}; a length needs a string or bytes.`, [...at, k]);
  }
  if (Number.isInteger(c.minLength) && Number.isInteger(c.maxLength) && c.minLength > c.maxLength) err('type.constraints', `Type "${t.id}" has a minLength above its maxLength.`, [...at, 'minLength']);
}

/**
 * The consistency rules of unions, encodings, constraints, map keys and recursion.
 * @param {Model} model @returns {Diagnostic[]}
 */
export function checkTypeShapes(model) {
  /** @type {Diagnostic[]} */
  const out = [];
  /** @param {string} code @param {Entity} e @param {string} message @param {(string|number)[]} [sub] */
  const report = (code, e, message, sub = []) => out.push({ code, severity: 'error', message, entityId: e.id, loc: e.loc, path: [...e.path, ...sub] });
  const types = model.byKind.type ?? [];

  for (const t of types) {
    const d = t.data;
    /** @param {string} code @param {string} message @param {(string|number)[]} [sub] */
    const err = (code, message, sub) => report(code, t, message, sub);
    if (d.kind === 'union') checkUnion(model, t, err);
    else {
      if (d.variants !== undefined) err('type.union-variants', `Type "${t.id}" is ${kindText(d.kind)} and has "variants"; only a union has variants.`, ['variants']);
      if (d.encoding !== undefined) err('type.encoding', `Type "${t.id}" is ${kindText(d.kind)} and has an "encoding"; only a union has a wire encoding.`, ['encoding']);
    }
    if (d.constraints !== undefined) checkConstraints(t, err);
  }

  // Map keys, wherever a type text is written.
  /** @param {Entity} e @param {any} text @param {(string|number)[]} sub */
  const keys = (e, text, sub) => {
    for (const k of badMapKeys(model, text)) report('type.map-key', e, `"${k}" cannot be the key of a map in "${String(text).trim()}"; a key is string, an integer type (${INTEGER_TYPES.join(', ')}), or an id or scalar type over one.`, sub);
  };
  /** @param {Entity} e @param {string} prop */
  const scan = (e, prop) => {
    (Array.isArray(e.data[prop]) ? e.data[prop] : []).forEach((/** @type {any} */ f, /** @type {number} */ i) => { if (isObj(f)) keys(e, f.type, [prop, i, 'type']); });
  };
  for (const t of types) {
    scan(t, 'fields');
    (Array.isArray(t.data.variants) ? t.data.variants : []).forEach((/** @type {any} */ v, /** @type {number} */ i) => {
      (isObj(v) && Array.isArray(v.fields) ? v.fields : []).forEach((/** @type {any} */ f, /** @type {number} */ j) => { if (isObj(f)) keys(t, f.type, ['variants', i, 'fields', j, 'type']); });
    });
  }
  for (const r of model.byKind.record ?? []) scan(r, 'fields');
  for (const c of model.byKind.contract ?? []) for (const p of ['inputs', 'outputs', 'errors']) scan(c, p);
  for (const e of model.byKind.event ?? []) scan(e, 'payload');
  for (const b of model.byKind.behavior ?? []) {
    (Array.isArray(b.data.variables) ? b.data.variables : []).forEach((/** @type {any} */ v, /** @type {number} */ i) => { if (isObj(v)) keys(b, v.repr, ['variables', i, 'repr']); });
  }

  // A struct that holds itself through struct fields alone would be infinitely large. A union variant, a list, a
  // set, an option or a map can be empty or absent, so each of them may close a cycle.
  const structs = types.filter((t) => t.data.kind === 'struct');
  /** @param {Entity} from @returns {Set<string>} */
  const reach = (from) => {
    /** @type {Set<string>} */
    const seen = new Set();
    const stack = directStructs(model, from);
    while (stack.length) {
      const n = /** @type {string} */ (stack.pop());
      if (seen.has(n)) continue;
      seen.add(n);
      const e = model.entities.get(n);
      if (e) stack.push(...directStructs(model, e));
    }
    return seen;
  };
  const reached = new Map(structs.map((t) => [t.id, reach(t)]));
  for (const t of structs) {
    if (!reached.get(t.id)?.has(t.id)) continue;
    const cycle = structs.filter((o) => reached.get(t.id)?.has(o.id) && reached.get(o.id)?.has(t.id));
    if (cycle[0] !== t) continue;
    report('type.recursion', t, `Struct "${t.id}" contains itself through struct fields alone (${cycle.map((o) => o.id).join(', ')}), so a value would be infinitely large; close the cycle through a list, set, option, map or union variant.`, ['fields']);
  }
  return out;
}
