// The JSON a value is written as on the wire, and read back from (WG-4968): the simulator of the wire encodings of
// unions (external, internal, adjacent and untagged tags, newtype and tuple variants, variantCase) and of struct
// field names in a wire case. Values are in memory as src/core/function-value.js holds them (a UnionValue for a union,
// null for an absent option, a Map for a map); the type is a TypeStructure from typeStructure in codegen-model.js.
// docs/model-and-format.md, "Unions, maps and constraints".
//
// An optional field (and an option<T> field) is read when absent or null; an optional field is left out when it is
// null, while an option<T> field is written as null. Unknown members are refused when a struct is read. An untagged
// union is read by trying its variants in declaration order and taking the first that reads the value; the rule
// type.encoding keeps two variants from being written as the same shape.

import { UnionValue, FnEvalError, decodeValue, primName, isNumberType, compareKeys } from './function-value.js';
import { variantWireName } from './type-shapes.js';

/** @typedef {import('./function-value.js').FnType} FnType */
/** @typedef {import('./function-value.js').FnField} FnField */

/** @param {any} v */
const isObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);
/** @param {any} v */
const show = (v) => JSON.stringify(v);

/**
 * The name of a struct or variant field on the wire in a wire case; the names as written (kebab-case) when none.
 * @param {string} name @param {string|undefined} wireCase snake_case, kebab-case or camelCase
 */
export function fieldWireName(name, wireCase) {
  if (wireCase === 'snake_case') return variantWireName(name, 'snake_case');
  if (wireCase === 'camelCase') {
    const [first, ...rest] = variantWireName(name, 'kebab-case').split('-');
    return first + rest.map((w) => w[0].toUpperCase() + w.slice(1)).join('');
  }
  return name;
}

/**
 * A value written as its wire JSON.
 * @param {FnType} type @param {any} value @param {{wireCase?: string}} [opts]
 * @returns {any}
 */
export function toWire(type, value, opts = {}) {
  /** @param {string} n */
  const name = (n) => fieldWireName(n, opts.wireCase);
  /** @param {FnType} t @param {any} v @returns {any} */
  const go = (t, v) => {
    if (v === null || v === undefined) return null;
    switch (t.k) {
      case 'option': return go(t.of, v);
      case 'list': return v.map((/** @type {any} */ x) => go(t.of, x));
      case 'map': {
        /** @type {Record<string, any>} */
        const out = {};
        for (const k of [...v.keys()].sort(compareKeys)) out[String(k)] = go(t.value, v.get(k));
        return out;
      }
      case 'struct': return fieldsOut(t.fields, v);
      case 'union': return unionOut(t, v);
      default: return v;
    }
  };
  /** @param {FnField[]} fields @param {any} src */
  const fieldsOut = (fields, src) => {
    /** @type {Record<string, any>} */
    const out = {};
    for (const f of fields) {
      const x = src[f.name];
      if ((x === null || x === undefined) && f.optional) continue;
      out[name(f.name)] = go(f.type, x);
    }
    return out;
  };
  /** @param {Extract<FnType, {k: 'union'}>} t @param {UnionValue} v */
  const unionOut = (t, v) => {
    const variant = t.variants.find((x) => x.name === v.variant);
    if (!variant) throw new FnEvalError(`${t.id} has no variant "${v.variant}"`);
    const enc = t.encoding;
    const w = variantWireName(variant.name, enc.variantCase);
    const fs = variant.fields;
    const content = () => (variant.newtype ? go(fs[0].type, v.fields[fs[0].name]) : variant.tuple ? fs.map((f) => go(f.type, v.fields[f.name])) : fieldsOut(fs, v.fields));
    switch (enc.tag) {
      case 'untagged': return fs.length ? content() : null;
      case 'internal': return { [/** @type {string} */ (enc.tagField)]: w, ...(fs.length ? fieldsOut(fs, v.fields) : {}) };
      case 'adjacent': return fs.length ? { [/** @type {string} */ (enc.tagField)]: w, [/** @type {string} */ (enc.contentField)]: content() } : { [/** @type {string} */ (enc.tagField)]: w };
      default: return fs.length ? { [w]: content() } : w;
    }
  };
  return go(type, value);
}

/**
 * A value read from its wire JSON. Throws FnEvalError when the JSON is not a value of the type.
 * @param {FnType} type @param {any} json @param {{wireCase?: string}} [opts]
 * @returns {any}
 */
export function fromWire(type, json, opts = {}) {
  /** @param {string} n */
  const name = (n) => fieldWireName(n, opts.wireCase);
  /** @param {string} at @param {any} j @param {string} why */
  const bad = (at, j, why) => new FnEvalError(`${at}: ${show(j)} is not ${why}`);
  /** @param {FnType} t @param {any} j @param {string} at @returns {any} */
  const go = (t, j, at) => {
    switch (t.k) {
      case 'option': return j === null || j === undefined ? null : go(t.of, j, at);
      case 'list':
        if (!Array.isArray(j)) throw bad(at, j, 'a list');
        return Object.freeze(j.map((x, i) => go(t.of, x, `${at}[${i}]`)));
      case 'map': {
        if (!isObj(j)) throw bad(at, j, 'a map (an object)');
        const m = new Map();
        for (const [k, v] of Object.entries(j)) m.set(isNumberType(t.key) && /^-?\d+$/.test(k) ? Number(k) : k, go(t.value, v, `${at}.${k}`));
        return m;
      }
      case 'struct': return fieldsIn(t.fields, j, at, t.id, []);
      case 'union': return unionIn(t, j, at);
      default: return decodeValue(t, j, at);
    }
  };
  /** @param {FnField[]} fields @param {any} j @param {string} at @param {string} what @param {string[]} extra members that belong to the encoding */
  const fieldsIn = (fields, j, at, what, extra) => {
    if (!isObj(j)) throw bad(at, j, `a ${what} object`);
    const known = new Set([...fields.map((f) => name(f.name)), ...extra]);
    for (const k of Object.keys(j)) if (!known.has(k)) throw new FnEvalError(`${at}: ${what} has no member "${k}"`);
    /** @type {Record<string, any>} */
    const out = {};
    for (const f of fields) {
      const x = j[name(f.name)];
      if (x === undefined || (x === null && (f.optional || f.type.k === 'option'))) {
        if (!f.optional && f.type.k !== 'option' && primName(f.type) !== 'json') throw new FnEvalError(`${at}: member "${name(f.name)}" of ${what} is missing`);
        out[f.name] = null;
      } else out[f.name] = go(f.type, x, `${at}.${name(f.name)}`);
    }
    return Object.freeze(out);
  };
  /** @param {Extract<FnType, {k: 'union'}>} t @param {any} j @param {string} at */
  const unionIn = (t, j, at) => {
    const enc = t.encoding;
    /** @param {{name: string}} v */
    const wireName = (v) => variantWireName(v.name, enc.variantCase);
    /** @param {Extract<FnType, {k: 'union'}>['variants'][number]} variant @param {any} c @param {string} where @param {string[]} extra */
    const body = (variant, c, where, extra) => {
      const fs = variant.fields;
      if (variant.newtype) return new UnionValue(t.id, variant.name, { [fs[0].name]: go(fs[0].type, c, where) });
      if (variant.tuple) {
        if (!Array.isArray(c) || c.length !== fs.length) throw bad(where, c, `an array of ${fs.length} values`);
        return new UnionValue(t.id, variant.name, Object.fromEntries(fs.map((f, i) => [f.name, go(f.type, c[i], `${where}[${i}]`)])));
      }
      return new UnionValue(t.id, variant.name, fieldsIn(fs, c, where, `${t.id}.${variant.name}`, extra));
    };
    switch (enc.tag) {
      case 'untagged': {
        for (const variant of t.variants) {
          if (!variant.fields.length) { if (j === null) return new UnionValue(t.id, variant.name, {}); continue; }
          try { return body(variant, j, at, []); } catch (e) { if (!(e instanceof FnEvalError)) throw e; }
        }
        throw bad(at, j, `a ${t.id}: no variant of the untagged union reads it`);
      }
      case 'internal': {
        const tf = /** @type {string} */ (enc.tagField);
        if (!isObj(j) || typeof j[tf] !== 'string') throw bad(at, j, `a ${t.id} object with a "${tf}" member`);
        const variant = t.variants.find((x) => wireName(x) === j[tf]);
        if (!variant) throw new FnEvalError(`${at}: ${t.id} has no variant written "${j[tf]}"`);
        const rest = Object.fromEntries(Object.entries(j).filter(([k]) => k !== tf));
        if (!variant.fields.length) {
          if (Object.keys(rest).length) throw new FnEvalError(`${at}: variant ${variant.name} of ${t.id} has no fields`);
          return new UnionValue(t.id, variant.name, {});
        }
        return body(variant, rest, at, []);
      }
      case 'adjacent': {
        const tf = /** @type {string} */ (enc.tagField), cf = /** @type {string} */ (enc.contentField);
        if (!isObj(j) || typeof j[tf] !== 'string') throw bad(at, j, `a ${t.id} object with a "${tf}" member`);
        const variant = t.variants.find((x) => wireName(x) === j[tf]);
        if (!variant) throw new FnEvalError(`${at}: ${t.id} has no variant written "${j[tf]}"`);
        for (const k of Object.keys(j)) if (k !== tf && k !== cf) throw new FnEvalError(`${at}: ${t.id} has no member "${k}"`);
        if (!variant.fields.length) {
          if (cf in j) throw new FnEvalError(`${at}: variant ${variant.name} of ${t.id} has no fields, so no "${cf}"`);
          return new UnionValue(t.id, variant.name, {});
        }
        if (!(cf in j)) throw new FnEvalError(`${at}: variant ${variant.name} of ${t.id} needs a "${cf}" member`);
        return body(variant, j[cf], `${at}.${cf}`, []);
      }
      default: {
        if (typeof j === 'string') {
          const variant = t.variants.find((x) => wireName(x) === j);
          if (!variant) throw new FnEvalError(`${at}: ${t.id} has no variant written "${j}"`);
          if (variant.fields.length) throw new FnEvalError(`${at}: variant ${variant.name} of ${t.id} has fields; write {"${j}": ...}`);
          return new UnionValue(t.id, variant.name, {});
        }
        if (!isObj(j) || Object.keys(j).length !== 1) throw bad(at, j, `a ${t.id}: a unit variant's name or {"Variant": content}`);
        const [k, c] = Object.entries(j)[0];
        const variant = t.variants.find((x) => wireName(x) === k);
        if (!variant) throw new FnEvalError(`${at}: ${t.id} has no variant written "${k}"`);
        if (!variant.fields.length) throw new FnEvalError(`${at}: variant ${variant.name} of ${t.id} is a unit variant; write "${k}"`);
        return body(variant, c, `${at}.${k}`, []);
      }
    }
  };
  return go(type, json, 'value');
}
