// Values of function bodies (WG-4933) as Exegra evaluates them in JavaScript, and how the examples of a function
// write them in JSON. Pure. docs/model-and-format.md, "Functions".
//
// In memory: bool, number and string as themselves; an enum value as its name; an id or scalar as its
// representation; a struct as a frozen object of its fields (an absent optional field is null); a union value as
// a UnionValue; a list as an array; a map as a Map; option<T> as null or the T; the unit value as UNIT (null in
// JSON). In examples (JSON) a union is
// written in serde's external form whatever its wire encoding: a unit variant is its name, a newtype variant
// {"Name": value}, any other {"Name": {fields}}; a map is an object (integer keys as decimal strings); result<T, E>
// is {"Ok": t} or {"Err": e}.

import { INT_RANGES } from './expr.js';

/** @typedef {import('./codegen-model.js').TypeStructure} TypeStructure */
/**
 * A type of the body language: a type of the format, result<T, E>, never (fail) and unknown (the element of [] or
 * {}, the inner type of null), which fits any type. A list made from set<T> carries set: true (it is written as a
 * set by the debug rule of format).
 * @typedef {{k: 'prim', name: string} | {k: 'enum', id: string, values: string[]} | {k: 'alias', id: string, repr: string}
 *   | {k: 'struct', id: string, fields: FnField[]} | {k: 'union', id: string, variants: {name: string, newtype: boolean, tuple?: boolean, fields: FnField[]}[]}
 *   | {k: 'list', of: FnType, set?: boolean} | {k: 'option', of: FnType} | {k: 'map', key: FnType, value: FnType}
 *   | {k: 'result', ok: FnType, err: FnType} | {k: 'never'} | {k: 'unknown'}} FnType
 * @typedef {{name: string, type: FnType, optional: boolean}} FnField
 */

/** The value of the built-in type unit (Rust `()`); examples write it as null. */
export class UnitValue {
  constructor() { Object.freeze(this); }
}
/** The one unit value. */
export const UNIT = new UnitValue();

export class UnionValue {
  /** @param {string} type @param {string} variant @param {Record<string, any>} fields */
  constructor(type, variant, fields) {
    this.type = type;
    this.variant = variant;
    this.fields = Object.freeze({ ...fields });
    Object.freeze(this);
  }
}

/** An error of evaluation: a wrong example value, an overflow, a division by zero. */
export class FnEvalError extends Error {
  /** @param {string} message */
  constructor(message) {
    super(message);
    this.name = 'FnEvalError';
  }
}

/** The type id result values carry. */
export const RESULT_TYPE = '$result';

/** @param {any} value */
export const ok = (value) => new UnionValue(RESULT_TYPE, 'Ok', { value });
/** @param {any} error */
export const errOf = (error) => new UnionValue(RESULT_TYPE, 'Err', { error });

/**
 * Structural equality of values.
 * @param {any} a @param {any} b @returns {boolean}
 */
export function valueEq(a, b) {
  if (a === b) return true;
  if (typeof a !== 'object' || typeof b !== 'object' || a === null || b === null) return false;
  if (a instanceof UnionValue || b instanceof UnionValue) {
    return a instanceof UnionValue && b instanceof UnionValue && a.variant === b.variant && valueEq(a.fields, b.fields);
  }
  if (a instanceof Map || b instanceof Map) {
    if (!(a instanceof Map && b instanceof Map) || a.size !== b.size) return false;
    for (const [k, v] of a) if (!b.has(k) || !valueEq(v, b.get(k))) return false;
    return true;
  }
  if (Array.isArray(a) !== Array.isArray(b)) return false;
  if (Array.isArray(a)) return a.length === b.length && a.every((x, i) => valueEq(x, b[i]));
  const ka = Object.keys(a);
  return ka.length === Object.keys(b).length && ka.every((k) => Object.hasOwn(b, k) && valueEq(a[k], b[k]));
}

/**
 * The order of map keys and of sortBy keys: numbers numerically, strings by Unicode scalar values (Rust's str
 * order), so a generated BTreeMap iterates as Exegra does.
 * @param {any} a @param {any} b @returns {number}
 */
export function compareKeys(a, b) {
  if (typeof a === 'number' && typeof b === 'number') return a < b ? -1 : a > b ? 1 : 0;
  const sa = [...String(a)], sb = [...String(b)];
  for (let i = 0; i < Math.min(sa.length, sb.length); i++) {
    const d = /** @type {number} */ (sa[i].codePointAt(0)) - /** @type {number} */ (sb[i].codePointAt(0));
    if (d !== 0) return d < 0 ? -1 : 1;
  }
  return sa.length - sb.length < 0 ? -1 : sa.length === sb.length ? 0 : 1;
}

/** The built-in number types. */
const NUMBER_PRIMS = ['u8', 'u16', 'u32', 'u64', 'i32', 'i64', 'f64', 'timestamp', 'duration'];

/** The built-in representation of a scalar type (itself, or an id's or scalar's repr). @param {FnType} t @returns {string|undefined} */
export function primName(t) {
  if (t.k === 'prim') return t.name;
  if (t.k === 'alias') return t.repr;
  return undefined;
}

/** Whether a type is one of the integer types (or an id or scalar over one). @param {FnType} t */
export function isIntType(t) {
  const n = primName(t);
  return n !== undefined && Object.hasOwn(INT_RANGES, n);
}

/** @param {FnType} t */
export function isNumberType(t) {
  const n = primName(t);
  return n !== undefined && (NUMBER_PRIMS.includes(n) || n === 'number');
}

/** A type as written. @param {FnType} t @returns {string} */
export function typeText(t) {
  switch (t.k) {
    case 'prim': return t.name === 'number' ? 'a number' : t.name;
    case 'enum': case 'alias': case 'struct': case 'union': return t.id;
    case 'list': case 'option': return `${t.k}<${typeText(t.of)}>`;
    case 'map': return `map<${typeText(t.key)}, ${typeText(t.value)}>`;
    case 'result': return `result<${typeText(t.ok)}, ${typeText(t.err)}>`;
    case 'never': return 'never';
    default: return 'unknown';
  }
}

/** @param {any} v */
const isObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);
/** @param {any} v */
const show = (v) => JSON.stringify(v);

/**
 * A JSON example value read as a value of type `t`. Throws FnEvalError when it is not one.
 * @param {FnType} t @param {any} json @param {string} at where the value is, for messages
 * @returns {any}
 */
export function decodeValue(t, json, at) {
  const bad = (/** @type {string} */ why) => new FnEvalError(`${at}: ${show(json)} is not ${why}`);
  switch (t.k) {
    case 'prim': case 'alias': {
      const n = /** @type {string} */ (primName(t));
      if (n === 'json') return json;
      if (n === 'unit') { if (json !== null) throw bad('the unit value, written null'); return UNIT; }
      if (n === 'bool') { if (typeof json !== 'boolean') throw bad('a bool'); return json; }
      if (n === 'string' || n === 'uuid' || n === 'bytes') { if (typeof json !== 'string') throw bad(`a ${n}`); return json; }
      if (typeof json !== 'number' || !Number.isFinite(json)) throw bad(`a ${n}`);
      if (Object.hasOwn(INT_RANGES, n)) {
        const [lo, hi] = INT_RANGES[n];
        if (!Number.isInteger(json) || json < lo || json > hi) throw bad(`a ${n}`);
      }
      return json;
    }
    case 'enum':
      if (typeof json !== 'string' || !t.values.includes(json)) throw bad(`a value of enum ${t.id} (${t.values.join(', ')})`);
      return json;
    case 'struct': {
      if (!isObj(json)) throw bad(`a ${t.id} object`);
      const fields = t.fields;
      for (const k of Object.keys(json)) if (!fields.some((f) => f.name === k)) throw new FnEvalError(`${at}: ${t.id} has no field "${k}"`);
      /** @type {Record<string, any>} */
      const out = {};
      for (const f of fields) {
        const v = json[f.name];
        if ((v === undefined || v === null) && primName(f.type) === 'unit') out[f.name] = UNIT;
        else if (v === undefined || v === null) {
          if (!f.optional && f.type.k !== 'option') throw new FnEvalError(`${at}: field "${f.name}" of ${t.id} is missing`);
          out[f.name] = null;
        } else out[f.name] = decodeValue(f.type, v, `${at}.${f.name}`);
      }
      return Object.freeze(out);
    }
    case 'union': {
      const variants = t.variants;
      if (typeof json === 'string') {
        const v = variants.find((x) => x.name === json);
        if (!v) throw bad(`a variant of ${t.id} (${variants.map((x) => x.name).join(', ')})`);
        if (v.fields.length) throw new FnEvalError(`${at}: variant ${json} of ${t.id} has fields; write {"${json}": ...}`);
        return new UnionValue(t.id, v.name, {});
      }
      if (!isObj(json) || Object.keys(json).length !== 1) throw bad(`a ${t.id} value: a unit variant's name or {"Variant": content}`);
      const [name, content] = Object.entries(json)[0];
      const v = variants.find((x) => x.name === name);
      if (!v) throw new FnEvalError(`${at}: ${t.id} has no variant "${name}"`);
      if (!v.fields.length) throw new FnEvalError(`${at}: variant ${name} of ${t.id} is a unit variant; write "${name}"`);
      if (v.newtype) return new UnionValue(t.id, v.name, { [v.fields[0].name]: decodeValue(v.fields[0].type, content, `${at}.${name}`) });
      return new UnionValue(t.id, v.name, decodeValue({ k: 'struct', id: `${t.id}.${name}`, fields: v.fields }, content, `${at}.${name}`));
    }
    case 'list':
      if (!Array.isArray(json)) throw bad('a list');
      return Object.freeze(json.map((x, i) => decodeValue(t.of, x, `${at}[${i}]`)));
    case 'option':
      return json === null ? null : decodeValue(t.of, json, at);
    case 'map': {
      if (!isObj(json)) throw bad('a map (an object)');
      const m = new Map();
      for (const [k, v] of Object.entries(json)) {
        const key = isNumberType(t.key) ? decodeValue(t.key, /^-?\d+$/.test(k) ? Number(k) : k, `${at} key`) : decodeValue(t.key, k, `${at} key`);
        m.set(key, decodeValue(t.value, v, `${at}.${k}`));
      }
      return m;
    }
    case 'result': {
      if (!isObj(json) || Object.keys(json).length !== 1 || !('Ok' in json || 'Err' in json)) throw bad('{"Ok": value} or {"Err": error}');
      return 'Ok' in json ? ok(decodeValue(t.ok, json.Ok, `${at}.Ok`)) : errOf(decodeValue(t.err, json.Err, `${at}.Err`));
    }
    default:
      return json;
  }
}

/**
 * A value written as JSON, the way examples write it.
 * @param {any} v @returns {any}
 */
export function encodeValue(v) {
  if (v instanceof UnitValue) return null;
  if (v instanceof UnionValue) {
    const names = Object.keys(v.fields);
    if (v.type === RESULT_TYPE) return { [v.variant]: encodeValue(v.variant === 'Ok' ? v.fields.value : v.fields.error) };
    if (!names.length) return v.variant;
    return { [v.variant]: encodeValue(v.fields) };
  }
  if (v instanceof Map) {
    /** @type {Record<string, any>} */
    const out = {};
    for (const k of [...v.keys()].sort(compareKeys)) out[String(k)] = encodeValue(v.get(k));
    return out;
  }
  if (Array.isArray(v)) return v.map(encodeValue);
  if (isObj(v)) return Object.fromEntries(Object.entries(v).map(([k, x]) => [k, encodeValue(x)]));
  return v;
}

/**
 * Encode with the type, so a newtype variant is written {"Name": value} as examples write it.
 * @param {FnType} t @param {any} v @returns {any}
 */
export function encodeTyped(t, v) {
  if (v === null || v === undefined) return null;
  switch (t.k) {
    case 'option': return encodeTyped(t.of, v);
    case 'list': return v.map((/** @type {any} */ x) => encodeTyped(t.of, x));
    case 'map': {
      /** @type {Record<string, any>} */
      const out = {};
      for (const k of [...v.keys()].sort(compareKeys)) out[String(k)] = encodeTyped(t.value, v.get(k));
      return out;
    }
    case 'struct': return Object.fromEntries(t.fields.map((f) => [f.name, encodeTyped(f.type, v[f.name])]).filter(([, x]) => x !== null));
    case 'union': {
      const variant = t.variants.find((x) => x.name === v.variant);
      if (!variant || !variant.fields.length) return v.variant;
      if (variant.newtype) return { [v.variant]: encodeTyped(variant.fields[0].type, v.fields[variant.fields[0].name]) };
      return { [v.variant]: encodeTyped({ k: 'struct', id: v.variant, fields: variant.fields }, v.fields) };
    }
    case 'result': return v.variant === 'Ok' ? { Ok: encodeTyped(t.ok, v.fields.value) } : { Err: encodeTyped(t.err, v.fields.error) };
    default: return encodeValue(v);
  }
}

/**
 * How format writes a value into a `{}` placeholder, as Rust's Display does: a string as it is, an integer in
 * decimal, an f64 in decimal without an exponent (Rust `{}` of f64: 1.0 is 1, 1e21 is 1000000000000000000000), a
 * bool as true or false, an enum value as its name.
 * @param {any} v @param {FnType} [t] the static type, which tells an f64 from an integer
 * @returns {string}
 */
export function displayValue(v, t) {
  if (typeof v === 'string') return v;
  if (typeof v === 'number') return t && primName(t) === 'f64' ? rustFloat(v, 'display') : Number.isInteger(v) ? intText(v) : rustFloat(v, 'display');
  if (typeof v === 'boolean') return String(v);
  return JSON.stringify(encodeValue(v));
}

/** An integer in decimal, without an exponent. @param {number} n */
const intText = (n) => (Object.is(n, -0) ? '0' : BigInt(n).toString());

/**
 * The shortest round-trip digits of a finite, non-zero number and its decimal exponent: x = 0.d1d2d3... * 10^point.
 * The digits are those Rust (Grisu/Ryu shortest) and serde_json (ryu) print; JavaScript's own shortest
 * representation has the same digits.
 * @param {number} x @returns {{digits: string, point: number}}
 */
function shortest(x) {
  const m = /^(\d)(?:\.(\d+))?e([+-]\d+)$/.exec(Math.abs(x).toExponential());
  if (!m) throw new FnEvalError(`Cannot write the number ${x}`);
  const digits = (m[1] + (m[2] ?? '')).replace(/0+$/, '') || '0';
  return { digits, point: Number(m[3]) + 1 };
}

/**
 * An f64 as Rust writes it: `display` is `{}` (decimal, no exponent, no fraction for a whole number), `debug` is
 * `{:?}` (decimal with at least one fractional digit, exponential below 1e-4 and from 1e16 on: 1e16, 1.5e-7).
 * NaN and the infinities are NaN, inf and -inf.
 * @param {number} x @param {'display'|'debug'} mode @returns {string}
 */
export function rustFloat(x, mode) {
  if (Number.isNaN(x)) return 'NaN';
  if (!Number.isFinite(x)) return x > 0 ? 'inf' : '-inf';
  const sign = x < 0 || Object.is(x, -0) ? '-' : '';
  if (x === 0) return sign + (mode === 'debug' ? '0.0' : '0');
  const abs = Math.abs(x);
  const { digits, point } = shortest(x);
  if (mode === 'debug' && (abs < 1e-4 || abs >= 1e16)) {
    const exp = point - 1;
    return `${sign}${digits[0]}${digits.length > 1 ? `.${digits.slice(1)}` : ''}e${exp}`;
  }
  let text;
  if (point <= 0) text = `0.${'0'.repeat(-point)}${digits}`;
  else if (point >= digits.length) text = digits + '0'.repeat(point - digits.length) + (mode === 'debug' ? '.0' : '');
  else text = `${digits.slice(0, point)}.${digits.slice(point)}`;
  return sign + text;
}

/**
 * A number as serde_json writes it (ryu): an integer type in decimal; an f64 from 1e-5 up to but not including
 * 1e16 in decimal with at least one fractional digit (1.0, 0.00001, 123.45), any other in exponential form with no
 * plus sign (1e16, 1.5e-7, -2.5e300); a non-finite f64 is null.
 * @param {number} x @param {boolean} float @returns {string}
 */
export function jsonNumber(x, float) {
  if (!float) return intText(x);
  if (!Number.isFinite(x)) return 'null';
  const sign = x < 0 || Object.is(x, -0) ? '-' : '';
  if (x === 0) return `${sign}0.0`;
  const { digits, point } = shortest(x);
  // ryu's pretty format: k = point - digits.length is the exponent of the last digit.
  const length = digits.length;
  const k = point - length;
  if (k >= 0 && point <= 16) return `${sign}${digits}${'0'.repeat(k)}.0`;
  if (point > 0 && point <= 16) return `${sign}${digits.slice(0, point)}.${digits.slice(point)}`;
  if (point > -5 && point <= 0) return `${sign}0.${'0'.repeat(-point)}${digits}`;
  const exp = point - 1;
  return `${sign}${digits[0]}${length > 1 ? `.${digits.slice(1)}` : ''}e${exp}`;
}

/**
 * A string as a JSON string literal, escaped as serde_json escapes it: \" \\ \b \f \n \r \t, any other control
 * character below U+0020 as \u00XX (lower-case hexadecimal); everything else, U+007F and non-ASCII included, as it is.
 * @param {string} s @returns {string}
 */
export function jsonString(s) {
  let out = '"';
  for (const c of s) {
    const n = /** @type {number} */ (c.codePointAt(0));
    if (c === '"') out += '\\"';
    else if (c === '\\') out += '\\\\';
    else if (c === '\b') out += '\\b';
    else if (c === '\f') out += '\\f';
    else if (c === '\n') out += '\\n';
    else if (c === '\r') out += '\\r';
    else if (c === '\t') out += '\\t';
    else if (n < 0x20) out += `\\u00${n.toString(16).padStart(2, '0')}`;
    else out += c;
  }
  return `${out}"`;
}

/** Characters Rust's char::is_printable refuses (Cc, Cf, Cs, Co, Cn, Zl, Zp, and Zs but the space). */
const NOT_PRINTABLE = /[\p{Cc}\p{Cf}\p{Cs}\p{Co}\p{Cn}\p{Zl}\p{Zp}\p{Zs}]/u;
const GRAPHEME_EXTEND = /\p{Grapheme_Extend}/u;

/**
 * A string as Rust's `{:?}` writes it (str Debug): in double quotes, with \0 \t \r \n \\ \" escaped, a combining
 * mark (Grapheme_Extend) or a character that is not printable as \u{hex}; a single quote is not escaped.
 * @param {string} s @returns {string}
 */
export function rustDebugStr(s) {
  let out = '"';
  for (const c of s) {
    if (c === '\0') out += '\\0';
    else if (c === '\t') out += '\\t';
    else if (c === '\r') out += '\\r';
    else if (c === '\n') out += '\\n';
    else if (c === '\\') out += '\\\\';
    else if (c === '"') out += '\\"';
    else if (c !== ' ' && (GRAPHEME_EXTEND.test(c) || NOT_PRINTABLE.test(c))) out += `\\u{${/** @type {number} */ (c.codePointAt(0)).toString(16)}}`;
    else out += c;
  }
  return `${out}"`;
}

// Rust names, as specc gives them (crates/spec-compiler/src/naming.rs): a name is split into lower-case ASCII words
// at every character that is not an ASCII letter or digit, at a change from lower case or a digit to upper case,
// and before the last capital of an acronym followed by a lower-case letter; PascalCase for types and variants,
// snake_case for fields. self, Self, super and crate take a trailing _.
const UNRAWABLE = ['self', 'Self', 'super', 'crate'];

/** @param {string} name @returns {string[]} */
function rustWords(name) {
  /** @type {string[]} */
  const out = [];
  for (const run of name.split(/[^A-Za-z0-9]/)) {
    const chars = [...run];
    let word = '';
    chars.forEach((c, i) => {
      if (i > 0) {
        const prev = chars[i - 1], next = chars[i + 1];
        const lowerToUpper = /[a-z0-9]/.test(prev) && /[A-Z]/.test(c);
        const acronymEnd = /[A-Z]/.test(prev) && /[A-Z]/.test(c) && next !== undefined && /[a-z]/.test(next);
        if ((lowerToUpper || acronymEnd) && word) { out.push(word); word = ''; }
      }
      word += c.toLowerCase();
    });
    if (word) out.push(word);
  }
  return out;
}

/** @param {string} n */
const unraw = (n) => (UNRAWABLE.includes(n) ? `${n}_` : n);

/** The Rust PascalCase name of a type or variant (`tenant-mismatch` is TenantMismatch). @param {string} name */
export function rustPascal(name) {
  return unraw(rustWords(name).map((w) => w[0].toUpperCase() + w.slice(1)).join(''));
}

/** The Rust snake_case name of a field (`next-record` is next_record). @param {string} name */
export function rustSnake(name) {
  return unraw(rustWords(name).join('_'));
}

/**
 * Whether format's debug placeholder `{:?}` can write a value of this type: everything but json and bytes.
 * @param {FnType} t @returns {boolean}
 */
export function debuggable(t) {
  const n = primName(t);
  if (n === 'json' || n === 'bytes') return false;
  switch (t.k) {
    case 'list': case 'option': return debuggable(t.of);
    case 'map': return debuggable(t.key) && debuggable(t.value);
    case 'result': return debuggable(t.ok) && debuggable(t.err);
    default: return true;
  }
}

/**
 * A value as Rust's derived Debug (`{:?}`) writes the type specc generates for it: an id or scalar is a newtype
 * (`ObjectTypeId("note")`, `RecordId(3)`); an enum value or unit variant its PascalCase name; a newtype variant
 * `Name(x)`, a tuple variant `Name(a, b)`, a struct-like variant or a struct `Name { field: x, .. }` with snake_case
 * field names; a string in double quotes with Rust's escapes; an f64 as Rust's `{:?}` (1.0, 1e16); an option
 * Some(x) or None; a list [a, b]; a set {a, b}; a map {k: v}; a result Ok(x) or Err(e); unit (); a uuid hyphenated
 * without quotes. Struct fields are written in declaration order, set items and map keys in order.
 * @param {FnType} t @param {any} v @returns {string}
 */
export function debugValue(t, v) {
  /** @param {{name: string, type: FnType, optional: boolean}[]} fields @param {Record<string, any>} values */
  const named = (fields, values) => fields.map((f) => `${rustSnake(f.name)}: ${debugValue(f.optional && f.type.k !== 'option' ? { k: 'option', of: f.type } : f.type, values[f.name] ?? null)}`).join(', ');
  switch (t.k) {
    case 'prim': {
      if (t.name === 'unit') return '()';
      if (t.name === 'string') return rustDebugStr(String(v));
      if (t.name === 'uuid') return String(v);
      if (t.name === 'bool') return String(v);
      if (t.name === 'f64') return rustFloat(v, 'debug');
      if (typeof v === 'number') return Number.isInteger(v) ? intText(v) : rustFloat(v, 'debug');
      return String(v);
    }
    case 'alias': return `${rustPascal(t.id)}(${debugValue({ k: 'prim', name: t.repr }, v)})`;
    case 'enum': return rustPascal(String(v));
    case 'struct': return t.fields.length ? `${rustPascal(t.id)} { ${named(t.fields, v)} }` : rustPascal(t.id);
    case 'union': {
      const variant = t.variants.find((x) => x.name === v.variant);
      const name = rustPascal(v.variant);
      if (!variant || !variant.fields.length) return name;
      if (variant.newtype || variant.tuple) return `${name}(${variant.fields.map((f) => debugValue(f.type, v.fields[f.name])).join(', ')})`;
      return `${name} { ${named(variant.fields, v.fields)} }`;
    }
    case 'list': {
      const items = /** @type {any[]} */ (v).map((x) => debugValue(t.of, x)).join(', ');
      return t.set ? `{${items}}` : `[${items}]`;
    }
    case 'option': return v === null || v === undefined ? 'None' : `Some(${debugValue(t.of, v)})`;
    case 'map': return `{${[.../** @type {Map<any, any>} */ (v).keys()].sort(compareKeys).map((k) => `${debugValue(t.key, k)}: ${debugValue(t.value, v.get(k))}`).join(', ')}}`;
    case 'result': return v.variant === 'Ok' ? `Ok(${debugValue(t.ok, v.fields.value)})` : `Err(${debugValue(t.err, v.fields.error)})`;
    default:
      if (v === null || v === undefined) return 'None';
      if (v instanceof UnitValue) return '()';
      if (typeof v === 'string') return rustDebugStr(v);
      return String(v);
  }
}

/**
 * Whether format's JSON placeholder `{:json}` can write a value of this type: a string, a number, a bool, json, and
 * options and lists of these.
 * @param {FnType} t @returns {boolean}
 */
export function jsonWritable(t) {
  if (t.k === 'option' || t.k === 'list') return jsonWritable(t.of);
  if (t.k === 'unknown' || t.k === 'never') return true;
  const n = primName(t);
  return n !== undefined && n !== 'bytes' && n !== 'unit';
}

/**
 * A value as compact JSON text, as serde_json's to_string writes it: a string escaped (jsonString), an f64 as ryu
 * writes it (jsonNumber), an integer in decimal, a bool, null for an absent option; a list as an array; a json
 * value with its object keys in order (serde_json's default map is sorted) and its integral numbers as integers.
 * @param {FnType} t @param {any} v @returns {string}
 */
export function jsonText(t, v) {
  if (v === null || v === undefined) return 'null';
  if (t.k === 'option') return jsonText(t.of, v);
  if (t.k === 'list') return `[${/** @type {any[]} */ (v).map((x) => jsonText(t.of, x)).join(',')}]`;
  const n = primName(t);
  if (n === 'json' || n === undefined) {
    if (typeof v === 'string') return jsonString(v);
    if (typeof v === 'number') return jsonNumber(v, !Number.isInteger(v));
    if (typeof v === 'boolean') return String(v);
    if (Array.isArray(v)) return `[${v.map((x) => jsonText({ k: 'prim', name: 'json' }, x)).join(',')}]`;
    if (isObj(v)) return `{${Object.keys(v).sort(compareKeys).map((k) => `${jsonString(k)}:${jsonText({ k: 'prim', name: 'json' }, v[k])}`).join(',')}}`;
    return 'null';
  }
  if (typeof v === 'string') return jsonString(v);
  if (typeof v === 'boolean') return String(v);
  if (typeof v === 'number') return jsonNumber(v, n === 'f64' || (n === 'number' && !Number.isInteger(v)));
  return 'null';
}
