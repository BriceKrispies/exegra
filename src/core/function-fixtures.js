// Example fixtures (WG-4963): values a specification declares once (section exampleFixtures, entity exampleFixture:
// {id, type, value, description?}) and function examples refer to, so that a tenant or a schema is not written out in
// every example. An argument, result or error of an example is either a JSON value or a reference
//   {"fixture": <id>}                              the fixture's value
//   {"fixture": <id>, "with": {"<path>": <value>}} the fixture's value with the value at each dotted path replaced
// Exegra resolves references before evaluating examples (src/core/function.js); a generator reads the same
// references (docs/model-and-format.md, "Example fixtures"). This module is the part that does not need the model:
// recognising a reference and applying an override to a JSON value along its type.

/** @typedef {import('./function-value.js').FnType} FnType */

/** @param {any} v */
const isObj = (v) => v !== null && typeof v === 'object' && !Array.isArray(v);

/** The failure of an override whose path does not lead into the value. */
export class OverrideError extends Error {}

/**
 * Whether an example value is a fixture reference: an object whose "fixture" is a string and whose other key, if
 * any, is "with". Any other object is a value of its own.
 * @param {any} v @returns {boolean}
 */
export function isFixtureRef(v) {
  return isObj(v) && typeof v.fixture === 'string' && Object.keys(v).every((k) => k === 'fixture' || k === 'with');
}

/**
 * The JSON value `json` of type `t` with the value at `segs` (a dotted path split at the dots) replaced. A path
 * goes through struct fields, map keys (the last segment may add a key), list indexes (decimal, in range) and
 * the variant name of a union value written {"Variant": content}; an option is looked through. The result is
 * a new value; the argument is not changed.
 * @param {any} json @param {FnType} t @param {string[]} segs @param {any} value @param {string} [at]
 * @returns {any}
 */
export function setAtPath(json, t, segs, value, at = '') {
  while (t.k === 'option') {
    if (segs.length && json === null) throw new OverrideError(`there is no value at "${at}" to go into`);
    t = t.of;
  }
  if (!segs.length) return value;
  const [seg, ...rest] = segs;
  const here = at ? `${at}.${seg}` : seg;
  /** @param {any} child @param {FnType} ct */
  const into = (child, ct) => {
    if (rest.length && (child === undefined || child === null)) throw new OverrideError(`there is no value at "${here}" to go into`);
    return setAtPath(child === undefined ? null : child, ct, rest, value, here);
  };
  switch (t.k) {
    case 'struct': {
      const f = t.fields.find((x) => x.name === seg);
      if (!f) throw new OverrideError(`${t.id} has no field "${seg}"${at ? ` (at "${at}")` : ''}`);
      if (json !== null && !isObj(json)) throw new OverrideError(`the value at "${at}" is not a ${t.id} object`);
      return { ...(json ?? {}), [seg]: into(json?.[seg], f.type) };
    }
    case 'map': {
      if (!isObj(json)) throw new OverrideError(`the value at "${at}" is not a map`);
      if (rest.length && !Object.hasOwn(json, seg)) throw new OverrideError(`the map at "${at}" has no key "${seg}"`);
      return { ...json, [seg]: into(json[seg], t.value) };
    }
    case 'list': {
      if (!Array.isArray(json)) throw new OverrideError(`the value at "${at}" is not a list`);
      if (!/^\d+$/.test(seg) || Number(seg) >= json.length) throw new OverrideError(`"${seg}" is not an index of the list at "${at}" (length ${json.length})`);
      const out = [...json];
      out[Number(seg)] = into(json[Number(seg)], t.of);
      return out;
    }
    case 'union': {
      if (!isObj(json) || Object.keys(json).length !== 1) throw new OverrideError(`the value at "${at}" is not a ${t.id} value with content to go into`);
      const name = Object.keys(json)[0];
      if (seg !== name) throw new OverrideError(`the value at "${at}" is the variant ${name} of ${t.id}, not "${seg}"`);
      const v = t.variants.find((x) => x.name === name);
      if (!v) throw new OverrideError(`${t.id} has no variant "${name}"`);
      const ct = v.newtype ? v.fields[0].type : { k: /** @type {const} */ ('struct'), id: `${t.id}.${name}`, fields: v.fields };
      return { [name]: into(json[name], ct) };
    }
    default:
      throw new OverrideError(`the value at "${at}" is not a struct, map, list or union, so "${seg}" does not lead into it`);
  }
}
