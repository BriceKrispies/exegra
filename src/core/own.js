// Own-property lookup: a spec-supplied key such as "constructor" or "toString"
// must never resolve to something inherited from Object.prototype.

/**
 * @template T
 * @param {Record<string, T>|undefined|null} obj @param {string} key
 * @returns {T|undefined}
 */
export function own(obj, key) {
  return obj != null && typeof key === 'string' && Object.hasOwn(obj, key) ? obj[key] : undefined;
}
