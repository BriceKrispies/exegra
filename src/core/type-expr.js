// Type strings of payload fields and contract inputs/outputs, such as `string`, `number`, `boolean`,
// `'a' | 'b'`, `string | null`, `string[]`. One small parser serves the static check of contract events
// (validate.js) and the check of a simulated trace (contract-trace.js).
//
// Anything the parser does not recognise (`Operation[]`, `{ok, hash}`, `number / string`) is an opaque
// atom: it only equals itself and any value fits it, so a type Exegra cannot read is never rejected.
// Pure: no DOM, no I/O.

/**
 * @typedef {{k:'string'|'number'|'boolean'|'null'|'any'}
 *   | {k:'lit', v:string|number|boolean}
 *   | {k:'array', of:Atom}
 *   | {k:'opaque', text:string}} Atom
 */

/**
 * Split on a separator that is outside quotes, brackets, braces, parentheses and the angle brackets of a generic
 * type (`map<K, map<K2, V>>`, `list<map<K, V>>`). A `>` closes an angle bracket only while one is open, so the
 * arrow of `(a) => b` is not one.
 * @param {string} s @param {string} sep @returns {string[]}
 */
export function splitTop(s, sep) {
  /** @type {string[]} */
  const parts = [];
  let depth = 0, angles = 0, quote = '', start = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s[i];
    if (quote) { if (c === quote) quote = ''; continue; }
    if (c === '"' || c === "'") quote = c;
    else if ('([{'.includes(c)) depth++;
    else if (')]}'.includes(c)) depth--;
    else if (c === '<') angles++;
    else if (c === '>' && angles > 0) angles--;
    else if (depth === 0 && angles === 0 && s.startsWith(sep, i)) { parts.push(s.slice(start, i)); start = i + sep.length; i += sep.length - 1; }
  }
  parts.push(s.slice(start));
  return parts.map((p) => p.trim());
}

/** @param {string} text @returns {Atom} */
function parseAtom(text) {
  if (text === 'string' || text === 'number' || text === 'boolean' || text === 'null') return { k: text };
  if (text === 'any' || text === 'unknown' || text === '') return { k: 'any' };
  if (text === 'true') return { k: 'lit', v: true };
  if (text === 'false') return { k: 'lit', v: false };
  if (/^-?\d+(\.\d+)?$/.test(text)) return { k: 'lit', v: Number(text) };
  const q = /^'([^']*)'$|^"([^"]*)"$/.exec(text);
  if (q) return { k: 'lit', v: q[1] ?? q[2] };
  if (text.endsWith('[]')) return { k: 'array', of: parseAtom(text.slice(0, -2).trim()) };
  return { k: 'opaque', text };
}

/**
 * Parse a type string into the atoms of its union. A missing or empty type is `any`.
 * @param {string|undefined|null} src
 * @returns {Atom[]}
 */
export function parseType(src) {
  if (typeof src !== 'string' || !src.trim()) return [{ k: 'any' }];
  return splitTop(src.trim(), '|').map(parseAtom);
}

/** @param {Atom} a @returns {string} */
function atomText(a) {
  if (a.k === 'lit') return typeof a.v === 'string' ? `'${a.v}'` : String(a.v);
  if (a.k === 'array') return `${atomText(a.of)}[]`;
  if (a.k === 'opaque') return a.text;
  return a.k;
}

/** @param {Atom[]} atoms @returns {string} */
export function typeText(atoms) { return atoms.map(atomText).join(' | '); }

/** @param {unknown} v @param {Atom} a @returns {boolean} */
function atomFits(v, a) {
  switch (a.k) {
    case 'any': case 'opaque': return true;
    case 'string': return typeof v === 'string';
    case 'number': return typeof v === 'number' && Number.isFinite(v);
    case 'boolean': return typeof v === 'boolean';
    case 'null': return v === null;
    case 'lit': return v === a.v;
    case 'array': return Array.isArray(v) && v.every((x) => atomFits(x, a.of));
    default: return true;
  }
}

/** Whether a value fits a type. @param {unknown} value @param {Atom[]} atoms @returns {boolean} */
export function valueFits(value, atoms) { return atoms.some((a) => atomFits(value, a)); }

/** @param {Atom} from @param {Atom} to @returns {boolean} */
function atomAssignable(from, to) {
  if (from.k === 'any' || to.k === 'any') return true;
  if (to.k === 'opaque') return from.k === 'opaque' && from.text === to.text;
  if (from.k === 'opaque') return false;
  if (from.k === 'lit') return to.k === 'lit' ? to.v === from.v : to.k === typeof from.v;
  if (from.k === 'array') return to.k === 'array' && atomAssignable(from.of, to.of);
  return from.k === to.k;
}

/**
 * Whether every value of type `from` is a value of type `to`.
 * @param {Atom[]} from @param {Atom[]} to @returns {boolean}
 */
export function typeAssignable(from, to) { return from.every((f) => to.some((t) => atomAssignable(f, t))); }

/** Describe a value in a request-log line. @param {unknown} v @returns {string} */
export function valueText(v) {
  const s = JSON.stringify(v);
  if (s === undefined) return String(v);
  return s.length > 48 ? `${s.slice(0, 45)}…` : s;
}
