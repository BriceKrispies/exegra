// Source text -> canonical semantic model.
//
// The JSONC source text is the serialized authority. This module is its text layer: it parses
// the JSONC (comments, trailing commas, syntax errors) and maps locations to lines and columns.
// The model itself is derived by the verified kernel in Lean (formal/Exegra/Model.lean, function
// model.derive at the call boundary src/core/lean.js): the meta-model (src/core/metamodel.json)
// extended by the specification's own `vocabulary` section, every entity with the JSON path where
// it is declared, every reference and expression, the structural diagnostics and the semantic
// hash. Anything the meta-model does not describe is reported, never dropped silently.
//
// The document goes to Lean as written: every object as {"o": [[key, value], ...]} with its
// members in source order and repeated keys kept. Lean reports every location as a raw path (the
// member and item indices from the root, written "3.0.12") and a part (the node, the key of the
// last member, or the node's first character); this module turns raw paths into source locations.
//
// The Lean core must be loaded: in Node the first call loads it; in a browser or worker,
// await initLean() (src/core/lean.js) first, as src/app/main.js does before opening a project.

import { parseTree, getNodeValue, printParseErrorCode } from 'jsonc-parser';
import { cachedStage } from './derivation-cache.js';
import metamodel from './metamodel.json' with { type: 'json' };
import { CLAIM_METHODS } from './claim-methods.js';
import { callText } from './lean.js';

/** @typedef {import('./types.js').Model} Model */
/** @typedef {import('./types.js').Entity} Entity */
/** @typedef {import('./types.js').Diagnostic} Diagnostic */
/** @typedef {import('./types.js').Loc} Loc */
/** @typedef {import('jsonc-parser').Node} JsonNode */

export const SCHEMA_VERSION = metamodel.schemaVersion;
export const BASE_METAMODEL = metamodel;
/** A ref whose allowed kinds contain this may point to an entity of any kind, including kinds a specification declares. */
export const ANY_KIND = '*';
/** The arguments of model.derive after the document. */
const KERNEL_ARGS = `,"metamodel":${JSON.stringify(metamodel)},"methods":${JSON.stringify(CLAIM_METHODS)}}`;

/** @param {string} text */
function lineIndex(text) {
  const starts = [0];
  for (let i = 0; i < text.length; i++) if (text.charCodeAt(i) === 10) starts.push(i + 1);
  return starts;
}

/**
 * @param {number[]} starts @param {number} offset @param {number} length
 * @returns {Loc}
 */
function locOf(starts, offset, length) {
  let lo = 0, hi = starts.length - 1;
  while (lo < hi) {
    const mid = (lo + hi + 1) >> 1;
    if (starts[mid] <= offset) lo = mid; else hi = mid - 1;
  }
  return { offset, length, line: lo + 1, column: offset - starts[lo] + 1 };
}

const SURROGATE = /[\uD800-\uDFFF]/;
const LONE_SURROGATE = /[\uD800-\uDBFF](?![\uDC00-\uDFFF])|(?<![\uD800-\uDBFF])[\uDC00-\uDFFF]/g;

/**
 * A string as JSON text, with a lone surrogate (which a Lean string cannot hold) replaced by U+FFFD.
 * @param {string} s
 */
const quote = (s) => JSON.stringify(SURROGATE.test(s) ? s.replace(LONE_SURROGATE, '�') : s);

/** Whether the last encoded document has a number JSON text cannot carry back (-0, beyond the double range). */
let unusualNumbers = false;

/**
 * The document as Lean reads it (Exegra.Model.decode): every object as {"o": [[key, value], ...]}.
 * @param {JsonNode} node @param {string[]} out
 */
function encode(node, out) {
  switch (node.type) {
    case 'object': {
      out.push('{"o":[');
      const props = node.children ?? [];
      for (let i = 0; i < props.length; i++) {
        const [k, v] = /** @type {JsonNode[]} */ (props[i].children);
        if (i) out.push(',');
        out.push('[', quote(k.value), ',');
        encode(v, out);
        out.push(']');
      }
      out.push(']}');
      return;
    }
    case 'array': {
      out.push('[');
      const items = node.children ?? [];
      for (let i = 0; i < items.length; i++) {
        if (i) out.push(',');
        encode(items[i], out);
      }
      out.push(']');
      return;
    }
    case 'string': out.push(quote(node.value)); return;
    case 'number': {
      const x = node.value;
      if (!Number.isFinite(x) || Object.is(x, -0)) unusualNumbers = true;
      out.push(Number.isFinite(x) ? (Object.is(x, -0) ? '-0' : JSON.stringify(x)) : (x > 0 ? '1e999' : '-1e999'));
      return;
    }
    case 'boolean': out.push(node.value ? 'true' : 'false'); return;
    default: out.push('null');
  }
}

/**
 * A JSON value with every object made prototype-free, as jsonc-parser's getNodeValue builds them,
 * so that a spec-supplied key such as "constructor" never reads something inherited.
 * @param {any} v @returns {any}
 */
function bare(v) {
  if (Array.isArray(v)) {
    for (let i = 0; i < v.length; i++) v[i] = bare(v[i]);
    return v;
  }
  if (v === null || typeof v !== 'object') return v;
  const o = Object.create(null);
  for (const k of Object.keys(v)) o[k] = bare(v[k]);
  return o;
}

/**
 * Parse specification source into a semantic model.
 * `model` is null only when the text is not syntactically usable.
 * Structural diagnostics are included; semantic rules live in validate.js.
 * @param {string} text
 * @returns {{model: Model|null, diagnostics: Diagnostic[]}}
 */
export function parseSpec(text) {
  return cachedStage('parse', text, () => deriveSpec(text), (r) => r.model !== null);
}

/** parseSpec without the persistent cache. @param {string} text @returns {{model: Model|null, diagnostics: Diagnostic[]}} */
function deriveSpec(text) {
  /** @type {Diagnostic[]} */
  const diagnostics = [];
  const starts = lineIndex(text);
  /** @type {import('jsonc-parser').ParseError[]} */
  const errors = [];
  const root = parseTree(text, errors, { allowTrailingComma: true, disallowComments: false });
  for (const e of errors) {
    diagnostics.push({ code: 'syntax.' + printParseErrorCode(e.error), severity: 'error', message: `Syntax error: ${humanize(printParseErrorCode(e.error))}.`, loc: locOf(starts, e.offset, Math.max(1, e.length)) });
  }
  if (errors.length || !root) {
    if (!errors.length) diagnostics.push({ code: 'syntax.empty', severity: 'error', message: 'The specification is empty.', loc: locOf(starts, 0, 0) });
    return { model: null, diagnostics };
  }

  /** @type {string[]} */
  const parts = ['{"spec":'];
  unusualNumbers = false;
  encode(root, parts);
  parts.push(KERNEL_ARGS);
  const r = callText('model.derive', parts.join(''));
  if (!r.ok) throw new Error(`The Lean kernel could not derive the model: ${r.error}`);
  const out = JSON.parse(r.text);

  /**
   * The node at a raw path and, when the path ends in an object member, that member's key.
   * @param {string} at @returns {[JsonNode, JsonNode|null]}
   */
  const walk = (at) => {
    let n = /** @type {JsonNode} */ (root);
    /** @type {JsonNode|null} */
    let key = null;
    if (at === '') return [n, key];
    for (const s of at.split('.')) {
      const c = /** @type {JsonNode[]} */ (n.children)[Number(s)];
      if (n.type === 'object') {
        key = /** @type {JsonNode[]} */ (c.children)[0];
        n = /** @type {JsonNode[]} */ (c.children)[1];
      } else {
        key = null;
        n = c;
      }
    }
    return [n, key];
  };
  /**
   * The source location of a raw path and part.
   * @param {string} at @param {string} [part] 'node', 'key' (of the last member) or 'start'
   * @returns {Loc}
   */
  const locate = (at, part = 'node') => {
    const [n, key] = walk(at);
    if (part === 'key' && key) return locOf(starts, key.offset, key.length);
    if (part === 'start') return locOf(starts, n.offset, 1);
    return locOf(starts, n.offset, n.length);
  };

  for (const d of out.diagnostics) {
    const message = d.lineOf !== undefined ? `${d.message}${locate(d.lineOf).line}${d.messageAfter}` : d.message;
    /** @type {Diagnostic} */
    const diag = { code: d.code, severity: d.severity, message, loc: locate(d.at, d.part) };
    if (d.path !== undefined) diag.path = d.path;
    if (d.entityId !== undefined) diag.entityId = d.entityId;
    diagnostics.push(diag);
  }
  const m = out.model;
  if (!m) return { model: null, diagnostics };

  // Lean's data is the document's value at each entity; the JSON reply writes -0 as 0 and an infinite
  // number as null, so a document with such a number takes the values from the syntax tree instead.
  /** @param {string} at @param {any} data */
  const valueAt = (at, data) => (unusualNumbers ? getNodeValue(walk(at)[0]) : bare(data));
  // getNodeValue of the vocabulary section when there is one (prototype-free), else a plain {}.
  const vocabProp = [...(root.children ?? [])].reverse().find((p) => p.children?.[0]?.value === 'vocabulary');
  const vocabulary = !vocabProp ? {} : unusualNumbers ? getNodeValue(/** @type {JsonNode[]} */ (vocabProp.children)[1]) : bare(m.vocabulary);

  /** @type {Model} */
  const model = {
    schemaVersion: m.schemaVersion,
    system: /** @type {any} */ (null),
    entities: new Map(),
    byKind: {},
    refs: [],
    exprs: [],
    meta: m.meta,
    vocabulary,
    semanticHash: m.semanticHash,
  };
  for (const kind of m.kinds) model.byKind[kind] = [];
  for (const e of m.entities) {
    /** @type {Entity} */
    const entity = { id: e.id, kind: e.kind, data: valueAt(e.at, e.data), owner: e.owner, path: e.path, loc: locate(e.at) };
    model.entities.set(e.id, entity);
    model.byKind[e.kind].push(entity);
  }
  model.system = model.byKind.system?.[0] ?? null;
  model.refs = m.refs.map((/** @type {any} */ x) => ({ from: x.from, path: x.path, target: x.target, allowed: x.allowed, loc: locate(x.at) }));
  model.exprs = m.exprs.map((/** @type {any} */ x) => ({ owner: x.owner, path: x.path, src: x.src, loc: locate(x.at) }));
  return { model, diagnostics };
}

/** @param {string} code */
function humanize(code) {
  return code.replace(/([a-z])([A-Z])/g, '$1 $2').toLowerCase();
}
